//! The machine: frames on a stack of their own, and one operand stack.
//!
//! Nothing runs on the host's stack, so a deep recursion is as deep as
//! memory allows, and a continuation is data: the frames from a `handle`'s
//! body to the operation, and their operands. Resuming it puts copies of
//! them back on top of the stack.

use std::cell::RefCell;
use std::rc::Rc;

use tauto_nir::{Arith, Cmp, Width};
use tauto_rt::messages;

use crate::builtins::{self, Out};
use std::sync::mpsc::{Receiver, Sender};

use crate::code::{Capture, Op, Pat, PrimOp, Program, Q, UnaryOp};
use crate::host::Host;
use crate::hostcall::Reply;
use crate::value::{
    Answer, Closure, Data, Env, Error, Path, Pending, PendingState, Place, R, Root, Signal, Step,
    TOO_LARGE, Value, equal, fail, show, temp_ref,
};

#[derive(Clone)]
pub struct Frame {
    code: u32,
    pc: u32,
    env: Env,
    base: usize,
    kind: Kind,
}

#[derive(Clone)]
enum Kind {
    /// A function's or closure's frame; `inst` for a function.
    Root(Option<u32>),
    /// A `handle`'s body: its arms answer what it performs while `active`.
    /// `site` holds the locals around the `handle`, which the arms borrow.
    Body {
        handle: u32,
        site: Env,
        active: bool,
    },
    /// A `direct` arm, running on top of the operation: the frames from it
    /// down to its handler's body (`dist` of them below it) answer nothing.
    Direct {
        dist: usize,
    },
    Arm,
    /// A `budget`'s body: `left` steps (or, for a memory budget, the count
    /// of cells past which it has run out); `None` is no limit.
    Budget {
        memory: bool,
        left: Option<i128>,
    },
}

/// A continuation: frames and their operands, with bases from the first.
pub struct Cont {
    frames: Vec<Frame>,
    stack: Vec<Value>,
    /// It resumes at most once: a run of it does not copy the locals.
    once: bool,
}

/// A task that is not running: its frames and operands, the signal it
/// waits for, and the pending its result goes to (none for the program's
/// top level).
struct Task {
    frames: Vec<Frame>,
    stack: Vec<Value>,
    wait: Option<Rc<Signal>>,
    result: Option<Rc<Pending>>,
    /// It asked whether this is ready, and gave the others a turn.
    asked: Option<Rc<Pending>>,
    job: Option<u64>,
}

pub struct Machine<'a> {
    p: &'a Program,
    frames: Vec<Frame>,
    stack: Vec<Value>,
    /// The tasks that do not run now, in the order they get a turn.
    tasks: std::collections::VecDeque<Task>,
    /// Where the running task's result goes; none for the top level.
    result: Option<Rc<Pending>>,
    switched: bool,
    pub timers: Vec<Rc<Pending>>,
    /// The requests of the host that have not answered, the replies that
    /// have, and where they come.
    jobs: std::collections::HashMap<u64, Rc<Signal>>,
    replies: std::collections::HashMap<u64, Reply>,
    next_job: u64,
    channel: (Sender<(u64, Reply)>, Receiver<(u64, Reply)>),
    fuel: u64,
    cells: i128,
    /// The cells the run may make in all; `None` is no limit.
    pub max_cells: Option<i128>,
    pub host: &'a mut dyn Host,
    pub known: builtins::Known,
    /// Each mutex whose content a task took, and where that task's result
    /// goes: if the task fails first, the mutex is poisoned.
    taken: Vec<(Rc<RefCell<crate::value::MutexState>>, Rc<Pending>)>,
}

thread_local! {
    /// The signals this thread's run registered with `Os::on_shutdown`:
    /// only these keep the run waiting for a request to end it, and they
    /// are forgotten when the run ends, so a later run in the same process
    /// neither waits for them nor sees them raised.
    pub(crate) static OUTSIDE: RefCell<Vec<tauto_rt::signal::Signal>> =
        const { RefCell::new(Vec::new()) };
}

fn forget_outside() {
    for s in OUTSIDE.with(|o| std::mem::take(&mut *o.borrow_mut())) {
        tauto_rt::shutdown::forget(&s);
    }
}

impl Drop for Machine<'_> {
    fn drop(&mut self) {
        forget_outside();
    }
}

/// The failure of a run that made more cells than `Machine::max_cells`.
pub const MEMORY_LIMIT: &str = "the run made more values than its host allows";

/// The most frames of calls that nest, one inside another, that a run keeps.
/// A recursion that does not end stops here with [`TOO_DEEP`] rather than
/// running the host out of memory or running out its whole step limit.
pub const MAX_FRAMES: usize = 1 << 21;

/// What a run says when its calls nest deeper than [`MAX_FRAMES`]; the
/// toolchain says it as `eval-too-deep` in the user's language.
pub const TOO_DEEP: &str = "the calls nest too deep";

fn new_env(n: u32) -> Env {
    Rc::new(RefCell::new(vec![Value::Unit; n as usize]))
}

impl<'a> Machine<'a> {
    pub fn new(p: &'a Program, host: &'a mut dyn Host, fuel: u64) -> Self {
        Machine {
            p,
            frames: Vec::new(),
            stack: Vec::new(),
            tasks: Default::default(),
            result: None,
            switched: false,
            timers: Vec::new(),
            jobs: Default::default(),
            replies: Default::default(),
            next_job: 0,
            channel: std::sync::mpsc::channel(),
            fuel,
            cells: 0,
            max_cells: None,
            host,
            known: builtins::Known::new(p),
            taken: Vec::new(),
        }
    }

    pub fn fuel_left(&self) -> u64 {
        self.fuel
    }

    pub fn cells_made(&self) -> i128 {
        self.cells
    }

    /// Calls function instance `inst` with `args`, runs every task it
    /// starts to its end, and gives what the call answered.
    pub fn run_fn(&mut self, inst: u32, args: Vec<Value>) -> R<Value> {
        self.call_value(Value::Fn(inst), args)?;
        let mut answer = None;
        loop {
            let v = match self.run(0) {
                Ok(v) => v,
                // A runtime error in a task ends that task only.
                Err(Error::Runtime(m)) if self.result.is_some() => {
                    self.fail_task(m);
                    if !self.next_task()? {
                        return fail(messages::DEADLOCK);
                    }
                    continue;
                }
                Err(e) => return Err(e),
            };
            if self.switched {
                self.switched = false;
            } else {
                match self.result.take() {
                    None => answer = Some(v),
                    Some(p) => p.finish(v),
                }
            }
            if !self.next_task()? {
                return match answer {
                    Some(v) => Ok(v),
                    None => fail(messages::DEADLOCK),
                };
            }
        }
    }

    pub fn run_top(&mut self) -> R<Value> {
        let Some(top) = self.p.top else {
            return Ok(Value::Unit);
        };
        self.call_value(Value::Fn(top), Vec::new())?;
        let mut top_done = false;
        loop {
            let v = match self.run(0) {
                Ok(v) => v,
                // A runtime error in a task ends that task only.
                Err(Error::Runtime(m)) if self.result.is_some() => {
                    self.fail_task(m);
                    if !self.next_task()? {
                        return fail(messages::DEADLOCK);
                    }
                    continue;
                }
                Err(e) => return Err(e),
            };
            if self.switched {
                self.switched = false;
            } else {
                match self.result.take() {
                    None => top_done = true,
                    Some(p) => p.finish(v),
                }
            }
            if !self.next_task()? {
                if top_done {
                    return Ok(Value::Unit);
                }
                return fail(messages::DEADLOCK);
            }
        }
    }

    /// Notes that the running task took the content of `mx`.
    pub fn took(&mut self, mx: &Rc<RefCell<crate::value::MutexState>>) {
        self.taken.retain(|(w, _)| !Rc::ptr_eq(w, mx));
        if let Some(p) = &self.result {
            self.taken.push((mx.clone(), p.clone()));
        }
    }

    /// Ends the running task with runtime error `m`: the host hears of it at
    /// once, whoever takes its result fails with it, and the mutexes whose content it held are poisoned, waking those waiting
    /// on them to fail.
    fn fail_task(&mut self, m: String) {
        let p = self.result.take().expect("a task runs");
        let mut held = Vec::new();
        self.taken.retain(|(mx, t)| {
            if Rc::ptr_eq(t, &p) {
                held.push(mx.clone());
                false
            } else {
                true
            }
        });
        for mx in held {
            let mut mx = mx.borrow_mut();
            if mx.value.is_none() {
                mx.poisoned = true;
                for s in mx.waiting.drain(..) {
                    s.raise();
                }
            }
        }
        // Its guards are dropped with its frames, and give nothing back to
        // a poisoned mutex.
        self.frames.clear();
        self.stack.clear();
        self.switched = false;
        *p.state.borrow_mut() = PendingState::Failed(m.clone());
        p.signal.raise();
        self.host.stderr(&format!("a task failed: {m}\n"));
    }

    /// Puts the running task aside, waiting for `wait` if given; with
    /// `front`, it is the next to run.
    fn park(&mut self, wait: Option<Rc<Signal>>, asked: Option<Rc<Pending>>, front: bool) {
        let t = Task {
            frames: std::mem::take(&mut self.frames),
            stack: std::mem::take(&mut self.stack),
            wait,
            result: self.result.take(),
            asked,
            job: None,
        };
        if front {
            self.tasks.push_front(t);
        } else {
            self.tasks.push_back(t);
        }
    }

    /// Runs the next task that may run, after the sleep that ends first if
    /// every task waits; false when none can.
    fn next_task(&mut self) -> R<bool> {
        loop {
            while let Ok((id, reply)) = self.channel.1.try_recv() {
                self.replied(id, reply)?;
            }
            let at = self.tasks.iter().position(|t| {
                t.wait.as_ref().is_none_or(|s| s.is_raised())
                    && t.asked.as_ref().is_none_or(|_| true)
            });
            if let Some(i) = at {
                let t = self.tasks.remove(i).unwrap();
                self.frames = t.frames;
                self.stack = t.stack;
                self.result = t.result;
                if let Some(p) = t.asked {
                    self.stack.push(Value::Bool(p.ready()));
                }
                if let Some(id) = t.job {
                    let reply = self.replies.remove(&id).expect("a reply");
                    let v = reply.value(&self.known);
                    self.stack.push(v);
                }
                return Ok(true);
            }
            // Nothing waits: neither a timer nor a request to end the run
            // could let anything run.
            if self.tasks.is_empty() && self.jobs.is_empty() {
                return Ok(false);
            }
            // A timer that has run out raises what its task waits for: that
            // task can run now, though none could a moment ago.
            let timers = self.timers.len();
            self.timers.retain(|p| !p.ready());
            if self.timers.len() < timers {
                continue;
            }
            let first = self
                .timers
                .iter()
                .filter_map(|p| match &*p.state.borrow() {
                    PendingState::Timer(at) => Some(*at),
                    _ => None,
                })
                .min();
            // A request to end the run may still raise what a task waits for.
            tauto_rt::shutdown::poll();
            let outside = OUTSIDE.with(|o| o.borrow().iter().any(|s| !s.is_raised()));
            let first = match (first, outside) {
                (None, true) => {
                    Some(std::time::Instant::now() + std::time::Duration::from_millis(10))
                }
                (f, _) => f,
            };
            if self.jobs.is_empty() {
                let Some(first) = first else {
                    return Ok(false);
                };
                let now = std::time::Instant::now();
                if first > now {
                    std::thread::sleep(first - now);
                }
            } else {
                // A reply, or the end of the first sleep.
                let got = match first {
                    Some(at) => self
                        .channel
                        .1
                        .recv_timeout(at.saturating_duration_since(std::time::Instant::now()))
                        .ok(),
                    None => self.channel.1.recv().ok(),
                };
                if let Some((id, reply)) = got {
                    self.replied(id, reply)?;
                }
            }
            self.timers.retain(|p| !p.ready());
        }
    }

    fn replied(&mut self, id: u64, reply: Reply) -> R<()> {
        if let Reply::Fail(message) = reply {
            return fail(message);
        }
        if let Some(s) = self.jobs.remove(&id) {
            s.raise();
        }
        self.replies.insert(id, reply);
        Ok(())
    }

    /// Starts a request of the host; the running task waits for its reply.
    fn request(&mut self, job: crate::hostcall::Job) {
        let id = self.next_job;
        self.next_job += 1;
        let s = Rc::new(Signal::default());
        self.jobs.insert(id, s.clone());
        crate::hostcall::start(job, id, self.channel.0.clone());
        self.park(Some(s), None, false);
        if let Some(t) = self.tasks.back_mut() {
            t.job = Some(id);
        }
        self.switched = true;
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().expect("an operand")
    }

    fn pop_n(&mut self, n: usize) -> Vec<Value> {
        let at = self.stack.len() - n;
        self.stack.split_off(at)
    }

    fn tick(&mut self) -> R<()> {
        if self.fuel == 0 {
            return fail(messages::STEP_LIMIT);
        }
        if self.max_cells.is_some_and(|n| self.cells > n) {
            return fail(MEMORY_LIMIT);
        }
        self.fuel -= 1;
        Ok(())
    }

    /// Pushes the frame of a call; its value lands where `f` was.
    fn call_value(&mut self, f: Value, args: Vec<Value>) -> R<()> {
        if self.frames.len() >= MAX_FRAMES && matches!(f, Value::Fn(_) | Value::Closure(_)) {
            return fail(TOO_DEEP);
        }
        match f {
            Value::Fn(inst) => {
                let code = &self.p.codes[self.p.fns[inst as usize] as usize];
                let env = new_env(code.slots);
                {
                    let mut slots = env.borrow_mut();
                    for (s, a) in code.params.iter().zip(args) {
                        slots[*s as usize] = a;
                    }
                }
                self.frames.push(Frame {
                    code: self.p.fns[inst as usize],
                    pc: 0,
                    env,
                    base: self.stack.len(),
                    kind: Kind::Root(Some(inst)),
                });
            }
            Value::Closure(c) => {
                let code = &self.p.codes[c.code as usize];
                let env = new_env(code.slots);
                {
                    let mut slots = env.borrow_mut();
                    for (s, v) in &c.captures {
                        slots[*s as usize] = v.clone();
                    }
                    for (s, a) in code.params.iter().zip(args) {
                        slots[*s as usize] = a;
                    }
                }
                self.frames.push(Frame {
                    code: c.code,
                    pc: 0,
                    env,
                    base: self.stack.len(),
                    kind: Kind::Root(None),
                });
            }
            Value::Cont(k) => {
                let start = self.stack.len();
                self.stack.extend(k.stack.iter().cloned());
                // Each run of a continuation that resumes more than once
                // has its own copy of the locals bound inside it; the
                // locals around the `handle` stay shared.
                let mut copies: Vec<(Env, Env)> = Vec::new();
                for f in &k.frames {
                    let mut f = f.clone();
                    f.base += start;
                    if !k.once {
                        let found = copies.iter().find(|(old, _)| Rc::ptr_eq(old, &f.env));
                        f.env = match found {
                            Some((_, new)) => new.clone(),
                            None => {
                                let new = Rc::new(RefCell::new(f.env.borrow().clone()));
                                copies.push((f.env.clone(), new.clone()));
                                new
                            }
                        };
                    }
                    self.frames.push(f);
                }
                self.stack
                    .push(args.into_iter().next().unwrap_or(Value::Unit));
            }
            Value::Ref(p) => return self.call_value(p.get()?, args),
            v => return fail(format!("internal: cannot call {}", v.kind())),
        }
        Ok(())
    }

    /// Leaves the frames from `j` and the operands from `start`, as an arm
    /// that does not resume leaves them: the operands are dropped last
    /// pushed first, then each frame's locals last defined first, so that
    /// what a host value's drop shows is the order the backends drop in.
    fn discard(&mut self, j: usize, start: usize) {
        for v in self.stack.split_off(start).into_iter().rev() {
            drop(v);
        }
        for f in self.frames.split_off(j).into_iter().rev() {
            if Rc::strong_count(&f.env) == 1 {
                let slots = std::mem::take(&mut *f.env.borrow_mut());
                for v in slots.into_iter().rev() {
                    drop(v);
                }
            }
        }
    }

    fn ret(&mut self, v: Value) {
        let f = self.frames.pop().expect("a frame");
        self.stack.truncate(f.base);
        self.stack.push(v);
    }

    /// Runs until the frames are down to `depth`; the value is the last
    /// one returned.
    fn run(&mut self, depth: usize) -> R<Value> {
        let p = self.p;
        while self.frames.len() > depth && !self.switched {
            let fi = self.frames.len() - 1;
            let (code, pc) = {
                let f = &mut self.frames[fi];
                let pc = f.pc;
                f.pc += 1;
                (f.code, pc)
            };
            let op = p.codes[code as usize].ops[pc as usize];
            match op {
                Op::Const(i) => self.stack.push(p.consts[i as usize].clone()),
                Op::Unit => self.stack.push(Value::Unit),
                Op::Load {
                    slot,
                    deref,
                    take,
                    indirect,
                } => {
                    let env = self.frames[fi].env.clone();
                    let v = if indirect {
                        let r = env.borrow()[slot as usize].clone();
                        match r {
                            Value::Ref(place) => {
                                let v = shallow(&place)?;
                                if take {
                                    place.set(Value::Moved)?;
                                }
                                v
                            }
                            v => v,
                        }
                    } else if take {
                        std::mem::replace(&mut env.borrow_mut()[slot as usize], Value::Moved)
                    } else {
                        env.borrow()[slot as usize].clone()
                    };
                    let v = if deref { v.get()? } else { v };
                    self.stack.push(v);
                }
                Op::Clear { slot } => {
                    let old = std::mem::replace(
                        &mut self.frames[fi].env.borrow_mut()[slot as usize],
                        Value::Moved,
                    );
                    drop(old);
                }
                Op::Define { slot, shared } => {
                    let v = self.pop();
                    let v = if shared {
                        Value::Ref(Rc::new(Place::new(
                            Root::Cell(Rc::new(RefCell::new(v))),
                            Path::default(),
                        )))
                    } else {
                        v
                    };
                    self.frames[fi].env.borrow_mut()[slot as usize] = v;
                }
                Op::Assign {
                    slot,
                    path,
                    through,
                    indirect,
                } => {
                    let v = self.pop();
                    let path = &p.paths[path as usize];
                    let env = self.frames[fi].env.clone();
                    let held = env.borrow()[slot as usize].clone();
                    match held {
                        Value::Ref(inner) if through || indirect => {
                            let q = Place::new(clone_root(&inner.root), inner.path.extended(path));
                            q.set(v)?;
                        }
                        _ if path.is_empty() => env.borrow_mut()[slot as usize] = v,
                        _ => Place::new(Root::Slot(env, slot), Path::of(path)).set(v)?,
                    }
                }
                Op::Borrow {
                    slot,
                    path,
                    through,
                    indirect,
                } => {
                    let env = self.frames[fi].env.clone();
                    let path = &p.paths[path as usize];
                    let held = env.borrow()[slot as usize].clone();
                    let place = match held {
                        Value::Ref(inner) if indirect || through => inner.further(path),
                        _ => Place::new(Root::Slot(env, slot), Path::of(path)),
                    };
                    self.stack.push(Value::Ref(Rc::new(place)));
                }
                Op::Pop => {
                    self.pop();
                }
                Op::Jump(t) => self.frames[fi].pc = t,
                Op::JumpIfNot(t) => {
                    if !self.pop().as_bool()? {
                        self.frames[fi].pc = t;
                    }
                }
                Op::Call { argc, ticked } => {
                    if ticked {
                        self.tick()?;
                    }
                    let args = self.pop_n(argc as usize);
                    let f = self.pop();
                    let mut native = None;
                    if let Value::Fn(inst) = f
                        && let Some(n) = &p.native
                        && n.has(inst)
                        && self.budgets().is_empty()
                    {
                        match n.call(inst, &args, &mut self.fuel) {
                            crate::native::Answer::Done(v) => native = Some(v),
                            crate::native::Answer::Fail(m) => return fail(m),
                            crate::native::Answer::Fallback => {}
                        }
                    }
                    match native {
                        Some(v) => self.stack.push(v),
                        None => self.call_value(f, args)?,
                    }
                }
                Op::TailSelf { inst, argc } => {
                    let args = self.pop_n(argc as usize);
                    let f = self.pop();
                    let reuse = matches!(self.frames[fi].kind, Kind::Root(Some(i)) if i == inst);
                    if reuse {
                        let code = &p.codes[self.frames[fi].code as usize];
                        let env = new_env(code.slots);
                        {
                            let mut slots = env.borrow_mut();
                            for (s, a) in code.params.iter().zip(args) {
                                slots[*s as usize] = a;
                            }
                        }
                        let base = self.frames[fi].base;
                        self.stack.truncate(base);
                        let fr = &mut self.frames[fi];
                        fr.env = env;
                        fr.pc = 0;
                    } else {
                        self.call_value(f, args)?;
                    }
                }
                Op::Builtin { name, argc } => {
                    let args = self.pop_n(argc as usize);
                    let name = &p.names[name as usize];
                    if let Some(answer) = self.host.builtin(p, name, &args) {
                        self.stack.push(answer?);
                        continue;
                    }
                    match builtins::call(self, name, args)? {
                        Out::Value(v) => self.stack.push(v),
                        Out::Perform(op) => self.perform(op, Q::Zero, Vec::new())?,
                        Out::Spawn(f, pending) => {
                            // The task runs at once, until it waits; then
                            // the spawner goes on.
                            self.stack.push(Value::Pending(pending.clone()));
                            self.park(None, None, true);
                            self.result = Some(pending);
                            self.call_value(f, Vec::new())?;
                        }
                        Out::Yield(pending) => {
                            self.park(None, Some(pending), false);
                            self.switched = true;
                        }
                        Out::Host(job) => self.request(job),
                    }
                }
                Op::Extern { index, argc } => {
                    let args = self.pop_n(argc as usize);
                    match self.host.call_extern(index, args) {
                        Ok(v) => self.stack.push(v),
                        Err(message) => {
                            let name = p.externs.get(index as usize).map_or("?", |n| n.as_str());
                            return fail(format!("extern {name}: {message}"));
                        }
                    }
                }
                Op::Prim { prim, argc } => {
                    let args = self.pop_n(argc as usize);
                    let arithmetic = matches!(
                        p.prims[prim as usize],
                        PrimOp::Arith(..) | PrimOp::FloatArith(_) | PrimOp::Float32Arith(_)
                    );
                    match self.prim(&p.prims[prim as usize], args) {
                        Ok(v) => self.stack.push(v),
                        // An operator whose result does not exist performs
                        // `overflow` or `divzero`, as its row says.
                        Err(Error::Runtime(m)) if arithmetic && m == TOO_LARGE => {
                            self.perform(Rc::from("overflow"), Q::Zero, Vec::new())?
                        }
                        Err(Error::Runtime(m)) if arithmetic && m == messages::DIVISION_BY_ZERO => {
                            self.perform(Rc::from("divzero"), Q::Zero, Vec::new())?
                        }
                        Err(e) => return Err(e),
                    }
                }
                Op::Unary(u) => {
                    let v = self.pop();
                    let v = self.unary(&p.unaries[u as usize], v)?;
                    self.stack.push(v);
                }
                Op::Closure(c) => {
                    let t = &p.closures[c as usize];
                    self.cells += 1;
                    let env = self.frames[fi].env.clone();
                    let mut captures = Vec::with_capacity(t.captures.len() + t.refs.len());
                    for &(outer, outer_indirect, inner, how) in &t.captures {
                        let v = match how {
                            Capture::Alias if !outer_indirect => Value::Ref(Rc::new(Place::new(
                                Root::Slot(env.clone(), outer),
                                Path::default(),
                            ))),
                            Capture::Move if !outer_indirect => std::mem::replace(
                                &mut env.borrow_mut()[outer as usize],
                                Value::Moved,
                            ),
                            _ => env.borrow()[outer as usize].clone(),
                        };
                        captures.push((inner, v));
                    }
                    for &(inner, outer, outer_indirect) in &t.refs {
                        let held = env.borrow()[outer as usize].clone();
                        let v = match held {
                            Value::Ref(_) if outer_indirect => held,
                            Value::Ref(_) => held,
                            _ => Value::Ref(Rc::new(Place::new(
                                Root::Slot(env.clone(), outer),
                                Path::default(),
                            ))),
                        };
                        captures.push((inner, v));
                    }
                    self.stack.push(Value::Closure(Rc::new(Closure {
                        code: t.code,
                        captures,
                    })));
                }
                Op::Perform { op, quant, argc } => {
                    let args = self.pop_n(argc as usize);
                    let op = p.names[op as usize].clone();
                    self.perform(op, quant, args)?;
                }
                Op::Handle(h) => {
                    let site = self.frames[fi].env.clone();
                    let t = &p.handles[h as usize];
                    let env = part_env(p.codes[t.body as usize].slots, &site, &t.aliases);
                    self.frames.push(Frame {
                        code: t.body,
                        pc: 0,
                        env,
                        base: self.stack.len(),
                        kind: Kind::Body {
                            handle: h,
                            site,
                            active: true,
                        },
                    });
                }
                Op::Unhandle => {
                    if let Kind::Body { active, .. } = &mut self.frames[fi].kind {
                        *active = false;
                    }
                }
                Op::Ret => {
                    let v = self.pop();
                    self.ret(v);
                }
                Op::Return => {
                    let v = self.pop();
                    // Out of the `handle` bodies and arms, to the
                    // function's frame.
                    while !matches!(self.frames.last().map(|f| &f.kind), Some(Kind::Root(_))) {
                        if self.frames.len() <= depth + 1 {
                            break;
                        }
                        self.frames.pop();
                    }
                    self.ret(v);
                }
                Op::Test { pat, fail: to } => {
                    let v = self.stack.last().expect("a scrutinee").clone();
                    let mut binds = Vec::new();
                    if self.matches(&p.pats[pat as usize], &v, &mut binds)? {
                        let env = self.frames[fi].env.clone();
                        let mut slots = env.borrow_mut();
                        for (s, v) in binds {
                            slots[s as usize] = v;
                        }
                    } else {
                        self.frames[fi].pc = to;
                    }
                }
                Op::NoArm => return fail(messages::NO_ARM),
                Op::Tick => {
                    let budgets = self.budgets();
                    if budgets.is_empty() {
                        self.tick()?;
                        self.frames[fi].pc += 1;
                    } else if let Some(&b) = budgets.iter().find(|b| self.out(**b)) {
                        self.perform_below(Rc::from("exceeded"), Q::Once, vec![Value::Info], b)?;
                    } else {
                        for b in budgets {
                            if let Kind::Budget {
                                memory: false,
                                left: Some(n),
                            } = &mut self.frames[b].kind
                            {
                                *n -= 1;
                            }
                        }
                        self.frames[fi].pc += 1;
                    }
                }
                Op::TickAnswer => {
                    let answer = self.pop();
                    let budgets = self.budgets();
                    let Some(&b) = budgets.iter().find(|b| self.out(**b)) else {
                        return fail("internal: an answer of exceeded with no budget run out");
                    };
                    match answer {
                        Value::Answer(a) => match &*a {
                            Answer::More(n) => {
                                let cells = self.cells;
                                if let Kind::Budget { memory, left } = &mut self.frames[b].kind {
                                    *left = match n {
                                        Some(n) if *memory => Some(cells + n),
                                        n => *n,
                                    };
                                }
                            }
                            Answer::Value(v) => {
                                let v = v.clone();
                                self.frames.truncate(b + 1);
                                self.ret(v);
                            }
                        },
                        v => return fail(format!("internal: exceeded answered {}", v.kind())),
                    }
                }
                Op::Budget(t) => {
                    let steps = self.pop();
                    let t = &p.budgets[t as usize];
                    let n = match steps.get()? {
                        Value::Int(n) => Some(n),
                        _ => None,
                    };
                    let left = match n {
                        Some(n) if t.memory => Some(self.cells + n),
                        n => n,
                    };
                    let site = self.frames[fi].env.clone();
                    let env = part_env(p.codes[t.body as usize].slots, &site, &t.aliases);
                    self.frames.push(Frame {
                        code: t.body,
                        pc: 0,
                        env,
                        base: self.stack.len(),
                        kind: Kind::Budget {
                            memory: t.memory,
                            left,
                        },
                    });
                }
            }
        }
        Ok(self.stack.pop().unwrap_or(Value::Unit))
    }

    pub fn matches(&self, pat: &Pat, v: &Value, binds: &mut Vec<(u32, Value)>) -> R<bool> {
        Ok(match pat {
            Pat::Wild => true,
            Pat::Bind { slot, borrow } => {
                let b = if *borrow {
                    match v {
                        Value::Ref(_) => v.clone(),
                        v => temp_ref(v.clone()),
                    }
                } else {
                    v.get()?
                };
                binds.push((*slot, b));
                true
            }
            Pat::Literal(l) => equal(l, v)?,
            Pat::Ctor { ctor, fields } => {
                let inner = v.get()?;
                let Value::Data(d) = &inner else {
                    return Ok(false);
                };
                if d.ctor.id != *ctor {
                    return Ok(false);
                }
                for (i, f) in fields.iter().enumerate() {
                    let part = match v {
                        Value::Ref(p) => Value::Ref(Rc::new(p.child(Step::Index(i)))),
                        _ => d.fields[i].clone(),
                    };
                    if !self.matches(f, &part, binds)? {
                        return Ok(false);
                    }
                }
                true
            }
            Pat::Variant { variant, pat } => {
                let inner = v.get()?;
                let Value::Inject(_, i, x) = &inner else {
                    return Ok(false);
                };
                if i != variant {
                    return Ok(false);
                }
                let part = match v {
                    Value::Ref(p) => Value::Ref(Rc::new(p.child(Step::Index(0)))),
                    _ => (**x).clone(),
                };
                self.matches(pat, &part, binds)?
            }
        })
    }

    /// The frames of the budgets in place, innermost first.
    fn budgets(&self) -> Vec<usize> {
        let mut out = Vec::new();
        // Only `Op::Budget` makes a budget's frame: a program with no
        // `budget` has none, and its steps need not look down a deep
        // recursion's frames at each tick.
        if self.p.budgets.is_empty() {
            return out;
        }
        let mut j = self.frames.len();
        while j > 0 {
            j -= 1;
            match &self.frames[j].kind {
                Kind::Direct { dist } => j -= dist,
                Kind::Budget { .. } => out.push(j),
                _ => {}
            }
        }
        out
    }

    /// Whether the budget of frame `b` has run out.
    fn out(&self, b: usize) -> bool {
        match &self.frames[b].kind {
            Kind::Budget {
                memory: true,
                left: Some(n),
            } => self.cells > *n,
            Kind::Budget {
                memory: false,
                left: Some(n),
            } => *n <= 0,
            _ => false,
        }
    }

    /// Performs `op`: the nearest arm for it answers.
    pub fn perform(&mut self, op: Rc<str>, quant: Q, args: Vec<Value>) -> R<()> {
        let top = self.frames.len();
        self.perform_below(op, quant, args, top)
    }

    /// Performs `op`, answered by an arm of the frames below `top`.
    fn perform_below(&mut self, op: Rc<str>, quant: Q, args: Vec<Value>, top: usize) -> R<()> {
        let p = self.p;
        let mut j = top;
        while j > 0 {
            j -= 1;
            let (handle, site) = match &self.frames[j].kind {
                Kind::Direct { dist } => {
                    j -= dist;
                    continue;
                }
                Kind::Body {
                    handle,
                    site,
                    active: true,
                } => (*handle, site.clone()),
                _ => continue,
            };
            for arm in &p.handles[handle as usize].arms {
                if *arm.op != *op {
                    continue;
                }
                let mut binds = Vec::new();
                let mut fits = arm.pats.len() == args.len();
                for (pat, a) in arm.pats.iter().zip(&args) {
                    if !fits {
                        break;
                    }
                    fits = self.matches(pat, a, &mut binds)?;
                }
                if !fits {
                    continue;
                }
                let env = part_env(p.codes[arm.code as usize].slots, &site, &arm.aliases);
                {
                    let mut slots = env.borrow_mut();
                    for (s, v) in binds {
                        slots[s as usize] = v;
                    }
                }
                if quant == Q::Direct {
                    let dist = self.frames.len() - j;
                    self.frames.push(Frame {
                        code: arm.code,
                        pc: 0,
                        env,
                        base: self.stack.len(),
                        kind: Kind::Direct { dist },
                    });
                    return Ok(());
                }
                let start = self.frames[j].base;
                if let Some(k) = arm.k {
                    let frames = self.frames[j..]
                        .iter()
                        .map(|f| {
                            let mut f = f.clone();
                            f.base -= start;
                            f
                        })
                        .collect();
                    let stack = self.stack[start..].to_vec();
                    let cont = Value::Cont(Rc::new(Cont {
                        frames,
                        stack,
                        once: quant != Q::Many,
                    }));
                    env.borrow_mut()[k as usize] = cont;
                }
                self.discard(j, start);
                self.frames.push(Frame {
                    code: arm.code,
                    pc: 0,
                    env,
                    base: start,
                    kind: Kind::Arm,
                });
                return Ok(());
            }
        }
        // The host answers `wait`: the task goes on once the signal is
        // raised.
        if &*op == "wait" && args.len() == 1 {
            if let Value::Signal(s) = args[0].get()? {
                self.stack.push(Value::Unit);
                if !s.is_raised() {
                    self.park(Some(s), None, false);
                    self.switched = true;
                }
                return Ok(());
            }
        }
        if &*op == "show" && args.len() == 2 {
            let name = args[0].as_text()?;
            let shown = match &args[1] {
                Value::Shown(t) => t.to_string(),
                v => show(v)?,
            };
            self.host.show(&name, &shown);
            self.stack.push(Value::Unit);
            return Ok(());
        }
        // The host answers `overflow` and `divzero` that nothing handles by
        // stopping the program with what went wrong.
        if args.is_empty() {
            match &*op {
                "overflow" => return fail(TOO_LARGE),
                "divzero" => return fail(messages::DIVISION_BY_ZERO),
                _ => {}
            }
        }
        if let Some(answer) = self.host.operation(self.p, &op, &args) {
            self.stack.push(answer?);
            return Ok(());
        }
        // A task runs outside the handler `Host::run` installs, so the
        // operations on a `Ref`, a `Mutex` or an `Atomic` it performs are
        // answered here by the builtin that `Host::run` answers them with.
        if let Some(name) = storage_builtin(&op) {
            return match builtins::call(self, name, args)? {
                Out::Value(v) => {
                    self.stack.push(v);
                    Ok(())
                }
                _ => fail(format!(
                    "internal: {name} answered {op} with more than a value"
                )),
            };
        }
        fail(messages::nothing_handles(&op))
    }

    fn prim(&mut self, op: &PrimOp, args: Vec<Value>) -> R<Value> {
        Ok(match op {
            PrimOp::Arith(a, Width::Nat)
                if args.iter().any(|v| matches!(v.get(), Ok(Value::Nat(_))))
                    || nat_overflows(*a, &args) =>
            {
                let x = args[0].as_nat()?;
                let n = match a {
                    Arith::Neg => return fail(TOO_LARGE),
                    Arith::Add => x.add(&args[1].as_nat()?),
                    Arith::Sub => match x.sub(&args[1].as_nat()?) {
                        Some(n) => n,
                        None => return fail(TOO_LARGE),
                    },
                    Arith::Mul => x.mul(&args[1].as_nat()?),
                    Arith::Div => return fail("internal: integer `/`"),
                };
                Value::of_nat(n)
            }
            PrimOp::Arith(a, w) => {
                let x = args[0].as_int()?;
                let n = match a {
                    Arith::Neg => x.checked_neg(),
                    Arith::Add => x.checked_add(args[1].as_int()?),
                    Arith::Sub => x.checked_sub(args[1].as_int()?),
                    Arith::Mul => x.checked_mul(args[1].as_int()?),
                    Arith::Div => return fail("internal: integer `/`"),
                };
                Value::Int(checked(n, *w)?)
            }
            PrimOp::FloatArith(a) => {
                let x = args[0].as_float()?;
                Value::Float(match a {
                    Arith::Neg => -x,
                    Arith::Add => x + args[1].as_float()?,
                    Arith::Sub => x - args[1].as_float()?,
                    Arith::Mul => x * args[1].as_float()?,
                    Arith::Div => match tauto_rt::float::div(x, args[1].as_float()?) {
                        Some(q) => q,
                        None => return fail(messages::DIVISION_BY_ZERO),
                    },
                })
            }
            PrimOp::Float32Arith(a) => {
                let x = args[0].as_float32()?;
                Value::Float32(match a {
                    Arith::Neg => -x,
                    Arith::Add => x + args[1].as_float32()?,
                    Arith::Sub => x - args[1].as_float32()?,
                    Arith::Mul => x * args[1].as_float32()?,
                    Arith::Div => match tauto_rt::float::div32(x, args[1].as_float32()?) {
                        Some(q) => q,
                        None => return fail(messages::DIVISION_BY_ZERO),
                    },
                })
            }
            PrimOp::Cmp(c) => {
                let (a, b) = (args[0].get()?, args[1].get()?);
                let ord = match (&a, &b) {
                    (Value::Int(x), Value::Int(y)) => x.partial_cmp(y),
                    (Value::Nat(x), Value::Nat(y)) => x.partial_cmp(y),
                    (Value::Nat(_), Value::Int(_)) => Some(std::cmp::Ordering::Greater),
                    (Value::Int(_), Value::Nat(_)) => Some(std::cmp::Ordering::Less),
                    (Value::Float(x), Value::Float(y)) => x.partial_cmp(y),
                    (Value::Float32(x), Value::Float32(y)) => x.partial_cmp(y),
                    (Value::Text(x), Value::Text(y)) => x.partial_cmp(y),
                    _ => return fail("internal: compared values of no order"),
                };
                let Some(o) = ord else {
                    return Ok(Value::Bool(false));
                };
                Value::Bool(match c {
                    Cmp::Lt => o.is_lt(),
                    Cmp::Gt => o.is_gt(),
                    Cmp::Le => o.is_le(),
                    Cmp::Ge => o.is_ge(),
                })
            }
            PrimOp::Eq(negate) => Value::Bool(equal(&args[0], &args[1])? != *negate),
            PrimOp::Construct { ctor, order } => {
                self.cells += 1 + order.len() as i128;
                let mut args: Vec<Option<Value>> = args.into_iter().map(Some).collect();
                let fields = order
                    .iter()
                    .map(|i| args[*i].take().unwrap_or(Value::Unit))
                    .collect();
                Value::Data(Rc::new(Data {
                    ctor: ctor.clone(),
                    fields,
                }))
            }
            PrimOp::Concat => {
                let (a, b) = (args[0].as_text()?, args[1].as_text()?);
                let mut s = String::with_capacity(a.len() + b.len());
                s.push_str(&a);
                s.push_str(&b);
                Value::Text(Rc::from(s))
            }
            PrimOp::TextOfInt => match args[0].get()? {
                Value::Nat(n) => Value::text(&n.to_string()),
                v => Value::text(&v.as_int()?.to_string()),
            },
            PrimOp::TextLen => Value::Int(args[0].as_text()?.len() as i128),
            PrimOp::SynParse(rt) => rt.parse(&self.known, &args[0].as_text()?),
            PrimOp::TextCompare => {
                let (a, b) = (args[0].as_text()?, args[1].as_text()?);
                Value::Int(match a.cmp(&b) {
                    std::cmp::Ordering::Less => -1,
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Greater => 1,
                })
            }
            PrimOp::Divide {
                modulo,
                width: Width::Nat,
            } if args.iter().any(|v| matches!(v.get(), Ok(Value::Nat(_)))) => {
                let (a, b) = (args[0].as_nat()?, args[1].as_nat()?);
                let Some((q, r)) = a.divmod(&b) else {
                    return fail(messages::DIVISION_BY_ZERO);
                };
                Value::of_nat(if *modulo { r } else { q })
            }
            PrimOp::Divide { modulo, width } => {
                let (a, b) = (args[0].as_int()?, args[1].as_int()?);
                if b == 0 {
                    return fail(messages::DIVISION_BY_ZERO);
                }
                let n = if *modulo {
                    a.checked_rem(b)
                } else {
                    a.checked_div(b)
                };
                Value::Int(checked(n, *width)?)
            }
        })
    }

    fn unary(&self, op: &UnaryOp, v: Value) -> R<Value> {
        Ok(match op {
            UnaryOp::Not => Value::Bool(!v.as_bool()?),
            UnaryOp::Field(s) => v.get()?.at(s)?.get()?,
            UnaryOp::Shown => Value::Shown(Rc::from(show(&v)?)),
            UnaryOp::TempRef => temp_ref(v),
            UnaryOp::Deref => v.get()?,
            UnaryOp::Inject(u, i) => Value::Inject(*u, *i, Rc::new(v)),
            UnaryOp::Remap(to, table) => match v.get()? {
                Value::Inject(_, i, x) => match to {
                    None => (*x).clone(),
                    Some(t) => match table.get(i as usize).copied().flatten() {
                        Some(j) => Value::Inject(*t, j as u32, x),
                        None => return fail("internal: a union member with no place"),
                    },
                },
                v => v,
            },
        })
    }
}

/// The slots of a part of a `handle`, holding borrows of the locals around
/// it that it uses.
fn part_env(n: u32, site: &Env, aliases: &[crate::code::Alias]) -> Env {
    let env = new_env(n);
    {
        let mut slots = env.borrow_mut();
        let around = site.borrow();
        for &(outer, outer_indirect, inner) in aliases {
            slots[inner as usize] = if outer_indirect {
                around[outer as usize].clone()
            } else {
                Value::Ref(Rc::new(Place::new(
                    Root::Slot(site.clone(), outer),
                    Path::default(),
                )))
            };
        }
    }
    env
}

/// The local's own value, at the place the slot borrows.
fn shallow(place: &Place) -> R<Value> {
    if place.path.is_empty() {
        return Ok(match &place.root {
            Root::Slot(env, i) => env.borrow()[*i as usize].clone(),
            Root::Cell(c) => c.borrow().clone(),
        });
    }
    place.get()
}

fn clone_root(r: &Root) -> Root {
    match r {
        Root::Slot(e, i) => Root::Slot(e.clone(), *i),
        Root::Cell(c) => Root::Cell(c.clone()),
    }
}

/// Whether the `nat` operation on these two `Int`s leaves `i128`, so that it
/// is done on big numbers.
fn nat_overflows(a: Arith, args: &[Value]) -> bool {
    let (Ok(Value::Int(x)), Some(Ok(Value::Int(y)))) = (
        args[0].get(),
        args.get(1).map(Value::get).or(Some(Ok(Value::Int(0)))),
    ) else {
        return false;
    };
    match a {
        Arith::Add => x.checked_add(y).is_none(),
        Arith::Mul => x.checked_mul(y).is_none(),
        _ => false,
    }
}

/// `n` checked to the width's range.
pub fn checked(n: Option<i128>, w: Width) -> R<i128> {
    let Some(n) = n else {
        return fail(TOO_LARGE);
    };
    let ok = match w {
        Width::W8 => i8::try_from(n).is_ok(),
        Width::W16 => i16::try_from(n).is_ok(),
        Width::W32 => i32::try_from(n).is_ok(),
        Width::W64 => i64::try_from(n).is_ok(),
        Width::U8 => u8::try_from(n).is_ok(),
        Width::U16 => u16::try_from(n).is_ok(),
        Width::U32 => u32::try_from(n).is_ok(),
        Width::U64 | Width::Host => u64::try_from(n).is_ok(),
        Width::Nat => n >= 0,
    };
    if ok { Ok(n) } else { fail(TOO_LARGE) }
}

impl From<String> for Error {
    fn from(s: String) -> Self {
        Error::Runtime(s)
    }
}

/// The builtin that answers a storage operation, as `Host::run` answers it.
fn storage_builtin(op: &str) -> Option<&'static str> {
    Some(match op {
        "ref_new" => "Ref::new",
        "ref_get" => "Ref::get",
        "ref_set" => "Ref::set",
        "weak_of" => "Weak::of",
        "weak_get" => "Weak::get",
        "mutex_new" => "Mutex::new",
        "mutex_claim" => "Mutex::claim",
        "mutex_take_claimed" => "Mutex::take_claimed",
        "mutex_put" => "Mutex::put",
        "mutex_withdraw" => "Mutex::withdraw",
        "atomic_new" => "Atomic::new",
        "atomic_load" => "Atomic::load",
        "atomic_store" => "Atomic::store",
        "atomic_fetch_add" => "Atomic::fetch_add",
        _ => return None,
    })
}
