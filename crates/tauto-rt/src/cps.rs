//! The M tier: operations that resume any number of times (`resume ω`),
//! in continuation-passing style.
//!
//! Stable Rust has no future that can be cloned, so code of this tier is
//! written with its continuations as values: a [`Kont`] is `Rc<dyn Fn>`, which
//! can be called any number of times. A function returns a [`Step`] to a
//! trampoline instead of calling deeper, so a long loop does not grow the
//! stack.
//!
//! The handlers in place are a persistent list ([`M`]) that every
//! continuation is called with: a continuation that is called again later
//! (`k(a) + k(b)`) finds the handlers it was captured under, rebuilt over the
//! handlers of the arm that calls it (`Resume::call`), which is what makes the
//! handler deep.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::a::Abort;
use crate::ev::Ev;
use crate::{Loc, Op, OpId, Payload, error, messages};

pub enum Step<'a> {
    /// The computation has delivered its value to the driver.
    Done,
    /// Go on from here, with the stack unwound.
    More(Box<dyn FnOnce() -> Step<'a> + 'a>),
    /// An operation no handler in the computation answers: the driver does,
    /// and calls `k` (with `m`) with the answer.
    Escape {
        op: Op,
        args: Payload,
        at: Loc,
        k: Kont<'a, Payload>,
        m: M<'a>,
    },
    Fail(Abort),
    /// An arm's answer when none of its patterns fit: the arguments go back
    /// and the search goes outward.
    NoMatch(Payload),
}

/// The rest of a computation: called with the handlers in place and a value.
pub type Kont<'a, T> = Rc<dyn Fn(&M<'a>, T) -> Step<'a> + 'a>;

/// What a handler does for an operation: with the chain outside the handler,
/// the continuation of the `handle` expression, the operation, its arguments,
/// and `k`. When no arm's pattern fits the arguments come back.
pub type ArmFn<'a> =
    dyn Fn(&M<'a>, Kont<'a, Payload>, Op, Payload, Loc, Resume<'a>) -> Step<'a> + 'a;

/// A budget in the handlers in place: the steps it has left are shared by every copy of the chain, so a
/// continuation that runs again goes on from where the count is.
#[derive(Clone)]
pub struct BudgetFrame {
    id: u32,
    /// As in the O tier: the steps left, or for a memory budget the count of
    /// cells past which it has run out.
    left: Rc<Cell<u64>>,
    memory: bool,
    /// The `info` of the `Exceeded` operation, and the way to read what the
    /// arm answers with, for the type of the budget's value.
    info: fn() -> Payload,
    answer: fn(Payload) -> Answer,
}

/// What an `exceeded` arm answered with, without the budget's value type.
pub enum Answer {
    /// `k(v)`: the budget ends with `v` (a boxed value of its type).
    Value(Payload),
    /// `info.more(m)`; `info.unbounded()` is the largest number.
    More(u64),
}

pub struct Frame<'a> {
    pub ops: &'static [OpId],
    budget: Option<BudgetFrame>,
    pub arm: Rc<ArmFn<'a>>,
    /// Where the value of the `handle` expression goes.
    pub target: Kont<'a, Payload>,
    pub outer: M<'a>,
}

/// The handlers in place, the innermost first. Changing it makes a new chain.
#[derive(Clone, Default)]
pub struct M<'a>(Option<Rc<Frame<'a>>>);

impl<'a> M<'a> {
    pub fn empty() -> M<'a> {
        M(None)
    }

    pub fn push(
        &self,
        ops: &'static [OpId],
        arm: Rc<ArmFn<'a>>,
        target: Kont<'a, Payload>,
    ) -> M<'a> {
        M(Some(Rc::new(Frame {
            ops,
            budget: None,
            arm,
            target,
            outer: self.clone(),
        })))
    }

    /// A chain with a `budget` of `steps` inside (budget number `id`, of the
    /// value type `T`); its value goes to `target`.
    pub fn push_budget<T: 'static>(&self, id: u32, steps: u64, target: Kont<'a, Payload>) -> M<'a> {
        self.push_budget_of::<T>(id, steps, false, target)
    }

    pub fn push_budget_memory<T: 'static>(
        &self,
        id: u32,
        cells: u64,
        target: Kont<'a, Payload>,
    ) -> M<'a> {
        self.push_budget_of::<T>(id, crate::budget::refill(cells, true), true, target)
    }

    fn push_budget_of<T: 'static>(
        &self,
        id: u32,
        keep: u64,
        memory: bool,
        target: Kont<'a, Payload>,
    ) -> M<'a> {
        M(Some(Rc::new(Frame {
            ops: &[],
            budget: Some(BudgetFrame {
                id,
                left: Rc::new(Cell::new(keep)),
                memory,
                info: crate::budget::info_payload::<T>,
                answer: crate::budget::answer_of::<T>,
            }),
            arm: arm(|_, _, _, args, _, _| Step::NoMatch(args)),
            target,
            outer: self.clone(),
        })))
    }

    /// The handler the body is under has ended: the chain outside it, and
    /// where the value of its `handle` goes.
    pub fn pop(&self) -> (M<'a>, Kont<'a, Payload>) {
        match &self.0 {
            Some(f) => (f.outer.clone(), f.target.clone()),
            None => panic!("tauto: no handler to leave (a bug in the generated code)"),
        }
    }
}

/// A handler of a [`Resume`]: what is rebuilt when it is called, and no
/// more. The handler whose arm runs keeps no `target` and no `outer`: they
/// are the code around the `handle`, which a resume gets afresh, and a
/// continuation that is kept must not keep them alive (the cycle check
/// counts only what the body and the handler hold).
struct Held<'a> {
    ops: &'static [OpId],
    budget: Option<BudgetFrame>,
    arm: Rc<ArmFn<'a>>,
    /// Where the value of a `handle` inside the body goes; `None` for the
    /// handler whose arm runs.
    target: Option<Kont<'a, Payload>>,
}

/// The continuation `k` of an arm: the body from the operation up to the
/// handler, which can be run any number of times.
#[derive(Clone)]
pub struct Resume<'a> {
    /// The handlers from the operation outward, ending with the one whose arm
    /// runs.
    prefix: Rc<Vec<Held<'a>>>,
    kont: Kont<'a, Payload>,
}

impl<'a> Resume<'a> {
    /// `k(value)`, called where the handlers are `base`: the body goes on
    /// under the same handlers, and when it ends its value goes to `target`.
    pub fn call(&self, base: &M<'a>, value: Payload, target: Kont<'a, Payload>) -> Step<'a> {
        let mut m = base.clone();
        for f in self.prefix.iter().rev() {
            let t = f.target.clone().unwrap_or_else(|| target.clone());
            m = M(Some(Rc::new(Frame {
                ops: f.ops,
                budget: f.budget.clone(),
                arm: f.arm.clone(),
                target: t,
                outer: m,
            })));
        }
        (self.kont)(&m, value)
    }

    /// The continuation of an operation that was not answered here, kept for
    /// the arm that does not call it.
    fn none() -> Resume<'a> {
        Resume {
            prefix: Rc::new(Vec::new()),
            kont: Rc::new(|_, _| {
                panic!("tauto: a resume 0 operation was resumed (a bug in the generated code)")
            }),
        }
    }
}

/// A continuation, from a closure (which gives the closure its signature).
pub fn kont<'a, T, F: Fn(&M<'a>, T) -> Step<'a> + 'a>(f: F) -> Kont<'a, T> {
    Rc::new(f)
}

pub fn arm<'a, F>(f: F) -> Rc<ArmFn<'a>>
where
    F: Fn(&M<'a>, Kont<'a, Payload>, Op, Payload, Loc, Resume<'a>) -> Step<'a> + 'a,
{
    Rc::new(f)
}

/// Calls a continuation with the stack unwound: a function returns through
/// it, and the chain of returns of a deep recursion does not grow the stack.
pub fn ret<'a, T: 'a>(k: &Kont<'a, T>, m: &M<'a>, v: T) -> Step<'a> {
    let (k, m) = (k.clone(), m.clone());
    Step::More(Box::new(move || k(&m, v)))
}

pub fn more<'a>(f: impl FnOnce() -> Step<'a> + 'a) -> Step<'a> {
    Step::More(Box::new(f))
}

/// A continuation that takes a `T`, for one that takes a `Payload`.
pub fn erase<'a, T: 'static>(k: Kont<'a, T>) -> Kont<'a, Payload> {
    Rc::new(move |m, p| k(m, *p.downcast::<T>().expect("tauto: payload type")))
}

/// `inside`: the operation is a budget's, performed outside it: the handlers
/// from the top to that budget do not see it (but are part of `k`).
fn route<'a>(
    m: &M<'a>,
    op: Op,
    mut args: Payload,
    at: Loc,
    k: Option<&Kont<'a, Payload>>,
    inside: Option<u32>,
) -> Result<Step<'a>, Payload> {
    let mut prefix: Vec<&Rc<Frame<'a>>> = Vec::new();
    let mut cur = m;
    let mut outside = inside.is_none();
    while let Some(f) = &cur.0 {
        prefix.push(f);
        if inside.is_some() && f.budget.as_ref().map(|b| b.id) == inside {
            outside = true;
        }
        if outside && f.ops.contains(&op.id) {
            let res = match k {
                Some(k) => {
                    let last = prefix.len() - 1;
                    let held = prefix
                        .iter()
                        .enumerate()
                        .map(|(i, f)| Held {
                            ops: f.ops,
                            budget: f.budget.clone(),
                            arm: f.arm.clone(),
                            target: (i != last).then(|| f.target.clone()),
                        })
                        .collect();
                    Resume {
                        prefix: Rc::new(held),
                        kont: k.clone(),
                    }
                }
                None => Resume::none(),
            };
            match (f.arm)(&f.outer, f.target.clone(), op, args, at, res) {
                Step::NoMatch(back) => args = back,
                step => return Ok(step),
            }
        }
        cur = &f.outer;
    }
    Err(args)
}

/// Performs `op`: the nearest handler with an arm that fits runs it, with
/// `k` the rest of the computation up to that handler. Nothing in the
/// computation answering is the driver's to do.
pub fn perform<'a>(m: &M<'a>, op: Op, args: Payload, at: Loc, k: Kont<'a, Payload>) -> Step<'a> {
    match route(m, op, args, at, Some(&k), None) {
        Ok(step) => step,
        Err(args) => Step::Escape {
            op,
            args,
            at,
            k,
            m: m.clone(),
        },
    }
}

/// A `direct` operation in code that holds no handler from around it: a
/// `direct` handler inside answers it in place; otherwise it goes out, to
/// the driver, which answers it with the handlers of the code that runs the
/// computation now.
pub fn perform_direct<'a>(
    ev: &Ev<'_>,
    m: &M<'a>,
    op: Op,
    args: Payload,
    at: Loc,
    k: Kont<'a, Payload>,
) -> Step<'a> {
    if ev.answers(op.id) {
        let answer = ev.perform(op, args, at);
        let m = m.clone();
        return Step::More(Box::new(move || k(&m, answer)));
    }
    perform(m, op, args, at, k)
}

/// An abort (an operation of `resume 0`): the nearest handler with an arm that
/// fits takes it.
pub fn abort<'a>(m: &M<'a>, a: Abort) -> Step<'a> {
    let Abort { op, args, at } = a;
    match route(m, op, args, at, None, None) {
        Ok(step) => step,
        Err(args) => Step::Fail(Abort { op, args, at }),
    }
}

/// One step of a loop or a call that may not stop, in the M tier: it takes a
/// step off every budget in the handlers in place; when one has none left,
/// `Exceeded` is performed outside it, and the computation goes on with `k`
/// as the arm answers.
pub fn tick<'a>(m: &M<'a>, at: Loc, k: Kont<'a, ()>) -> Step<'a> {
    let mut ran_out: Option<BudgetFrame> = None;
    let mut cur = m;
    let mut any = false;
    while let Some(f) = &cur.0 {
        if let Some(b) = &f.budget {
            any = true;
            // The innermost one that has run out, as the O tier chooses.
            if crate::budget::ran_out(b.left.get(), b.memory) && ran_out.is_none() {
                ran_out = Some(b.clone());
            }
        }
        cur = &f.outer;
    }
    if !any {
        crate::host_tick(at);
        return k(m, ());
    }
    let Some(b) = ran_out else {
        let mut cur = m;
        while let Some(f) = &cur.0 {
            if let Some(b) = &f.budget
                && !b.memory
                && b.left.get() != crate::budget::UNBOUNDED
            {
                b.left.set(b.left.get() - 1);
            }
            cur = &f.outer;
        }
        return k(m, ());
    };
    let id = b.id;
    let cont: Kont<'a, Payload> = Rc::new(move |m2, answer| match (b.answer)(answer) {
        Answer::Value(v) => {
            // The budget ends: its value goes where the budget's goes, under
            // the handlers outside it.
            let mut cur = m2;
            while let Some(f) = &cur.0 {
                if f.budget.as_ref().map(|x| x.id) == Some(id) {
                    return (f.target)(&f.outer, v);
                }
                cur = &f.outer;
            }
            panic!("tauto: the budget is not in place (a bug in the generated code)")
        }
        Answer::More(n) => {
            b.left.set(crate::budget::refill(n, b.memory));
            k(m2, ())
        }
    });
    let args = (b_info(m, id))();
    match route(
        m,
        crate::budget::OP_EXCEEDED,
        args,
        at,
        Some(&cont),
        Some(id),
    ) {
        Ok(step) => step,
        Err(args) => Step::Escape {
            op: crate::budget::OP_EXCEEDED,
            args,
            at,
            k: cont,
            m: m.clone(),
        },
    }
}

fn b_info<'a>(m: &M<'a>, id: u32) -> fn() -> Payload {
    let mut cur = m;
    while let Some(f) = &cur.0 {
        if let Some(b) = &f.budget
            && b.id == id
        {
            return b.info;
        }
        cur = &f.outer;
    }
    unreachable!("tauto: the budget is not in place")
}

/// A borrowed function of the O tier (`&f`, which may diverge under a
/// budget) held in code of the M tier. A continuation is called any number
/// of times, so it holds a shared handle rather than the `&mut` the O tier
/// lends.
pub struct OCb<'a, A, R>(Rc<RefCell<dyn crate::o::OFnMut<A, R> + 'a>>);

impl<A, R> Clone for OCb<'_, A, R> {
    fn clone(&self) -> Self {
        OCb(self.0.clone())
    }
}

impl<'a, A, R> OCb<'a, A, R> {
    pub fn new(f: impl crate::o::OFnMut<A, R> + 'a) -> Self {
        OCb(Rc::new(RefCell::new(f)))
    }
}

/// A call of an [`OCb`] in code of the M tier: its future is polled here,
/// with the budgets in the handlers in place counting its steps. When one
/// runs out, `Exceeded` is performed outside it as [`tick`] does, and the
/// call goes on (or the budget ends) as the arm answers.
///
/// The future borrows the callback, so it cannot outlive this call: the arm
/// is run to its answer here, and an operation it leaves to the driver
/// outside must be one `ev` answers.
pub fn call_o<'a, A, R: 'static>(
    ev: &Ev<'_>,
    m: &M<'a>,
    at: Loc,
    f: &OCb<'a, A, R>,
    args: A,
    k: Kont<'a, R>,
) -> Step<'a> {
    let mut held = f.0.borrow_mut();
    let mut fut = held.call(ev, args);
    let mut m = m.clone();
    loop {
        let polled = {
            let mut frames = Vec::new();
            let mut cur = &m;
            while let Some(fr) = &cur.0 {
                if let Some(b) = &fr.budget {
                    frames.push(b.clone());
                }
                cur = &fr.outer;
            }
            // The innermost budget last, as the O tier's drivers nest.
            let _active: Vec<_> = frames
                .iter()
                .rev()
                .map(|b| crate::budget::ActiveBudget::enter(b.id, b.left.clone(), b.memory))
                .collect();
            crate::o::poll_once(fut.as_mut())
        };
        let id = match polled {
            std::task::Poll::Ready(v) => {
                drop(fut);
                drop(held);
                return k(&m, v);
            }
            std::task::Poll::Pending => match crate::o::peek() {
                crate::o::Peek::Budget(_) => crate::o::take_budget(),
                _ => panic!(
                    "tauto: a divergent callback suspended for an operation (a bug in the generated code)"
                ),
            },
        };
        let b = find_budget(&m, id).unwrap_or_else(|| {
            panic!("tauto: the budget is not in place (a bug in the generated code)")
        });
        let answered: Rc<RefCell<Option<(M<'a>, Answer)>>> = Rc::new(RefCell::new(None));
        let slot = answered.clone();
        let answer = b.answer;
        let cont: Kont<'a, Payload> = Rc::new(move |m2, a| {
            *slot.borrow_mut() = Some((m2.clone(), answer(a)));
            Step::Done
        });
        let args = (b.info)();
        let mut step = match route(
            &m,
            crate::budget::OP_EXCEEDED,
            args,
            at,
            Some(&cont),
            Some(id),
        ) {
            Ok(step) => step,
            Err(_) => error(
                messages::nothing_handles(crate::budget::OP_EXCEEDED.name),
                at,
            ),
        };
        loop {
            match step {
                Step::Done => break,
                Step::More(g) => step = g(),
                Step::Fail(a) => return Step::Fail(a),
                Step::Escape { op, args, at, k, m } => {
                    if !ev.answers(op.id) {
                        error(messages::nothing_handles(op.name), at)
                    }
                    step = k(&m, ev.perform(op, args, at));
                }
                Step::NoMatch(_) => {
                    panic!("tauto: an arm answered nothing (a bug in the generated code)")
                }
            }
        }
        let Some((m2, a)) = answered.borrow_mut().take() else {
            // The arm ended the computation without answering.
            return Step::Done;
        };
        match a {
            Answer::More(n) => {
                b.left.set(crate::budget::refill(n, b.memory));
                m = m2;
            }
            Answer::Value(v) => {
                // The budget ends: the stopped call is dropped.
                drop(fut);
                drop(held);
                let mut cur = &m2;
                while let Some(fr) = &cur.0 {
                    if fr.budget.as_ref().map(|x| x.id) == Some(id) {
                        return (fr.target)(&fr.outer, v);
                    }
                    cur = &fr.outer;
                }
                panic!("tauto: the budget is not in place (a bug in the generated code)")
            }
        }
    }
}

fn find_budget(m: &M<'_>, id: u32) -> Option<BudgetFrame> {
    let mut cur = m;
    while let Some(f) = &cur.0 {
        if let Some(b) = &f.budget
            && b.id == id
        {
            return Some(b.clone());
        }
        cur = &f.outer;
    }
    None
}

type Slot<T> = Rc<RefCell<Option<T>>>;

fn start<'a, T: 'static>(
    start: impl FnOnce(&M<'a>, Kont<'a, T>) -> Step<'a>,
) -> (Step<'a>, Slot<T>) {
    let slot: Slot<T> = Rc::new(RefCell::new(None));
    let s2 = slot.clone();
    let fin: Kont<'a, T> = Rc::new(move |_, v| {
        *s2.borrow_mut() = Some(v);
        Step::Done
    });
    (start(&M::empty(), fin), slot)
}

fn start_r<'a, T: 'static, R: 'static>(
    start: impl FnOnce(&M<'a>, Kont<'a, T>, Kont<'a, R>) -> Step<'a>,
) -> (Step<'a>, Slot<Flow<T, R>>) {
    let slot: Slot<Flow<T, R>> = Rc::new(RefCell::new(None));
    let (s1, s2) = (slot.clone(), slot.clone());
    let fin: Kont<'a, T> = Rc::new(move |_, v| {
        *s1.borrow_mut() = Some(Flow::Value(v));
        Step::Done
    });
    let fret: Kont<'a, R> = Rc::new(move |_, v| {
        *s2.borrow_mut() = Some(Flow::Return(v));
        Step::Done
    });
    (start(&M::empty(), fin, fret), slot)
}

fn finished<T>(slot: &Slot<T>) -> T {
    slot.borrow_mut()
        .take()
        .expect("tauto: the computation ended without a value (a bug in the generated code)")
}

/// Runs a computation of the M tier in a function of the S tier: every
/// operation it performs is answered inside it.
pub fn run<'a, T: 'static>(f: impl FnOnce(&M<'a>, Kont<'a, T>) -> Step<'a>) -> T {
    run_in(&Ev::empty(), f)
}

/// [`run`] in a function of the A tier: an abort no handler of the
/// computation takes goes on in the caller.
pub fn run_a<'a, T: 'static>(f: impl FnOnce(&M<'a>, Kont<'a, T>) -> Step<'a>) -> Result<T, Abort> {
    run_a_in(&Ev::empty(), f)
}

/// [`run`] in a function of the O tier: an operation no handler of the
/// computation answers is performed in the caller's.
pub async fn run_o<'a, T: 'static>(f: impl FnOnce(&M<'a>, Kont<'a, T>) -> Step<'a>) -> T {
    run_o_in(&Ev::empty(), f).await
}

/// [`run`] for a computation that holds no `direct` handler from around
/// it (the body of a `handle` whose `k` is kept as a value): a `direct`
/// operation it does not answer is answered by `ev`, the handlers of the
/// code that runs it now.
pub fn run_in<'a, T: 'static>(ev: &Ev<'_>, f: impl FnOnce(&M<'a>, Kont<'a, T>) -> Step<'a>) -> T {
    match run_a_in(ev, f) {
        Ok(v) => v,
        Err(a) => crate::a::unhandled(a),
    }
}

pub fn run_a_in<'a, T: 'static>(
    ev: &Ev<'_>,
    f: impl FnOnce(&M<'a>, Kont<'a, T>) -> Step<'a>,
) -> Result<T, Abort> {
    let (step, slot) = start(f);
    drive_a(ev, step, &slot)
}

pub async fn run_o_in<'a, T: 'static>(
    ev: &Ev<'_>,
    f: impl FnOnce(&M<'a>, Kont<'a, T>) -> Step<'a>,
) -> T {
    let (step, slot) = start(f);
    drive_o(ev, step, &slot).await
}

/// How a computation of the M tier ended, when its code can `return` from
/// the function around it: with its value, or with the function's.
pub enum Flow<T, R> {
    Value(T),
    Return(R),
}

/// [`run`] for a computation that may `return`: the second continuation
/// ends it with the value the function returns.
pub fn run_r<'a, T: 'static, R: 'static>(
    f: impl FnOnce(&M<'a>, Kont<'a, T>, Kont<'a, R>) -> Step<'a>,
) -> Flow<T, R> {
    run_r_in(&Ev::empty(), f)
}

pub fn run_ar<'a, T: 'static, R: 'static>(
    f: impl FnOnce(&M<'a>, Kont<'a, T>, Kont<'a, R>) -> Step<'a>,
) -> Result<Flow<T, R>, Abort> {
    run_ar_in(&Ev::empty(), f)
}

pub async fn run_or<'a, T: 'static, R: 'static>(
    f: impl FnOnce(&M<'a>, Kont<'a, T>, Kont<'a, R>) -> Step<'a>,
) -> Flow<T, R> {
    run_or_in(&Ev::empty(), f).await
}

pub fn run_r_in<'a, T: 'static, R: 'static>(
    ev: &Ev<'_>,
    f: impl FnOnce(&M<'a>, Kont<'a, T>, Kont<'a, R>) -> Step<'a>,
) -> Flow<T, R> {
    match run_ar_in(ev, f) {
        Ok(v) => v,
        Err(a) => crate::a::unhandled(a),
    }
}

pub fn run_ar_in<'a, T: 'static, R: 'static>(
    ev: &Ev<'_>,
    f: impl FnOnce(&M<'a>, Kont<'a, T>, Kont<'a, R>) -> Step<'a>,
) -> Result<Flow<T, R>, Abort> {
    let (step, slot) = start_r(f);
    drive_a(ev, step, &slot)
}

pub async fn run_or_in<'a, T: 'static, R: 'static>(
    ev: &Ev<'_>,
    f: impl FnOnce(&M<'a>, Kont<'a, T>, Kont<'a, R>) -> Step<'a>,
) -> Flow<T, R> {
    let (step, slot) = start_r(f);
    drive_o(ev, step, &slot).await
}

fn drive_a<'a, T>(ev: &Ev<'_>, mut step: Step<'a>, slot: &Slot<T>) -> Result<T, Abort> {
    loop {
        match step {
            Step::Done => return Ok(finished(slot)),
            Step::More(f) => step = f(),
            Step::Fail(a) => return Err(a),
            Step::Escape { op, args, at, k, m } => {
                if !ev.answers(op.id) {
                    error(messages::nothing_handles(op.name), at)
                }
                step = k(&m, ev.perform(op, args, at));
            }
            Step::NoMatch(_) => {
                panic!("tauto: an arm answered nothing (a bug in the generated code)")
            }
        }
    }
}

async fn drive_o<'a, T>(ev: &Ev<'_>, mut step: Step<'a>, slot: &Slot<T>) -> T {
    loop {
        match step {
            Step::Done => return finished(slot),
            Step::More(f) => step = f(),
            Step::Fail(a) => crate::o::reraise(a).await,
            Step::NoMatch(_) => {
                panic!("tauto: an arm answered nothing (a bug in the generated code)")
            }
            Step::Escape { op, args, at, k, m } => {
                let answer = if ev.answers(op.id) {
                    ev.perform(op, args, at)
                } else {
                    crate::o::perform(op, args, at).await
                };
                step = k(&m, answer);
            }
        }
    }
}

/// `k(a)` called outside its arm, in code of the S tier: the body goes on
/// from the operation, under the handler, to the end of the `handle`.
pub fn resume<'a, A: 'static, R: 'static>(ev: &Ev<'_>, k: &Resume<'a>, a: A) -> R {
    run_in(ev, |m, fin| k.call(m, Box::new(a), erase(fin)))
}

pub fn resume_a<'a, A: 'static, R: 'static>(ev: &Ev<'_>, k: &Resume<'a>, a: A) -> Result<R, Abort> {
    run_a_in(ev, |m, fin| k.call(m, Box::new(a), erase(fin)))
}

pub async fn resume_o<'a, A: 'static, R: 'static>(ev: &Ev<'_>, k: &Resume<'a>, a: A) -> R {
    run_o_in(ev, |m, fin| k.call(m, Box::new(a), erase(fin))).await
}

// `k` kept as a value, as a function value of the S or A tier: each call
// runs the body from the operation on, under the handler, with the
// caller's `direct` handlers answering what the body does not.
macro_rules! resume_fn {
    ($rc:ident, $boxed:ident, $run:ident; $r:ty) => {
        pub fn $rc<A: 'static, R: 'static>(k: Resume<'static>) -> Rc<dyn Fn(&Ev<'_>, A) -> $r> {
            Rc::new(move |ev, a| $run(ev, |m, fin| k.call(m, Box::new(a), erase(fin))))
        }

        pub fn $boxed<A: 'static, R: 'static>(
            k: Resume<'static>,
        ) -> Box<dyn FnOnce(&Ev<'_>, A) -> $r> {
            Box::new(move |ev, a| $run(ev, |m, fin| k.call(m, Box::new(a), erase(fin))))
        }
    };
}

resume_fn!(resume_rc, resume_box, run_in; R);
resume_fn!(resume_rc_a, resume_box_a, run_a_in; Result<R, Abort>);

// A closure of the M tier, as a value: a function of the evidence, the
// handlers in place, its arguments and its own continuation. The helpers give
// the closure that signature (a `Rc::new(closure)` alone could not).
macro_rules! mfn {
    ($rc:ident, $boxed:ident; $($a:ident),*) => {
        #[allow(non_snake_case)]
        pub fn $rc<'a, R: 'static, $($a: 'static,)* F>(f: F) -> Rc<dyn Fn(&Ev<'a>, &M<'a>, $($a,)* Kont<'a, R>) -> Step<'a> + 'a>
        where
            F: Fn(&Ev<'a>, &M<'a>, $($a,)* Kont<'a, R>) -> Step<'a> + 'a,
        {
            Rc::new(f)
        }

        #[allow(non_snake_case)]
        pub fn $boxed<'a, R: 'static, $($a: 'static,)* F>(f: F) -> Box<dyn FnOnce(&Ev<'a>, &M<'a>, $($a,)* Kont<'a, R>) -> Step<'a> + 'a>
        where
            F: FnOnce(&Ev<'a>, &M<'a>, $($a,)* Kont<'a, R>) -> Step<'a> + 'a,
        {
            Box::new(f)
        }
    };
}

mfn!(mfn_rc0, mfn_box0;);
mfn!(mfn_rc1, mfn_box1; A0);
mfn!(mfn_rc2, mfn_box2; A0, A1);
mfn!(mfn_rc3, mfn_box3; A0, A1, A2);
mfn!(mfn_rc4, mfn_box4; A0, A1, A2, A3);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_kept_resume_does_not_keep_the_code_around_the_handle() {
        const OPS: &[OpId] = &[7];
        let at = Loc {
            file: "t",
            line: 1,
            col: 1,
        };
        let around = Rc::new(());
        let alive = Rc::downgrade(&around);
        let kept: Rc<RefCell<Option<Resume<'static>>>> = Rc::default();
        {
            let into = kept.clone();
            let target = kont(move |_, _: Payload| {
                let _ = &around;
                Step::Done
            });
            let a = arm(move |_, _, _, _, _, k| {
                *into.borrow_mut() = Some(k);
                Step::Done
            });
            let m = M::empty().push(OPS, a, target);
            let step = perform(
                &m,
                Op::new(7, "tick"),
                Box::new(()),
                at,
                kont(|_, _| Step::Done),
            );
            assert!(matches!(step, Step::Done));
        }
        assert!(kept.borrow().is_some());
        assert!(
            alive.upgrade().is_none(),
            "the kept resume holds the target of its handle"
        );
    }
}
