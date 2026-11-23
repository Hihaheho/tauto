//! The machine's values.
//!
//! A value is immutable and shared (`Rc`): a copy is a new handle, and a
//! write through a borrow copies the path to the change (`Rc::make_mut`), as
//! persistent data does. A borrow (`Ref`) is a place: a root and the path of
//! fields to the part it borrows.

use std::cell::RefCell;
use std::fmt::Write as _;
use std::rc::Rc;

use crate::code::Ctor;
use crate::machine::Cont;

/// The slots of a frame: the locals of a function, shared by the frames of
/// its `handle` bodies and arms.
pub type Env = Rc<RefCell<Vec<Value>>>;

#[derive(Clone)]
pub enum Value {
    /// An opaque declaration reference supplied by a macro host.
    Declaration(tauto_rt::identity::DeclRef),
    Unit,
    Bool(bool),
    Int(i128),
    /// A `nat` past `i128`; a `nat` that fits is an `Int`.
    Nat(Rc<tauto_rt::nat::Nat>),
    Float(f64),
    Float32(f32),
    Text(Rc<str>),
    Buf(Rc<String>),
    Data(Rc<Data>),
    Inject(u32, u32, Rc<Value>),
    Vec(Rc<Vec<Value>>),
    Array(Rc<Vec<Value>>),
    Bytes(Rc<[u8]>),
    /// `Secret` of the prelude: its content, which only `expose` reads.
    Secret(Rc<Value>),
    /// `Slots`: the slots with the marks and the state kept beside them.
    Slots(Rc<SlotsVal>),
    /// `Ref`, `Mutex` and `Atomic` of the prelude: one slot every copy shares.
    Shared(SharedKind, Rc<RefCell<Value>>),
    /// `Weak` of the prelude: a handle on a `Ref`'s slot that does not keep
    /// it alive. It upgrades while some strong handle on the slot remains.
    Weak(std::rc::Weak<RefCell<Value>>),
    /// What `show` carries: the value already shown.
    Shown(Rc<str>),
    Ref(Rc<Place>),
    Fn(u32),
    Closure(Rc<Closure>),
    Cont(Rc<Cont>),
    /// A signal: raised once, never lowered.
    Signal(Rc<Signal>),
    /// The result of a task, or of a wait on the host.
    Pending(Rc<Pending>),
    /// A mutex: its content and the places in line for it.
    Mutex(Rc<RefCell<MutexState>>),
    /// A locked mutex's content: handed back when the guard is dropped.
    Guard(Rc<GuardState>),
    /// What the arm of `exceeded` gets.
    Info,
    /// What the arm of `exceeded` answers (`budget_value` and `info_*`).
    Answer(Rc<Answer>),
    Moved,
    /// A value of an extern type: the host's, which the machine only holds
    /// and hands back. The name is the type's, for showing it.
    Host(Rc<str>, Rc<dyn std::any::Any>),
}

/// What `Slots` holds: a slot that was never written, or whose value was
/// taken, is `Moved`; the drop of the slots drops the used ones only.
#[derive(Clone)]
pub struct SlotsVal {
    pub state: Value,
    /// The mark of a slot that holds no value.
    pub vacant: Value,
    pub marks: Vec<Value>,
    pub items: Vec<Value>,
}

#[derive(Default)]
pub struct Signal {
    pub inputs: Vec<Rc<Signal>>,
    pub raised: std::cell::Cell<bool>,
    /// What a `mutex_put` hands to the place the signal stands for.
    pub handed: RefCell<Option<Value>>,
    /// Raised by a request to end the run (`Os::on_shutdown`).
    pub outside: RefCell<Option<tauto_rt::signal::Signal>>,
}

impl Signal {
    fn own(&self) -> bool {
        self.raised.get()
            || self.outside.borrow().as_ref().is_some_and(|s| {
                tauto_rt::shutdown::poll();
                s.is_raised()
            })
    }
    pub fn is_raised(&self) -> bool {
        self.own() || self.inputs.iter().any(|s| s.own())
    }
    pub fn raise(&self) {
        self.raised.set(true);
    }
}

pub struct Pending {
    pub state: RefCell<PendingState>,
    /// Raised when the result is there.
    pub signal: Rc<Signal>,
}

pub enum PendingState {
    Ready(Value),
    Running,
    /// A sleep that ends at the instant.
    Timer(std::time::Instant),
    /// The task ended with this runtime error.
    Failed(String),
    Taken,
}

impl Pending {
    pub fn new(state: PendingState) -> Rc<Pending> {
        let signal = Rc::new(Signal::default());
        if matches!(state, PendingState::Ready(_)) {
            signal.raise();
        }
        Rc::new(Pending {
            state: RefCell::new(state),
            signal,
        })
    }

    pub fn finish(&self, v: Value) {
        *self.state.borrow_mut() = PendingState::Ready(v);
        self.signal.raise();
    }

    /// Whether the result is there; a sleep whose time has come ends.
    pub fn ready(&self) -> bool {
        let due = match &*self.state.borrow() {
            PendingState::Timer(at) => *at <= std::time::Instant::now(),
            PendingState::Running => false,
            _ => true,
        };
        if due && matches!(&*self.state.borrow(), PendingState::Timer(_)) {
            self.finish(Value::Unit);
        }
        due
    }
}

#[derive(Default)]
pub struct MutexState {
    pub value: Option<Value>,
    pub waiting: std::collections::VecDeque<Rc<Signal>>,
    /// A task that held the content failed: taking from it fails.
    pub poisoned: bool,
}

impl MutexState {
    /// Hands `v` to the first place in line, or keeps it if there is none.
    pub fn put(&mut self, v: Value) {
        match self.waiting.pop_front() {
            Some(s) => {
                *s.handed.borrow_mut() = Some(v);
                s.raise();
            }
            None => self.value = Some(v),
        }
    }
}

/// What `MutexGuard::claimed` made: the mutex and the content taken from it.
pub struct GuardState {
    pub mutex: Rc<RefCell<MutexState>>,
    pub content: Rc<RefCell<Value>>,
}

impl Drop for GuardState {
    fn drop(&mut self) {
        let v = std::mem::replace(&mut *self.content.borrow_mut(), Value::Moved);
        if !matches!(v, Value::Moved) && !self.mutex.borrow().poisoned {
            self.mutex.borrow_mut().put(v);
        }
    }
}

pub enum Answer {
    /// The budget's value: its body stops.
    Value(Value),
    /// More steps (or cells), or no more limit: the body goes on.
    More(Option<i128>),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SharedKind {
    Ref,
    Mutex,
    Atomic,
}

pub struct Data {
    pub ctor: Rc<Ctor>,
    pub fields: Vec<Value>,
}

impl Clone for Data {
    fn clone(&self) -> Self {
        Data {
            ctor: self.ctor.clone(),
            fields: self.fields.clone(),
        }
    }
}

pub struct Closure {
    pub code: u32,
    /// The captured values, by the slot they take in the closure's frame.
    pub captures: Vec<(u32, Value)>,
}

pub struct Place {
    pub root: Root,
    pub path: Path,
    /// The value at the root when the place was last read, and the value the
    /// path named then. A value is never changed in place while another handle
    /// holds it (a write copies the path to the change), so while the root
    /// still holds that same value the path names the same part: a read takes
    /// it instead of walking the path, and a borrow one step further down finds
    /// its part at once. What it keeps does not keep a vector, map, buffer or
    /// constructor value alive (`Held`): were the place to hold them, a write
    /// through another place on the same root would copy the whole value
    /// instead of changing it in place, and a recursion whose frames each
    /// hold a place would hold a copy for every frame.
    seen: RefCell<Option<(Held, Held)>>,
}

/// A value a place keeps, without keeping the parts a write changes in place
/// alive. While the root still holds the value, upgrading it succeeds.
#[derive(Clone)]
enum Held {
    Value(Value),
    Data(std::rc::Weak<Data>),
    Inject(u32, u32, std::rc::Weak<Value>),
    Vec(std::rc::Weak<Vec<Value>>),
    Array(std::rc::Weak<Vec<Value>>),
    Slots(std::rc::Weak<SlotsVal>),
    Buf(std::rc::Weak<String>),
}

impl Held {
    fn of(v: &Value) -> Held {
        match v {
            Value::Data(x) => Held::Data(Rc::downgrade(x)),
            Value::Inject(a, b, x) => Held::Inject(*a, *b, Rc::downgrade(x)),
            Value::Vec(x) => Held::Vec(Rc::downgrade(x)),
            Value::Array(x) => Held::Array(Rc::downgrade(x)),
            Value::Slots(x) => Held::Slots(Rc::downgrade(x)),
            Value::Buf(x) => Held::Buf(Rc::downgrade(x)),
            v => Held::Value(v.clone()),
        }
    }

    fn get(&self) -> Option<Value> {
        Some(match self {
            Held::Value(v) => v.clone(),
            Held::Data(x) => Value::Data(x.upgrade()?),
            Held::Inject(a, b, x) => Value::Inject(*a, *b, x.upgrade()?),
            Held::Vec(x) => Value::Vec(x.upgrade()?),
            Held::Array(x) => Value::Array(x.upgrade()?),
            Held::Slots(x) => Value::Slots(x.upgrade()?),
            Held::Buf(x) => Value::Buf(x.upgrade()?),
        })
    }
}

/// Whether `a` and `b` are the same handle on one value (not merely equal).
fn same(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Data(x), Value::Data(y)) => Rc::ptr_eq(x, y),
        (Value::Inject(_, _, x), Value::Inject(_, _, y)) => Rc::ptr_eq(x, y),
        (Value::Vec(x), Value::Vec(y)) | (Value::Array(x), Value::Array(y)) => Rc::ptr_eq(x, y),
        (Value::Slots(x), Value::Slots(y)) => Rc::ptr_eq(x, y),
        _ => false,
    }
}

/// A place's path, its most recent step first, so that a step further down
/// shares the steps before it.
#[derive(Clone, Default)]
pub struct Path(Option<Rc<(Step, Path)>>);

impl Path {
    pub fn of(steps: &[Step]) -> Path {
        let mut p = Path::default();
        for s in steps {
            p = p.then(s.clone());
        }
        p
    }

    pub fn then(&self, step: Step) -> Path {
        Path(Some(Rc::new((step, self.clone()))))
    }

    pub fn extended(&self, steps: &[Step]) -> Path {
        let mut p = self.clone();
        for s in steps {
            p = p.then(s.clone());
        }
        p
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// The steps from the root.
    pub fn steps(&self) -> Vec<Step> {
        let mut out = Vec::new();
        let mut p = self;
        while let Some(node) = &p.0 {
            out.push(node.0.clone());
            p = &node.1;
        }
        out.reverse();
        out
    }
}

pub enum Root {
    Slot(Env, u32),
    /// A cell: a shared `var`, or a temporary that was borrowed.
    Cell(Rc<RefCell<Value>>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Step {
    /// A field of a constructor or a member of a product, by index.
    Index(usize),
    /// A field by name, found in the constructor's names.
    Name(Rc<str>),
    Item(usize),
}

pub type R<T> = Result<T, Error>;

/// What ends a run that does not end normally.
#[derive(Debug)]
pub enum Error {
    Runtime(String),
    Exit(i32),
}

pub fn fail<T>(message: impl Into<String>) -> R<T> {
    Err(Error::Runtime(message.into()))
}

pub const TOO_LARGE: &str = "the number is too large";

impl Value {
    pub fn text(s: &str) -> Value {
        Value::Text(Rc::from(s))
    }

    /// The value a borrow points at; any other value is itself.
    pub fn get(&self) -> R<Value> {
        match self {
            Value::Ref(p) => p.get(),
            v => Ok(v.clone()),
        }
    }

    pub fn as_int(&self) -> R<i128> {
        match self {
            Value::Int(n) => Ok(*n),
            Value::Nat(_) => fail(TOO_LARGE),
            Value::Ref(p) => p.get()?.as_int(),
            v => fail(format!("internal: expected an integer, got {}", v.kind())),
        }
    }

    /// The `nat` this integer or big `nat` is; a negative integer is none.
    pub fn as_nat(&self) -> R<tauto_rt::nat::Nat> {
        match self {
            Value::Int(n) => match u128::try_from(*n) {
                Ok(n) => Ok(tauto_rt::nat::Nat::from_u128(n)),
                Err(_) => fail(TOO_LARGE),
            },
            Value::Nat(n) => Ok((**n).clone()),
            Value::Ref(p) => p.get()?.as_nat(),
            v => fail(format!("internal: expected a nat, got {}", v.kind())),
        }
    }

    /// The `nat` `n` as a value: an `Int` when it fits in `i128`.
    pub fn of_nat(n: tauto_rt::nat::Nat) -> Value {
        match n.to_u128().map(i128::try_from) {
            Some(Ok(n)) => Value::Int(n),
            _ => Value::Nat(Rc::new(n)),
        }
    }

    pub fn as_bool(&self) -> R<bool> {
        match self {
            Value::Bool(b) => Ok(*b),
            Value::Ref(p) => p.get()?.as_bool(),
            v => fail(format!("internal: expected a Bool, got {}", v.kind())),
        }
    }

    pub fn as_float(&self) -> R<f64> {
        match self {
            Value::Float(x) => Ok(*x),
            Value::Ref(p) => p.get()?.as_float(),
            v => fail(format!("internal: expected a Float, got {}", v.kind())),
        }
    }

    pub fn as_float32(&self) -> R<f32> {
        match self {
            Value::Float32(x) => Ok(*x),
            Value::Ref(p) => p.get()?.as_float32(),
            v => fail(format!("internal: expected a Float32, got {}", v.kind())),
        }
    }

    pub fn as_text(&self) -> R<Rc<str>> {
        match self {
            Value::Text(t) => Ok(t.clone()),
            Value::Buf(b) => Ok(Rc::from(b.as_str())),
            Value::Ref(p) => p.get()?.as_text(),
            v => fail(format!("internal: expected a Text, got {}", v.kind())),
        }
    }

    pub fn kind(&self) -> &'static str {
        match self {
            Value::Declaration(_) => "a declaration reference",
            Value::Unit => "()",
            Value::Bool(_) => "Bool",
            Value::Int(_) | Value::Nat(_) => "an integer",
            Value::Float(_) => "Float",
            Value::Float32(_) => "Float32",
            Value::Text(_) => "Text",
            Value::Buf(_) => "Buf",
            Value::Data(_) => "a constructor",
            Value::Inject(..) => "a union",
            Value::Vec(_) => "Vec",
            Value::Array(_) => "Array",
            Value::Bytes(_) => "Bytes",
            Value::Secret(_) => "Secret",
            Value::Slots(_) => "Slots",
            Value::Shared(..) => "a shared slot",
            Value::Weak(_) => "Weak",
            Value::Shown(_) => "a shown value",
            Value::Ref(_) => "a borrow",
            Value::Fn(_) | Value::Closure(_) => "a function",
            Value::Cont(_) => "a continuation",
            Value::Signal(_) => "Signal",
            Value::Pending(_) => "Pending",
            Value::Mutex(_) => "Mutex",
            Value::Guard(_) => "MutexGuard",
            Value::Info => "Info",
            Value::Answer(_) => "a budget answer",
            Value::Moved => "a moved value",
            Value::Host(..) => "a value of an extern type",
        }
    }

    pub fn at(&self, step: &Step) -> R<Value> {
        match (self, step) {
            (Value::Ref(p), _) => p.get()?.at(step),
            // What a union value holds, as a pattern on its member reaches it.
            (Value::Inject(_, _, x), Step::Index(0)) => Ok((**x).clone()),
            (Value::Data(d), Step::Index(i)) => d
                .fields
                .get(*i)
                .cloned()
                .ok_or_else(|| internal("a field index")),
            (Value::Data(d), Step::Name(n)) => {
                let i = d.ctor.field(n)?;
                Ok(d.fields[i].clone())
            }
            (Value::Vec(xs) | Value::Array(xs), Step::Item(i)) => {
                xs.get(*i).cloned().ok_or_else(|| internal("an item"))
            }
            (Value::Slots(r), Step::Item(i)) => match r.items.get(*i) {
                Some(Value::Moved) => fail("internal: a slot that holds no value"),
                Some(x) => Ok(x.clone()),
                None => Err(internal("a slot")),
            },
            (v, s) => fail(format!("internal: no {s:?} in {}", v.kind())),
        }
    }

    /// The part of the value at one step, to change in place.
    pub fn at_mut(&mut self, step: &Step) -> R<&mut Value> {
        match (self, step) {
            (Value::Inject(_, _, x), Step::Index(0)) => Ok(Rc::make_mut(x)),
            (Value::Data(d), Step::Index(i)) => {
                let d = Rc::make_mut(d);
                d.fields
                    .get_mut(*i)
                    .ok_or_else(|| internal("a field index"))
            }
            (Value::Data(d), Step::Name(n)) => {
                let i = d.ctor.field(n)?;
                Ok(&mut Rc::make_mut(d).fields[i])
            }
            (Value::Vec(xs) | Value::Array(xs), Step::Item(i)) => Rc::make_mut(xs)
                .get_mut(*i)
                .ok_or_else(|| internal("an item")),
            (Value::Slots(r), Step::Item(i)) => Rc::make_mut(r)
                .items
                .get_mut(*i)
                .ok_or_else(|| internal("a slot")),
            (v, s) => fail(format!("internal: no {s:?} to change in {}", v.kind())),
        }
    }
}

fn internal(what: &str) -> Error {
    Error::Runtime(format!("internal: {what} out of range"))
}

impl Place {
    pub fn new(root: Root, path: Path) -> Place {
        Place {
            root,
            path,
            seen: RefCell::new(None),
        }
    }

    fn root_value(&self) -> Value {
        match &self.root {
            Root::Slot(env, i) => env.borrow()[*i as usize].clone(),
            Root::Cell(c) => c.borrow().clone(),
        }
    }

    /// What the place kept, with the root's value, while the root holds it.
    fn kept(&self) -> Option<(Value, Value)> {
        let seen = self.seen.borrow();
        let (root, part) = seen.as_ref()?;
        // A dropped root fails to upgrade; one that upgrades is still
        // allocated, so the same handle is the same value.
        let root = root.get()?;
        if !same(&root, &self.root_value()) {
            return None;
        }
        Some((root, part.get()?))
    }

    pub fn get(&self) -> R<Value> {
        if let Some((_, part)) = self.kept() {
            return Ok(part);
        }
        let v = self.walk()?;
        let root = self.root_value();
        if !matches!(v, Value::Ref(_)) && !through_ref(&root, &self.path.steps()) {
            *self.seen.borrow_mut() = Some((Held::of(&root), Held::of(&v)));
        }
        Ok(v)
    }

    fn walk(&self) -> R<Value> {
        let mut v = match &self.root {
            Root::Slot(env, i) => env.borrow()[*i as usize].clone(),
            Root::Cell(c) => c.borrow().clone(),
        };
        // A borrow stored in the place is read through.
        if let Value::Ref(p) = &v {
            v = p.get()?;
        }
        for s in &self.path.steps() {
            v = v.at(s)?;
            if let Value::Ref(p) = &v {
                v = p.get()?;
            }
        }
        Ok(v)
    }

    pub fn with_mut<T>(&self, f: impl FnOnce(&mut Value) -> R<T>) -> R<T> {
        let path = self.path.steps();
        match &self.root {
            Root::Slot(env, i) => {
                let inner = match &env.borrow()[*i as usize] {
                    Value::Ref(p) => Some(p.clone()),
                    _ => None,
                };
                match inner {
                    Some(p) => p.with_path_mut(&path, f),
                    None => {
                        let mut slots = env.borrow_mut();
                        walk_mut(&mut slots[*i as usize], &path, f)
                    }
                }
            }
            Root::Cell(c) => {
                let inner = match &*c.borrow() {
                    Value::Ref(p) => Some(p.clone()),
                    _ => None,
                };
                match inner {
                    Some(p) => p.with_path_mut(&path, f),
                    None => walk_mut(&mut c.borrow_mut(), &path, f),
                }
            }
        }
    }

    fn with_path_mut<T>(&self, more: &[Step], f: impl FnOnce(&mut Value) -> R<T>) -> R<T> {
        Place::new(
            match &self.root {
                Root::Slot(e, i) => Root::Slot(e.clone(), *i),
                Root::Cell(c) => Root::Cell(c.clone()),
            },
            self.path.extended(more),
        )
        .with_mut(f)
    }

    pub fn set(&self, v: Value) -> R<()> {
        self.with_mut(|slot| {
            *slot = v;
            Ok(())
        })
    }

    /// The place `steps` further down, keeping what this one keeps.
    pub fn further(&self, steps: &[Step]) -> Place {
        let mut p = Place {
            root: match &self.root {
                Root::Slot(e, i) => Root::Slot(e.clone(), *i),
                Root::Cell(c) => Root::Cell(c.clone()),
            },
            path: self.path.clone(),
            seen: RefCell::new(self.seen.borrow().clone()),
        };
        for s in steps {
            p = p.child(s.clone());
        }
        p
    }

    pub fn child(&self, step: Step) -> Place {
        let seen = self.kept().and_then(|(root, v)| match v.at(&step).ok()? {
            Value::Ref(_) => None,
            part => Some((Held::of(&root), Held::of(&part))),
        });
        Place {
            root: match &self.root {
                Root::Slot(e, i) => Root::Slot(e.clone(), *i),
                Root::Cell(c) => Root::Cell(c.clone()),
            },
            path: self.path.then(step),
            seen: RefCell::new(seen),
        }
    }
}

/// Whether the path from `root` goes through a borrow held in the value: what
/// it names then depends on another root, so the place keeps nothing.
fn through_ref(root: &Value, path: &[Step]) -> bool {
    let mut v = root.clone();
    if matches!(v, Value::Ref(_)) {
        return true;
    }
    for s in path {
        match v.at(s) {
            Ok(Value::Ref(_)) | Err(_) => return true,
            Ok(next) => v = next,
        }
    }
    false
}

fn walk_mut<T>(v: &mut Value, path: &[Step], f: impl FnOnce(&mut Value) -> R<T>) -> R<T> {
    let Some((first, rest)) = path.split_first() else {
        return f(v);
    };
    if let Value::Ref(p) = v {
        let p = p.clone();
        return p.with_path_mut(path, f);
    }
    let next = v.at_mut(first)?;
    if let Value::Ref(p) = next {
        let p = p.clone();
        return p.with_path_mut(rest, f);
    }
    walk_mut(next, rest, f)
}

/// A temporary borrowed: a cell of its own.
pub fn temp_ref(v: Value) -> Value {
    Value::Ref(Rc::new(Place::new(
        Root::Cell(Rc::new(RefCell::new(v))),
        Path::default(),
    )))
}

/// Whether two values are equal, as `==` compares them. The parts are
/// compared from a list of pairs still to compare, not by recursion: a long
/// list compared with `==` is as deep as it is long, deeper than a thread's
/// stack holds.
pub fn equal(a: &Value, b: &Value) -> R<bool> {
    let mut pending: Vec<(Value, Value)> = vec![(a.clone(), b.clone())];
    while let Some((a, b)) = pending.pop() {
        let (a, b) = (a.get()?, b.get()?);
        // Parts are pushed last first, so that they are compared in order.
        let same = match (&a, &b) {
            (Value::Inject(_, _, x), _) => {
                pending.push(((**x).clone(), b.clone()));
                true
            }
            (_, Value::Inject(_, _, y)) => {
                pending.push((a.clone(), (**y).clone()));
                true
            }
            (Value::Declaration(x), Value::Declaration(y)) => x == y,
            (Value::Unit, Value::Unit) => true,
            (Value::Bool(x), Value::Bool(y)) => x == y,
            (Value::Int(x), Value::Int(y)) => x == y,
            (Value::Nat(x), Value::Nat(y)) => x == y,
            (Value::Float(x), Value::Float(y)) => x == y,
            (Value::Float32(x), Value::Float32(y)) => x == y,
            (Value::Text(x), Value::Text(y)) => x == y,
            (Value::Buf(x), Value::Buf(y)) => x == y,
            (Value::Shown(x), Value::Shown(y)) => x == y,
            (Value::Bytes(x), Value::Bytes(y)) => x == y,
            (Value::Data(x), Value::Data(y)) => {
                if Rc::ptr_eq(x, y) {
                    true
                } else if x.ctor.id != y.ctor.id || x.fields.len() != y.fields.len() {
                    false
                } else {
                    for (p, q) in x.fields.iter().zip(&y.fields).rev() {
                        pending.push((p.clone(), q.clone()));
                    }
                    true
                }
            }
            (Value::Vec(x), Value::Vec(y)) | (Value::Array(x), Value::Array(y)) => {
                if x.len() != y.len() {
                    false
                } else {
                    for (p, q) in x.iter().zip(y.iter()).rev() {
                        pending.push((p.clone(), q.clone()));
                    }
                    true
                }
            }
            (Value::Shared(_, x), Value::Shared(_, y)) => Rc::ptr_eq(x, y),
            (Value::Weak(x), Value::Weak(y)) => std::rc::Weak::ptr_eq(x, y),
            (Value::Signal(x), Value::Signal(y)) => Rc::ptr_eq(x, y),
            (Value::Mutex(x), Value::Mutex(y)) => Rc::ptr_eq(x, y),
            (Value::Guard(x), Value::Guard(y)) => Rc::ptr_eq(x, y),
            _ => false,
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}

/// The value as `show` writes it.
pub fn show(v: &Value) -> R<String> {
    let mut out = String::new();
    show_into(v, &mut out)?;
    Ok(out)
}

/// Whether `d` is a `Pair`, which `#(a, b)` is.
fn is_pair(d: &Data) -> bool {
    d.fields.len() == 2 && d.ctor.is_struct && tauto_nir::display_name(&d.ctor.owner) == "Pair"
}

fn show_into(v: &Value, out: &mut String) -> R<()> {
    let list = |out: &mut String, items: &[Value], open: &str, close: &str| -> R<()> {
        out.push_str(open);
        for (i, x) in items.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            show_into(x, out)?;
        }
        out.push_str(close);
        Ok(())
    };
    match v {
        Value::Ref(p) => show_into(&p.get()?, out)?,
        Value::Host(name, _) => {
            out.push('<');
            out.push_str(name);
            out.push('>');
        }
        Value::Unit => out.push_str("()"),
        Value::Bool(b) => write!(out, "{b}").unwrap(),
        Value::Int(n) => write!(out, "{n}").unwrap(),
        Value::Nat(n) => write!(out, "{n}").unwrap(),
        Value::Float(x) => out.push_str(&tauto_rt::float::text_of_float(*x)),
        Value::Float32(x) => out.push_str(&tauto_rt::float::text_of_float(f64::from(*x))),
        Value::Text(t) => write!(out, "{:?}", &**t).unwrap(),
        Value::Buf(b) => write!(out, "Buf({:?})", b.as_str()).unwrap(),
        Value::Shown(t) => out.push_str(t),
        Value::Inject(_, _, x) => show_into(x, out)?,
        Value::Vec(xs) => list(out, xs, "Vec[", "]")?,
        Value::Array(xs) => list(out, xs, "Array[", "]")?,
        Value::Bytes(b) => {
            out.push_str("Bytes[");
            for (i, x) in b.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write!(out, "{x}").unwrap();
            }
            out.push(']');
        }
        Value::Shared(SharedKind::Ref, c) => {
            out.push_str("Ref(");
            let inner = c.borrow().clone();
            show_into(&inner, out)?;
            out.push(')');
        }
        Value::Shared(SharedKind::Atomic, c) => {
            out.push_str("Atomic(");
            let inner = c.borrow().clone();
            show_into(&inner, out)?;
            out.push(')');
        }
        Value::Shared(SharedKind::Mutex, _) | Value::Mutex(_) => out.push_str("Mutex"),
        Value::Weak(_) => out.push_str("Weak"),
        Value::Signal(_) => out.push_str("Signal"),
        Value::Guard(_) => out.push_str("MutexGuard"),
        // A secret's content is never shown.
        Value::Secret(_) => out.push_str("Secret"),
        Value::Declaration(_) => {
            write!(out, "<declaration reference>").unwrap();
        }
        Value::Pending(_) => out.push_str("Pending"),
        // `#(a, b, c)`: the `Pair`s nested to the right, as the value was written.
        Value::Data(d) if is_pair(d) => {
            out.push_str("#(");
            show_into(&d.fields[0], out)?;
            let mut rest = d.fields[1].clone();
            loop {
                let next = match &rest {
                    Value::Data(r) if is_pair(r) => {
                        out.push_str(", ");
                        show_into(&r.fields[0], out)?;
                        r.fields[1].clone()
                    }
                    _ => break,
                };
                rest = next;
            }
            out.push_str(", ");
            show_into(&rest, out)?;
            out.push(')');
        }
        Value::Data(d) => {
            let tag = if d.ctor.is_struct {
                tauto_nir::display_name(&d.ctor.owner)
            } else {
                d.ctor.tag.rsplit("::").next().unwrap_or(&d.ctor.tag)
            };
            let named = d.ctor.names.iter().all(Option::is_some);
            if (d.ctor.is_struct || !d.fields.is_empty()) && named {
                out.push_str(tag);
                out.push_str(" {");
                if !d.fields.is_empty() {
                    out.push(' ');
                    for (i, x) in d.fields.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        out.push_str(d.ctor.names[i].as_deref().unwrap_or(""));
                        out.push_str(": ");
                        show_into(x, out)?;
                    }
                    out.push(' ');
                }
                out.push('}');
            } else {
                out.push_str(tag);
                if !d.fields.is_empty() {
                    list(out, &d.fields, "(", ")")?;
                }
            }
        }
        v => return fail(format!("internal: cannot show {}", v.kind())),
    }
    Ok(())
}

#[cfg(test)]
mod declaration_tests {
    use super::*;

    #[test]
    fn declaration_values_keep_identity_and_do_not_coerce_to_scalars() {
        let reference = tauto_rt::identity::DeclRef::fresh("same");
        let value = Value::Declaration(reference.clone());
        let other = Value::Declaration(tauto_rt::identity::DeclRef::fresh("same"));
        assert!(equal(&value, &value.clone()).unwrap());
        assert!(!equal(&value, &other).unwrap());
        assert!(value.as_text().is_err());
        assert!(value.as_int().is_err());
        let borrowed = temp_ref(value);
        assert!(equal(&borrowed, &Value::Declaration(reference)).unwrap());
    }
}

/// The `i`-th argument of a builtin. The checker and the prelude fix how many
/// arguments each builtin takes, so a call with fewer is malformed bytecode:
/// it stops with an internal error instead of indexing past the end.
pub fn arg(a: &[Value], i: usize) -> R<&Value> {
    match a.get(i) {
        Some(x) => Ok(x),
        None => fail(format!(
            "internal: a builtin read argument {i} of {} arguments",
            a.len()
        )),
    }
}
