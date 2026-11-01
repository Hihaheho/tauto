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
    Unit,
    Bool(bool),
    /// Every width of integer, `nat` included, checked to its range.
    Int(i128),
    Float(f64),
    Float32(f32),
    Text(Rc<str>),
    /// `Buf`: a text that grows.
    Buf(Rc<String>),
    Data(Rc<Data>),
    /// A product's members.
    Product(Rc<Vec<Value>>),
    /// A member of a union.
    Inject(u32, u32, Rc<Value>),
    Vec(Rc<Vec<Value>>),
    Array(Rc<Vec<Value>>),
    Bytes(Rc<[u8]>),
    /// `Secret` of the prelude: its content, which only `expose` reads.
    Secret(Rc<Value>),
    /// `HashMap`, in insertion order.
    Map(Rc<Vec<(Value, Value)>>),
    /// `Ref`, `Mutex` and `Atomic` of the prelude: one slot every copy shares.
    Shared(SharedKind, Rc<RefCell<Value>>),
    /// What `show` carries: the value already shown.
    Shown(Rc<str>),
    /// A borrow of a place.
    Ref(Rc<Place>),
    /// A function of the program.
    Fn(u32),
    Closure(Rc<Closure>),
    /// A continuation of a handler arm.
    Cont(Rc<Cont>),
    /// A signal: raised once, never lowered.
    Signal(Rc<Signal>),
    /// The result of a task, or of a wait on the host.
    Pending(Rc<Pending>),
    /// A mutex: its content and the places in line for it.
    Mutex(Rc<RefCell<MutexState>>),
    /// What the arm of `exceeded` gets.
    Info,
    /// What the arm of `exceeded` answers (`budget_value` and `info_*`).
    Answer(Rc<Answer>),
    /// A moved-out slot.
    Moved,
}

#[derive(Default)]
pub struct Signal {
    pub raised: std::cell::Cell<bool>,
    /// What a `mutex_put` hands to the place the signal stands for.
    pub handed: RefCell<Option<Value>>,
}

impl Signal {
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
    /// A task that still runs.
    Running,
    /// A sleep that ends at the instant.
    Timer(std::time::Instant),
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

/// Where a borrow points.
pub struct Place {
    pub root: Root,
    pub path: Vec<Step>,
}

pub enum Root {
    /// A slot of a frame.
    Slot(Env, u32),
    /// A cell: a shared `var`, or a temporary that was borrowed.
    Cell(Rc<RefCell<Value>>),
}

/// A step of a path.
#[derive(Clone, Debug, PartialEq)]
pub enum Step {
    /// A field of a constructor or a member of a product, by index.
    Index(usize),
    /// A field by name, found in the constructor's names.
    Name(Rc<str>),
    /// An item of a `Vec` or an `Array`.
    Item(usize),
    /// The value of a `HashMap` entry.
    Entry(usize),
}

pub type R<T> = Result<T, Error>;

/// What ends a run that does not end normally.
#[derive(Debug)]
pub enum Error {
    /// A run-time error: the message.
    Runtime(String),
    /// `exit(code)`.
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
            Value::Ref(p) => p.get()?.as_int(),
            v => fail(format!("internal: expected an integer, got {}", v.kind())),
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
            Value::Unit => "()",
            Value::Bool(_) => "Bool",
            Value::Int(_) => "an integer",
            Value::Float(_) => "Float",
            Value::Float32(_) => "Float32",
            Value::Text(_) => "Text",
            Value::Buf(_) => "Buf",
            Value::Data(_) => "a constructor",
            Value::Product(_) => "a product",
            Value::Inject(..) => "a union",
            Value::Vec(_) => "Vec",
            Value::Array(_) => "Array",
            Value::Bytes(_) => "Bytes",
            Value::Secret(_) => "Secret",
            Value::Map(_) => "HashMap",
            Value::Shared(..) => "a shared slot",
            Value::Shown(_) => "a shown value",
            Value::Ref(_) => "a borrow",
            Value::Fn(_) | Value::Closure(_) => "a function",
            Value::Cont(_) => "a continuation",
            Value::Signal(_) => "Signal",
            Value::Pending(_) => "Pending",
            Value::Mutex(_) => "Mutex",
            Value::Info => "Info",
            Value::Answer(_) => "a budget answer",
            Value::Moved => "a moved value",
        }
    }

    /// The part of the value at one step.
    pub fn at(&self, step: &Step) -> R<Value> {
        match (self, step) {
            (Value::Ref(p), _) => p.get()?.at(step),
            (Value::Data(d), Step::Index(i)) => d
                .fields
                .get(*i)
                .cloned()
                .ok_or_else(|| internal("a field index")),
            (Value::Data(d), Step::Name(n)) => {
                let i = d.ctor.field(n)?;
                Ok(d.fields[i].clone())
            }
            (Value::Product(ms), Step::Index(i)) => {
                ms.get(*i).cloned().ok_or_else(|| internal("a member"))
            }
            (Value::Vec(xs) | Value::Array(xs), Step::Item(i)) => {
                xs.get(*i).cloned().ok_or_else(|| internal("an item"))
            }
            (Value::Map(m), Step::Entry(i)) => m
                .get(*i)
                .map(|e| e.1.clone())
                .ok_or_else(|| internal("an entry")),
            (v, s) => fail(format!("internal: no {s:?} in {}", v.kind())),
        }
    }

    /// The part of the value at one step, to change in place.
    pub fn at_mut(&mut self, step: &Step) -> R<&mut Value> {
        match (self, step) {
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
            (Value::Product(ms), Step::Index(i)) => Rc::make_mut(ms)
                .get_mut(*i)
                .ok_or_else(|| internal("a member")),
            (Value::Vec(xs) | Value::Array(xs), Step::Item(i)) => Rc::make_mut(xs)
                .get_mut(*i)
                .ok_or_else(|| internal("an item")),
            (Value::Map(m), Step::Entry(i)) => Rc::make_mut(m)
                .get_mut(*i)
                .map(|e| &mut e.1)
                .ok_or_else(|| internal("an entry")),
            (v, s) => fail(format!("internal: no {s:?} to change in {}", v.kind())),
        }
    }
}

fn internal(what: &str) -> Error {
    Error::Runtime(format!("internal: {what} out of range"))
}

impl Place {
    pub fn get(&self) -> R<Value> {
        let mut v = match &self.root {
            Root::Slot(env, i) => env.borrow()[*i as usize].clone(),
            Root::Cell(c) => c.borrow().clone(),
        };
        // A borrow stored in the place is read through.
        if let Value::Ref(p) = &v {
            v = p.get()?;
        }
        for s in &self.path {
            v = v.at(s)?;
            if let Value::Ref(p) = &v {
                v = p.get()?;
            }
        }
        Ok(v)
    }

    /// Changes the value at the place with `f`.
    pub fn with_mut<T>(&self, f: impl FnOnce(&mut Value) -> R<T>) -> R<T> {
        match &self.root {
            Root::Slot(env, i) => {
                let inner = match &env.borrow()[*i as usize] {
                    Value::Ref(p) => Some(p.clone()),
                    _ => None,
                };
                match inner {
                    Some(p) => p.with_path_mut(&self.path, f),
                    None => {
                        let mut slots = env.borrow_mut();
                        walk_mut(&mut slots[*i as usize], &self.path, f)
                    }
                }
            }
            Root::Cell(c) => {
                let inner = match &*c.borrow() {
                    Value::Ref(p) => Some(p.clone()),
                    _ => None,
                };
                match inner {
                    Some(p) => p.with_path_mut(&self.path, f),
                    None => walk_mut(&mut c.borrow_mut(), &self.path, f),
                }
            }
        }
    }

    fn with_path_mut<T>(&self, more: &[Step], f: impl FnOnce(&mut Value) -> R<T>) -> R<T> {
        let mut path = self.path.clone();
        path.extend(more.iter().cloned());
        Place {
            root: match &self.root {
                Root::Slot(e, i) => Root::Slot(e.clone(), *i),
                Root::Cell(c) => Root::Cell(c.clone()),
            },
            path,
        }
        .with_mut(f)
    }

    pub fn set(&self, v: Value) -> R<()> {
        self.with_mut(|slot| {
            *slot = v;
            Ok(())
        })
    }

    /// The place one step further.
    pub fn child(&self, step: Step) -> Place {
        let mut path = self.path.clone();
        path.push(step);
        Place {
            root: match &self.root {
                Root::Slot(e, i) => Root::Slot(e.clone(), *i),
                Root::Cell(c) => Root::Cell(c.clone()),
            },
            path,
        }
    }
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
    Value::Ref(Rc::new(Place {
        root: Root::Cell(Rc::new(RefCell::new(v))),
        path: Vec::new(),
    }))
}

/// Whether two values are equal, as `==` compares them.
pub fn equal(a: &Value, b: &Value) -> R<bool> {
    let (a, b) = (a.get()?, b.get()?);
    Ok(match (&a, &b) {
        (Value::Inject(_, _, x), _) => return equal(x, &b),
        (_, Value::Inject(_, _, y)) => return equal(&a, y),
        (Value::Unit, Value::Unit) => true,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Float(x), Value::Float(y)) => x == y,
        (Value::Float32(x), Value::Float32(y)) => x == y,
        (Value::Text(x), Value::Text(y)) => x == y,
        (Value::Buf(x), Value::Buf(y)) => x == y,
        (Value::Shown(x), Value::Shown(y)) => x == y,
        (Value::Bytes(x), Value::Bytes(y)) => x == y,
        (Value::Data(x), Value::Data(y)) => {
            if Rc::ptr_eq(x, y) {
                return Ok(true);
            }
            if x.ctor.id != y.ctor.id || x.fields.len() != y.fields.len() {
                return Ok(false);
            }
            for (p, q) in x.fields.iter().zip(&y.fields) {
                if !equal(p, q)? {
                    return Ok(false);
                }
            }
            true
        }
        (Value::Product(x), Value::Product(y))
        | (Value::Vec(x), Value::Vec(y))
        | (Value::Array(x), Value::Array(y)) => {
            if x.len() != y.len() {
                return Ok(false);
            }
            for (p, q) in x.iter().zip(y.iter()) {
                if !equal(p, q)? {
                    return Ok(false);
                }
            }
            true
        }
        (Value::Map(x), Value::Map(y)) => {
            if x.len() != y.len() {
                return Ok(false);
            }
            for ((k1, v1), (k2, v2)) in x.iter().zip(y.iter()) {
                if !equal(k1, k2)? || !equal(v1, v2)? {
                    return Ok(false);
                }
            }
            true
        }
        (Value::Shared(_, x), Value::Shared(_, y)) => Rc::ptr_eq(x, y),
        (Value::Signal(x), Value::Signal(y)) => Rc::ptr_eq(x, y),
        (Value::Mutex(x), Value::Mutex(y)) => Rc::ptr_eq(x, y),
        _ => false,
    })
}

/// The value as `show` writes it.
pub fn show(v: &Value) -> R<String> {
    let mut out = String::new();
    show_into(v, &mut out)?;
    Ok(out)
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
        Value::Unit => out.push_str("()"),
        Value::Bool(b) => write!(out, "{b}").unwrap(),
        Value::Int(n) => write!(out, "{n}").unwrap(),
        Value::Float(x) => out.push_str(&tauto_rt::float::text_of_float(*x)),
        Value::Float32(x) => out.push_str(&tauto_rt::float::text_of_float(f64::from(*x))),
        Value::Text(t) => write!(out, "{:?}", &**t).unwrap(),
        Value::Buf(b) => write!(out, "Buf({:?})", b.as_str()).unwrap(),
        Value::Shown(t) => out.push_str(t),
        Value::Inject(_, _, x) => show_into(x, out)?,
        Value::Product(ms) => {
            for (i, m) in ms.iter().enumerate() {
                if i > 0 {
                    out.push_str(" × ");
                }
                show_into(m, out)?;
            }
        }
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
        Value::Map(m) => {
            out.push_str("HashMap{");
            for (i, (k, x)) in m.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                show_into(k, out)?;
                out.push_str(": ");
                show_into(x, out)?;
            }
            out.push('}');
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
        Value::Signal(_) => out.push_str("Signal"),
        // A secret's content is never shown.
        Value::Secret(_) => out.push_str("Secret"),
        Value::Pending(_) => out.push_str("Pending"),
        Value::Data(d) => {
            // Shown by the name written, not by its full name `m.T.C`.
            let tag = d.ctor.tag.rsplit('.').next().unwrap_or(&d.ctor.tag);
            let tag = tag.strip_prefix(':').unwrap_or(tag);
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
