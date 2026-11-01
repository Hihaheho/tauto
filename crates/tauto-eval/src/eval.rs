//! An abstract machine for programs: control, environment and an explicit
//! continuation, never the Rust call stack, so a handler's arm can hold the
//! rest of the handled computation as a value and resume it any number of
//! times (deep, multi-shot handlers).
//!
//! - A `handle` installs a frame in the continuation. `perform` looks for the
//!   nearest frame with an arm for the effect, sets aside the frames from the
//!   `perform` up to and including that frame as the continuation `k`, and runs
//!   the arm outside the handler. Resuming `k` puts a copy of those frames
//!   back, handler included.
//! - `var`s live in cells apart from the frames: copying a continuation copies
//!   the environment, not the cells, so every resumption shares them.
//! - The step count is the session's, not the machine's: copying or resuming a
//!   continuation never gives steps back.
//!
//! - When a `budget` runs out, the body's state (what it was about to do and
//!   its frames up to the budget) is set aside in `info`, and `exceeded(info)`
//!   is performed where the budget is written. `info.more(m)` puts the body
//!   back with `m` more steps, and the frames from the budget to the handler,
//!   as `k` would.
//!
//! Borrows: `&x` is the value itself, `&mut x` a
//! reference to the place in `x`'s cell. `Buf`, `Vec` and `HashMap` are the
//! evaluator's own, the prelude's `extern` functions; a program's `extern`
//! function is a signature only and cannot run.
//!
//! With dynamic ownership checking enabled, each affine
//! or linear value a program makes carries a token, and the machine stops
//! when a name is used after it was moved, when a linear value is dropped,
//! when a continuation that an `ω` effect may copy holds a token, and when a
//! continuation that resumes at most once is resumed twice. A block's end
//! drops what its names still own, in reverse order; the check records the
//! drops. This check compares runtime ownership behavior with the static use
//! checker (`tauto_nibcheck::lin`).
//!
//! A program runs after `tauto_nibcheck::types` and `tauto_nibcheck::lin` have
//! checked it; the inferred widths decide where an `i32` operation overflows. Its results are
//! what it `show`s: the host answers `perform show(name, v)` that no handler
//! takes.
//!
//! It implements Nib's semantics.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use crate::macros::Node;
use crate::rows::check_program_rows;
use crate::surface::{
    BudgetLimit, FnDecl, Handler, MatchArm, Pattern, Program, Stmt, SurfaceTerm, TermKind,
};
use crate::types::{Datas, Kind, Quant, Ty, TypeReport, Width, check_program, prelude, site};
use tauto_message::{Message, msg};
use tauto_rt::nat::Nat;
pub use tauto_rt::permissions::{Grant, Permissions};

/// Steps a run may take unless the caller says otherwise.
pub const DEFAULT_BUDGET: u64 = 10_000_000;

#[derive(Clone)]
pub enum Value<'a> {
    Int(i128),
    /// A `nat` past what an `Int` holds, or made by `nat`'s arithmetic. A
    /// literal of type `nat` is an `Int`; the two are compared as numbers.
    Nat(Nat),
    /// A `Float`: IEEE 754 binary64.
    Float(f64),
    /// A `Float32`: IEEE 754 binary32.
    Float32(f32),
    Bool(bool),
    Text(Rc<str>),
    Unit,
    Closure(Rc<Closure<'a>>),
    /// A continuation captured by a handler arm; with the ownership check,
    /// whether one that resumes at most once has been resumed.
    Cont(Captured<'a>, Option<Rc<Cell<bool>>>),
    /// A function the evaluator implements: `div`, `mod`, `clone` and the
    /// prelude's `extern` ones.
    Builtin(&'a str),
    /// A function of a program's `extern` block: a signature only.
    Extern(&'a str),
    /// A constructor with fields, as a function.
    Ctor(&'a str),
    /// A stopped `budget` body, before a handler has it.
    Stopped(Rc<Stopped<'a>>),
    /// What an `exceeded` arm receives.
    Info(Rc<Info<'a>>),
    /// `info.more` (with `true`) or `info.unbounded`.
    Resume(Rc<Info<'a>>, bool),
    /// A `struct`'s or an `enum`'s value.
    Data(Rc<Data<'a>>),
    /// `Buf`, `Vec(A)`, `HashMap(K, V)`.
    Res(Rc<Res<'a>>),
    /// `Array(A)`: shared and read-only.
    Array(Rc<[Value<'a>]>),
    /// `Bytes`: shared and read-only; a slice shares the storage.
    Bytes(tauto_rt::stdlib::Bytes),
    /// A product's members in its type's order, each with its type as
    /// `types.rs` writes it, by which they are told apart.
    Product(Rc<[(Rc<str>, Value<'a>)]>),
    /// `&mut p`: the place `p` in a `var`'s cell.
    Ref(Place<'a>),
    /// What a `var` holds once the ownership check saw its value moved out.
    Moved,
}

/// A budget's body where it stopped: what it was about to do, and its frames
/// from there up to and including the budget's.
pub struct Stopped<'a> {
    ctrl: Ctrl<'a>,
    frames: Vec<Frame<'a>>,
}

pub struct Info<'a> {
    stopped: Rc<Stopped<'a>>,
    /// The frames from the budget expression up to and including the
    /// handler: `k`'s.
    rest: Captured<'a>,
}

/// The frames a handler arm captured; opaque outside the evaluator.
#[derive(Clone)]
pub struct Captured<'a>(Rc<Vec<Frame<'a>>>);

pub struct Closure<'a> {
    params: &'a [String],
    body: &'a SurfaceTerm,
    env: Env<'a>,
    /// With the ownership check, the captured names whose values moved into
    /// the closure: it drops them when it is dropped, called or not.
    owns: Vec<&'a str>,
}

/// A value of a declared type: its constructor, and its fields in the
/// declaration's order.
pub struct Data<'a> {
    shape: Rc<Shape>,
    fields: Vec<Value<'a>>,
    token: Option<Token>,
    /// Whether the value may hold a token, itself or in its fields; set
    /// once by `data`, so the check's walks skip token-free values (a long
    /// chain of plain data) instead of visiting all of it on every drop.
    owns: bool,
}

/// What every value of one constructor has in common, held once.
pub struct Shape {
    ty: String,
    ctor: String,
    names: Vec<Option<String>>,
}

/// A value as long as the memory allows (a `List` of millions of cells) is
/// let go of one cell at a time, not by a recursion as deep as the value.
impl Drop for Data<'_> {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        let mut fields = std::mem::take(&mut self.fields);
        loop {
            for v in fields.drain(..) {
                if let Value::Data(d) = v {
                    pending.push(d);
                }
            }
            let Some(next) = pending.pop() else { break };
            if let Ok(mut d) = Rc::try_unwrap(next) {
                fields = std::mem::take(&mut d.fields);
            }
        }
    }
}

pub struct Res<'a> {
    kind: ResKind<'a>,
    token: Option<Token>,
}

enum ResKind<'a> {
    Buf(RefCell<String>),
    Vec(RefCell<Vec<Value<'a>>>),
    Map(RefCell<Entries<'a>>),
    /// A `Ref`, a `Mutex` or an `Atomic` (the name it shows as): one
    /// shared slot, so it has no ownership token.
    Cell(RefCell<Value<'a>>, &'static str),
    /// A `Weak`: the cell while a strong handle on it remains.
    Weak(std::rc::Weak<Res<'a>>),
}

/// A `HashMap`'s entries in the order of insertion, which `show` and
/// `HashMap::into_vec` keep, with an index from each key's `key_hash` to the
/// entries whose keys have it: a lookup compares only the keys of one bucket.
/// A `Root::Elem` names an entry by its position, which never changes: keys
/// are only added.
struct Entries<'a> {
    list: Vec<(Value<'a>, Value<'a>)>,
    index: HashMap<u64, Vec<usize>>,
}

impl<'a> Entries<'a> {
    fn new() -> Self {
        Entries {
            list: Vec::new(),
            index: HashMap::new(),
        }
    }

    /// Entries whose keys are distinct, as a map's copy has them.
    fn of(list: Vec<(Value<'a>, Value<'a>)>) -> Self {
        let mut index: HashMap<u64, Vec<usize>> = HashMap::new();
        for (i, (k, _)) in list.iter().enumerate() {
            index.entry(key_hash(k)).or_default().push(i);
        }
        Entries { list, index }
    }

    /// The position of the entry of `k`.
    fn find(&self, k: &Value<'a>) -> Result<Option<usize>, RunError> {
        for &i in self.index.get(&key_hash(k)).into_iter().flatten() {
            if equal(&self.list[i].0, k)? {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    /// Replaces the value of `k`'s entry, or adds one; the old value.
    fn insert(&mut self, k: Value<'a>, v: Value<'a>) -> Result<Option<Value<'a>>, RunError> {
        Ok(match self.find(&k)? {
            Some(i) => Some(std::mem::replace(&mut self.list[i].1, v)),
            None => {
                self.index
                    .entry(key_hash(&k))
                    .or_default()
                    .push(self.list.len());
                self.list.push((k, v));
                None
            }
        })
    }

    fn take(&mut self) -> Vec<(Value<'a>, Value<'a>)> {
        self.index.clear();
        std::mem::take(&mut self.list)
    }
}

impl<'a> std::ops::Deref for Entries<'a> {
    type Target = [(Value<'a>, Value<'a>)];

    fn deref(&self) -> &Self::Target {
        &self.list
    }
}

/// A field path in a cell, or in an element of a `Vec` or a `HashMap`
/// (`Vec::get_mut`).
#[derive(Clone)]
pub struct Place<'a> {
    root: Root<'a>,
    path: Vec<usize>,
}

#[derive(Clone)]
enum Root<'a> {
    Cell(Rc<RefCell<Value<'a>>>),
    /// The `i`th element of a `Vec`, or the value of the `i`th entry of a
    /// `HashMap`.
    Elem(Rc<Res<'a>>, usize),
}

impl<'a> Root<'a> {
    fn get(&self) -> Value<'a> {
        match self {
            Root::Cell(c) => c.borrow().clone(),
            Root::Elem(r, i) => match &r.kind {
                ResKind::Vec(items) => items
                    .borrow()
                    .get(*i)
                    .cloned()
                    .expect("evaluator place: missing vector element"),
                ResKind::Map(entries) => entries
                    .borrow()
                    .get(*i)
                    .map(|e| e.1.clone())
                    .expect("evaluator place: missing map entry"),
                ResKind::Buf(_) | ResKind::Cell(..) | ResKind::Weak(_) => {
                    unreachable!("evaluator place: element root is not a container")
                }
            },
        }
    }

    fn set(&self, value: Value<'a>) {
        match self {
            Root::Cell(c) => *c.borrow_mut() = value,
            Root::Elem(r, i) => match &r.kind {
                ResKind::Vec(items) => {
                    *items
                        .borrow_mut()
                        .get_mut(*i)
                        .expect("evaluator place: missing vector element") = value;
                }
                ResKind::Map(entries) => {
                    entries
                        .borrow_mut()
                        .list
                        .get_mut(*i)
                        .expect("evaluator place: missing map entry")
                        .1 = value;
                }
                ResKind::Buf(_) | ResKind::Cell(..) | ResKind::Weak(_) => {
                    unreachable!("evaluator place: element root is not a container")
                }
            },
        }
    }
}

impl<'a> Root<'a> {
    fn same(&self, other: &Root<'a>) -> bool {
        match (self, other) {
            (Root::Cell(a), Root::Cell(b)) => Rc::ptr_eq(a, b),
            (Root::Elem(a, i), Root::Elem(b, j)) => Rc::ptr_eq(a, b) && i == j,
            _ => false,
        }
    }
}

/// What a place takes when `value` reads the place through the `&mut` that
/// is being assigned (`slot := Cons(p, slot)` with `slot` from
/// `Vec::get_mut`): the place's value, not the reference. A program cannot
/// store a reference to a place in the place itself, so such a reference is
/// a read, and keeping it would make the place contain itself.
fn unalias<'a>(value: &Value<'a>, place: &Place<'a>) -> Value<'a> {
    match value {
        Value::Ref(p)
            if p.root.same(&place.root)
                && (p.path.starts_with(&place.path) || place.path.starts_with(&p.path)) =>
        {
            deref(value)
        }
        Value::Data(d) => {
            let fields: Vec<Value<'a>> = d.fields.iter().map(|f| unalias(f, place)).collect();
            data(Data {
                shape: d.shape.clone(),
                fields,
                token: d.token,
                owns: false,
            })
        }
        Value::Product(members) => Value::Product(
            members
                .iter()
                .map(|(t, v)| (t.clone(), unalias(v, place)))
                .collect(),
        ),
        Value::Array(items) => Value::Array(items.iter().map(|v| unalias(v, place)).collect()),
        other => other.clone(),
    }
}

/// The ownership check's mark on an affine or linear value.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Token {
    id: u64,
    linear: bool,
}

impl<'a> Place<'a> {
    fn get(&self) -> Value<'a> {
        let mut v = self.root.get();
        for i in &self.path {
            v = match deref(&v) {
                Value::Data(d) => d
                    .fields
                    .get(*i)
                    .cloned()
                    .expect("evaluator place: missing field"),
                _ => unreachable!("evaluator place: field path does not refer to data"),
            };
        }
        v
    }

    fn set(&self, value: Value<'a>) {
        let old = self.root.get();
        let new = set_path(&old, &self.path, value);
        self.root.set(new);
    }

    fn field(&self, i: usize) -> Place<'a> {
        let mut path = self.path.clone();
        path.push(i);
        Place {
            root: self.root.clone(),
            path,
        }
    }
}

fn set_path<'a>(v: &Value<'a>, path: &[usize], value: Value<'a>) -> Value<'a> {
    let Some((first, rest)) = path.split_first() else {
        return value;
    };
    match v {
        Value::Data(d) => {
            let mut fields = d.fields.clone();
            let field = fields
                .get_mut(*first)
                .expect("evaluator place: missing field");
            *field = set_path(field, rest, value);
            data(Data {
                shape: d.shape.clone(),
                fields,
                token: d.token,
                owns: false,
            })
        }
        _ => unreachable!("evaluator place: field path does not refer to data"),
    }
}

/// The value a `&mut` reference refers to; any other value is itself.
fn deref<'a>(v: &Value<'a>) -> Value<'a> {
    match v {
        Value::Ref(p) => deref(&p.get()),
        other => other.clone(),
    }
}

impl fmt::Display for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = |f: &mut fmt::Formatter<'_>, vs: &[Value<'_>]| {
            for (i, v) in vs.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{v}")?;
            }
            Ok(())
        };
        match self {
            Value::Int(n) => write!(f, "{n}"),
            Value::Nat(n) => write!(f, "{n}"),
            Value::Float(x) => write!(f, "{x}"),
            // The digits of the same number as a `Float` (`tauto_rt::show`).
            Value::Float32(x) => write!(f, "{}", f64::from(*x)),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Text(t) => write!(f, "{t:?}"),
            Value::Unit => write!(f, "()"),
            Value::Closure(_) | Value::Ctor(_) | Value::Extern(_) => write!(f, "<function>"),
            Value::Cont(..) => write!(f, "<continuation>"),
            Value::Builtin(name) => write!(f, "<{name}>"),
            Value::Stopped(_) | Value::Info(_) => write!(f, "<budget info>"),
            Value::Resume(..) => write!(f, "<function>"),
            Value::Data(d) if d.shape.ctor == SECRET => write!(f, "Secret"),
            Value::Data(d)
                if d.fields.is_empty()
                    && d.shape.names.is_empty()
                    && d.shape.ctor == d.shape.ty =>
            {
                write!(f, "{} {{}}", shown(&d.shape.ctor))
            }
            Value::Data(d) if d.fields.is_empty() => write!(f, "{}", shown(&d.shape.ctor)),
            Value::Data(d) if d.shape.names.iter().all(|n| n.is_some()) => {
                write!(f, "{} {{ ", shown(&d.shape.ctor))?;
                for (i, (n, v)) in d.shape.names.iter().zip(&d.fields).enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {v}", n.as_deref().unwrap_or(""))?;
                }
                write!(f, " }}")
            }
            Value::Data(d) => {
                write!(f, "{}(", shown(&d.shape.ctor))?;
                list(f, &d.fields)?;
                write!(f, ")")
            }
            Value::Product(ms) => {
                for (i, (_, v)) in ms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " × ")?;
                    }
                    write!(f, "{v}")?;
                }
                Ok(())
            }
            Value::Res(r) => match &r.kind {
                ResKind::Buf(b) => write!(f, "Buf({:?})", b.borrow()),
                // As the backends show it: a `Mutex` hides what it holds.
                ResKind::Cell(_, "Mutex") => write!(f, "Mutex"),
                ResKind::Cell(_, "Signal") => write!(f, "Signal"),
                ResKind::Cell(c, name) => write!(f, "{name}({})", c.borrow()),
                ResKind::Weak(_) => write!(f, "Weak"),
                ResKind::Vec(v) => {
                    write!(f, "Vec[")?;
                    list(f, &v.borrow())?;
                    write!(f, "]")
                }
                ResKind::Map(m) => {
                    write!(f, "HashMap{{")?;
                    for (i, (k, v)) in m.borrow().iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{k}: {v}")?;
                    }
                    write!(f, "}}")
                }
            },
            Value::Array(items) => {
                write!(f, "Array[")?;
                list(f, items)?;
                write!(f, "]")
            }
            Value::Bytes(b) => {
                write!(f, "Bytes[")?;
                for (i, x) in b.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, "]")
            }
            Value::Ref(p) => write!(f, "{}", p.get()),
            Value::Moved => write!(f, "<moved>"),
        }
    }
}

/// What a program showed, in order: `perform show(name, v)` as `(name, v)`.
#[derive(Debug, Clone, PartialEq)]
pub struct Outcome {
    pub outputs: Vec<(String, String)>,
    /// With the ownership check: the affine and linear values dropped, by
    /// their type's name, in order.
    pub drops: Vec<String>,
    /// What `os_print` wrote, and `os_eprint`.
    pub stdout: String,
    pub stderr: String,
    /// The code `os_exit` ended the run with.
    pub exit: Option<i32>,
    /// What `perform test(name, body)` ran, in order: the name and the error
    /// that stopped the body, if one did.
    pub tests: Vec<(String, Option<String>)>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RunError {
    Syntax(String),
    /// The checker rejected the program; it did not run.
    Type(String),
    /// The use check (`lin.rs`) rejected the program; it did not run.
    Use(String),
    /// An error of the running program (a type confusion, an unbound name, an
    /// effect nothing handles).
    Runtime(String),
    /// The dynamic ownership check stopped the program.
    Ownership(String),
    /// The session's step limit ran out outside any `budget`.
    Interrupted,
    /// `os_exit` ended the run: not an error, `run_program` turns it into the
    /// outcome's `exit`.
    Exit,
    /// A macro performed `macro_error`: the message, the byte it is about,
    /// and the code.
    MacroError(String, u64, String),
    /// A macro called a function the macro host does not allow.
    NotAllowed(String),
    /// A macro made more values than the host allows.
    Memory,
    /// The program needs a permission the run was not given; it did not run.
    Denied(String),
    /// The row check rejected the program (an effect performed where it is
    /// not allowed); it did not run, as `tauto run` does not run it.
    Row(String),
    /// A macro asked `syn_expand` for an expression the host has not expanded yet:
    /// the host expands it and runs the macro again.
    NeedExpand(Node),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RunError::Syntax(m) => write!(f, "{}", msg!("eval-syntax-error", error = m)),
            RunError::Type(m) => write!(f, "{}", msg!("eval-type-error", error = m)),
            RunError::Use(m) => write!(f, "{}", msg!("eval-use-error", error = m)),
            RunError::Runtime(m) => write!(f, "{m}"),
            RunError::Ownership(m) => write!(f, "{}", msg!("eval-ownership-check", error = m)),
            RunError::Interrupted => write!(f, "{}", tauto_rt::messages::STEP_LIMIT),
            RunError::Exit => write!(f, "{}", msg!("eval-exited")),
            RunError::MacroError(m, _, _) => write!(f, "{m}"),
            RunError::NotAllowed(n) => write!(f, "{}", msg!("eval-not-allowed-in-macro", name = n)),
            RunError::Memory => write!(f, "{}", msg!("eval-macro-too-many-values")),
            RunError::Denied(m) => write!(f, "{m}"),
            RunError::Row(m) => write!(f, "{m}"),
            RunError::NeedExpand(_) => write!(f, "{}", msg!("eval-macro-asked-for-expansion")),
        }
    }
}

fn runtime<T>(message: impl Into<Message>) -> Result<T, RunError> {
    Err(RunError::Runtime(message.into().to_string()))
}

fn ownership<T>(message: impl Into<Message>) -> Result<T, RunError> {
    Err(RunError::Ownership(message.into().to_string()))
}

/// What a run is given besides the program and its step limit.
#[derive(Debug, Clone, Default)]
pub struct RunOptions {
    /// Enables dynamic ownership checking.
    pub check_ownership: bool,
    /// What `argv` answers.
    pub args: Vec<String>,
    /// What the standard effects may ask of the host
    /// (`docs/design/host-effects.md`); nothing by default.
    pub permissions: tauto_rt::permissions::Permissions,
    /// `show`, `os_print` and `os_eprint` are written to the process's
    /// streams as they happen, not kept for the outcome (`tauto dev`).
    pub live: bool,
    /// When set, the run stops with `Interrupted` at its next step
    /// (`tauto dev`, on a change of a file).
    pub cancel: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
    /// The case runner's host: a program's `Probe::new(&name: Text): Probe`
    /// extern makes a value whose drop the ownership check records as
    /// `probe:<name>`.
    pub probes: bool,
}

/// Checks and runs an already parsed program. The facade's
/// `tauto::eval::run_with_budget` and file-loading APIs use this entry point.
pub fn run_program_with(
    program: &Program,
    budget: u64,
    options: RunOptions,
) -> Result<Outcome, RunError> {
    let rows = check_program_rows(program);
    run_program_with_rows(program, budget, options, &rows)
}

/// Runs with the compiler's row report. The caller is responsible for checking
/// that this report belongs to this exact program.
pub fn run_program_with_rows(
    program: &Program,
    budget: u64,
    options: RunOptions,
    rows: &crate::rows::RowReport,
) -> Result<Outcome, RunError> {
    if let Some(e) = rows.errors.first() {
        return Err(RunError::Row(e.to_string()));
    }
    // The standard effects that reach the top level or that a task
    // performs: the run needs their permissions, and the prelude's
    // `host_run` answers them.
    if !rows.host_effects.is_empty() || !rows.task_effects.is_empty() {
        let needed = crate::host::permissions(rows.host_effects.iter().chain(&rows.task_effects));
        let missing = options.permissions.missing(needed);
        if !missing.is_empty() {
            return Err(RunError::Denied(tauto_rt::permissions::missing_message(
                &missing,
            )));
        }
        if let Some(wrapped) = crate::host::wrap(program) {
            // The caller judged the program's own rows; these are the same
            // but for what `host_run` answers.
            let mut rows = check_program_rows(&wrapped);
            rows.host_effects.clear();
            rows.task_effects.clear();
            return run_program_with_rows(&wrapped, budget, options, &rows);
        }
    }
    let report = check_program(program);
    if let Some(e) = report.errors.first() {
        return Err(RunError::Type(e.to_string()));
    }
    if let Some(e) = crate::lin::check(program, &report, rows).first() {
        return Err(RunError::Use(e.to_string()));
    }
    run_program(program, budget, &report.with_prelude(), options)
}

/// What [`run_program_with_rows`] rejects in `program`, with its `rows`,
/// before running anything: its type errors, or else its use errors, each
/// as a message and the byte it is at. `tauto check` reports these, so that
/// a program it accepts is not one `run` rejects.
pub fn errors_before_run(program: &Program, rows: &crate::rows::RowReport) -> Vec<(String, u32)> {
    if !rows.host_effects.is_empty() || !rows.task_effects.is_empty() {
        if let Some(wrapped) = crate::host::wrap(program) {
            let mut rows = check_program_rows(&wrapped);
            rows.host_effects.clear();
            rows.task_effects.clear();
            return errors_before_run(&wrapped, &rows);
        }
    }
    let report = check_program(program);
    if !report.errors.is_empty() {
        return report
            .errors
            .into_iter()
            .map(|e| (e.message, e.span.start))
            .collect();
    }
    crate::lin::check(program, &report, rows)
        .into_iter()
        .map(|e| (e.message, e.span.start))
        .collect()
}

#[derive(Clone)]
enum Slot<'a> {
    Val(Value<'a>),
    Cell(Rc<RefCell<Value<'a>>>),
    /// A name bound to a borrow: never moved out of nor dropped.
    Borrow(Value<'a>),
}

struct EnvNode<'a> {
    name: &'a str,
    slot: Slot<'a>,
    next: Env<'a>,
    /// Unique among the nodes of a run, for the ownership check.
    id: usize,
}

static NODES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

type Env<'a> = Option<Rc<EnvNode<'a>>>;

fn bind<'a>(env: &Env<'a>, name: &'a str, slot: Slot<'a>) -> Env<'a> {
    Some(Rc::new(EnvNode {
        name,
        slot,
        next: env.clone(),
        id: NODES.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
    }))
}

fn lookup_node<'a>(env: &Env<'a>, name: &str) -> Option<Rc<EnvNode<'a>>> {
    let mut at = env;
    while let Some(node) = at {
        if node.name == name {
            return Some(node.clone());
        }
        at = &node.next;
    }
    None
}

/// What a closure keeps: the bindings of its free names and nothing else
/// (`docs/design/shared-levels.md`, 実行系の捕捉). Keeping the whole scope
/// would hold storages the closure never names, which the cycle check does
/// not see.
fn captured_env<'a>(env: &Env<'a>, names: &[String]) -> Env<'a> {
    let mut out: Env<'a> = None;
    let mut seen: Vec<&str> = Vec::new();
    for name in names {
        if seen.contains(&name.as_str()) {
            continue;
        }
        seen.push(name);
        if let Some(node) = lookup_node(env, name) {
            out = bind(&out, node.name, node.slot.clone());
        }
    }
    out
}

fn lookup<'a>(env: &Env<'a>, name: &str) -> Option<Slot<'a>> {
    lookup_node(env, name).map(|n| n.slot.clone())
}

fn node_id(node: &Rc<EnvNode<'_>>) -> usize {
    node.id
}

/// The nodes of `env` down to (not including) `base`.
fn nodes_down_to<'a>(env: &Env<'a>, base: &Env<'a>) -> Vec<Rc<EnvNode<'a>>> {
    let stop = base.as_ref().map(node_id);
    let mut out = Vec::new();
    let mut at = env;
    while let Some(node) = at {
        if Some(node_id(node)) == stop {
            break;
        }
        out.push(node.clone());
        at = &node.next;
    }
    out
}

/// What the machine is doing.
#[derive(Clone)]
enum Ctrl<'a> {
    Eval(&'a SurfaceTerm, Env<'a>),
    Ret(Value<'a>),
    Perform(String, Vec<Value<'a>>),
}

#[derive(Clone)]
enum Frame<'a> {
    /// The callee is evaluated; next the arguments.
    AppFn {
        args: &'a [SurfaceTerm],
        env: Env<'a>,
    },
    AppArg {
        callee: Value<'a>,
        done: Vec<Value<'a>>,
        rest: &'a [SurfaceTerm],
        env: Env<'a>,
    },
    /// An operator waits for its operands.
    OpArg {
        op: &'a str,
        width: Width,
        done: Vec<Value<'a>>,
        rest: &'a [SurfaceTerm],
        env: Env<'a>,
    },
    /// `a && b`, `a || b`: the right side only when the left does not decide.
    Logic {
        and: bool,
        rhs: &'a SurfaceTerm,
        env: Env<'a>,
    },
    If {
        then: &'a SurfaceTerm,
        otherwise: Option<&'a SurfaceTerm>,
        env: Env<'a>,
    },
    /// The value of statement `at` of a block has arrived; `start` is the
    /// environment the block began with.
    Stmt {
        stmts: &'a [Stmt],
        at: usize,
        env: Env<'a>,
        start: Env<'a>,
        root: bool,
        /// Temporaries borrowed while the statement runs (`f(&T.new())`):
        /// the statement owns them and drops them, last first, when it ends.
        temps: Vec<Value<'a>>,
    },
    /// A temporary that is borrowed is evaluated; the enclosing statement
    /// takes it as its own.
    BorrowTemp,
    WhileTest {
        stmts: &'a [Stmt],
        at: usize,
        env: Env<'a>,
        start: Env<'a>,
        root: bool,
    },
    WhileBody {
        stmts: &'a [Stmt],
        at: usize,
        env: Env<'a>,
        start: Env<'a>,
        root: bool,
    },
    Match {
        arms: &'a [MatchArm],
        env: Env<'a>,
        /// The scrutinee is owned: the chosen arm consumes it.
        owned: bool,
    },
    MatchGuard {
        arms: &'a [MatchArm],
        at: usize,
        scrutinee: Value<'a>,
        outer: Env<'a>,
        arm_env: Env<'a>,
        owned: bool,
    },
    PerformArgs {
        effect: &'a str,
        done: Vec<Value<'a>>,
        rest: &'a [SurfaceTerm],
        env: Env<'a>,
    },
    /// A struct's fields, in the order written.
    RecordArgs {
        name: &'a str,
        fields: &'a [(String, SurfaceTerm)],
        done: Vec<Value<'a>>,
        env: Env<'a>,
    },
    /// `Pair { fst, snd }` whose type is a product: its members as the product's.
    PairArgs {
        term: &'a SurfaceTerm,
        fields: &'a [(String, SurfaceTerm)],
        done: Vec<Value<'a>>,
        env: Env<'a>,
    },
    Handle {
        handlers: &'a [Handler],
        env: Env<'a>,
    },
    /// A budget's body runs above it until the count it keeps, of steps
    /// or of cells, passes `end`.
    Budget { limit: BudgetLimit, end: u64 },
    BudgetSteps {
        limit: BudgetLimit,
        body: &'a SurfaceTerm,
        env: Env<'a>,
    },
    /// A function call returns here; `return` unwinds to it. The names from
    /// `env` down to `base` are its parameters.
    Call { env: Env<'a>, base: Env<'a> },
    /// `base.name`: the base is evaluated.
    Field { name: &'a str },
    /// A product's members, in the order written.
    ProductArgs {
        term: &'a SurfaceTerm,
        members: &'a [SurfaceTerm],
        done: Vec<Value<'a>>,
        env: Env<'a>,
    },
    /// `(base: T)`: the base is evaluated; the member has type `key`.
    Project { key: Rc<str> },
    /// A product taken to fewer members (`A × B <: A`).
    Fit { to: &'a Ty },
}

impl<'a> Frame<'a> {
    /// The environment and the values a frame holds, for the ownership
    /// check of a continuation that may be copied.
    fn held(&self) -> (Option<&Env<'a>>, Vec<&Value<'a>>) {
        match self {
            Frame::AppFn { env, .. }
            | Frame::Logic { env, .. }
            | Frame::If { env, .. }
            | Frame::Match { env, .. }
            | Frame::Handle { env, .. }
            | Frame::BudgetSteps { env, .. } => (Some(env), Vec::new()),
            Frame::Stmt { env, temps, .. } => (Some(env), temps.iter().collect()),
            Frame::WhileTest { env, .. } | Frame::WhileBody { env, .. } => (Some(env), Vec::new()),
            Frame::AppArg {
                callee, done, env, ..
            } => (Some(env), std::iter::once(callee).chain(done).collect()),
            Frame::OpArg { done, env, .. }
            | Frame::PerformArgs { done, env, .. }
            | Frame::RecordArgs { done, env, .. }
            | Frame::PairArgs { done, env, .. }
            | Frame::ProductArgs { done, env, .. } => (Some(env), done.iter().collect()),
            Frame::MatchGuard {
                scrutinee, arm_env, ..
            } => (Some(arm_env), vec![scrutinee]),
            Frame::Call { env, .. } => (Some(env), Vec::new()),
            Frame::Budget { .. }
            | Frame::BorrowTemp
            | Frame::Field { .. }
            | Frame::Project { .. }
            | Frame::Fit { .. } => (None, Vec::new()),
        }
    }
}

struct KNode<'a> {
    frame: Frame<'a>,
    next: Kont<'a>,
}

type Kont<'a> = Option<Rc<KNode<'a>>>;

/// A continuation of millions of frames (a macro that runs out of its steps)
/// is let go of one frame at a time, not by a recursion as deep.
impl Drop for KNode<'_> {
    fn drop(&mut self) {
        let mut next = self.next.take();
        while let Some(node) = next {
            match Rc::try_unwrap(node) {
                Ok(mut node) => next = node.next.take(),
                Err(_) => break,
            }
        }
    }
}

fn push<'a>(kont: Kont<'a>, frame: Frame<'a>) -> Kont<'a> {
    Some(Rc::new(KNode { frame, next: kont }))
}

const OPERATORS: &[&str] = &["+", "-", "*", "/", "==", "!=", "<", ">", "<=", ">="];

struct Machine<'a> {
    /// Every step of the machine: what a `budget` and a macro's limit count.
    steps: u64,
    /// The cells allocated so far: what a `budget(memory: n)` counts.
    cells: u64,
    /// The calls and loop rounds outside a macro: what the host's limit
    /// counts, as the backends count it.
    calls: u64,
    limit: u64,
    any_budget: bool,
    /// The fields a function that returns `&mut A` gives back
    /// (`fn f(&mut s: S): &mut u64 { s.n }`): each is lent, not read.
    lent_fields: HashSet<*const SurfaceTerm>,
    globals: HashMap<String, Value<'a>>,
    /// The `Shape` of each constructor made so far, shared by its values.
    shapes: HashMap<String, Rc<Shape>>,
    outputs: Vec<(String, String)>,
    tests: Vec<(String, Option<String>)>,
    report: &'a TypeReport,
    /// The locals whose type is a borrow, by where they are bound, and
    /// whether the borrow is `&mut`: every other local gets a plain slot.
    borrow_locals: HashMap<crate::surface::TermId, Vec<(&'a str, bool)>>,
    /// The constructor a name or a record names where it is written, once
    /// resolved: the occurrence's type does not change while it runs.
    ctor_keys: RefCell<HashMap<crate::surface::TermId, &'a str>>,
    /// The dynamic ownership check is on.
    check: bool,
    probes: bool,
    /// The names (by their node) whose value was moved out.
    moved: HashSet<usize>,
    /// Function values that are called or lent to a borrowed parameter
    /// where they are named: naming them does not move them. A closure
    /// that consumes what it captured still fails on its second call.
    called: HashSet<crate::surface::TermId>,
    next_token: u64,
    /// The tokens of the values alive: linear, and the type's name.
    live: HashMap<u64, (bool, String)>,
    drops: Vec<String>,
    args: Vec<String>,
    permissions: tauto_rt::permissions::Permissions,
    stdout: String,
    stderr: String,
    streaming: bool,
    cancel: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
    exit: Option<i32>,
    /// Set when the machine runs a macro (`call_function`).
    host: Option<HostState>,
    /// How many test bodies the host is running: a `fail` in one fails the
    /// test with its message.
    in_test: usize,
}

/// What a macro's run counts and allows.
struct HostState {
    allowed: &'static [&'static str],
    max_allocations: u64,
    allocations: u64,
    /// The `macro_warn`s: message, byte, code.
    warnings: Vec<(String, u64, String)>,
    elab: Option<ElabFn>,
    /// What `syn_expand` answers: an expression and its expansion.
    expanded: Vec<(Node, Node)>,
}

/// What answers the `elab_*` operations: the operation and its arguments.
pub type ElabFn = Rc<dyn Fn(&str, &[Node]) -> Result<Node, String>>;

fn run_program<'a>(
    program: &'a Program,
    budget: u64,
    report: &'a TypeReport,
    options: RunOptions,
) -> Result<Outcome, RunError> {
    let mut machine = machine_for(program, budget, report, options);
    match machine.run_block(&program.stmts) {
        Ok(_) | Err(RunError::Exit) => {}
        Err(e) => return Err(e),
    }
    Ok(Outcome {
        outputs: machine.outputs,
        drops: machine.drops,
        stdout: machine.stdout,
        stderr: machine.stderr,
        exit: machine.exit,
        tests: machine.tests,
    })
}

fn borrow_locals(report: &TypeReport) -> HashMap<crate::surface::TermId, Vec<(&str, bool)>> {
    let mut locals: HashMap<_, Vec<_>> = HashMap::new();
    for ((name, at), ty) in &report.locals {
        if let Ty::Borrow(_, mutable) = ty {
            locals
                .entry(*at)
                .or_default()
                .push((name.as_str(), *mutable));
        }
    }
    locals
}

/// A machine with the prelude's functions and the program's defined.
fn machine_for<'a>(
    program: &'a Program,
    budget: u64,
    report: &'a TypeReport,
    options: RunOptions,
) -> Machine<'a> {
    let mut machine = Machine {
        steps: 0,
        cells: 0,
        calls: 0,
        limit: budget,
        any_budget: false,
        lent_fields: HashSet::new(),
        globals: HashMap::new(),
        shapes: HashMap::new(),
        outputs: Vec::new(),
        tests: Vec::new(),
        in_test: 0,
        report,
        borrow_locals: borrow_locals(report),
        ctor_keys: RefCell::new(HashMap::new()),
        check: options.check_ownership,
        probes: options.probes,
        moved: HashSet::new(),
        called: if options.check_ownership {
            called_functions(program, report)
        } else {
            HashSet::new()
        },
        next_token: 0,
        live: HashMap::new(),
        drops: Vec::new(),
        args: options.args,
        permissions: options.permissions,
        stdout: String::new(),
        stderr: String::new(),
        streaming: options.live,
        cancel: options.cancel,
        exit: None,
        host: None,
    };
    let lib: &'static Program = prelude();
    let closure = |f: &'a FnDecl| {
        Value::Closure(Rc::new(Closure {
            params: &f.params,
            body: &f.body,
            env: None,
            owns: Vec::new(),
        }))
    };
    // The prelude's functions, then the program's, which hide them. Named
    // functions are written at the top level and see each other.
    for (stmts, own) in [(&lib.stmts, false), (&program.stmts, true)] {
        for stmt in stmts {
            match stmt {
                Stmt::Fn(f) => {
                    note_lent_fields(f, &mut machine.lent_fields);
                    machine.globals.insert(f.name.clone(), closure(f));
                }
                Stmt::Extern { fns, .. } => {
                    for f in fns {
                        let v = if !own {
                            Value::Builtin(&f.name)
                        } else {
                            Value::Extern(&f.name)
                        };
                        machine.globals.insert(f.name.clone(), v);
                    }
                }
                _ => {}
            }
        }
    }
    machine
}

/// What a macro's host allows and limits.
pub struct Host {
    /// The builtins a macro may call; a name ending in `*` stands for every
    /// name that starts so.
    pub allowed: &'static [&'static str],
    pub max_steps: u64,
    pub max_allocations: u64,
    /// The `macro_warn`s of the calls: message, byte, code.
    pub warnings: Vec<(String, u64, String)>,
    /// Answers `elab_*`; none outside a typed macro.
    pub elab: Option<ElabFn>,
    /// The expressions `syn_expand` has been asked for, with their expansions.
    pub expanded: Vec<(Node, Node)>,
}

/// What a call used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallStats {
    pub steps: u64,
    pub allocations: u64,
}

/// The builtins a macro may call.
pub const MACRO_BUILTINS: &[&str] = &[
    "div",
    "div_i32",
    "mod",
    "clone",
    "concat",
    "words",
    "replace",
    "Text::*",
    "Buf::*",
    "Vec::*",
    "HashMap::*",
    "I64::of_*",
    "I32::of_*",
    "U64::of_*",
    "U32::of_*",
    "U8::of_*",
    "map",
    "each",
    "fold",
    "fold_once",
    "Syn::*",
    "Judgement::*",
    "Elab::*",
];

impl Host {
    pub fn new(max_steps: u64, max_allocations: u64) -> Self {
        Host {
            allowed: MACRO_BUILTINS,
            max_steps,
            max_allocations,
            warnings: Vec::new(),
            elab: None,
            expanded: Vec::new(),
        }
    }
}

/// Calls the function `name` of a checked program with `args` and returns what it
/// made. `report` is the program's report with the prelude's.
pub fn call_function(
    program: &Program,
    report: &TypeReport,
    name: &str,
    args: &[Node],
    host: &mut Host,
) -> Result<(Node, CallStats), RunError> {
    let call = std::panic::AssertUnwindSafe(|| {
        let mut machine = machine_for(program, host.max_steps, report, RunOptions::default());
        machine.host = Some(HostState {
            allowed: host.allowed,
            max_allocations: host.max_allocations,
            allocations: 0,
            warnings: Vec::new(),
            elab: host.elab.clone(),
            expanded: host.expanded.clone(),
        });
        let callee = machine.globals.get(name).cloned().ok_or_else(|| {
            RunError::Runtime(msg!("eval-is-not-defined", name = name).to_string())
        })?;
        let mut values = Vec::new();
        for a in args {
            values.push(machine.node_value(a)?);
        }
        let (ctrl, kont) = machine.apply(callee, values, None)?;
        let value = machine.run(ctrl, kont)?;
        let node = machine.value_node(&value)?;
        let state = machine.host.take().expect("the host is set");
        Ok((
            node,
            CallStats {
                steps: machine.steps,
                allocations: state.allocations,
            },
            state.warnings,
        ))
    });
    match std::panic::catch_unwind(call) {
        Ok(Ok((node, stats, warnings))) => {
            host.warnings.extend(warnings);
            Ok((node, stats))
        }
        Ok(Err(e)) => Err(e),
        Err(_) => Err(RunError::Runtime(
            msg!("eval-macro-stopped-evaluator").to_string(),
        )),
    }
}

impl<'a> Machine<'a> {
    fn datas(&self) -> &'a Datas {
        &self.report.datas
    }

    /// Whether the value of `t` is moved where it is used: its type is
    /// affine or linear and not a borrow.
    fn moves(&self, t: &SurfaceTerm) -> bool {
        self.check
            && self.report.term(t).is_some_and(|ty| {
                !matches!(ty, Ty::Borrow(..))
                    && !self.report.kind(ty).dup()
                    && !(matches!(ty, Ty::Fn(..)) && self.called.contains(&t.id()))
            })
    }

    /// The slot a name bound at `site` gets: a borrow's, when its type is one.
    fn slot_for(&self, name: &str, at: crate::surface::TermId, value: Value<'a>) -> Slot<'a> {
        match self.borrow_local(name, at) {
            Some(_) => Slot::Borrow(value),
            None => Slot::Val(value),
        }
    }

    /// Whether the local `name` bound at `at` is a `&mut`, when it is a borrow.
    fn borrow_local(&self, name: &str, at: crate::surface::TermId) -> Option<bool> {
        let locals = self.borrow_locals.get(&at)?;
        locals
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, mutable)| *mutable)
    }

    fn token(&mut self, linear: bool, ty: &str) -> Option<Token> {
        if !self.check {
            return None;
        }
        self.next_token += 1;
        self.live.insert(self.next_token, (linear, ty.to_string()));
        Some(Token {
            id: self.next_token,
            linear,
        })
    }

    /// A value of constructor `ctor`: with the ownership check, a token
    /// when its type is affine or linear (`kind(T)`, from what the
    /// value holds).
    fn make(&mut self, ctor: &str, fields: Vec<Value<'a>>) -> Result<Value<'a>, RunError> {
        self.allocated()?;
        self.alloc(1 + fields.len() as u64);
        let datas = self.datas();
        let Some((d, c)) = datas.ctors.get(ctor) else {
            return runtime(msg!("eval-is-not-a-constructor", ctor = ctor.to_string()));
        };
        let decl = &datas.decls[d];
        let constructor = &decl.constructors[*c];
        if constructor.fields.len() != fields.len() {
            return runtime(msg!(
                "eval-takes-values-got",
                ctor = ctor.to_string(),
                fields = constructor.fields.len().to_string(),
                fields2 = fields.len().to_string()
            ));
        }
        let mut kind = decl.declared.unwrap_or(Kind::Copy);
        for f in &fields {
            if let Some(t) = token_of(f) {
                kind = kind.join(if t.linear { Kind::Linear } else { Kind::Affine });
            }
        }
        let token = if kind.dup() {
            None
        } else {
            self.token(kind == Kind::Linear, &decl.name)
        };
        let shape = match self.shapes.get(ctor) {
            Some(s) => s.clone(),
            None => {
                let s = Rc::new(Shape {
                    ty: decl.name.clone(),
                    ctor: constructor.name.clone(),
                    names: constructor.fields.iter().map(|(n, _)| n.clone()).collect(),
                });
                self.shapes.insert(ctor.to_string(), s.clone());
                s
            }
        };
        Ok(data(Data {
            shape,
            fields,
            token,
            owns: false,
        }))
    }

    /// A `SynDiag`'s message, byte and code.
    fn diag_parts(&self, diag: &Value<'a>) -> (String, u64, String) {
        let text = |v: Option<&Value<'a>>| match v.map(deref) {
            Some(Value::Text(t)) => t.to_string(),
            _ => String::new(),
        };
        match deref(diag) {
            Value::Data(d) => {
                let at = match d.fields.get(1).map(deref) {
                    Some(Value::Int(n)) => n as u64,
                    _ => 0,
                };
                (text(d.fields.first()), at, text(d.fields.get(3)))
            }
            _ => (String::new(), 0, String::new()),
        }
    }

    /// A [`Node`] as the value it stands for.
    fn node_value(&mut self, n: &Node) -> Result<Value<'a>, RunError> {
        Ok(match n {
            Node::Int(i) => Value::Int(i128::from(*i)),
            Node::Bool(b) => Value::Bool(*b),
            Node::Text(t) => Value::Text(Rc::from(t.as_str())),
            Node::List(items) => {
                let mut vs = Vec::new();
                for i in items {
                    vs.push(self.node_value(i)?);
                }
                self.list(vs)?
            }
            Node::Option(None) => self.option(None)?,
            Node::Option(Some(v)) => {
                let v = self.node_value(v)?;
                self.option(Some(v))?
            }
            Node::Product(ms) => {
                let mut vs = Vec::new();
                for (k, m) in ms {
                    vs.push((Rc::from(k.as_str()), self.node_value(m)?));
                }
                Value::Product(vs.into())
            }
            Node::Ctor(name, fields) => {
                let mut vs = Vec::new();
                for (_, f) in fields {
                    vs.push(self.node_value(f)?);
                }
                let key = if self.datas().decls.get(name).is_some_and(|d| d.is_struct) {
                    format!("{name}::{name}")
                } else {
                    name.clone()
                };
                self.make(&key, vs)?
            }
            Node::Splice(_) | Node::SpliceList(_) => {
                return runtime(msg!("eval-a-quote-s-hole-is-not"));
            }
        })
    }

    /// A value a macro made as a [`Node`].
    fn value_node(&self, v: &Value<'a>) -> Result<Node, RunError> {
        Ok(match deref(v) {
            Value::Int(i) => Node::Int(i64::try_from(i).map_err(|_| overflow())?),
            Value::Bool(b) => Node::Bool(b),
            Value::Text(t) => Node::Text(t.to_string()),
            Value::Data(d) => match (d.shape.ty.as_str(), d.shape.ctor.as_str()) {
                ("List", _) => {
                    let mut items = Vec::new();
                    let mut at = Value::Data(d.clone());
                    while let Value::Data(cell) = deref(&at)
                        && cell.shape.ctor == "Cons"
                    {
                        items.push(self.value_node(&cell.fields[0])?);
                        at = cell.fields[1].clone();
                    }
                    Node::List(items)
                }
                ("Option", "None") => Node::none(),
                ("Option", _) => Node::some(self.value_node(&d.fields[0])?),

                (ty, ctor) => {
                    let is_struct = self.datas().decls.get(ty).is_some_and(|x| x.is_struct);
                    let name = if is_struct {
                        ty.to_string()
                    } else {
                        format!("{ty}::{ctor}")
                    };
                    let mut fields = Vec::new();
                    for (i, f) in d.fields.iter().enumerate() {
                        fields.push((d.shape.names.get(i).cloned().flatten(), self.value_node(f)?));
                    }
                    Node::Ctor(name, fields)
                }
            },
            Value::Product(ms) => {
                let mut out = Vec::new();
                for (k, m) in ms.iter() {
                    out.push((k.to_string(), self.value_node(m)?));
                }
                out.sort_by_cached_key(|(k, _)| tauto_surface::macros::node::key_order(k));
                Node::Product(out)
            }
            other => return runtime(msg!("eval-is-not-syntax", other = other.to_string())),
        })
    }

    /// `syn_parse`: the text read with the tables of the grammar `sha`, as the
    /// values the syntax's types describe (`Ok`), or why it is not of the syntax.
    fn syn_parse(&mut self, syntax: &str, sha: &str, text: &str) -> Result<Value<'a>, RunError> {
        use crate::syntax::{SynOutcome, parse_text};
        match parse_text(syntax, sha, text) {
            SynOutcome::Parsed(tables, ast) => {
                let v = self.syn_value(syntax, &tables, text, &ast)?;
                self.make("Result::Ok", vec![v])
            }
            SynOutcome::Failed {
                message,
                at,
                expected,
            } => {
                let expected: Vec<Value<'a>> = expected
                    .iter()
                    .map(|e| Value::Text(Rc::from(e.as_str())))
                    .collect();
                let expected = self.list(expected)?;
                let diag = self.make(
                    "SynDiag::SynDiag",
                    vec![
                        Value::Text(Rc::from(message.as_str())),
                        Value::Int(at as i128),
                        expected,
                        Value::Text(Rc::from("macro.syntax_error")),
                    ],
                )?;
                self.make("Result::Err", vec![diag])
            }
        }
    }

    fn syn_span(&mut self, start: u32) -> Result<Value<'a>, RunError> {
        self.make("SynSpan::SynSpan", vec![Value::Int(start as i128)])
    }

    fn syn_value(
        &mut self,
        syntax: &str,
        tables: &tauto_syntax::Tables,
        text: &str,
        ast: &tauto_syntax::Ast,
    ) -> Result<Value<'a>, RunError> {
        use tauto_syntax::{Ast, Payload, TypeDef};
        Ok(match ast {
            Ast::Token(t) => {
                let s = text.get(t.start as usize..t.end as usize).unwrap_or("");
                let span = self.syn_span(t.start)?;
                let scopes = self.list(Vec::new())?;
                let ctx = self.make("SynCtx::SynCtx", vec![scopes])?;
                self.make(
                    "SynToken::SynToken",
                    vec![Value::Text(Rc::from(s)), span, ctx],
                )?
            }
            Ast::List(items) => {
                let mut out = Vec::new();
                for i in items {
                    out.push(self.syn_value(syntax, tables, text, i)?);
                }
                self.list(out)?
            }
            Ast::Opt(None) => self.option(None)?,
            Ast::Opt(Some(v)) => {
                let v = self.syn_value(syntax, tables, text, v)?;
                self.option(Some(v))?
            }
            Ast::Node {
                ty,
                ctor,
                span,
                fields,
            } => {
                let mut out = Vec::new();
                let values = |this: &mut Self, out: &mut Vec<Value<'a>>| -> Result<(), RunError> {
                    for f in fields {
                        out.push(this.syn_value(syntax, tables, text, f)?);
                    }
                    Ok(())
                };
                match &tables.schema().types[*ty as usize] {
                    TypeDef::Struct { name, .. } => {
                        out.push(self.syn_span(span.0)?);
                        values(self, &mut out)?;
                        let ty = tauto_syntax::type_name(syntax, name);
                        self.make(&format!("{ty}::{ty}"), out)?
                    }
                    TypeDef::Enum { name, ctors } => {
                        let c = &ctors[*ctor as usize];
                        if matches!(c.payload, Payload::Record(_)) {
                            out.push(self.syn_span(span.0)?);
                        }
                        values(self, &mut out)?;
                        let ty = tauto_syntax::type_name(syntax, name);
                        self.make(&format!("{ty}::{}", c.name), out)?
                    }
                }
            }
        })
    }

    /// The count a budget of `limit` keeps.
    fn count(&self, limit: BudgetLimit) -> u64 {
        match limit {
            BudgetLimit::Steps => self.steps,
            BudgetLimit::Memory => self.cells,
        }
    }

    /// Counts `cells` allocated, for `budget(memory: n)`.
    fn alloc(&mut self, cells: u64) {
        self.cells = self.cells.saturating_add(cells);
    }

    /// The cells of text of `len` bytes: one, and one per 8 bytes.
    fn alloc_text(&mut self, len: usize) {
        self.alloc(1 + len as u64 / 8);
    }

    /// Counts a value made when a macro runs.
    fn allocated(&mut self) -> Result<(), RunError> {
        if let Some(h) = &mut self.host {
            h.allocations += 1;
            if h.allocations > h.max_allocations {
                return Err(RunError::Memory);
            }
        }
        Ok(())
    }

    /// A `Signal`, raised or not: a shared slot, so it has no ownership token.
    fn signal(&self, raised: bool) -> Value<'a> {
        Value::Res(Rc::new(Res {
            kind: ResKind::Cell(RefCell::new(Value::Bool(raised)), "Signal"),
            token: None,
        }))
    }

    fn resource(&mut self, kind: ResKind<'a>) -> Value<'a> {
        self.alloc(1);
        let name = match kind {
            ResKind::Buf(_) => "Buf",
            ResKind::Vec(_) => "Vec",
            ResKind::Map(_) => "HashMap",
            ResKind::Cell(..) => "Cell",
            ResKind::Weak(_) => "Weak",
        };
        let token = self.token(false, name);
        Value::Res(Rc::new(Res { kind, token }))
    }

    fn list(&mut self, items: Vec<Value<'a>>) -> Result<Value<'a>, RunError> {
        let mut list = self.make("List::Nil", Vec::new())?;
        for item in items.into_iter().rev() {
            list = self.make("List::Cons", vec![item, list])?;
        }
        Ok(list)
    }

    /// The elements of a `List`.
    fn list_items(&self, l: &Value<'a>) -> Result<Vec<Value<'a>>, RunError> {
        let mut out = Vec::new();
        let mut at = l.clone();
        loop {
            let Value::Data(d) = &at else {
                return runtime(msg!("eval-a-list-was-expected"));
            };
            match (d.shape.ctor.as_str(), d.fields.as_slice()) {
                ("Nil", []) => return Ok(out),
                ("Cons", [h, t]) => {
                    out.push(h.clone());
                    let t = t.clone();
                    at = t;
                }
                _ => return runtime(msg!("eval-a-list-was-expected")),
            }
        }
    }

    /// A host's `Result(List(Text), Text)`.
    fn text_list_result(
        &mut self,
        r: Result<Vec<tauto_rt::Text>, tauto_rt::Text>,
    ) -> Result<Value<'a>, RunError> {
        match r {
            Ok(items) => {
                let items = items.iter().map(|t| Value::Text(Rc::from(&**t))).collect();
                let list = self.list(items)?;
                self.make("Result::Ok", vec![list])
            }
            Err(e) => self.make(
                "Result::Err",
                vec![Value::Text(Rc::from(e.to_string().as_str()))],
            ),
        }
    }

    /// Whether `tauto dev` stopped the run.
    fn cancelled(&self) -> bool {
        self.cancel
            .as_ref()
            .is_some_and(|c| c.load(std::sync::atomic::Ordering::Relaxed))
    }

    /// A deadline of the stream requests: an `Option(i64)`.
    fn deadline(&self, v: &Value<'a>) -> Result<Option<i64>, RunError> {
        match v {
            Value::Data(d) => match (d.shape.ctor.as_str(), d.fields.as_slice()) {
                ("None", []) => Ok(None),
                ("Some", [Value::Int(ns)]) => Ok(Some(i64::try_from(*ns).unwrap_or(i64::MAX))),
                _ => runtime(msg!("eval-an-option-i64-was-expected")),
            },
            _ => runtime(msg!("eval-an-option-i64-was-expected")),
        }
    }

    /// A host's `Result(Option(List(Text)), Text)`, `None` for a deadline
    /// that passed.
    fn timed_text_list(
        &mut self,
        r: Result<Option<Vec<tauto_rt::Text>>, tauto_rt::Text>,
    ) -> Result<Value<'a>, RunError> {
        match r {
            Ok(Some(items)) => {
                let items = items.iter().map(|t| Value::Text(Rc::from(&**t))).collect();
                let list = self.list(items)?;
                let some = self.option(Some(list))?;
                self.make("Result::Ok", vec![some])
            }
            Ok(None) => {
                let none = self.option(None)?;
                self.make("Result::Ok", vec![none])
            }
            Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(&*e))]),
        }
    }

    /// The functions of `Float` (`std/prelude/Num.taut`), as the Rust
    /// backend computes them (`tauto_rt::float`).
    fn float_builtin(&mut self, name: &str, args: &[Value<'a>]) -> Result<Value<'a>, RunError> {
        use Value::{Float, Int};
        use tauto_rt::float as f;
        Ok(match (name, args) {
            ("Float::of_i64", [Int(n)]) => Float(f::float_of_i64(*n as i64)),
            ("I64::of_float", [Float(x)]) => Int(i128::from(
                f::i64_of_float_checked(*x).ok_or_else(overflow)?,
            )),
            ("Float::of_text", [Value::Text(t)]) => {
                let x = f::float_of_str(t).map(Float);
                self.option(x)?
            }
            ("Text::of_float", [Float(x)]) => Value::Text(Rc::from(format!("{x}").as_str())),
            // The evaluator holds a `u64` as its value, as the other `u64`s.
            ("Float::bits", [Float(x)]) => Int(i128::from(f::float_bits(*x))),
            ("Float::of_bits", [Int(b)]) => Float(f::float_of_bits(*b as u64)),
            ("Float::is_nan", [Float(x)]) => Value::Bool(f::float_is_nan(*x)),
            ("Float::of_float32", [Value::Float32(x)]) => Float(f::float_of_float32(*x)),
            ("Float::pow", [Float(x), Float(y)]) => Float(f::float_pow(*x, *y)),
            ("Float::atan2", [Float(y), Float(x)]) => Float(f::float_atan2(*y, *x)),
            (_, [Float(x)]) => Float(match name {
                "Float::abs" => f::float_abs(*x),
                "Float::floor" => f::float_floor(*x),
                "Float::ceil" => f::float_ceil(*x),
                "Float::trunc" => f::float_trunc(*x),
                "Float::round" => f::float_round(*x),
                "Float::sqrt" => f::float_sqrt(*x),
                "Float::cbrt" => f::float_cbrt(*x),
                "Float::exp" => f::float_exp(*x),
                "Float::ln" => f::float_ln(*x),
                "Float::log2" => f::float_log2(*x),
                "Float::log10" => f::float_log10(*x),
                "Float::sin" => f::float_sin(*x),
                "Float::cos" => f::float_cos(*x),
                "Float::tan" => f::float_tan(*x),
                "Float::asin" => f::float_asin(*x),
                "Float::acos" => f::float_acos(*x),
                "Float::atan" => f::float_atan(*x),
                "Float::sinh" => f::float_sinh(*x),
                "Float::cosh" => f::float_cosh(*x),
                "Float::tanh" => f::float_tanh(*x),
                _ => return runtime(msg!("eval-unknown-builtin", name = name.to_string())),
            }),
            _ => return runtime(msg!("eval-takes-other-arguments", name = name.to_string())),
        })
    }

    /// The functions of `Float32` (`std/prelude/Num.taut`), as the Rust
    /// backend computes them (`tauto_rt::float`).
    fn float32_builtin(&mut self, name: &str, args: &[Value<'a>]) -> Result<Value<'a>, RunError> {
        use Value::{Float32, Int};
        use tauto_rt::float as f;
        Ok(match (name, args) {
            ("Float32::of_float", [Value::Float(x)]) => Float32(f::float32_of_float(*x)),
            ("Float32::bits", [Float32(x)]) => Int(i128::from(f::float32_bits(*x))),
            ("Float32::of_bits", [Int(b)]) => Float32(f::float32_of_bits(*b as u32)),
            ("Float32::is_nan", [Float32(x)]) => Value::Bool(f::float32_is_nan(*x)),
            ("Float32::pow", [Float32(x), Float32(y)]) => Float32(f::float32_pow(*x, *y)),
            ("Float32::atan2", [Float32(y), Float32(x)]) => Float32(f::float32_atan2(*y, *x)),
            (_, [Float32(x)]) => Float32(match name {
                "Float32::abs" => f::float32_abs(*x),
                "Float32::floor" => f::float32_floor(*x),
                "Float32::ceil" => f::float32_ceil(*x),
                "Float32::trunc" => f::float32_trunc(*x),
                "Float32::round" => f::float32_round(*x),
                "Float32::sqrt" => f::float32_sqrt(*x),
                "Float32::cbrt" => f::float32_cbrt(*x),
                "Float32::exp" => f::float32_exp(*x),
                "Float32::ln" => f::float32_ln(*x),
                "Float32::log2" => f::float32_log2(*x),
                "Float32::log10" => f::float32_log10(*x),
                "Float32::sin" => f::float32_sin(*x),
                "Float32::cos" => f::float32_cos(*x),
                "Float32::tan" => f::float32_tan(*x),
                "Float32::asin" => f::float32_asin(*x),
                "Float32::acos" => f::float32_acos(*x),
                "Float32::atan" => f::float32_atan(*x),
                "Float32::sinh" => f::float32_sinh(*x),
                "Float32::cosh" => f::float32_cosh(*x),
                "Float32::tanh" => f::float32_tanh(*x),
                _ => return runtime(msg!("eval-unknown-builtin", name = name.to_string())),
            }),
            _ => return runtime(msg!("eval-takes-other-arguments", name = name.to_string())),
        })
    }

    /// The text list and the bytes the host gave, as `Result(Pair(List(Text), Bytes), Text)`.
    fn text_list_bytes_result(
        &mut self,
        r: Result<(Vec<tauto_rt::Text>, tauto_rt::stdlib::Bytes), tauto_rt::Text>,
    ) -> Result<Value<'a>, RunError> {
        match r {
            Ok((items, body)) => {
                let items = items.iter().map(|t| Value::Text(Rc::from(&**t))).collect();
                let list = self.list(items)?;
                let pair = self.make("Pair::Pair", vec![list, Value::Bytes(body)])?;
                self.make("Result::Ok", vec![pair])
            }
            Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(&*e))]),
        }
    }

    /// A TLS session the host gave, as `Result(Option(Pair(List(Text), Bytes)), Text)`.
    fn tls_session(
        &mut self,
        r: Result<Option<tauto_rt::tls_host::Established>, tauto_rt::Text>,
    ) -> Result<Value<'a>, RunError> {
        match r {
            Ok(Some((items, peer))) => {
                let items = items.iter().map(|t| Value::Text(Rc::from(&**t))).collect();
                let list = self.list(items)?;
                let pair = self.make("Pair::Pair", vec![list, Value::Bytes(peer.into())])?;
                let some = self.option(Some(pair))?;
                self.make("Result::Ok", vec![some])
            }
            Ok(None) => {
                let none = self.option(None)?;
                self.make("Result::Ok", vec![none])
            }
            Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(&*e))]),
        }
    }

    /// The texts of a `List(Text)`.
    fn text_items(&self, l: &Value<'a>, what: &str) -> Result<Vec<tauto_rt::Text>, RunError> {
        let mut texts = Vec::new();
        for t in self.list_items(l)? {
            match t {
                Value::Text(t) => texts.push(tauto_rt::Text::from(&*t)),
                _ => return runtime(msg!("eval-takes-a-list-text", what = what.to_string())),
            }
        }
        Ok(texts)
    }

    /// The items of a `List(Bytes)`.
    fn bytes_items(
        &self,
        l: &Value<'a>,
        what: &str,
    ) -> Result<Vec<tauto_rt::stdlib::Bytes>, RunError> {
        let mut items = Vec::new();
        for b in self.list_items(l)? {
            match b {
                Value::Bytes(b) => items.push(b.clone()),
                _ => return runtime(msg!("eval-takes-a-list-bytes", what = what.to_string())),
            }
        }
        Ok(items)
    }

    /// The bytes of a `List(u8)`.
    fn byte_items(&mut self, l: &Value<'a>, what: &str) -> Result<Vec<u8>, RunError> {
        let mut bytes = Vec::new();
        for b in self.list_items(l)? {
            match b {
                Value::Int(b) if (0..=255).contains(&b) => bytes.push(b as u8),
                _ => return runtime(msg!("eval-takes-a-list-u8", what = what.to_string())),
            }
        }
        Ok(bytes)
    }

    fn option(&mut self, v: Option<Value<'a>>) -> Result<Value<'a>, RunError> {
        match v {
            Some(v) => self.make("Option::Some", vec![v]),
            None => self.make("Option::None", Vec::new()),
        }
    }

    /// Drops what a value owns: records each token and reports a
    /// linear one.
    fn drop_value(&mut self, v: &Value<'a>) -> Result<(), RunError> {
        if !self.check {
            return Ok(());
        }
        match v {
            Value::Data(d) if !d.owns => {}
            Value::Data(d) => {
                if let Some(t) = d.token
                    && self.live.remove(&t.id).is_some()
                {
                    if t.linear {
                        return ownership(msg!(
                            "eval-a-linear-is-dropped",
                            ty = d.shape.ty.to_string()
                        ));
                    }
                    self.drops.push(d.shape.ty.clone());
                }
                for f in &d.fields {
                    self.drop_value(f)?;
                }
            }
            Value::Res(r) => {
                if let Some(t) = r.token
                    && let Some((_, name)) = self.live.remove(&t.id)
                {
                    self.drops.push(name);
                }
                match &r.kind {
                    ResKind::Buf(_) | ResKind::Cell(..) | ResKind::Weak(_) => {}
                    ResKind::Vec(items) => {
                        let items: Vec<Value<'a>> = items.borrow_mut().drain(..).collect();
                        for item in &items {
                            self.drop_value(item)?;
                        }
                    }
                    ResKind::Map(entries) => {
                        let entries = entries.borrow_mut().take();
                        for (k, v) in &entries {
                            self.drop_value(k)?;
                            self.drop_value(v)?;
                        }
                    }
                }
            }
            // The captures it owns and has not given away.
            Value::Closure(c) => {
                for name in c.owns.iter().rev() {
                    let Some(node) = lookup_node(&c.env, name) else {
                        continue;
                    };
                    if !self.moved.insert(node_id(&node)) {
                        continue;
                    }
                    if let Slot::Val(v) = &node.slot {
                        self.drop_value(v)?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// A value consumed whole (destructured, or taken by a builtin): its own
    /// token goes, what it holds stays owned.
    fn consume(&mut self, v: &Value<'a>) {
        if let Some(t) = token_of(v) {
            self.live.remove(&t.id);
        }
    }

    /// Drops the names a scope bound, from `env` down to `start`, the last
    /// bound first.
    fn drop_scope(&mut self, env: &Env<'a>, start: &Env<'a>) -> Result<(), RunError> {
        if !self.check {
            return Ok(());
        }
        for node in nodes_down_to(env, start) {
            // A value with no token has nothing to drop, and a continuation
            // that resumes more than once leaves this scope more than once.
            let holds = match &node.slot {
                Slot::Val(v) => holds_token(v),
                Slot::Cell(c) => holds_token(&c.borrow()),
                Slot::Borrow(_) => false,
            };
            if !holds {
                continue;
            }
            if !self.moved.insert(node_id(&node)) {
                continue;
            }
            match &node.slot {
                Slot::Val(v) => self.drop_value(v)?,
                Slot::Cell(c) => {
                    let v = c.borrow().clone();
                    self.drop_value(&v)?;
                }
                Slot::Borrow(_) => {}
            }
        }
        Ok(())
    }

    fn run_block(&mut self, stmts: &'a [Stmt]) -> Result<Value<'a>, RunError> {
        let (ctrl, kont) = self.start_stmt(stmts, 0, None, None, true, None)?;
        self.run(ctrl, kont)
    }

    /// Starts statement `at` of a block (or ends the block).
    fn start_stmt(
        &mut self,
        stmts: &'a [Stmt],
        at: usize,
        env: Env<'a>,
        start: Env<'a>,
        root: bool,
        kont: Kont<'a>,
    ) -> Result<(Ctrl<'a>, Kont<'a>), RunError> {
        let Some(stmt) = stmts.get(at) else {
            self.drop_scope(&env, &start)?;
            return Ok((Ctrl::Ret(Value::Unit), kont));
        };
        let frame = Frame::Stmt {
            stmts,
            at,
            env: env.clone(),
            start: start.clone(),
            root,
            temps: Vec::new(),
        };
        Ok(match stmt {
            Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
                (Ctrl::Eval(value, env), push(kont, frame))
            }
            Stmt::Expr(e) => (Ctrl::Eval(e, env), push(kont, frame)),
            Stmt::Return(Some(e)) => (Ctrl::Eval(e, env), push(kont, frame)),
            Stmt::Return(None) => (Ctrl::Ret(Value::Unit), push(kont, frame)),
            Stmt::Fn(f) => {
                if !root {
                    note_lent_fields(f, &mut self.lent_fields);
                    let free: Vec<String> = crate::lin::free_vars(&f.body)
                        .into_iter()
                        .filter(|n| !f.params.contains(n))
                        .collect();
                    self.alloc(1);
                    let closure = Value::Closure(Rc::new(Closure {
                        params: &f.params,
                        body: &f.body,
                        env: captured_env(&env, &free),
                        owns: Vec::new(),
                    }));
                    let env = bind(&env, &f.name, Slot::Val(closure));
                    return self.start_stmt(stmts, at + 1, env, start, root, kont);
                }
                return self.start_stmt(stmts, at + 1, env, start, root, kont);
            }
            Stmt::Effect(_)
            | Stmt::Struct(_)
            | Stmt::Enum(_)
            | Stmt::Extern { .. }
            | Stmt::Class(_)
            | Stmt::Instance(_)
            | Stmt::Theorem(_)
            | Stmt::Def(_)
            | Stmt::Import { .. }
            | Stmt::Module { .. }
            | Stmt::Mutual { .. }
            | Stmt::Attributed { .. }
            | Stmt::Called { .. }
            | Stmt::Inductive(_) => {
                return self.start_stmt(stmts, at + 1, env, start, root, kont);
            }
            Stmt::While { condition, .. } => (
                Ctrl::Eval(condition, env.clone()),
                push(
                    kont,
                    Frame::WhileTest {
                        stmts,
                        at,
                        env,
                        start,
                        root,
                    },
                ),
            ),
            Stmt::Other(what, span) => {
                return runtime(msg!(
                    "eval-not-supported-yet-byte",
                    what = what.to_string(),
                    start = span.start.to_string()
                ));
            }
            Stmt::Syntax { span, .. } | Stmt::Macro { span, .. } => {
                return runtime(msg!(
                    "eval-a-syntax-or-macro-is-not",
                    start = span.start.to_string()
                ));
            }
        })
    }

    /// A run that does not stop calls or loops without end, so the host's
    /// limit counts only those. A macro's limit counts every step.
    fn count_call(&mut self) -> Result<(), RunError> {
        if self.host.is_none() {
            self.calls += 1;
            if self.calls > self.limit {
                return Err(RunError::Interrupted);
            }
        }
        Ok(())
    }

    fn run(&mut self, mut ctrl: Ctrl<'a>, mut kont: Kont<'a>) -> Result<Value<'a>, RunError> {
        loop {
            self.steps += 1;
            if self.host.is_some() && self.steps > self.limit {
                return Err(RunError::Interrupted);
            }
            if self.steps % 1024 == 0
                && let Some(cancel) = &self.cancel
                && cancel.load(std::sync::atomic::Ordering::Relaxed)
            {
                return Err(RunError::Interrupted);
            }
            if self.any_budget
                && let Some((frames, after)) = self.exceeded_budget(&kont)
            {
                // The body stops here; `exceeded` is performed where the
                // budget is written, and `k(v)` is the budget expression's value.
                let stopped = Stopped { ctrl, frames };
                kont = after;
                ctrl = Ctrl::Perform("exceeded".into(), vec![Value::Stopped(Rc::new(stopped))]);
                continue;
            }
            match ctrl {
                Ctrl::Eval(term, env) => {
                    if let Some(to) = self.report.product_fits.get(&term.span) {
                        kont = push(kont, Frame::Fit { to });
                    }
                    let (c, k) = self.eval_term(term, env, kont)?;
                    ctrl = c;
                    kont = k;
                }
                Ctrl::Ret(value) => match kont {
                    None => return Ok(value),
                    Some(node) => {
                        let next = node.next.clone();
                        let (c, k) = self.resume_frame(&node.frame, value, next)?;
                        ctrl = c;
                        kont = k;
                    }
                },
                Ctrl::Perform(effect, args) => {
                    let (c, k) = self.perform(&effect, args, kont)?;
                    ctrl = c;
                    kont = k;
                }
            }
        }
    }

    /// The innermost budget that has run out: the frames up to and including
    /// its own, and what follows it.
    fn exceeded_budget(&self, kont: &Kont<'a>) -> Option<(Vec<Frame<'a>>, Kont<'a>)> {
        let mut frames = Vec::new();
        let mut at = kont;
        while let Some(node) = at {
            frames.push(node.frame.clone());
            if let Frame::Budget { limit, end } = node.frame
                && self.count(limit) > end
            {
                return Some((frames, node.next.clone()));
            }
            at = &node.next;
        }
        None
    }

    /// The value of name `name`: with the ownership check, using it where
    /// its value moves marks it moved.
    fn name(
        &mut self,
        term: &'a SurfaceTerm,
        name: &str,
        env: &Env<'a>,
    ) -> Result<Value<'a>, RunError> {
        if let Some(node) = lookup_node(env, name) {
            let value = match &node.slot {
                Slot::Val(v) | Slot::Borrow(v) => v.clone(),
                Slot::Cell(cell) => cell.borrow().clone(),
            };
            if self.check {
                if matches!(value, Value::Moved) || self.moved.contains(&node_id(&node)) {
                    return ownership(msg!("eval-is-used-after-move", name = name.to_string()));
                }
                if self.moves(term) {
                    match &node.slot {
                        Slot::Val(_) => {
                            self.moved.insert(node_id(&node));
                        }
                        Slot::Cell(cell) => *cell.borrow_mut() = Value::Moved,
                        Slot::Borrow(_) => {}
                    }
                }
            }
            return Ok(value);
        }
        if let Some(v) = self.globals.get(name) {
            return Ok(v.clone());
        }
        match name {
            // `i32::MIN / -1` overflows an `i32` but not the `i64` it is held in.
            "div" if self.report.widths.get(&term.id()) == Some(&Width::W32) => {
                return Ok(Value::Builtin("div_i32"));
            }
            "div" => return Ok(Value::Builtin("div")),
            "mod" => return Ok(Value::Builtin("mod")),
            "clone" => return Ok(Value::Builtin("clone")),
            _ => {}
        }
        let datas = self.datas();
        if let Ok((d, c)) = datas.resolve_ctor(name, self.report.term(term)) {
            let ctor = &datas.decls[d].constructors[*c];
            let key = self.ctor_key_at(term, name)?;
            if ctor.fields.is_empty() {
                return self.make(key, Vec::new());
            }
            return Ok(Value::Ctor(key));
        }
        runtime(msg!("eval-is-not-defined", name = name.to_string()))
    }

    /// The value at a place (`x`, `x.f.g`) without moving it.
    fn place_value(
        &mut self,
        t: &'a SurfaceTerm,
        env: &Env<'a>,
    ) -> Result<Option<Value<'a>>, RunError> {
        match &*t.kind {
            TermKind::Var(name) => match lookup_node(env, name) {
                Some(node) => {
                    let v = match &node.slot {
                        Slot::Val(v) | Slot::Borrow(v) => v.clone(),
                        Slot::Cell(c) => c.borrow().clone(),
                    };
                    if self.check
                        && (matches!(v, Value::Moved) || self.moved.contains(&node_id(&node)))
                    {
                        return ownership(msg!(
                            "eval-is-borrowed-after-move",
                            name = name.to_string()
                        ));
                    }
                    Ok(Some(v))
                }
                None => Ok(None),
            },
            TermKind::Field { base, name } => match self.place_value(base, env)? {
                Some(v) => Ok(Some(field_of(&v, name)?)),
                None => Ok(None),
            },
            _ => Ok(None),
        }
    }

    /// `&mut p`: the place `p` names in a cell.
    fn place_ref(&mut self, t: &'a SurfaceTerm, env: &Env<'a>) -> Result<Place<'a>, RunError> {
        match &*t.kind {
            TermKind::Var(name) => match lookup(env, name) {
                Some(Slot::Cell(cell)) => Ok(Place {
                    root: Root::Cell(cell),
                    path: Vec::new(),
                }),
                Some(Slot::Val(Value::Ref(p)) | Slot::Borrow(Value::Ref(p))) => Ok(p),
                _ => runtime(msg!("eval-is-not-a-var", name = name.to_string())),
            },
            TermKind::Field { base, name } => {
                let place = self.place_ref(base, env)?;
                let Value::Data(d) = deref(&place.get()) else {
                    return runtime(msg!("eval-no-field", name = name.to_string()));
                };
                match d
                    .shape
                    .names
                    .iter()
                    .position(|n| n.as_deref() == Some(name.as_str()))
                {
                    Some(i) => Ok(place.field(i)),
                    None => runtime(msg!(
                        "eval-has-no-field",
                        ty = d.shape.ty.to_string(),
                        name = name.to_string()
                    )),
                }
            }
            _ => runtime(msg!("eval-only-a-var-or-its-field")),
        }
    }

    /// A closure. With the ownership check, the owned values it captures
    /// move into it: they are its own names from now on.
    fn closure(
        &mut self,
        lam: &'a SurfaceTerm,
        params: &'a [String],
        body: &'a SurfaceTerm,
        env: Env<'a>,
    ) -> Value<'a> {
        let mut env = env;
        let mut owns = Vec::new();
        if self.check {
            for name in crate::lin::free_vars(lam) {
                let Some(node) = lookup_node(&env, &name) else {
                    continue;
                };
                if let Slot::Val(v) = &node.slot
                    && holds_token(v)
                    && !self.moved.contains(&node_id(&node))
                {
                    self.moved.insert(node_id(&node));
                    env = bind(&env, node.name, Slot::Val(v.clone()));
                    owns.push(node.name);
                }
            }
        }
        let env = captured_env(&env, &crate::lin::free_vars(lam));
        self.alloc(1);
        Value::Closure(Rc::new(Closure {
            params,
            body,
            env,
            owns,
        }))
    }

    fn eval_term(
        &mut self,
        term: &'a SurfaceTerm,
        env: Env<'a>,
        kont: Kont<'a>,
    ) -> Result<(Ctrl<'a>, Kont<'a>), RunError> {
        Ok(match &*term.kind {
            TermKind::Nat(n) => match (n.parse::<i128>(), Nat::parse(n)) {
                (Ok(n), _) => (Ctrl::Ret(Value::Int(n)), kont),
                // Only a `nat` holds a literal past an `i128`.
                (_, Some(n)) => (Ctrl::Ret(Value::Nat(n)), kont),
                _ => return runtime(msg!("eval-is-too-large", n = n.to_string())),
            },
            TermKind::Float(x) => match tauto_rt::float::parse_literal(x) {
                Some(x) => (Ctrl::Ret(Value::Float(x)), kont),
                None => return runtime(msg!("eval-is-not-a-float", x = x.to_string())),
            },
            TermKind::Text(t) => (Ctrl::Ret(Value::Text(Rc::from(t.as_str()))), kont),
            TermKind::Bool(b) => (Ctrl::Ret(Value::Bool(*b)), kont),
            TermKind::Var(name) => (Ctrl::Ret(self.name(term, name, &env)?), kont),
            TermKind::Lam { params, body, .. } => {
                (Ctrl::Ret(self.closure(term, params, body, env)), kont)
            }
            TermKind::BorrowLam { lam, .. } => match &*lam.kind {
                TermKind::Lam { params, body, .. } => {
                    (Ctrl::Ret(self.closure(lam, params, body, env)), kont)
                }
                _ => return runtime(msg!("eval-a-borrowing-lambda-without-a-lambda")),
            },
            TermKind::Borrow {
                mutable: true,
                term: place,
            } => (Ctrl::Ret(Value::Ref(self.place_ref(place, &env)?)), kont),
            TermKind::Borrow {
                mutable: false,
                term: inner,
            } => match self.place_value(inner, &env)? {
                Some(v) => (Ctrl::Ret(v), kont),
                // A borrow of a temporary: the value itself, owned by the
                // enclosing statement.
                None => (Ctrl::Eval(inner, env), push(kont, Frame::BorrowTemp)),
            },
            TermKind::Record { name, fields, .. }
                if is_pair_name(name)
                    && fields.len() == 2
                    // A product, or what a product with one member or none is
                    // (`#(a, #())` is an `A`); a `Pair` the checker kept as a record is one.
                    && matches!(
                        self.report.term(term).map(|t| t.unborrowed()),
                        Some(t) if !matches!(t, Ty::Named(n, _) if is_pair_name(n))
                    ) =>
            {
                (
                    Ctrl::Eval(&fields[0].1, env.clone()),
                    push(
                        kont,
                        Frame::PairArgs {
                            term,
                            fields,
                            done: Vec::new(),
                            env,
                        },
                    ),
                )
            }
            TermKind::Record { name, fields, .. } => {
                let name = self.ctor_key_at(term, name)?;
                match fields.split_first() {
                    None => (Ctrl::Ret(self.make(name, Vec::new())?), kont),
                    Some((first, _)) => (
                        Ctrl::Eval(&first.1, env.clone()),
                        push(
                            kont,
                            Frame::RecordArgs {
                                name,
                                fields,
                                done: Vec::new(),
                                env,
                            },
                        ),
                    ),
                }
            }
            TermKind::App {
                function,
                arguments,
            } => {
                if let TermKind::Var(name) = &*function.kind
                    && lookup(&env, name).is_none()
                {
                    if name == "Tuple" && arguments.is_empty() {
                        return Ok((Ctrl::Ret(Value::Unit), kont));
                    }
                    // `start()`: a nullary constructor's value, as `start`.
                    if arguments.is_empty() && self.datas().only_nullary(name) {
                        return Ok((Ctrl::Eval(function, env), kont));
                    }
                    if (name == "&&" || name == "||") && arguments.len() == 2 {
                        let frame = Frame::Logic {
                            and: name == "&&",
                            rhs: &arguments[1],
                            env: env.clone(),
                        };
                        return Ok((Ctrl::Eval(&arguments[0], env), push(kont, frame)));
                    }
                    if OPERATORS.contains(&name.as_str()) {
                        let op: &'a str = name;
                        let width = self
                            .report
                            .widths
                            .get(&term.id())
                            .copied()
                            .unwrap_or(Width::W64);
                        return Ok(self.start_args(
                            |done, rest, env| Frame::OpArg {
                                op,
                                width,
                                done,
                                rest,
                                env,
                            },
                            arguments,
                            env,
                            kont,
                        ));
                    }
                }
                (
                    Ctrl::Eval(function, env.clone()),
                    push(
                        kont,
                        Frame::AppFn {
                            args: arguments,
                            env,
                        },
                    ),
                )
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => (
                Ctrl::Eval(condition, env.clone()),
                push(
                    kont,
                    Frame::If {
                        then,
                        otherwise: otherwise.as_deref(),
                        env,
                    },
                ),
            ),
            TermKind::Block(stmts) => {
                return self.start_stmt(stmts, 0, env.clone(), env, false, kont);
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                let owned = self.check
                    && !matches!(self.report.term(scrutinee), Some(Ty::Borrow(..)))
                    && !matches!(&*scrutinee.kind, TermKind::Borrow { .. })
                    && !borrowed_name(scrutinee, &env);
                (
                    Ctrl::Eval(scrutinee, env.clone()),
                    push(kont, Frame::Match { arms, env, owned }),
                )
            }
            TermKind::Perform { effect, args } if args.is_empty() => {
                (Ctrl::Perform(effect.clone(), Vec::new()), kont)
            }
            TermKind::Perform { effect, args } => self.start_args(
                |done, rest, env| Frame::PerformArgs {
                    effect,
                    done,
                    rest,
                    env,
                },
                args,
                env,
                kont,
            ),
            TermKind::Handle { body, handlers } => (
                Ctrl::Eval(body, env.clone()),
                push(kont, Frame::Handle { handlers, env }),
            ),
            TermKind::Field { .. } if self.lent_fields.contains(&(term as *const _)) => {
                (Ctrl::Ret(Value::Ref(self.place_ref(term, &env)?)), kont)
            }
            TermKind::Field { base, name } => match self.place_value(base, &env)? {
                // A field of a place is read where it is, nothing moves.
                Some(v) => (Ctrl::Ret(self.field(v, name)?), kont),
                None => (Ctrl::Eval(base, env), push(kont, Frame::Field { name })),
            },
            TermKind::Budget { limit, steps, body } => {
                self.any_budget = true;
                (
                    Ctrl::Eval(steps, env.clone()),
                    push(
                        kont,
                        Frame::BudgetSteps {
                            limit: *limit,
                            body,
                            env,
                        },
                    ),
                )
            }
            TermKind::Tagged { term, .. } => (Ctrl::Eval(term, env), kont),
            TermKind::Product(members) | TermKind::Tuple(members) => match members.first() {
                Some(first) => (
                    Ctrl::Eval(first, env.clone()),
                    push(
                        kont,
                        Frame::ProductArgs {
                            term,
                            members,
                            done: Vec::new(),
                            env,
                        },
                    ),
                ),
                None => (Ctrl::Ret(Value::Unit), kont),
            },
            // `(e: T)`: one member of a product is read out of it; fewer members are
            // taken where the checker recorded the fit (`product_fits`).
            TermKind::Ascribe { term: base, .. } => {
                let key: Rc<str> = match self.report.term(term) {
                    Some(Ty::Product(_) | Ty::Union(_)) => {
                        return Ok((Ctrl::Eval(base, env), kont));
                    }
                    Some(t) => Rc::from(t.unborrowed().to_string()),
                    None => return runtime(msg!("eval-a-product-s-member-of-unknown")),
                };
                match self.place_value(base, &env)? {
                    // A member of a place is read where it is, nothing moves.
                    Some(v) => (Ctrl::Ret(project(v, &key)?), kont),
                    None => (Ctrl::Eval(base, env), push(kont, Frame::Project { key })),
                }
            }
            other => {
                return runtime(msg!(
                    "eval-not-supported-yet",
                    other = format!("{:?}", other)
                ));
            }
        })
    }

    /// A product of the members' values: a member that is a product gives
    /// its members, a `()` none; in the order of the product's type.
    fn make_product(
        &self,
        term: &'a SurfaceTerm,
        members: &'a [SurfaceTerm],
        values: Vec<Value<'a>>,
    ) -> Result<Value<'a>, RunError> {
        let members: Vec<&SurfaceTerm> = members.iter().collect();
        self.make_product_of(term, &members, values)
    }

    fn make_product_of(
        &self,
        term: &SurfaceTerm,
        members: &[&SurfaceTerm],
        values: Vec<Value<'a>>,
    ) -> Result<Value<'a>, RunError> {
        let mut entries: Vec<(Rc<str>, Value<'a>)> = Vec::new();
        for (m, v) in members.iter().zip(values) {
            match (v, self.report.term(m).map(|t| t.unborrowed())) {
                (Value::Product(inner), _) => entries.extend(inner.iter().cloned()),
                (_, Some(Ty::Unit)) => {}
                (v, Some(t)) => entries.push((Rc::from(t.to_string()), v)),
                (_, None) => return runtime(msg!("eval-a-product-s-member-of-unknown")),
            }
        }
        let order: Vec<String> = match self.report.term(term).map(|t| t.unborrowed()) {
            Some(Ty::Product(ts)) => ts.iter().map(|t| t.to_string()).collect(),
            _ => return Ok(entries.pop().map_or(Value::Unit, |(_, v)| v)),
        };
        entries.sort_by_key(|(k, _)| order.iter().position(|o| **o == **k));
        Ok(Value::Product(entries.into()))
    }

    /// `v.name`: a struct's field, or `info.more` / `info.unbounded`.
    fn field(&self, v: Value<'a>, name: &str) -> Result<Value<'a>, RunError> {
        match (deref(&v), name) {
            (Value::Info(info), "more") => Ok(Value::Resume(info, true)),
            (Value::Info(info), "unbounded") => Ok(Value::Resume(info, false)),
            (v, name) => field_of(&v, name),
        }
    }

    /// Evaluates `args` left to right into a frame built by `make`.
    fn start_args(
        &mut self,
        make: impl FnOnce(Vec<Value<'a>>, &'a [SurfaceTerm], Env<'a>) -> Frame<'a>,
        args: &'a [SurfaceTerm],
        env: Env<'a>,
        kont: Kont<'a>,
    ) -> (Ctrl<'a>, Kont<'a>) {
        match args.split_first() {
            None => {
                let frame = make(Vec::new(), args, env);
                // No operands: finish at once.
                (Ctrl::Ret(Value::Unit), push(kont, frame))
            }
            Some((first, rest)) => (
                Ctrl::Eval(first, env.clone()),
                push(kont, make(Vec::new(), rest, env)),
            ),
        }
    }

    fn resume_frame(
        &mut self,
        frame: &Frame<'a>,
        value: Value<'a>,
        kont: Kont<'a>,
    ) -> Result<(Ctrl<'a>, Kont<'a>), RunError> {
        Ok(match frame {
            Frame::AppFn { args, env } => {
                let callee = value;
                match args.split_first() {
                    None => return self.apply(callee, Vec::new(), kont),
                    Some((first, rest)) => (
                        Ctrl::Eval(first, env.clone()),
                        push(
                            kont,
                            Frame::AppArg {
                                callee,
                                done: Vec::new(),
                                rest,
                                env: env.clone(),
                            },
                        ),
                    ),
                }
            }
            Frame::AppArg {
                callee,
                done,
                rest,
                env,
            } => {
                let mut done = done.clone();
                done.push(value);
                match rest.split_first() {
                    None => return self.apply(callee.clone(), done, kont),
                    Some((first, rest)) => (
                        Ctrl::Eval(first, env.clone()),
                        push(
                            kont,
                            Frame::AppArg {
                                callee: callee.clone(),
                                done,
                                rest,
                                env: env.clone(),
                            },
                        ),
                    ),
                }
            }
            Frame::OpArg {
                op,
                width,
                done,
                rest,
                env,
            } => {
                let mut done = done.clone();
                done.push(deref(&value));
                match rest.split_first() {
                    None => (Ctrl::Ret(operate(op, *width, &done)?), kont),
                    Some((first, rest)) => (
                        Ctrl::Eval(first, env.clone()),
                        push(
                            kont,
                            Frame::OpArg {
                                op,
                                width: *width,
                                done,
                                rest,
                                env: env.clone(),
                            },
                        ),
                    ),
                }
            }
            Frame::PairArgs {
                term,
                fields,
                done,
                env,
            } => {
                let mut done = done.clone();
                done.push(value);
                match fields.get(done.len()) {
                    Some((_, next)) => (
                        Ctrl::Eval(next, env.clone()),
                        push(
                            kont,
                            Frame::PairArgs {
                                term,
                                fields,
                                done,
                                env: env.clone(),
                            },
                        ),
                    ),
                    None => {
                        let members: Vec<&SurfaceTerm> = fields.iter().map(|(_, t)| t).collect();
                        (Ctrl::Ret(self.make_product_of(term, &members, done)?), kont)
                    }
                }
            }
            Frame::RecordArgs {
                name,
                fields,
                done,
                env,
            } => {
                let mut done = done.clone();
                done.push(value);
                match fields.get(done.len()) {
                    Some((_, next)) => (
                        Ctrl::Eval(next, env.clone()),
                        push(
                            kont,
                            Frame::RecordArgs {
                                name,
                                fields,
                                done,
                                env: env.clone(),
                            },
                        ),
                    ),
                    None => {
                        // The declaration's order.
                        let datas = self.datas();
                        let Some((d, c)) = datas.ctors.get(*name) else {
                            return runtime(msg!("eval-is-not-a-struct", name = name.to_string()));
                        };
                        let mut ordered = Vec::new();
                        for (n, _) in &datas.decls[d].constructors[*c].fields {
                            let at = fields.iter().position(|(f, _)| Some(f) == n.as_ref());
                            match at {
                                Some(i) => ordered.push(done[i].clone()),
                                None => {
                                    return runtime(msg!(
                                        "eval-a-field-is-missing",
                                        name = name.to_string()
                                    ));
                                }
                            }
                        }
                        (Ctrl::Ret(self.make(name, ordered)?), kont)
                    }
                }
            }
            Frame::Logic { and, rhs, env } => match deref(&value) {
                Value::Bool(b) if b == *and => (Ctrl::Eval(rhs, env.clone()), kont),
                Value::Bool(b) => (Ctrl::Ret(Value::Bool(b)), kont),
                other => {
                    return runtime(msg!(
                        "eval-expected-a-boolean-got",
                        other = other.to_string()
                    ));
                }
            },
            Frame::If {
                then,
                otherwise,
                env,
            } => match (deref(&value), otherwise) {
                (Value::Bool(true), _) => (Ctrl::Eval(then, env.clone()), kont),
                (Value::Bool(false), Some(e)) => (Ctrl::Eval(e, env.clone()), kont),
                (Value::Bool(false), None) => (Ctrl::Ret(Value::Unit), kont),
                (other, _) => {
                    return runtime(msg!(
                        "eval-expected-a-boolean-got",
                        other = other.to_string()
                    ));
                }
            },
            Frame::Stmt {
                stmts,
                at,
                env,
                start,
                root,
                temps,
            } => {
                let (stmts, at, root) = (*stmts, *at, *root);
                let mut env = env.clone();
                // The statement has its value: its temporaries are done with.
                for v in temps.iter().rev() {
                    self.drop_value(v)?;
                }
                match &stmts[at] {
                    Stmt::Let { name, value: v, .. } => {
                        env = bind(&env, name, self.slot_for(name, site(v), value));
                    }
                    Stmt::Var { name, .. } => {
                        env = bind(&env, name, Slot::Cell(Rc::new(RefCell::new(value))));
                    }
                    Stmt::Assign {
                        place: Some(place), ..
                    } => {
                        let p = self.place_ref(place, &env)?;
                        let old = p.get();
                        let value = match (&old, &value) {
                            (Value::Ref(_), _) => value,
                            (_, Value::Ref(_)) => deref(&value),
                            _ => unalias(&value, &p),
                        };
                        p.set(value);
                        self.drop_value(&old)?;
                    }
                    Stmt::Assign { name, .. } => match lookup(&env, name) {
                        Some(Slot::Cell(cell)) => {
                            let old = std::mem::replace(&mut *cell.borrow_mut(), value);
                            self.drop_value(&old)?;
                        }
                        Some(Slot::Val(Value::Ref(p)) | Slot::Borrow(Value::Ref(p))) => {
                            let old = p.get();
                            // A place that holds plain data takes plain data:
                            // an argument read through the same `&mut` (as in
                            // `slot := same(slot, true)`) comes back as the
                            // reference, and storing it would make the place
                            // point at itself.
                            let value = match (&old, &value) {
                                (Value::Ref(_), _) => value,
                                (_, Value::Ref(_)) => deref(&value),
                                _ => unalias(&value, &p),
                            };
                            p.set(value);
                            self.drop_value(&old)?;
                        }
                        _ => return runtime(msg!("eval-is-not-a-var", name = name.to_string())),
                    },
                    Stmt::Return(_) => return self.unwind_return(value, kont),
                    Stmt::Expr(_) if at + 1 == stmts.len() => {
                        self.drop_scope(&env, start)?;
                        return Ok((Ctrl::Ret(value), kont));
                    }
                    Stmt::Expr(e) => {
                        // A statement's value is dropped, unless it borrows.
                        if !matches!(self.report.term(e), Some(Ty::Borrow(..))) {
                            self.drop_value(&value)?;
                        }
                    }
                    _ => {}
                }
                if at + 1 == stmts.len() {
                    self.drop_scope(&env, start)?;
                    (Ctrl::Ret(Value::Unit), kont)
                } else {
                    return self.start_stmt(stmts, at + 1, env, start.clone(), root, kont);
                }
            }
            Frame::WhileTest {
                stmts,
                at,
                env,
                start,
                root,
            } => match deref(&value) {
                Value::Bool(true) => {
                    self.count_call()?;
                    let Stmt::While { body, .. } = &stmts[*at] else {
                        return runtime(msg!("eval-a-loop-frame-without-a-loop"));
                    };
                    (
                        Ctrl::Eval(body, env.clone()),
                        push(
                            kont,
                            Frame::WhileBody {
                                stmts,
                                at: *at,
                                env: env.clone(),
                                start: start.clone(),
                                root: *root,
                            },
                        ),
                    )
                }
                Value::Bool(false) => {
                    if at + 1 == stmts.len() {
                        self.drop_scope(env, start)?;
                        (Ctrl::Ret(Value::Unit), kont)
                    } else {
                        return self.start_stmt(
                            stmts,
                            at + 1,
                            env.clone(),
                            start.clone(),
                            *root,
                            kont,
                        );
                    }
                }
                other => {
                    return runtime(msg!(
                        "eval-expected-a-boolean-got",
                        other = other.to_string()
                    ));
                }
            },
            Frame::WhileBody {
                stmts,
                at,
                env,
                start,
                root,
            } => {
                let Stmt::While { condition, .. } = &stmts[*at] else {
                    return runtime(msg!("eval-a-loop-frame-without-a-loop"));
                };
                (
                    Ctrl::Eval(condition, env.clone()),
                    push(
                        kont,
                        Frame::WhileTest {
                            stmts,
                            at: *at,
                            env: env.clone(),
                            start: start.clone(),
                            root: *root,
                        },
                    ),
                )
            }
            Frame::Match { arms, env, owned } => {
                return self.try_arm(arms, 0, deref(&value), env.clone(), *owned, kont);
            }
            Frame::MatchGuard {
                arms,
                at,
                scrutinee,
                outer,
                arm_env,
                owned,
            } => match deref(&value) {
                Value::Bool(true) => {
                    self.take_apart(&arms[*at].pattern, scrutinee, *owned)?;
                    (Ctrl::Eval(&arms[*at].body, arm_env.clone()), kont)
                }
                Value::Bool(false) => {
                    return self.try_arm(
                        arms,
                        at + 1,
                        scrutinee.clone(),
                        outer.clone(),
                        *owned,
                        kont,
                    );
                }
                other => {
                    return runtime(msg!(
                        "eval-a-guard-must-be-a-boolean",
                        other = other.to_string()
                    ));
                }
            },
            Frame::PerformArgs {
                effect,
                done,
                rest,
                env,
            } => {
                let mut done = done.clone();
                done.push(value);
                match rest.split_first() {
                    None => (Ctrl::Perform(effect.to_string(), done), kont),
                    Some((first, rest)) => (
                        Ctrl::Eval(first, env.clone()),
                        push(
                            kont,
                            Frame::PerformArgs {
                                effect,
                                done,
                                rest,
                                env: env.clone(),
                            },
                        ),
                    ),
                }
            }
            Frame::Handle { handlers, env } => {
                // The handled computation returned.
                for h in handlers.iter() {
                    if let Handler::Return { pattern, body } = h {
                        let Some(arm_env) =
                            self.bind_pattern(pattern, &value, env.clone(), site(body))
                        else {
                            return runtime(msg!("eval-the-return-arm-s-pattern-does"));
                        };
                        return Ok((Ctrl::Eval(body, arm_env), kont));
                    }
                }
                (Ctrl::Ret(value), kont)
            }
            Frame::Budget { .. } => (Ctrl::Ret(value), kont),
            Frame::BorrowTemp => (Ctrl::Ret(value.clone()), self.own_temp(value, kont)),
            Frame::BudgetSteps { limit, body, env } => match deref(&value) {
                Value::Int(n) if n >= 0 => (
                    Ctrl::Eval(body, env.clone()),
                    push(
                        kont,
                        Frame::Budget {
                            limit: *limit,
                            end: self.count(*limit).saturating_add(n as u64),
                        },
                    ),
                ),
                other => {
                    return runtime(msg!(
                        "eval-budget-must-be-a-number-got",
                        limit = limit.name().to_string(),
                        other = other.to_string()
                    ));
                }
            },
            Frame::Call { env, base } => {
                self.drop_scope(env, base)?;
                (Ctrl::Ret(value), kont)
            }
            Frame::Field { name } => (Ctrl::Ret(self.field(value, name)?), kont),
            Frame::Project { key } => (Ctrl::Ret(project(value, &key)?), kont),
            Frame::Fit { to } => (Ctrl::Ret(fit(value, to)?), kont),
            Frame::ProductArgs {
                term,
                members,
                done,
                env,
            } => {
                let mut done = done.clone();
                done.push(value);
                match members.get(done.len()) {
                    Some(next) => (
                        Ctrl::Eval(next, env.clone()),
                        push(
                            kont,
                            Frame::ProductArgs {
                                term,
                                members,
                                done,
                                env: env.clone(),
                            },
                        ),
                    ),
                    None => {
                        self.alloc(1 + members.len() as u64);
                        (Ctrl::Ret(self.make_product(term, members, done)?), kont)
                    }
                }
            }
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn try_arm(
        &mut self,
        arms: &'a [MatchArm],
        from: usize,
        scrutinee: Value<'a>,
        env: Env<'a>,
        owned: bool,
        kont: Kont<'a>,
    ) -> Result<(Ctrl<'a>, Kont<'a>), RunError> {
        for (at, arm) in arms.iter().enumerate().skip(from) {
            let Some(arm_env) =
                self.bind_pattern(&arm.pattern, &scrutinee, env.clone(), site(&arm.body))
            else {
                continue;
            };
            return Ok(match &arm.guard {
                None => {
                    self.take_apart(&arm.pattern, &scrutinee, owned)?;
                    (Ctrl::Eval(&arm.body, arm_env), kont)
                }
                Some(guard) => (
                    Ctrl::Eval(guard, arm_env.clone()),
                    push(
                        kont,
                        Frame::MatchGuard {
                            arms,
                            at,
                            scrutinee,
                            outer: env,
                            arm_env,
                            owned,
                        },
                    ),
                ),
            });
        }
        runtime(tauto_rt::messages::NO_ARM)
    }

    /// Binds the names in `pattern` if it fits `value`; a name of a pattern
    /// at `at` whose type is a borrow binds a borrow.
    fn bind_pattern(
        &self,
        pattern: &'a Pattern,
        value: &Value<'a>,
        env: Env<'a>,
        at: crate::surface::TermId,
    ) -> Option<Env<'a>> {
        let original = value;
        let value = deref(value);
        match (pattern, &value) {
            (Pattern::Wild, _) => Some(env),
            // `@a p`: a label is not on the value, which `p` matches.
            (Pattern::Ctor { args, .. }, _) if pattern.label().is_some() => {
                self.bind_pattern(&args[0], original, env, at)
            }
            // A name that is a `&mut` keeps the place (`Some(x)` of a
            // `Vec::get_mut`).
            (Pattern::Bind(name), _)
                if matches!(original, Value::Ref(_))
                    && self.borrow_local(name, at) == Some(true) =>
            {
                Some(bind(&env, name, Slot::Borrow(original.clone())))
            }
            (Pattern::Bind(name), Value::Data(d)) if self.is_nullary(name, d) => {
                self.matches_ctor(name, d).then_some(env)
            }
            (Pattern::Bind(name), v) => Some(bind(&env, name, self.slot_for(name, at, v.clone()))),
            (Pattern::Int(a), Value::Int(b)) if i128::from(*a) == *b => Some(env),
            (Pattern::Int(a), Value::Nat(b))
                if as_nat(&Value::Int(i128::from(*a))).as_ref() == Some(b) =>
            {
                Some(env)
            }
            (Pattern::Bool(a), Value::Bool(b)) if a == b => Some(env),
            (Pattern::Text(a), Value::Text(b)) if a.as_str() == &**b => Some(env),
            (Pattern::Ctor { name, args }, Value::Data(d)) => {
                if !self.matches_ctor(name, d) || args.len() != d.fields.len() {
                    return None;
                }
                let mut env = env;
                for (p, v) in args.iter().zip(&d.fields) {
                    env = self.bind_pattern(p, v, env, at)?;
                }
                Some(env)
            }
            // `#(p₁, …, pₙ)` on a product: by labels, or in the product's order.
            (Pattern::Record { .. } | Pattern::Tuple(_), Value::Product(ms))
                if is_tuple_pattern(pattern) =>
            {
                let pats = pair_pattern_members(pattern);
                if pats.len() != ms.len() {
                    return None;
                }
                let mut env = env;
                let labelled = pats.iter().all(|p| p.label().is_some());
                for (i, p) in pats.iter().enumerate() {
                    let v = if labelled {
                        let (tag, _) = p.label()?;
                        let prefix = format!("@{tag} ");
                        &ms.iter().find(|(k, _)| k.starts_with(&prefix))?.1
                    } else {
                        &ms[i].1
                    };
                    env = self.bind_pattern(p, v, env, at)?;
                }
                Some(env)
            }
            // `#(p, #())` is `p`, and `#(#(), #())` is `#()`, on a value that is no product.
            (Pattern::Record { .. } | Pattern::Tuple(_), _)
                if is_tuple_pattern(pattern) && pair_pattern_members(pattern).len() < 2 =>
            {
                match pair_pattern_members(pattern).as_slice() {
                    [one] => self.bind_pattern(one, original, env, at),
                    _ => Some(env),
                }
            }
            // `#(p, q, …)` on a `Pair` the checker kept as a record: `p` on its
            // first field and `#(q, …)` on the second.
            (Pattern::Tuple(items), Value::Data(_)) => self.bind_tuple_data(items, original, env, at),
            (Pattern::Record { name, fields }, Value::Data(d)) => {
                if !self.matches_ctor(name, d) {
                    return None;
                }
                let mut env = env;
                for (f, p) in fields {
                    let i = d
                        .shape
                        .names
                        .iter()
                        .position(|n| n.as_deref() == Some(f.as_str()))?;
                    env = self.bind_pattern(p, &d.fields[i], env, at)?;
                }
                Some(env)
            }
            _ => None,
        }
    }

    /// `#(p₁, …, pₙ)` on nested `Pair` records: `p₁` on the first field, the rest
    /// on the second.
    fn bind_tuple_data(
        &self,
        items: &'a [Pattern],
        value: &Value<'a>,
        env: Env<'a>,
        at: crate::surface::TermId,
    ) -> Option<Env<'a>> {
        match items {
            [] => Some(env),
            [one] => self.bind_pattern(one, value, env, at),
            [first, rest @ ..] => match deref(value) {
                Value::Data(d) if is_pair_name(&d.shape.ty) && d.fields.len() == 2 => {
                    let env = self.bind_pattern(first, &d.fields[0], env, at)?;
                    self.bind_tuple_data(rest, &d.fields[1], env, at)
                }
                _ => None,
            },
        }
    }

    /// The chosen arm takes an owned scrutinee apart: its constructors'
    /// tokens are consumed, and what `_` stands for is dropped.
    fn take_apart(
        &mut self,
        pattern: &Pattern,
        value: &Value<'a>,
        owned: bool,
    ) -> Result<(), RunError> {
        if !self.check || !owned {
            return Ok(());
        }
        let value = deref(value);
        match (pattern, &value) {
            (Pattern::Wild, v) => self.drop_value(v),
            (Pattern::Ctor { args, .. }, _) if pattern.label().is_some() => {
                self.take_apart(&args[0], &value, owned)
            }
            (Pattern::Bind(name), Value::Data(d)) if self.is_nullary(name, d) => {
                self.consume(&value);
                Ok(())
            }
            (Pattern::Ctor { args, .. }, Value::Data(d)) => {
                self.consume(&value);
                for (p, v) in args.iter().zip(&d.fields) {
                    self.take_apart(p, v, owned)?;
                }
                Ok(())
            }
            (Pattern::Record { fields, .. }, Value::Data(d)) => {
                self.consume(&value);
                for (n, v) in d.shape.names.iter().zip(&d.fields) {
                    match fields.iter().find(|(f, _)| Some(f) == n.as_ref()) {
                        Some((_, p)) => self.take_apart(p, v, owned)?,
                        None => self.drop_value(v)?,
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// [`Self::ctor_key`] of `name` written at `term`, as its type gives it.
    fn ctor_key_at(&self, term: &SurfaceTerm, name: &str) -> Result<&'a str, RunError> {
        if let Some(key) = self.ctor_keys.borrow().get(&term.id()) {
            return Ok(key);
        }
        let key = self.ctor_key(name, self.report.term(term))?;
        self.ctor_keys.borrow_mut().insert(term.id(), key);
        Ok(key)
    }

    fn ctor_key(&self, name: &str, expected: Option<&Ty>) -> Result<&'a str, RunError> {
        let datas = self.datas();
        let (d, c) = match datas.resolve_ctor(name, expected) {
            Ok(c) => c,
            Err(e) => return runtime(e),
        };
        let decl = &datas.decls[d];
        let key = format!("{}::{}", d, decl.constructors[*c].name);
        match datas.ctors.get_key_value(&key) {
            Some((key, _)) => Ok(key.as_str()),
            None => runtime(msg!("eval-is-not-a-constructor", ctor = name.to_string())),
        }
    }

    // A name only one type has resolves without the value's type, which is
    // then not built.
    fn is_nullary(&self, name: &str, data: &Data<'_>) -> bool {
        let datas = self.datas();
        if datas.ctors.contains_key(name) {
            return datas.nullary(name, None);
        }
        datas.nullary(name, Some(&Ty::Named(data.shape.ty.clone(), Vec::new())))
    }

    fn matches_ctor(&self, name: &str, data: &Data<'_>) -> bool {
        let datas = self.datas();
        let resolved = if datas.ctors.contains_key(name) {
            datas.resolve_ctor(name, None)
        } else {
            datas.resolve_ctor(name, Some(&Ty::Named(data.shape.ty.clone(), Vec::new())))
        };
        resolved.is_ok_and(|(d, c)| {
            d == &data.shape.ty && datas.decls[d].constructors[*c].name == data.shape.ctor
        })
    }

    fn unwind_return(
        &mut self,
        value: Value<'a>,
        mut kont: Kont<'a>,
    ) -> Result<(Ctrl<'a>, Kont<'a>), RunError> {
        while let Some(node) = kont {
            // The blocks `return` leaves drop what they own.
            if let Frame::Stmt { temps, .. } = &node.frame {
                for v in temps.iter().rev() {
                    self.drop_value(v)?;
                }
            }
            self.drop_frame(&node.frame)?;
            if let Frame::Call { .. } = &node.frame {
                return Ok((Ctrl::Ret(value), node.next.clone()));
            }
            kont = node.next.clone();
        }
        runtime(msg!("eval-return-outside-a-function"))
    }

    /// Drops what a frame's scope owns when control leaves it without
    /// finishing it.
    fn drop_frame(&mut self, frame: &Frame<'a>) -> Result<(), RunError> {
        match frame {
            Frame::Call { env, base } => self.drop_scope(env, base),
            Frame::Stmt { env, start, .. }
            | Frame::WhileTest { env, start, .. }
            | Frame::WhileBody { env, start, .. } => self.drop_scope(env, start),
            _ => Ok(()),
        }
    }

    /// Gives a borrowed temporary to the statement that encloses it, as Rust
    /// and JavaScript keep it until the end of the statement. A
    /// `let x = &T.new()` keeps its temporary as long as `x`, so the
    /// statement does not take it then; nor does anything past a call.
    fn own_temp(&self, value: Value<'a>, kont: Kont<'a>) -> Kont<'a> {
        let mut above = Vec::new();
        let mut at = kont.clone();
        while let Some(node) = at {
            match &node.frame {
                Frame::Stmt {
                    stmts,
                    at: i,
                    env,
                    start,
                    root,
                    temps,
                } => {
                    if let Stmt::Let { value: v, .. } | Stmt::Var { value: v, .. } = &stmts[*i] {
                        if matches!(&*v.kind, TermKind::Borrow { .. }) {
                            return kont;
                        }
                    }
                    let mut temps = temps.clone();
                    temps.push(value);
                    let frame = Frame::Stmt {
                        stmts,
                        at: *i,
                        env: env.clone(),
                        start: start.clone(),
                        root: *root,
                        temps,
                    };
                    let mut rebuilt = push(node.next.clone(), frame);
                    for frame in above.into_iter().rev() {
                        rebuilt = push(rebuilt, frame);
                    }
                    return rebuilt;
                }
                Frame::Call { .. } => return kont,
                frame => above.push(frame.clone()),
            }
            at = node.next.clone();
        }
        kont
    }

    fn apply(
        &mut self,
        callee: Value<'a>,
        args: Vec<Value<'a>>,
        kont: Kont<'a>,
    ) -> Result<(Ctrl<'a>, Kont<'a>), RunError> {
        self.count_call()?;
        match deref(&callee) {
            Value::Closure(c) => {
                if c.params.len() != args.len() {
                    return runtime(msg!(
                        "eval-a-function-takes-values-got",
                        params = c.params.len().to_string(),
                        args = args.len().to_string()
                    ));
                }
                let mut env = c.env.clone();
                for (name, arg) in c.params.iter().zip(args) {
                    env = bind(&env, name, self.slot_for(name, site(c.body), arg));
                }
                let frame = Frame::Call {
                    env: env.clone(),
                    base: c.env.clone(),
                };
                Ok((Ctrl::Eval(c.body, env), push(kont, frame)))
            }
            Value::Cont(frames, once) => {
                let [arg] = args.as_slice() else {
                    return runtime(msg!("eval-a-continuation-takes-one-value"));
                };
                if let Some(once) = once {
                    if once.get() {
                        return ownership(msg!("eval-a-continuation-that-resumes-at-most"));
                    }
                    once.set(true);
                }
                // A copy of the set-aside frames goes back on top of the caller.
                let mut kont = kont;
                for frame in frames.0.iter().rev() {
                    kont = push(kont, frame.clone());
                }
                Ok((Ctrl::Ret(arg.clone()), kont))
            }
            Value::Ctor(name) => Ok((Ctrl::Ret(self.make(name, args)?), kont)),
            Value::Builtin(name) => self.builtin(name, args, kont),
            Value::Extern(name) => match (&*name.to_string(), args.as_slice()) {
                ("Probe::new", [Value::Text(probe)]) if self.probes => {
                    self.alloc(1);
                    let token = self.token(false, &format!("probe:{probe}"));
                    let kind = ResKind::Buf(RefCell::new(probe.to_string()));
                    Ok((Ctrl::Ret(Value::Res(Rc::new(Res { kind, token }))), kont))
                }
                _ => runtime(msg!("eval-extern-is-not-runnable", name = name.to_string())),
            },
            Value::Resume(info, more) => {
                let more = match (more, args.as_slice()) {
                    (true, [Value::Int(m)]) if *m >= 0 => Some(*m as u64),
                    (false, []) => None,
                    _ => return runtime(msg!("eval-more-takes-a-number-unbounded-nothing")),
                };
                // `k`'s frames, then the body's with the budget's new end.
                let mut kont = kont;
                for frame in info.rest.0.iter().rev() {
                    kont = push(kont, frame.clone());
                }
                // The stopped budget's frame is the last, and only it gets the
                // new end, in its count: a budget nested in it keeps its own.
                let mut frames = info.stopped.frames.clone();
                if let Some(Frame::Budget { limit, end }) = frames.last_mut() {
                    *end = match more {
                        Some(m) => self.count(*limit).saturating_add(m),
                        None => u64::MAX,
                    };
                }
                for frame in frames.into_iter().rev() {
                    kont = push(kont, frame);
                }
                Ok((info.stopped.ctrl.clone(), kont))
            }
            other => runtime(msg!("eval-is-not-a-function", other = other.to_string())),
        }
    }

    /// The functions the evaluator implements.
    fn builtin(
        &mut self,
        name: &str,
        args: Vec<Value<'a>>,
        kont: Kont<'a>,
    ) -> Result<(Ctrl<'a>, Kont<'a>), RunError> {
        let ret = |v: Value<'a>, kont: Kont<'a>| Ok((Ctrl::Ret(v), kont));
        if let Some(h) = &self.host
            && !h.allowed.iter().any(|a| match a.strip_suffix('*') {
                Some(prefix) => name.starts_with(prefix),
                None => *a == name,
            })
        {
            return Err(RunError::NotAllowed(name.to_string()));
        }
        let plain: Vec<Value<'a>> = args.iter().map(deref).collect();
        match (name, plain.as_slice()) {
            ("Syn::expr_of", [Value::Data(d)]) => {
                let v = match d.shape.ty.as_str() {
                    "SynExpr" => plain[0].clone(),
                    "SynIdent" => self.make("SynExpr::ExVar", vec![plain[0].clone()])?,
                    // The term of a typed `Judgement`.
                    "Judgement" => d.fields[0].clone(),
                    other => {
                        return runtime(msg!(
                            "eval-is-not-filled-in-as-an",
                            other = other.to_string()
                        ));
                    }
                };
                ret(v, kont)
            }
            (
                op @ ("Elab::defeq"
                | "Elab::whnf"
                | "Elab::check"
                | "Elab::global"
                | "Elab::resolve"
                | "Elab::siblings"
                | "Elab::constructor_arity"),
                _,
            ) => {
                let Some(elab) = self.host.as_ref().and_then(|h| h.elab.clone()) else {
                    return runtime(msg!("eval-is-for-a-typed-macro", op = op.to_string()));
                };
                let mut nodes = Vec::new();
                for a in &plain {
                    nodes.push(self.value_node(a)?);
                }
                let answer = elab(op, &nodes).map_err(RunError::Runtime)?;
                let v = self.node_value(&answer)?;
                ret(v, kont)
            }
            ("Syn::expand", [e]) => {
                let node = self.value_node(e)?;
                let known = self.host.as_ref().and_then(|h| {
                    h.expanded
                        .iter()
                        .find(|(from, _)| *from == node)
                        .map(|(_, to)| to.clone())
                });
                match known {
                    Some(to) => {
                        let v = self.node_value(&to)?;
                        ret(v, kont)
                    }
                    None => Err(RunError::NeedExpand(node)),
                }
            }
            ("Judgement::mentions", [Value::Data(d), Value::Int(n)]) => {
                let term = self.value_node(&d.fields[0])?;
                ret(
                    Value::Bool(term.mentions_atom(i64::try_from(*n).map_err(|_| overflow())?)),
                    kont,
                )
            }
            ("Judgement::same_atom", [Value::Data(d), Value::Int(n)]) => {
                let term = self.value_node(&d.fields[0])?;
                let same = term.ctor_name() == Some("ExAtom")
                    && term.field(0).and_then(Node::as_int).map(i128::from) == Some(*n);
                ret(Value::Bool(same), kont)
            }
            ("Syn::open", [e, Value::Text(name), Value::Int(atom)]) => {
                let node = self.value_node(e)?;
                let opened = node
                    .open_var(name, i64::try_from(*atom).map_err(|_| overflow())?)
                    .map(|n| Node::Option(Some(Box::new(n))));
                let v = self.node_value(&opened.unwrap_or_else(Node::none))?;
                ret(v, kont)
            }
            ("div" | "mod", [a, b]) if matches!(a, Value::Nat(_)) || matches!(b, Value::Nat(_)) => {
                let (Some(a), Some(b)) = (as_nat(a), as_nat(b)) else {
                    return Err(overflow());
                };
                let (q, r) = a.divmod(&b).ok_or_else(|| {
                    RunError::Runtime(tauto_rt::messages::DIVISION_BY_ZERO.into())
                })?;
                ret(Value::Nat(if name == "div" { q } else { r }), kont)
            }
            ("Text::of_nat", [n]) => {
                let n = as_nat(n).ok_or_else(overflow)?;
                ret(Value::Text(Rc::from(n.to_string().as_str())), kont)
            }
            ("Nat::of_u64", [Value::Int(n)]) => ret(Value::Int(*n), kont),
            ("U64::of_nat", [n]) => {
                let n = as_nat(n).ok_or_else(overflow)?;
                let n = n.to_u64().ok_or_else(overflow)?;
                ret(Value::Int(i128::from(n)), kont)
            }
            ("div" | "div_i32" | "mod", [Value::Int(a), Value::Int(b)]) => {
                if *b == 0 {
                    return runtime(tauto_rt::messages::DIVISION_BY_ZERO);
                }
                let r = if name == "mod" {
                    a.checked_rem(*b)
                } else {
                    a.checked_div(*b)
                };
                // A negative divisor means signed operands, so `i64::MIN / -1`
                // must fail like the compiled backends instead of leaving i64.
                let r = r.filter(|r| match name {
                    "div_i32" => Width::W32.fits(*r),
                    _ => *b > 0 || *r <= i128::from(i64::MAX),
                });
                ret(Value::Int(r.ok_or_else(overflow)?), kont)
            }
            ("clone", [v]) => {
                let v = self.deep_clone(v)?;
                ret(v, kont)
            }
            ("concat", [Value::Text(a), Value::Text(b)]) => {
                self.alloc_text(a.len() + b.len());
                ret(Value::Text(Rc::from(format!("{a}{b}").as_str())), kont)
            }
            ("words", [Value::Text(t)]) => {
                let words = t
                    .split_whitespace()
                    .map(|w| Value::Text(Rc::from(w)))
                    .collect();
                let list = self.list(words)?;
                ret(list, kont)
            }
            ("Text::of", [b @ Value::Res(r)]) => match &r.kind {
                ResKind::Buf(s) => {
                    let t = Value::Text(Rc::from(s.borrow().as_str()));
                    self.consume(b);
                    ret(t, kont)
                }
                _ => runtime(msg!("eval-text-of-takes-a-buf")),
            },
            ("Pending::ready" | "Pending::take", [v]) => ret(v.clone(), kont),
            // The host ran the body at its `spawn`.
            ("Pending::is_ready", [_]) => ret(Value::Bool(true), kont),
            (new @ ("Ref::new" | "Mutex::new" | "Atomic::new"), [v]) => {
                let name = match new {
                    "Ref::new" => "Ref",
                    "Mutex::new" => "Mutex",
                    _ => "Atomic",
                };
                let c = Value::Res(Rc::new(Res {
                    kind: ResKind::Cell(RefCell::new(v.clone()), name),
                    token: None,
                }));
                ret(c, kont)
            }
            ("Weak::of", [Value::Res(r)]) => {
                let w = Value::Res(Rc::new(Res {
                    kind: ResKind::Weak(Rc::downgrade(r)),
                    token: None,
                }));
                ret(w, kont)
            }
            ("Weak::get", [Value::Res(w)]) => {
                let ResKind::Weak(w) = &w.kind else {
                    return runtime(msg!("eval-weak-get-takes-a-weak"));
                };
                let v = self.option(w.upgrade().map(Value::Res))?;
                ret(v, kont)
            }
            ("Ref::get" | "Atomic::load", [Value::Res(r)]) => {
                let ResKind::Cell(c, _) = &r.kind else {
                    return runtime(msg!("eval-cell-get-takes-a-cell"));
                };
                let v = c.borrow().clone();
                ret(v, kont)
            }
            ("Ref::set" | "Atomic::store" | "Mutex::put", [Value::Res(r), v]) => {
                let ResKind::Cell(c, _) = &r.kind else {
                    return runtime(msg!("eval-cell-set-takes-a-cell"));
                };
                *c.borrow_mut() = v.clone();
                ret(Value::Unit, kont)
            }
            // The evaluator runs each spawned body to its end at its `spawn`,
            // so a task's result is there and a mutex's line never forms: a
            // place in it is handed the content at once, or never.
            ("Pending::signal", [_]) => ret(self.signal(true), kont),
            ("Mutex::claim", [Value::Res(r)]) => {
                let ResKind::Cell(c, _) = &r.kind else {
                    return runtime(msg!("eval-mutex-claim-takes-a-mutex"));
                };
                let full = !matches!(*c.borrow(), Value::Moved);
                ret(self.signal(full), kont)
            }
            ("Mutex::take_claimed", [Value::Res(r), _]) => {
                let ResKind::Cell(c, _) = &r.kind else {
                    return runtime(msg!("eval-mutex-take-claimed-takes-a-mutex"));
                };
                let v = std::mem::replace(&mut *c.borrow_mut(), Value::Moved);
                if matches!(v, Value::Moved) {
                    return runtime(msg!("eval-mutex-take-claimed-of-an-empty"));
                }
                ret(v, kont)
            }
            ("Atomic::fetch_add", [Value::Res(r), Value::Int(n)]) => {
                let ResKind::Cell(c, _) = &r.kind else {
                    return runtime(msg!("eval-atomic-fetch-add-takes-an-atomic"));
                };
                let old = c.replace(Value::Unit);
                let Value::Int(old) = old else {
                    return runtime(msg!("eval-atomic-fetch-add-takes-an-atomic"));
                };
                *c.borrow_mut() = Value::Int(old.wrapping_add(*n));
                ret(Value::Int(old), kont)
            }
            ("Buf::new", []) => {
                let b = self.resource(ResKind::Buf(RefCell::new(String::new())));
                ret(b, kont)
            }
            ("Buf::push", [Value::Res(r), Value::Text(t)]) => {
                let ResKind::Buf(s) = &r.kind else {
                    return runtime(msg!("eval-buf-push-takes-a-buf"));
                };
                s.borrow_mut().push_str(t);
                self.alloc_text(t.len());
                ret(Value::Unit, kont)
            }
            ("Buf::of", [Value::Text(t)]) => {
                self.alloc_text(t.len());
                let b = self.resource(ResKind::Buf(RefCell::new(t.to_string())));
                ret(b, kont)
            }
            ("Buf::clone", [b @ Value::Res(_)]) => {
                let b = self.deep_clone(b)?;
                ret(b, kont)
            }
            ("Vec::new", []) => {
                let v = self.resource(ResKind::Vec(RefCell::new(Vec::new())));
                ret(v, kont)
            }
            ("HashMap::new", []) => {
                let v = self.resource(ResKind::Map(RefCell::new(Entries::new())));
                ret(v, kont)
            }
            ("Vec::push", [Value::Res(r), _]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-vec-push-takes-a-vec"));
                };
                items.borrow_mut().push(args[1].clone());
                self.alloc(1);
                ret(Value::Unit, kont)
            }
            ("Vec::pop", [Value::Res(r)]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-vec-pop-takes-a-vec"));
                };
                let last = items.borrow_mut().pop();
                let v = self.option(last)?;
                ret(v, kont)
            }
            ("Vec::swap", [Value::Res(r), Value::Int(i), Value::Int(j)]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-vec-swap-takes-a-vec"));
                };
                let len = items.borrow().len();
                match (usize::try_from(*i), usize::try_from(*j)) {
                    (Ok(i), Ok(j)) if i < len && j < len => {
                        items.borrow_mut().swap(i, j);
                        ret(Value::Unit, kont)
                    }
                    _ => Ok((Ctrl::Perform("out_of_bounds".into(), Vec::new()), kont)),
                }
            }
            ("Vec::as_slice" | "Vec::as_mut_slice", [v @ Value::Res(_)]) => ret(v.clone(), kont),
            ("Vec::len" | "Slice::len", [Value::Res(r)]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-vec-len-takes-a-vec"));
                };
                ret(Value::Int(items.borrow().len() as i128), kont)
            }
            ("Vec::index", [Value::Res(r), Value::Int(i)]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-vec-index-takes-a-vec"));
                };
                let item = usize::try_from(*i)
                    .ok()
                    .and_then(|i| items.borrow().get(i).cloned());
                match item {
                    Some(v) => ret(v, kont),
                    None => Ok((Ctrl::Perform("out_of_bounds".into(), Vec::new()), kont)),
                }
            }
            ("Vec::clear" | "Vec::truncate", [Value::Res(r), rest @ ..]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-takes-a-vec", name = name.to_string()));
                };
                let keep = match rest {
                    [Value::Int(n)] => usize::try_from(*n).unwrap_or(0),
                    _ => 0,
                };
                let gone: Vec<Value<'a>> = {
                    let mut items = items.borrow_mut();
                    let keep = keep.min(items.len());
                    items.drain(keep..).collect()
                };
                for v in &gone {
                    self.drop_value(v)?;
                }
                ret(Value::Unit, kont)
            }
            ("Vec::into_list", [v @ Value::Res(r)]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-vec-into-list-takes-a-vec"));
                };
                let items: Vec<Value<'a>> = items.borrow_mut().drain(..).collect();
                self.consume(v);
                let list = self.list(items)?;
                ret(list, kont)
            }
            ("Vec::into_array", [v @ Value::Res(r)]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-vec-into-array-takes-a-vec"));
                };
                let items: Vec<Value<'a>> = items.borrow_mut().drain(..).collect();
                self.consume(v);
                ret(Value::Array(items.into()), kont)
            }
            ("Array::of_list", [l]) => {
                let items = self.list_items(l)?;
                self.alloc(1 + items.len() as u64);
                ret(Value::Array(items.into()), kont)
            }
            ("Array::get", [Value::Array(items), Value::Int(i)]) => {
                let item = usize::try_from(*i).ok().and_then(|i| items.get(i).cloned());
                let v = self.option(item)?;
                ret(v, kont)
            }
            ("Array::len", [Value::Array(items)]) => ret(Value::Int(items.len() as i128), kont),
            ("Array::to_list", [Value::Array(items)]) => {
                let list = self.list(items.to_vec())?;
                ret(list, kont)
            }
            ("Bytes::of_list", [l]) => {
                let bytes = self.byte_items(l, "Bytes::of_list")?;
                ret(Value::Bytes(bytes.into()), kont)
            }
            ("Bytes::to_list", [Value::Bytes(b)]) => {
                let list = self.list(b.iter().map(|x| Value::Int((*x).into())).collect())?;
                ret(list, kont)
            }
            ("Bytes::len", [Value::Bytes(b)]) => ret(Value::Int(b.len() as i128), kont),
            // A `u64` is held as its bits in an `i64`.
            ("Bytes::get", [Value::Bytes(b), Value::Int(i)]) => {
                let x = tauto_rt::stdlib::bytes_get(b.clone(), *i as u64);
                let v = self.option(x.map(|x| Value::Int(x.into())))?;
                ret(v, kont)
            }
            ("Bytes::slice", [Value::Bytes(b), Value::Int(s), Value::Int(e)]) => {
                let x = tauto_rt::stdlib::bytes_slice(b.clone(), *s as u64, *e as u64);
                let v = self.option(x.map(Value::Bytes))?;
                ret(v, kont)
            }
            ("Bytes::concat", [Value::Bytes(a), Value::Bytes(b)]) => {
                let v = tauto_rt::stdlib::bytes_concat(a.clone(), b.clone());
                ret(Value::Bytes(v), kont)
            }
            ("Bytes::eq", [Value::Bytes(a), Value::Bytes(b)]) => ret(Value::Bool(a == b), kont),
            ("Bytes::of_text", [Value::Text(t)]) => {
                ret(Value::Bytes(t.as_bytes().to_vec().into()), kont)
            }
            ("Text::of_bytes", [Value::Bytes(b)]) => {
                let t = std::str::from_utf8(b)
                    .ok()
                    .map(|t| Value::Text(Rc::from(t)));
                let v = self.option(t)?;
                ret(v, kont)
            }
            ("Vec::get" | "Slice::get", [Value::Res(r), Value::Int(i)]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-vec-get-takes-a-vec"));
                };
                let item = usize::try_from(*i)
                    .ok()
                    .and_then(|i| items.borrow().get(i).cloned());
                let v = self.option(item)?;
                ret(v, kont)
            }
            ("Vec::get_mut", [Value::Res(r), Value::Int(i)]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-vec-get-mut-takes-a-vec"));
                };
                let at = usize::try_from(*i)
                    .ok()
                    .filter(|i| *i < items.borrow().len());
                let place = at.map(|i| {
                    Value::Ref(Place {
                        root: Root::Elem(r.clone(), i),
                        path: Vec::new(),
                    })
                });
                let v = self.option(place)?;
                ret(v, kont)
            }
            ("Vec::last_mut", [Value::Res(r)]) => {
                let ResKind::Vec(items) = &r.kind else {
                    return runtime(msg!("eval-vec-last-mut-takes-a-vec"));
                };
                let len = items.borrow().len();
                let place = len.checked_sub(1).map(|i| {
                    Value::Ref(Place {
                        root: Root::Elem(r.clone(), i),
                        path: Vec::new(),
                    })
                });
                let v = self.option(place)?;
                ret(v, kont)
            }
            ("HashMap::get" | "HashMap::get_mut", [Value::Res(r), k]) => {
                let ResKind::Map(entries) = &r.kind else {
                    return runtime(msg!("eval-hashmap-get-takes-a-hashmap"));
                };
                let at = entries.borrow().find(k)?;
                let item = at.map(|i| {
                    if name == "HashMap::get_mut" {
                        Value::Ref(Place {
                            root: Root::Elem(r.clone(), i),
                            path: Vec::new(),
                        })
                    } else {
                        entries.borrow()[i].1.clone()
                    }
                });
                let v = self.option(item)?;
                ret(v, kont)
            }
            ("HashMap::index", [Value::Res(r), k]) => {
                let ResKind::Map(entries) = &r.kind else {
                    return runtime(msg!("eval-hashmap-index-takes-a-hashmap"));
                };
                let found = {
                    let entries = entries.borrow();
                    entries.find(k)?.map(|i| entries[i].1.clone())
                };
                match found {
                    Some(v) => ret(v, kont),
                    None => Ok((Ctrl::Perform("missing".into(), Vec::new()), kont)),
                }
            }
            ("HashMap::insert", [Value::Res(r), k, _]) => {
                let ResKind::Map(entries) = &r.kind else {
                    return runtime(msg!("eval-hashmap-insert-takes-a-hashmap"));
                };
                let old = entries.borrow_mut().insert(k.clone(), args[2].clone())?;
                if old.is_none() {
                    self.alloc(2);
                }
                let v = self.option(old)?;
                ret(v, kont)
            }
            ("HashMap::into_vec", [m @ Value::Res(r)]) => {
                let ResKind::Map(entries) = &r.kind else {
                    return runtime(msg!("eval-hashmap-into-vec-takes-a-hashmap"));
                };
                let entries = entries.borrow_mut().take();
                self.consume(m);
                let mut pairs = Vec::new();
                for (k, v) in entries {
                    pairs.push(self.make("Pair::Pair", vec![k, v])?);
                }
                let v = self.resource(ResKind::Vec(RefCell::new(pairs)));
                ret(v, kont)
            }
            ("Text::len", [Value::Text(t)]) => ret(Value::Int(t.len() as i128), kont),
            ("Text::byte", [Value::Text(t), Value::Int(i)]) => {
                let byte = usize::try_from(*i)
                    .ok()
                    .and_then(|i| t.as_bytes().get(i))
                    .map(|b| Value::Int(i128::from(*b)));
                let v = self.option(byte)?;
                ret(v, kont)
            }
            ("Text::slice", [Value::Text(t), Value::Int(start), Value::Int(end)]) => {
                let part = match (usize::try_from(*start), usize::try_from(*end)) {
                    (Ok(s), Ok(e)) => t.get(s..e).map(|p| Value::Text(Rc::from(p))),
                    _ => None,
                };
                let v = self.option(part)?;
                ret(v, kont)
            }
            ("Text::compare", [Value::Text(a), Value::Text(b)]) => {
                ret(Value::Int(a.as_bytes().cmp(b.as_bytes()) as i128), kont)
            }
            ("Text::of_code_point", [Value::Int(c)]) => {
                let ch = u32::try_from(*c).ok().and_then(char::from_u32);
                let v = self.option(ch.map(|c| Value::Text(Rc::from(c.to_string().as_str()))))?;
                ret(v, kont)
            }
            ("Text::of_utf8", [l]) => {
                let mut bytes = Vec::new();
                for b in self.list_items(l)? {
                    match b {
                        Value::Int(b) => match u8::try_from(b) {
                            Ok(b) => bytes.push(b),
                            Err(_) => return runtime(msg!("eval-text-of-utf8-takes-bytes")),
                        },
                        _ => return runtime(msg!("eval-text-of-utf8-takes-bytes")),
                    }
                }
                let text = String::from_utf8(bytes).ok();
                let v = self.option(text.map(|t| Value::Text(Rc::from(t.as_str()))))?;
                ret(v, kont)
            }
            (
                "U32::and" | "U32::or" | "U32::xor" | "U32::shl" | "U32::shr" | "U32::rotl" | "U32::rotr"
                | "U64::and" | "U64::or" | "U64::xor" | "U64::shl" | "U64::shr" | "U64::rotl"
                | "U64::rotr",
                [Value::Int(a), Value::Int(b)],
            ) => {
                // The evaluator holds a `u64` in an `i64`: a result past
                // `i64::MAX` is too large here, as for the other `u64`s.
                let (a, b) = (*a as u64, *b as u64);
                let wide = name.starts_with("u64");
                let bits = if wide { 64 } else { 32 };
                let mask = if wide { u64::MAX } else { u32::MAX as u64 };
                let s = (b % bits) as u32;
                let out = match name.split_once('_').map_or("", |(_, op)| op) {
                    "and" => a & b,
                    "or" => a | b,
                    "xor" => a ^ b,
                    "shl" => a.wrapping_shl(s) & mask,
                    "shr" => a >> s,
                    "rotl" if wide => a.rotate_left(s),
                    "rotr" if wide => a.rotate_right(s),
                    "rotl" => (a as u32).rotate_left(s) as u64,
                    _ => (a as u32).rotate_right(s) as u64,
                };
                ret(Value::Int(i128::from(out)), kont)
            }
            // The evaluator does not run these in constant time.
            ("secret", [v]) => ret(secret(v.clone()), kont),
            ("expose", [s]) => ret(revealed(s)?.clone(), kont),
            // A secret byte string's length and index are public.
            ("Ct::bytes_len", [s]) => match revealed(s)? {
                Value::Bytes(b) => ret(Value::Int(b.len() as i128), kont),
                _ => runtime(msg!("eval-ct-bytes-len-takes-secret-bytes")),
            },
            ("Ct::bytes_get", [s, Value::Int(i)]) => match revealed(s)? {
                Value::Bytes(b) => {
                    let x = tauto_rt::stdlib::bytes_get(b.clone(), *i as u64);
                    let v = self.option(x.map(|x| secret(Value::Int(x.into()))))?;
                    ret(v, kont)
                }
                _ => runtime(msg!("eval-ct-bytes-get-takes-secret-bytes")),
            },
            (n, args) if n.starts_with("Ct::") => {
                let contents = args
                    .iter()
                    .map(|a| revealed(a).cloned())
                    .collect::<Result<Vec<_>, _>>()?;
                let out = secret_op(n, &contents)?;
                ret(secret(out), kont)
            }
            (name, args) if name.starts_with("Float32::") => {
                let v = self.float32_builtin(name, args)?;
                ret(v, kont)
            }
            (name, args) if name.starts_with("Float::") || name.ends_with("of_float") => {
                let v = self.float_builtin(name, args)?;
                ret(v, kont)
            }
            ("Text::of_i64" | "Text::of_u64", [Value::Int(n)]) => {
                ret(Value::Text(Rc::from(n.to_string().as_str())), kont)
            }
            (
                "I64::of_i32" | "I32::of_i64" | "I64::of_u64" | "U64::of_i64" | "U64::of_u32"
                | "U32::of_u64" | "U64::of_u8" | "U8::of_u64",
                [Value::Int(n)],
            ) => {
                // The result's width is the name's first part.
                let width = match name.split('_').next() {
                    Some("i32") => Width::W32,
                    Some("i64") => Width::W64,
                    Some("u8") => Width::U8,
                    Some("u32") => Width::U32,
                    _ => Width::U64,
                };
                if !width.fits(*n) {
                    return Err(overflow());
                }
                ret(Value::Int(*n), kont)
            }
            ("Os::args", []) => {
                let args = self
                    .args
                    .iter()
                    .map(|a| Value::Text(Rc::from(a.as_str())))
                    .collect();
                let list = self.list(args)?;
                ret(list, kont)
            }
            ("Syn::parse", [Value::Text(syntax), Value::Text(sha), Value::Text(text)]) => {
                let result = self.syn_parse(syntax, sha, text)?;
                ret(result, kont)
            }
            ("Os::read_file", [Value::Text(path)]) => {
                let result = match std::fs::read_to_string(&**path) {
                    Ok(text) => {
                        self.make("Result::Ok", vec![Value::Text(Rc::from(text.as_str()))])?
                    }
                    Err(e) => self.make(
                        "Result::Err",
                        vec![Value::Text(Rc::from(e.to_string().as_str()))],
                    )?,
                };
                ret(result, kont)
            }
            ("Os::write_file", [Value::Text(path), Value::Text(contents)]) => {
                let result = match std::fs::write(&**path, contents.as_bytes()) {
                    Ok(()) => self.make("Result::Ok", vec![Value::Unit])?,
                    Err(e) => self.make(
                        "Result::Err",
                        vec![Value::Text(Rc::from(e.to_string().as_str()))],
                    )?,
                };
                ret(result, kont)
            }
            ("Os::read_bytes", [Value::Text(path)]) => {
                let result = match std::fs::read(&**path) {
                    Ok(bytes) => self.make("Result::Ok", vec![Value::Bytes(bytes.into())])?,
                    Err(e) => self.make(
                        "Result::Err",
                        vec![Value::Text(Rc::from(e.to_string().as_str()))],
                    )?,
                };
                ret(result, kont)
            }
            ("Os::create_dir", [Value::Text(path)]) => {
                let result = match std::fs::create_dir_all(&**path) {
                    Ok(()) => self.make("Result::Ok", vec![Value::Unit])?,
                    Err(e) => self.make(
                        "Result::Err",
                        vec![Value::Text(Rc::from(e.to_string().as_str()))],
                    )?,
                };
                ret(result, kont)
            }
            ("Os::list_dir", [Value::Text(path)]) => {
                let result = tauto_rt::stdlib::os_list_dir_vec(tauto_rt::Text::from(&**path));
                let v = self.text_list_result(result)?;
                ret(v, kont)
            }
            ("Os::remove", [Value::Text(path)]) => {
                let result = match tauto_rt::host::Host::remove(&tauto_rt::host::System, path) {
                    Ok(()) => self.make("Result::Ok", vec![Value::Unit])?,
                    Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(e.as_str()))])?,
                };
                ret(result, kont)
            }
            // The run may read and write under the directory, as under one
            // the user picked (`Permissions::choose`).
            ("Os::temp_dir", []) => {
                let made =
                    tauto_rt::host::Host::temp_dir(&tauto_rt::host::System).and_then(|dir| {
                        self.permissions.choose("read", &dir, true);
                        self.permissions
                            .choose("write", &dir, true)
                            .ok_or_else(|| format!("{dir}: cannot be resolved"))
                    });
                let result = match made {
                    Ok(dir) => {
                        self.make("Result::Ok", vec![Value::Text(Rc::from(dir.as_str()))])?
                    }
                    Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(e.as_str()))])?,
                };
                ret(result, kont)
            }
            (
                "Os::run",
                [
                    Value::Text(program),
                    args,
                    Value::Text(dir),
                    env,
                    Value::Bytes(stdin),
                ],
            ) => {
                let args = self.text_items(args, "Os::run")?;
                let env = self.text_items(env, "Os::run")?;
                let result = tauto_rt::stdlib::os_run_vec(
                    tauto_rt::Text::from(&**program),
                    args,
                    tauto_rt::Text::from(&**dir),
                    env,
                    stdin.clone(),
                );
                let v = self.text_list_bytes_result(result)?;
                ret(v, kont)
            }
            ("Os::write_bytes", [Value::Text(path), Value::Bytes(bytes)]) => {
                let result = match std::fs::write(&**path, &**bytes) {
                    Ok(()) => self.make("Result::Ok", vec![Value::Unit])?,
                    Err(e) => self.make(
                        "Result::Err",
                        vec![Value::Text(Rc::from(e.to_string().as_str()))],
                    )?,
                };
                ret(result, kont)
            }
            ("Os::read_line", []) => {
                let line = tauto_rt::stdlib::os_read_line().map(|t| Value::Text(Rc::from(&*t)));
                let v = self.option(line)?;
                ret(v, kont)
            }
            ("Os::env", [Value::Text(name)]) => {
                let v = std::env::var(&**name)
                    .ok()
                    .map(|t| Value::Text(Rc::from(t.as_str())));
                let v = self.option(v)?;
                ret(v, kont)
            }
            ("Os::wall_ms", []) => ret(Value::Int(i128::from(tauto_rt::stdlib::os_wall_ms())), kont),
            ("Os::monotonic_ns", []) => ret(
                Value::Int(i128::from(tauto_rt::stdlib::os_monotonic_ns())),
                kont,
            ),
            // A `Pending` is its value (`Pending::ready`): what takes a while is
            // done here, before the answer.
            ("Os::sleep_pending", [Value::Int(ms)]) => {
                std::thread::sleep(std::time::Duration::from_millis((*ms).max(0) as u64));
                ret(Value::Unit, kont)
            }
            ("Os::offload", [f]) => self.apply(f.clone(), Vec::new(), kont),
            // A `u64` is held as its bits in an `i64`, as the literals are.
            ("Os::secure_random", [Value::Int(n)]) => {
                let result = match u64::try_from(*n)
                    .map_err(|_| tauto_rt::Text::from("a negative byte count"))
                    .and_then(|n| {
                        let n = usize::try_from(n)
                            .map_err(|_| tauto_rt::Text::from("too many random bytes asked for"))?;
                        tauto_rt::host::get()
                            .secure_random(n)
                            .map_err(tauto_rt::Text::from)
                    }) {
                    Ok(bytes) => self.make("Result::Ok", vec![Value::Bytes(bytes.into())])?,
                    Err(e) => self.make(
                        "Result::Err",
                        vec![Value::Text(Rc::from(e.to_string().as_str()))],
                    )?,
                };
                ret(result, kont)
            }
            ("Os::random", []) => ret(Value::Int(tauto_rt::stdlib::os_random() as i128), kont),
            ("Os::status", [Value::Text(t)]) => ret(Value::Int(t.parse().unwrap_or(0)), kont),
            ("Os::check", [Value::Text(kind), Value::Text(target)]) => {
                let checked = self
                    .permissions
                    .check_or_ask(kind, target)
                    .map(|t| Value::Text(Rc::from(t.as_str())));
                let v = self.option(checked)?;
                ret(v, kont)
            }
            ("Os::resolve", [Value::Text(url)]) => {
                let result = tauto_rt::stdlib::os_resolve_vec(tauto_rt::Text::from(&**url));
                let v = self.text_list_result(result)?;
                ret(v, kont)
            }
            ("Os::tcp_listen", [Value::Text(address)]) => {
                let result = tauto_rt::tcp::os_tcp_listen_vec(tauto_rt::Text::from(&**address));
                let v = self.text_list_result(result)?;
                ret(v, kont)
            }
            ("Os::tcp_accept", [Value::Int(listener), deadline]) => {
                let deadline = self.deadline(deadline)?;
                let result = tauto_rt::tcp::os_tcp_accept_vec(*listener as u64, deadline);
                // Stopped while waiting: the program does not see the wait fail.
                if self.cancelled() {
                    return Err(RunError::Interrupted);
                }
                let v = self.timed_text_list(result)?;
                ret(v, kont)
            }
            ("Os::tcp_connect", [Value::Text(address), deadline]) => {
                let deadline = self.deadline(deadline)?;
                let result =
                    tauto_rt::tcp::os_tcp_connect_vec(tauto_rt::Text::from(&**address), deadline);
                // Stopped while waiting: the program does not see the wait fail.
                if self.cancelled() {
                    return Err(RunError::Interrupted);
                }
                let v = self.timed_text_list(result)?;
                ret(v, kont)
            }
            ("Os::tcp_read", [Value::Int(stream), Value::Int(max), deadline]) => {
                let deadline = self.deadline(deadline)?;
                let read = tauto_rt::tcp::os_tcp_read(*stream as u64, *max as u64, deadline);
                if self.cancelled() {
                    return Err(RunError::Interrupted);
                }
                let v = match read {
                    Ok(bytes) => {
                        let bytes = self.option(bytes.map(Value::Bytes))?;
                        self.make("Result::Ok", vec![bytes])?
                    }
                    Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(&*e))])?,
                };
                ret(v, kont)
            }
            ("Os::tcp_write", [Value::Int(stream), Value::Bytes(bytes), deadline]) => {
                let deadline = self.deadline(deadline)?;
                let wrote = tauto_rt::tcp::os_tcp_write(*stream as u64, bytes.clone(), deadline);
                if self.cancelled() {
                    return Err(RunError::Interrupted);
                }
                let v = match wrote {
                    Ok(done) => {
                        let done = self.option(done.map(|()| Value::Unit))?;
                        self.make("Result::Ok", vec![done])?
                    }
                    Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(&*e))])?,
                };
                ret(v, kont)
            }
            ("Os::tcp_shutdown", [Value::Int(stream), Value::Int(how)]) => {
                let v = match tauto_rt::tcp::os_tcp_shutdown(*stream as u64, *how as u64) {
                    Ok(()) => self.make("Result::Ok", vec![Value::Unit])?,
                    Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(&*e))])?,
                };
                ret(v, kont)
            }
            ("Os::tcp_close", [Value::Int(stream)]) => {
                tauto_rt::tcp::os_tcp_close(*stream as u64);
                ret(Value::Unit, kont)
            }
            ("Os::tcp_unlisten", [Value::Int(listener)]) => {
                tauto_rt::tcp::os_tcp_unlisten(*listener as u64);
                ret(Value::Unit, kont)
            }
            (
                "Os::tls_accept",
                [
                    Value::Int(stream),
                    names,
                    pems,
                    alpn,
                    Value::Bytes(roots),
                    deadline,
                ],
            ) => {
                let names = self.text_items(names, name)?;
                let pems = self.bytes_items(pems, name)?;
                let alpn = self.text_items(alpn, name)?;
                let deadline = self.deadline(deadline)?;
                let result = tauto_rt::tls_host::os_tls_accept_vec(
                    *stream as u64,
                    names,
                    pems,
                    alpn,
                    roots.clone(),
                    deadline,
                );
                if self.cancelled() {
                    return Err(RunError::Interrupted);
                }
                let v = self.tls_session(result)?;
                ret(v, kont)
            }
            (
                "Os::tls_connect",
                [
                    Value::Int(stream),
                    Value::Text(server),
                    Value::Int(roots),
                    pems,
                    alpn,
                    deadline,
                ],
            ) => {
                let pems = self.bytes_items(pems, name)?;
                let alpn = self.text_items(alpn, name)?;
                let deadline = self.deadline(deadline)?;
                let result = tauto_rt::tls_host::os_tls_connect_vec(
                    *stream as u64,
                    tauto_rt::Text::from(&**server),
                    *roots as u64,
                    pems,
                    alpn,
                    deadline,
                );
                if self.cancelled() {
                    return Err(RunError::Interrupted);
                }
                let v = self.tls_session(result)?;
                ret(v, kont)
            }
            ("Os::tls_read", [Value::Int(stream), Value::Int(max), deadline]) => {
                let deadline = self.deadline(deadline)?;
                let read = tauto_rt::tls_host::os_tls_read(*stream as u64, *max as u64, deadline);
                if self.cancelled() {
                    return Err(RunError::Interrupted);
                }
                let v = match read {
                    Ok(bytes) => {
                        let bytes = self.option(bytes.map(Value::Bytes))?;
                        self.make("Result::Ok", vec![bytes])?
                    }
                    Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(&*e))])?,
                };
                ret(v, kont)
            }
            ("Os::tls_write", [Value::Int(stream), Value::Bytes(bytes), deadline]) => {
                let deadline = self.deadline(deadline)?;
                let wrote =
                    tauto_rt::tls_host::os_tls_write(*stream as u64, bytes.clone(), deadline);
                if self.cancelled() {
                    return Err(RunError::Interrupted);
                }
                let v = match wrote {
                    Ok(done) => {
                        let done = self.option(done.map(|()| Value::Unit))?;
                        self.make("Result::Ok", vec![done])?
                    }
                    Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(&*e))])?,
                };
                ret(v, kont)
            }
            ("Os::tls_shutdown", [Value::Int(stream), Value::Int(how)]) => {
                let v = match tauto_rt::tls_host::os_tls_shutdown(*stream as u64, *how as u64) {
                    Ok(()) => self.make("Result::Ok", vec![Value::Unit])?,
                    Err(e) => self.make("Result::Err", vec![Value::Text(Rc::from(&*e))])?,
                };
                ret(v, kont)
            }
            ("Os::tls_close", [Value::Int(stream)]) => {
                tauto_rt::tls_host::os_tls_close(*stream as u64);
                ret(Value::Unit, kont)
            }
            (
                "Os::fetch",
                [
                    Value::Text(method),
                    Value::Text(url),
                    Value::Text(address),
                    headers,
                    Value::Bytes(body),
                ],
            ) => {
                let mut flat = Vec::new();
                for h in self.list_items(headers)? {
                    match h {
                        Value::Text(t) => flat.push(tauto_rt::Text::from(&*t)),
                        _ => return runtime(msg!("eval-a-header-is-text")),
                    }
                }
                let result = tauto_rt::stdlib::os_fetch_vec(
                    tauto_rt::Text::from(&**method),
                    tauto_rt::Text::from(&**url),
                    tauto_rt::Text::from(&**address),
                    flat,
                    body.clone(),
                );
                let v = self.text_list_bytes_result(result)?;
                ret(v, kont)
            }
            ("Os::stop", [Value::Text(t)]) => runtime(t.to_string()),
            ("Os::print", [Value::Text(t)]) if self.streaming => {
                use std::io::Write;
                let mut out = std::io::stdout().lock();
                let _ = out.write_all(t.as_bytes()).and_then(|()| out.flush());
                ret(Value::Unit, kont)
            }
            ("Os::eprint", [Value::Text(t)]) if self.streaming => {
                eprint!("{t}");
                ret(Value::Unit, kont)
            }
            ("Os::print", [Value::Text(t)]) => {
                self.stdout.push_str(t);
                ret(Value::Unit, kont)
            }
            ("Os::eprint", [Value::Text(t)]) => {
                self.stderr.push_str(t);
                ret(Value::Unit, kont)
            }
            ("Os::exit", [Value::Int(code)]) => {
                if !(0..=255).contains(code) {
                    return Err(overflow());
                }
                self.exit = Some(*code as i32);
                Err(RunError::Exit)
            }
            ("replace", [_, _]) => match &args[0] {
                Value::Ref(p) => {
                    let old = p.get();
                    p.set(args[1].clone());
                    ret(old, kont)
                }
                _ => runtime(msg!("eval-replace-takes-mut-x")),
            },
            _ => {
                let shown: Vec<String> = plain.iter().map(|a| a.to_string()).collect();
                runtime(msg!(
                    "eval-cannot-take",
                    name = name.to_string(),
                    join = shown.join(", ").to_string()
                ))
            }
        }
    }

    /// `clone(&x)`: a copy of everything the value holds, each affine
    /// part with a token of its own.
    fn deep_clone(&mut self, v: &Value<'a>) -> Result<Value<'a>, RunError> {
        Ok(match deref(v) {
            Value::Data(d) => {
                let mut fields = Vec::new();
                for f in &d.fields {
                    fields.push(self.deep_clone(f)?);
                }
                let token = match d.token {
                    Some(t) => self.token(t.linear, &d.shape.ty),
                    None => None,
                };
                data(Data {
                    shape: d.shape.clone(),
                    fields,
                    token,
                    owns: false,
                })
            }
            Value::Res(r) if matches!(&r.kind, ResKind::Cell(..) | ResKind::Weak(_)) => {
                Value::Res(r.clone())
            }
            Value::Res(r) => {
                let kind = match &r.kind {
                    ResKind::Buf(b) => ResKind::Buf(RefCell::new(b.borrow().clone())),
                    ResKind::Vec(items) => {
                        let items: Vec<Value<'a>> = items.borrow().clone();
                        let mut copies = Vec::new();
                        for i in &items {
                            copies.push(self.deep_clone(i)?);
                        }
                        ResKind::Vec(RefCell::new(copies))
                    }
                    ResKind::Map(entries) => {
                        let entries: Vec<(Value<'a>, Value<'a>)> = entries.borrow().to_vec();
                        let mut copies = Vec::new();
                        for (k, v) in &entries {
                            copies.push((self.deep_clone(k)?, self.deep_clone(v)?));
                        }
                        ResKind::Map(RefCell::new(Entries::of(copies)))
                    }
                    ResKind::Cell(..) | ResKind::Weak(_) => unreachable!(),
                };
                self.resource(kind)
            }
            other => other,
        })
    }

    /// Finds the nearest handler with an arm for `effect`, sets aside the
    /// frames up to it as the continuation, and runs the arm outside it.
    fn perform(
        &mut self,
        effect: &str,
        args: Vec<Value<'a>>,
        kont: Kont<'a>,
    ) -> Result<(Ctrl<'a>, Kont<'a>), RunError> {
        let mut captured: Vec<Frame<'a>> = Vec::new();
        let start = kont.clone();
        let mut at = kont;
        while let Some(node) = at {
            captured.push(node.frame.clone());
            if let Frame::Handle { handlers, env } = &node.frame {
                for h in handlers.iter() {
                    let Handler::Operation {
                        effect: name,
                        patterns,
                        cont,
                        guard,
                        body,
                        ..
                    } = h
                    else {
                        continue;
                    };
                    if name != effect || patterns.len() != args.len() {
                        continue;
                    }
                    let rest = Captured(Rc::new(captured.clone()));
                    let args: Vec<Value<'a>> = args
                        .iter()
                        .map(|a| match a {
                            Value::Stopped(stopped) => Value::Info(Rc::new(Info {
                                stopped: stopped.clone(),
                                rest: rest.clone(),
                            })),
                            other => other.clone(),
                        })
                        .collect();
                    let mut arm_env = env.clone();
                    let mut fits = true;
                    for (p, v) in patterns.iter().zip(&args) {
                        match self.bind_pattern(p, v, arm_env.clone(), site(body)) {
                            Some(e) => arm_env = e,
                            None => {
                                fits = false;
                                break;
                            }
                        }
                    }
                    if !fits {
                        continue;
                    }
                    if guard.is_some() {
                        return runtime(msg!("eval-guards-on-handler-arms-are-not"));
                    }
                    let quant = self
                        .report
                        .quants
                        .get(effect)
                        .copied()
                        .unwrap_or(Quant::AtMostOne);
                    if self.check && quant == Quant::Many {
                        self.no_tokens_in(&captured, env, effect)?;
                    }
                    // A `resume 0` arm never runs `k`, so what the continuation
                    // holds is left here, as a `return` leaves it: the
                    // innermost frame first, its temporaries then its scope,
                    // before the arm runs.
                    if quant == Quant::Zero {
                        for frame in &captured {
                            for v in frame.held().1.into_iter().rev() {
                                self.drop_value(v)?;
                            }
                            self.drop_frame(frame)?;
                        }
                    }
                    if let Some(k) = cont {
                        let once =
                            (self.check && quant != Quant::Many).then(|| Rc::new(Cell::new(false)));
                        arm_env = bind(&arm_env, k, Slot::Val(Value::Cont(rest, once)));
                    }
                    return Ok((Ctrl::Eval(body, arm_env), node.next.clone()));
                }
            }
            at = node.next.clone();
        }
        if self.host.is_some() {
            if let ("macro_error" | "macro_warn", [diag]) = (effect, args.as_slice()) {
                let (message, at, code) = self.diag_parts(diag);
                if effect == "macro_error" {
                    return Err(RunError::MacroError(message, at, code));
                }
                if let Some(h) = &mut self.host {
                    h.warnings.push((message, at, code));
                }
                return Ok((Ctrl::Ret(Value::Unit), start));
            }
            return runtime(tauto_rt::messages::nothing_handles(&effect));
        }
        // The host answers `wait`: it runs each spawned task to its end at its
        // `spawn`, so a signal not raised is one no task can raise.
        if let ("wait", [Value::Res(r)]) = (effect, args.as_slice())
            && let ResKind::Cell(c, "Signal") = &r.kind
        {
            if !matches!(*c.borrow(), Value::Bool(true)) {
                return runtime(msg!(
                    "eval-deadlock",
                    deadlock = tauto_rt::messages::DEADLOCK.to_string()
                ));
            }
            return Ok((Ctrl::Ret(Value::Unit), start));
        }
        // The host answers `spawn`: it runs the body to its end at the
        // `spawn`, apart from the handlers around it, and gives the task.
        if let ("spawn", [body]) = (effect, args.as_slice()) {
            let body = body.clone();
            let (ctrl, kont) = self.apply(body, Vec::new(), None)?;
            let v = self.run(ctrl, kont)?;
            let ctor = self.ctor_key("Task", None)?;
            return Ok((Ctrl::Ret(self.make(ctor, vec![v])?), start));
        }
        // The host answers `show`.
        if let ("show", [Value::Text(name), value]) = (effect, args.as_slice()) {
            if self.streaming {
                println!("{name} = {value}");
                return Ok((Ctrl::Ret(Value::Unit), start));
            }
            self.outputs.push((name.to_string(), value.to_string()));
            return Ok((Ctrl::Ret(Value::Unit), start));
        }
        // The host runs a test's body to its end; its error fails only that test.
        if let ("test", [Value::Text(name), body]) = (effect, args.as_slice()) {
            let (name, body) = (name.to_string(), body.clone());
            self.in_test += 1;
            let result = self
                .apply(body, Vec::new(), None)
                .and_then(|(ctrl, kont)| self.run(ctrl, kont));
            self.in_test -= 1;
            let error = match result {
                Ok(_) => None,
                Err(RunError::Exit) => return Err(RunError::Exit),
                Err(e) => Some(e.to_string()),
            };
            self.tests.push((name, error));
            return Ok((Ctrl::Ret(Value::Unit), start));
        }
        if let ("fail" | "fail@Text", [Value::Text(why)]) = (effect, args.as_slice()) {
            // The host answers a test's `fail`: the test fails with its message.
            if self.in_test > 0 {
                return runtime(why.to_string());
            }
            return runtime(msg!(
                "eval-nothing-handles-because",
                unhandled = tauto_rt::messages::nothing_handles(&effect).to_string(),
                why = why.to_string()
            ));
        }
        runtime(tauto_rt::messages::nothing_handles(&effect))
    }

    /// A continuation an `ω` effect may copy holds no token:
    /// nothing its frames own, down to the handler's own environment.
    fn no_tokens_in(
        &self,
        frames: &[Frame<'a>],
        outside: &Env<'a>,
        effect: &str,
    ) -> Result<(), RunError> {
        let mut stop = HashSet::new();
        let mut at = outside;
        while let Some(node) = at {
            stop.insert(node_id(node));
            at = &node.next;
        }
        for frame in frames {
            let (env, values) = frame.held();
            for v in values {
                if let Some(ty) = owner(v) {
                    return ownership(msg!(
                        "eval-may-resume-more-than-once-and",
                        effect = effect.to_string(),
                        ty = ty.to_string()
                    ));
                }
            }
            let mut at = env;
            while let Some(Some(node)) = at {
                if stop.contains(&node_id(node)) {
                    break;
                }
                if !self.moved.contains(&node_id(node)) {
                    let v = match &node.slot {
                        Slot::Val(v) => Some(v.clone()),
                        Slot::Cell(c) => Some(c.borrow().clone()),
                        Slot::Borrow(_) => None,
                    };
                    if let Some(ty) = v.as_ref().and_then(owner) {
                        return ownership(msg!(
                            "eval-may-resume-more-than-once-and-2",
                            effect = effect.to_string(),
                            node = node.name.to_string(),
                            ty = ty.to_string()
                        ));
                    }
                }
                at = Some(&node.next);
            }
        }
        Ok(())
    }
}

/// A name bound to a borrow: `match x` over it borrows too.
fn borrowed_name(t: &SurfaceTerm, env: &Env<'_>) -> bool {
    match &*t.kind {
        TermKind::Var(n) => matches!(lookup(env, n), Some(Slot::Borrow(_))),
        TermKind::Field { base, .. } => borrowed_name(base, env),
        _ => false,
    }
}

fn field_of<'a>(v: &Value<'a>, name: &str) -> Result<Value<'a>, RunError> {
    match deref(v) {
        Value::Data(d) => match d
            .shape
            .names
            .iter()
            .position(|n| n.as_deref() == Some(name))
        {
            Some(i) => Ok(d.fields[i].clone()),
            None => runtime(msg!(
                "eval-has-no-field",
                ty = d.shape.ty.to_string(),
                name = name.to_string()
            )),
        },
        other => runtime(msg!(
            "eval-has-no-field-2",
            other = other.to_string(),
            name = name.to_string()
        )),
    }
}

/// A value of a declared type, with `owns` computed from what it holds.
fn data(mut d: Data<'_>) -> Value<'_> {
    d.owns = d.token.is_some() || d.fields.iter().any(may_own);
    Value::Data(Rc::new(d))
}

/// Whether a value may hold a token: false only for values the check's
/// walks can skip whole.
fn may_own(v: &Value<'_>) -> bool {
    match v {
        Value::Data(d) => d.owns,
        Value::Res(_) => true,
        _ => false,
    }
}

fn token_of(v: &Value<'_>) -> Option<Token> {
    match v {
        Value::Data(d) => d.token,
        Value::Res(r) => r.token,
        _ => None,
    }
}

/// Whether a value holds a token, itself or in what it holds.
fn holds_token(v: &Value<'_>) -> bool {
    owner(v).is_some()
}

/// The type of an affine or linear value a value holds.
fn owner(v: &Value<'_>) -> Option<String> {
    match v {
        Value::Data(d) if d.token.is_some() => Some(d.shape.ty.clone()),
        Value::Data(d) if !d.owns => None,
        Value::Data(d) => d.fields.iter().find_map(owner),
        Value::Closure(c) => c.owns.iter().find_map(|name| match lookup(&c.env, name) {
            Some(Slot::Val(v)) => owner(&v),
            _ => None,
        }),
        Value::Res(r) if r.token.is_some() => Some(match &r.kind {
            ResKind::Buf(_) => "Buf".into(),
            ResKind::Vec(_) => "Vec".into(),
            ResKind::Map(_) => "HashMap".into(),
            ResKind::Cell(_, name) => (*name).into(),
            ResKind::Weak(_) => "Weak".into(),
        }),
        _ => None,
    }
}

/// An operator; integer arithmetic overflows at `width`, never wraps.
fn operate<'a>(op: &str, width: Width, args: &[Value<'a>]) -> Result<Value<'a>, RunError> {
    use Value::{Bool, Int};
    if let [Value::Float(_), ..] = args {
        return operate_float(op, args);
    }
    if let [Value::Float32(_), ..] = args {
        return operate_float32(op, args);
    }
    if width == Width::Nat || args.iter().any(|a| matches!(a, Value::Nat(_))) {
        return operate_nat(op, args);
    }
    let int = |r: Option<i128>| match r {
        Some(n) if width.fits(n) => Ok(Int(n)),
        _ => Err(overflow()),
    };
    Ok(match (op, args) {
        ("-", [Int(a)]) => int(a.checked_neg())?,
        ("+", [Int(a)]) => Int(*a),
        ("+", [Int(a), Int(b)]) => int(a.checked_add(*b))?,
        ("-", [Int(a), Int(b)]) => int(a.checked_sub(*b))?,
        ("*", [Int(a), Int(b)]) => int(a.checked_mul(*b))?,
        ("==", [a, b]) => Bool(equal(a, b)?),
        ("!=", [a, b]) => Bool(!equal(a, b)?),
        ("<", [Int(a), Int(b)]) => Bool(a < b),
        (">", [Int(a), Int(b)]) => Bool(a > b),
        ("<=", [Int(a), Int(b)]) => Bool(a <= b),
        (">=", [Int(a), Int(b)]) => Bool(a >= b),
        _ => {
            let shown: Vec<String> = args.iter().map(|a| a.to_string()).collect();
            return runtime(msg!(
                "eval-cannot-apply-to",
                op = op.to_string(),
                join = shown.join(", ").to_string()
            ));
        }
    })
}

/// A number as a `nat`; `None` for one below zero or not a number.
fn as_nat(v: &Value<'_>) -> Option<Nat> {
    match deref(v) {
        Value::Nat(n) => Some(n),
        Value::Int(n) => match u64::try_from(n) {
            Ok(n) => Some(Nat::from_u64(n)),
            Err(_) if n > 0 => Nat::parse(&n.to_string()),
            Err(_) => None,
        },
        _ => None,
    }
}

/// `nat`'s operators: it does not overflow, and a difference below zero is
/// the run-time error of an overflow.
fn operate_nat<'a>(op: &str, args: &[Value<'a>]) -> Result<Value<'a>, RunError> {
    use Value::Bool;
    let ns: Vec<Nat> = match args.iter().map(as_nat).collect::<Option<Vec<_>>>() {
        Some(ns) => ns,
        None if matches!(op, "==" | "!=") => {
            let same = equal(&args[0], &args[1])?;
            return Ok(Bool(if op == "==" { same } else { !same }));
        }
        None => return Err(overflow()),
    };
    Ok(match (op, ns.as_slice()) {
        ("+", [a]) => Value::Nat(a.clone()),
        ("-", [a]) => Value::Nat(Nat::zero().sub(a).ok_or_else(overflow)?),
        ("+", [a, b]) => Value::Nat(a.add(b)),
        ("-", [a, b]) => Value::Nat(a.sub(b).ok_or_else(overflow)?),
        ("*", [a, b]) => Value::Nat(a.mul(b)),
        ("==", [a, b]) => Bool(a == b),
        ("!=", [a, b]) => Bool(a != b),
        ("<", [a, b]) => Bool(a < b),
        (">", [a, b]) => Bool(a > b),
        ("<=", [a, b]) => Bool(a <= b),
        (">=", [a, b]) => Bool(a >= b),
        _ => return runtime(msg!("eval-cannot-apply-to-nat", op = op.to_string())),
    })
}

/// `Float`'s operators: IEEE 754's, except that `/` by zero is the run-time
/// error of a division by zero.
fn operate_float<'a>(op: &str, args: &[Value<'a>]) -> Result<Value<'a>, RunError> {
    use Value::{Bool, Float};
    Ok(match (op, args) {
        ("-", [Float(a)]) => Float(-a),
        ("+", [Float(a)]) => Float(*a),
        ("+", [Float(a), Float(b)]) => Float(a + b),
        ("-", [Float(a), Float(b)]) => Float(a - b),
        ("*", [Float(a), Float(b)]) => Float(a * b),
        ("/", [Float(a), Float(b)]) => {
            Float(tauto_rt::float::div(*a, *b).ok_or_else(division_by_zero)?)
        }
        ("==", [Float(a), Float(b)]) => Bool(a == b),
        ("!=", [Float(a), Float(b)]) => Bool(a != b),
        ("<", [Float(a), Float(b)]) => Bool(a < b),
        (">", [Float(a), Float(b)]) => Bool(a > b),
        ("<=", [Float(a), Float(b)]) => Bool(a <= b),
        (">=", [Float(a), Float(b)]) => Bool(a >= b),
        _ => return runtime(msg!("eval-cannot-apply-to-float", op = op.to_string())),
    })
}

/// `Float32`'s operators, as `Float`'s.
fn operate_float32<'a>(op: &str, args: &[Value<'a>]) -> Result<Value<'a>, RunError> {
    use Value::{Bool, Float32};
    Ok(match (op, args) {
        ("-", [Float32(a)]) => Float32(-a),
        ("+", [Float32(a)]) => Float32(*a),
        ("+", [Float32(a), Float32(b)]) => Float32(a + b),
        ("-", [Float32(a), Float32(b)]) => Float32(a - b),
        ("*", [Float32(a), Float32(b)]) => Float32(a * b),
        ("/", [Float32(a), Float32(b)]) => {
            Float32(tauto_rt::float::div32(*a, *b).ok_or_else(division_by_zero)?)
        }
        ("==", [Float32(a), Float32(b)]) => Bool(a == b),
        ("!=", [Float32(a), Float32(b)]) => Bool(a != b),
        ("<", [Float32(a), Float32(b)]) => Bool(a < b),
        (">", [Float32(a), Float32(b)]) => Bool(a > b),
        ("<=", [Float32(a), Float32(b)]) => Bool(a <= b),
        (">=", [Float32(a), Float32(b)]) => Bool(a >= b),
        _ => return runtime(msg!("eval-cannot-apply-to-float32", op = op.to_string())),
    })
}

fn division_by_zero() -> RunError {
    RunError::Runtime(tauto_rt::messages::DIVISION_BY_ZERO.into())
}

fn overflow() -> RunError {
    RunError::Runtime(tauto_rt::messages::TOO_LARGE.into())
}

/// A hash of a `HashMap` key that agrees with `equal`: values it calls
/// equal hash the same. Values `equal` cannot compare share one bucket, so a
/// lookup among them still fails as `equal` does.
fn key_hash(v: &Value<'_>) -> u64 {
    use std::hash::{Hash, Hasher};
    fn feed(v: &Value<'_>, h: &mut std::collections::hash_map::DefaultHasher) {
        match deref(v) {
            // An `Int` and a `Nat` of the same number are equal.
            v @ (Value::Int(_) | Value::Nat(_)) => match as_nat(&v) {
                Some(n) => (0u8, n).hash(h),
                None => {
                    1u8.hash(h);
                    if let Value::Int(i) = v {
                        i.hash(h);
                    }
                }
            },
            Value::Bool(b) => (2u8, b).hash(h),
            Value::Text(t) => (3u8, &*t).hash(h),
            Value::Unit => 4u8.hash(h),
            Value::Data(d) => {
                (5u8, &d.shape.ty, &d.shape.ctor, d.fields.len()).hash(h);
                for f in &d.fields {
                    feed(f, h);
                }
            }
            Value::Res(r) => match &r.kind {
                ResKind::Buf(b) => (6u8, &*b.borrow()).hash(h),
                _ => 7u8.hash(h),
            },
            _ => 7u8.hash(h),
        }
    }
    let mut h = std::collections::hash_map::DefaultHasher::new();
    feed(v, &mut h);
    h.finish()
}

/// `Secret(A)` of `std/prelude/Secret.taut`: a value no program reads but
/// through the secret operations. It shows as `Secret`, as the backends show it.
const SECRET: &str = "Secret@";

fn secret(v: Value<'_>) -> Value<'_> {
    data(Data {
        shape: Rc::new(Shape {
            ty: SECRET.into(),
            ctor: SECRET.into(),
            names: vec![None],
        }),
        fields: vec![v],
        token: None,
        owns: false,
    })
}

/// A secret's content; a public argument (a shift's amount) as it is.
fn revealed<'v, 'a>(v: &'v Value<'a>) -> Result<&'v Value<'a>, RunError> {
    match v {
        Value::Data(d) if d.shape.ctor == SECRET => Ok(&d.fields[0]),
        v => Ok(v),
    }
}

/// The secret words of `std/prelude/Secret.taut`, on their contents:
/// `ct_<width>_<op>`, `ct_<to>_of_<from>` and `ct_bool_<op>`.
fn secret_op<'a>(name: &str, args: &[Value<'a>]) -> Result<Value<'a>, RunError> {
    let Some((width, op)) = name.strip_prefix("Ct::").and_then(|n| n.split_once('_')) else {
        return runtime(msg!(
            "eval-is-not-a-secret-operation",
            name = name.to_string()
        ));
    };
    let bits: u32 = match width {
        "u8" => 8,
        "u32" => 32,
        "u64" => 64,
        "bool" => {
            return Ok(match (op, args) {
                ("and", [Value::Bool(a), Value::Bool(b)]) => Value::Bool(*a && *b),
                ("or", [Value::Bool(a), Value::Bool(b)]) => Value::Bool(*a || *b),
                ("not", [Value::Bool(a)]) => Value::Bool(!*a),
                ("select", [Value::Bool(c), a, b]) => (if *c { a } else { b }).clone(),
                _ => return runtime(msg!("eval-takes-secret-yes-or-no", name = name.to_string())),
            });
        }
        _ => {
            return runtime(msg!(
                "eval-is-not-a-secret-operation",
                name = name.to_string()
            ));
        }
    };
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let word = |v: &Value<'a>| match v {
        Value::Int(n) => u64::try_from(*n).map_err(|_| overflow()),
        _ => Err(RunError::Runtime(
            msg!("eval-takes-secret-words", name = name).to_string(),
        )),
    };
    let int = |n: u64| Value::Int(i128::from(n));
    if op.starts_with("of_") {
        // A wider word holds the narrower one; a narrower one keeps the low bits.
        let [a] = args else {
            return runtime(msg!("eval-takes-one-secret-word", name = name.to_string()));
        };
        return Ok(int(word(a)? & mask));
    }
    Ok(match (op, args) {
        ("not", [a]) => int(!word(a)? & mask),
        ("select", [Value::Bool(c), a, b]) => (if *c { a } else { b }).clone(),
        ("eq", [a, b]) => Value::Bool(word(a)? == word(b)?),
        ("lt", [a, b]) => Value::Bool(word(a)? < word(b)?),
        ("shl" | "shr" | "rotl" | "rotr", [a, s]) => {
            let (a, s) = (word(a)?, (word(s)? % u64::from(bits)) as u32);
            int(match op {
                _ if s == 0 && op.starts_with("rot") => a,
                "shl" => a.wrapping_shl(s) & mask,
                "shr" => a >> s,
                "rotl" => ((a << s) | (a >> (bits - s))) & mask,
                _ => ((a >> s) | (a << (bits - s))) & mask,
            })
        }
        (_, [a, b]) => {
            let (a, b) = (word(a)?, word(b)?);
            int(match op {
                "add" => a.wrapping_add(b) & mask,
                "sub" => a.wrapping_sub(b) & mask,
                "mul" => a.wrapping_mul(b) & mask,
                "mul_hi" => ((u128::from(a) * u128::from(b)) >> 64) as u64,
                "and" => a & b,
                "or" => a | b,
                "xor" => a ^ b,
                _ => {
                    return runtime(msg!(
                        "eval-is-not-a-secret-operation",
                        name = name.to_string()
                    ));
                }
            })
        }
        _ => {
            return runtime(msg!(
                "eval-is-not-a-secret-operation",
                name = name.to_string()
            ));
        }
    })
}

fn equal(a: &Value<'_>, b: &Value<'_>) -> Result<bool, RunError> {
    Ok(match (deref(a), deref(b)) {
        (Value::Int(a), Value::Int(b)) => a == b,
        (a @ (Value::Int(_) | Value::Nat(_)), b @ (Value::Int(_) | Value::Nat(_))) => {
            as_nat(&a).is_some() && as_nat(&a) == as_nat(&b)
        }
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Float(a), Value::Float(b)) => a == b,
        (Value::Float32(a), Value::Float32(b)) => a == b,
        (Value::Text(a), Value::Text(b)) => a == b,
        (Value::Bytes(a), Value::Bytes(b)) => a == b,
        (Value::Unit, Value::Unit) => true,
        (Value::Data(a), Value::Data(b)) => {
            if a.shape.ty != b.shape.ty
                || a.shape.ctor != b.shape.ctor
                || a.fields.len() != b.fields.len()
            {
                return Ok(false);
            }
            for (x, y) in a.fields.iter().zip(&b.fields) {
                if !equal(x, y)? {
                    return Ok(false);
                }
            }
            true
        }
        (Value::Res(a), Value::Res(b)) => match (&a.kind, &b.kind) {
            (ResKind::Buf(x), ResKind::Buf(y)) => *x.borrow() == *y.borrow(),
            _ => return runtime(msg!("eval-cannot-compare-containers")),
        },
        (a, b) => {
            return runtime(msg!(
                "eval-cannot-compare-with",
                a = a.to_string(),
                b = b.to_string()
            ));
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_places_update_their_shared_root() {
        let root = Rc::new(RefCell::new(data(Data {
            shape: Rc::new(Shape {
                ty: "Pair".into(),
                ctor: "Pair".into(),
                names: vec![None, None],
            }),
            fields: vec![Value::Int(1), Value::Int(2)],
            token: None,
            owns: false,
        })));
        let place = Place {
            root: Root::Cell(root.clone()),
            path: vec![1],
        };
        assert!(matches!(place.get(), Value::Int(2)));
        place.set(Value::Int(42));
        assert!(matches!(place.get(), Value::Int(42)));
        let Value::Data(data) = root.borrow().clone() else {
            panic!("data root")
        };
        assert!(matches!(data.fields[0], Value::Int(1)));
    }

    #[test]
    #[should_panic(expected = "evaluator place: missing vector element")]
    fn stale_element_reads_fail_at_the_place() {
        Root::Elem(
            Rc::new(Res {
                kind: ResKind::Vec(RefCell::new(vec![])),
                token: None,
            }),
            0,
        )
        .get();
    }

    #[test]
    #[should_panic(expected = "evaluator place: missing vector element")]
    fn stale_element_writes_fail_at_the_place() {
        Root::Elem(
            Rc::new(Res {
                kind: ResKind::Vec(RefCell::new(vec![])),
                token: None,
            }),
            0,
        )
        .set(Value::Int(1));
    }

}

/// The member of a product whose type is `key`; a value that is not a
/// product is its only member.
fn project<'a>(v: Value<'a>, key: &str) -> Result<Value<'a>, RunError> {
    match deref(&v) {
        Value::Product(ms) => match ms.iter().find(|(k, _)| &**k == key) {
            Some((_, m)) => Ok(m.clone()),
            None => runtime(msg!(
                "eval-the-product-has-no-member",
                key = key.to_string()
            )),
        },
        _ => Ok(v),
    }
}

/// A product taken to the type `to`: the members `to` has, or the one
/// member that is `to`.
fn fit<'a>(v: Value<'a>, to: &Ty) -> Result<Value<'a>, RunError> {
    let Value::Product(ms) = deref(&v) else {
        return Ok(v);
    };
    match to.unborrowed() {
        Ty::Product(ts) => {
            let keep: Vec<(Rc<str>, Value<'a>)> = ts
                .iter()
                .map(|t| {
                    let key = t.to_string();
                    ms.iter().find(|(k, _)| **k == *key).cloned().ok_or(())
                })
                .collect::<Result<_, ()>>()
                .or_else(|()| {
                    runtime(msg!(
                        "eval-the-product-has-no-member-of",
                        to = to.to_string()
                    ))
                })?;
            Ok(Value::Product(keep.into()))
        }
        Ty::Unit => Ok(Value::Unit),
        t => project(v, &t.to_string()),
    }
}

/// The names of function values that a call calls, or lends to one of its
/// borrowed parameters.
fn called_functions(program: &Program, report: &TypeReport) -> HashSet<crate::surface::TermId> {
    let mut out = HashSet::new();
    for s in &program.stmts {
        crate::surface::walk::values_stmt(s, &mut |node| {
            let crate::surface::walk::Node::Term(t) = node else {
                return;
            };
            let TermKind::App {
                function,
                arguments,
            } = &*t.kind
            else {
                return;
            };
            if matches!(&*function.kind, TermKind::Var(_)) {
                out.insert(function.id());
            }
            if let Some(Ty::Fn(ps, _, _)) = report.term(function).map(|t| t.unborrowed()) {
                for (p, a) in ps.iter().zip(arguments) {
                    if matches!(p, Ty::Borrow(..)) && matches!(&*a.kind, TermKind::Var(_)) {
                        out.insert(a.id());
                    }
                }
            }
        });
    }
    out
}

/// A constructor by the name written, not by its full name `m::C`.
fn shown(ctor: &str) -> &str {
    crate::surface::qualify::short(ctor)
}

/// The fields in result position (under blocks, `if` and `match`) of a
/// function that returns `&mut A`.
fn note_lent_fields(f: &FnDecl, out: &mut HashSet<*const SurfaceTerm>) {
    fn tail(t: &SurfaceTerm, out: &mut HashSet<*const SurfaceTerm>) {
        match &*t.kind {
            TermKind::Field { .. } => {
                out.insert(t as *const _);
            }
            TermKind::Block(stmts) => {
                if let Some(Stmt::Expr(e)) = stmts.last() {
                    tail(e, out);
                }
            }
            TermKind::If {
                then, otherwise, ..
            } => {
                tail(then, out);
                if let Some(o) = otherwise {
                    tail(o, out);
                }
            }
            TermKind::Match { arms, .. } => arms.iter().for_each(|a| tail(&a.body, out)),
            _ => {}
        }
    }
    if let Some(r) = &f.result
        && matches!(&*r.kind, TermKind::Borrow { mutable: true, .. })
    {
        tail(&f.body, out);
    }
}

/// Whether `n` names the prelude's `Pair`, which `#(a, b)` is read to.
fn is_pair_name(n: &str) -> bool {
    n == "Pair" || n.ends_with("::Pair")
}

/// Whether `p` is `#(…)`: a product's pattern, or the `Pair { fst, snd }` it is read to.
fn is_tuple_pattern(p: &Pattern) -> bool {
    match p {
        Pattern::Tuple(_) => true,
        Pattern::Record { name, fields } => {
            is_pair_name(name) && fields.len() == 2 && fields[0].0 == "fst" && fields[1].0 == "snd"
        }
        _ => false,
    }
}

/// The members of `#(p₁, …, pₙ)`, read from `Pair { fst, snd }` nested to the right: a member
/// that is itself `#(…)` gives its members and a member `#()` gives none, as the value's do.
fn pair_pattern_members(p: &Pattern) -> Vec<&Pattern> {
    fn go<'p>(p: &'p Pattern, out: &mut Vec<&'p Pattern>) {
        match p {
            Pattern::Record { name, fields }
                if is_pair_name(name)
                    && fields.len() == 2
                    && fields[0].0 == "fst"
                    && fields[1].0 == "snd" =>
            {
                go(&fields[0].1, out);
                go(&fields[1].1, out);
            }
            Pattern::Tuple(items) => items.iter().for_each(|q| go(q, out)),
            Pattern::Ctor { name, args }
                if args.is_empty() && (name == "Star" || name.ends_with("::Star")) => {}
            other => out.push(other),
        }
    }
    let mut out = Vec::new();
    go(p, &mut out);
    out
}
