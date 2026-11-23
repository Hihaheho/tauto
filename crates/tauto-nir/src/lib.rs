//! NIR: the checked program as the code generators read it.
//!
//! Lowering (`lower`) only restates what the checks (`types.rs`, `rows.rs`,
//! `lin.rs`) already decided: which use of a name moves or copies, which
//! argument is a borrow, which tier a function runs in. Every node keeps its
//! source `Span`, which the generator turns into a comment and a place for
//! run-time errors.
//!
//! Two differences from `docs/design/rust-backend.md`「NIR」「方針」:
//! expressions are not flattened into A-normal form (Rust itself evaluates
//! arguments left to right and drops a statement's temporaries at its end,
//! which is what the ownership rules ask for), and a `Local` carries its representation
//! (`Repr`) so a use needs no table lookup.
//!
//! Every type is written: lowering leaves none for a backend to infer. A
//! type the checker left open (nothing in the program fixes it, as the
//! element of a `None` that is only shown) is written `Ty::Never`, which
//! is one of the types it may be.
//!
//! NIR states what the ownership rules decided, not how Rust stores it: a
//! shared `var` is `Repr::SharedVar`/`Ty::SharedVar`, a field that holds its
//! own type is `Indirect::Shared` or `Indirect::Unique`, and the Rust
//! generator picks `Rc<Cell>`/`Rc<RefCell>` and `Rc`/`Box` from these. A
//! generator that also ignores how a shared `var`'s content is stored reads
//! `Local::storage` (`Storage`).
//!
//! `cps` lowers a function to continuation-passing style for a backend that
//! cannot suspend natively; such a backend only prints that tree.

use std::collections::BTreeSet;
pub(crate) use tauto_message::{Message, msg};
pub use tauto_surface::bindings::{is_library, library_name};
pub use tauto_surface::identity::DeclRef;
pub use tauto_surface::surface::Name;
pub use tauto_surface::surface::qualify::short as display_name;

pub use tauto_parol::Span;
pub use tauto_surface::kinds::{Kind, Quant, Width};

pub mod accumulate;
pub mod anf;
pub mod arms;
pub mod blocks;
pub mod borrow;
pub mod builtins;
pub mod cps;
pub mod decision;
pub mod effects;
pub mod evidence;
pub mod glue;
pub mod kont;
pub mod last_use;
pub mod loans;
pub mod mono;
pub mod ownership;
pub mod pass;
pub mod replaceable_extern;
pub mod stack;
pub mod tail;
pub mod text;
pub mod wf;

pub use replaceable_extern::{
    external_data_names, external_fn_names, pass_of, select_replaceable_blocks, ExternSelection,
};

pub use tail::{mark as mark_tail_calls, passed_on, recurs};

/// The backend a program is checked for, as the capabilities that change
/// what the checker accepts. A backend states its profile here once, and the
/// checker and NIR ask the profile, never which backend it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Target {
    #[default]
    Rust,
    JavaScript,
    /// The LLVM backend: it answers the standard effects itself, so a
    /// program gets no host's handler outside it.
    Llvm,
}

impl Target {
    /// A host callback crosses a Promise boundary: it may not take an
    /// effect that resumes more than once or an open row.
    pub fn promise_callbacks(self) -> bool {
        matches!(self, Target::JavaScript)
    }
}

/// What the bounded, directly executed body establishes about an arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperationAdmission {
    Legacy,
    Unique,
    Incomplete,
    ExplicitReturn,
    Missing,
    Indeterminate,
    Distinct,
    Unresolved,
}

impl OperationAdmission {
    pub fn limitation(self) -> Option<&'static str> {
        match self {
            Self::Legacy | Self::Unique => None,
            Self::Incomplete => {
                Some("the handled body has an opaque or storage-sensitive operation context")
            }
            Self::ExplicitReturn => {
                Some("an explicit return arm is outside checked operation-instance admission")
            }
            Self::Missing => {
                Some("the handled body supplies no directly determined operation instance")
            }
            Self::Indeterminate => {
                Some("the handled operation instances are not determined before checking the arm")
            }
            Self::Distinct => {
                Some("the handled body has distinct parameterized operation instances")
            }
            Self::Unresolved => {
                Some("a checked operation instance still has unresolved type arguments")
            }
        }
    }
}

pub type InstId = usize;
pub type OpIndex = usize;
pub type UnionId = usize;

/// A function's tier: `S` plain, `A` returns `Result` for `resume 0`,
/// `O` is a `Future` (`resume <=1`, `1`), `M` is a state machine (`resume ω`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Tier {
    S,
    A,
    O,
    M,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Unsupported {
    pub what: Message,
    pub span: Option<Span>,
}

impl std::fmt::Display for Unsupported {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let m = msg!("nir-unsupported", what = self.what.clone());
        write!(f, "{m}")
    }
}

/// A shared type of `tauto_rt::stdlib` that the lowering knows by kind, not by
/// its spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum StdType {
    SynDeclaration,
    Ref,
    Weak,
    Mutex,
    /// The one holder of a lock.
    MutexGuard,
    Atomic,
    Bytes,
    /// A thread's result, taken once.
    Pending,
    Secret,
    Signal,
    CancelSource,
    /// A scoped region (`tauto_rt::region`).
    Region,
    /// Where a value goes in a region.
    Place,
    /// A counted region (`tauto_rt::region`).
    RcRegion,
    /// Where a value goes in a counted region or on the heap.
    RcPlace,
    /// Slots of an element with a mark beside each and a state of the whole
    /// (`std/prelude/collections.taut`), whose arguments are the state, the
    /// mark and the element.
    Slots,
    /// A host value no tauto type names (the boundary cannot carry it).
    OpaqueHost,
}

impl StdType {
    /// The name of the type in the standard library.
    pub fn name(self) -> &'static str {
        match self {
            StdType::SynDeclaration => "SynDeclaration",
            StdType::Ref => "Ref",
            StdType::Weak => "Weak",
            StdType::Mutex => "Mutex",
            StdType::MutexGuard => "MutexGuard",
            StdType::Atomic => "Atomic",
            StdType::Bytes => "Bytes",
            StdType::Pending => "Pending",
            StdType::Secret => "Secret",
            StdType::Signal => "Signal",
            StdType::CancelSource => "CancelSource",
            StdType::Region => "Region",
            StdType::Place => "Place",
            StdType::RcRegion => "RcRegion",
            StdType::RcPlace => "RcPlace",
            StdType::Slots => "Slots",
            StdType::OpaqueHost => "OpaqueHost",
        }
    }

    /// Whether a value of this type is taken once: a `Pending` can hold a
    /// thread's result, a guard is the one holder of a lock.
    pub fn taken_once(self) -> bool {
        matches!(self, StdType::Pending | StdType::MutexGuard)
    }
}

impl std::fmt::Display for StdType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Ty {
    Int(Width),
    Bool,
    Text,
    Unit,
    Never,
    Float,
    Float32,
    /// `Buf`: Rust's `String`.
    Buf,
    Vec(Box<Ty>),
    /// `Array(A)`: `tauto_rt::stdlib::Array<A>`, shared and read-only.
    Array(Box<Ty>),
    /// A shared type of `tauto_rt::stdlib` by name (`Ref`, `Mutex`,
    /// `Atomic`): `tauto_rt::stdlib::<name><args>`.
    Std(StdType, Vec<Ty>),
    /// `Slice(A)`, behind a borrow only: `[A]`.
    Slice(Box<Ty>),
    Option(Box<Ty>),
    Result(Box<Ty>, Box<Ty>),
    /// `Pair(A, B)`: a product of two members; a product of more members is nested to the right.
    Pair(Box<Ty>, Box<Ty>),
    /// A struct or enum the generator writes (the program's and the
    /// library's: `List`, `Map`).
    Data(Name, Vec<Ty>),
    /// A union's enum.
    Union(UnionId),
    Param(String),
    Fn(Box<FnTy>),
    Ref(Box<Ty>),
    RefMut(Box<Ty>),
    /// A `var` shared with a closure that may outlive it, as a lifted
    /// function is passed it: one place shared by the function and its
    /// closures. The flag says whether the content is `copy`, which a
    /// backend may store differently (Rust: `Rc<Cell<A>>` for `copy`,
    /// `Rc<RefCell<A>>` otherwise).
    SharedVar(bool, Box<Ty>),
    Info(Box<Ty>),
    /// What the arm of `exceeded` answers with (`BudgetAnswer<T>`).
    BudgetAnswer(Box<Ty>),
    /// What `show` carries: the value already shown.
    Shown,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FnTy {
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub kind: Kind,
    pub tier: Tier,
}

impl Ty {
    /// Whether a function type occurs anywhere in this type.
    pub fn has_fn(&self) -> bool {
        match self {
            Ty::Fn(_) => true,
            Ty::Ref(a)
            | Ty::RefMut(a)
            | Ty::Vec(a)
            | Ty::Array(a)
            | Ty::Slice(a)
            | Ty::Option(a)
            | Ty::Info(a)
            | Ty::BudgetAnswer(a) => a.has_fn(),
            Ty::Result(a, b) | Ty::Pair(a, b) => a.has_fn() || b.has_fn(),
            Ty::Data(_, args) | Ty::Std(_, args) => args.iter().any(Ty::has_fn),
            Ty::SharedVar(_, a) => a.has_fn(),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Text
            | Ty::Unit
            | Ty::Never
            | Ty::Float
            | Ty::Float32
            | Ty::Buf
            | Ty::Union(_)
            | Ty::Param(_)
            | Ty::Shown => false,
        }
    }

    pub fn shared_var(&self) -> Option<&Ty> {
        match self {
            Ty::SharedVar(_, a) => Some(a),
            _ => None,
        }
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Ty::Unit)
    }

    /// Whether the type names the generic of an arm for every instance
    /// (`∀ A. op<A>(a)`) that no `perform` of the program fixes
    /// (`arms::instantiate`): the arm has no type to run at.
    pub fn has_arm_generic(&self) -> bool {
        match self {
            Ty::Param(p) => arms::is_skolem(p),
            Ty::Vec(a)
            | Ty::Array(a)
            | Ty::Slice(a)
            | Ty::Option(a)
            | Ty::Ref(a)
            | Ty::RefMut(a)
            | Ty::Info(a)
            | Ty::BudgetAnswer(a)
            | Ty::SharedVar(_, a) => a.has_arm_generic(),
            Ty::Result(a, b) | Ty::Pair(a, b) => {
                a.has_arm_generic() || b.has_arm_generic()
            }
            Ty::Data(_, args) | Ty::Std(_, args) => args.iter().any(Ty::has_arm_generic),
            Ty::Fn(f) => f.params.iter().any(Ty::has_arm_generic) || f.ret.has_arm_generic(),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Text
            | Ty::Unit
            | Ty::Never
            | Ty::Float
            | Ty::Float32
            | Ty::Buf
            | Ty::Union(_)
            | Ty::Shown => false,
        }
    }

    pub fn params(&self, out: &mut BTreeSet<String>) {
        match self {
            Ty::Param(p) => {
                out.insert(p.clone());
            }
            Ty::Vec(a)
            | Ty::Array(a)
            | Ty::Slice(a)
            | Ty::Option(a)
            | Ty::Ref(a)
            | Ty::RefMut(a)
            | Ty::Info(a)
            | Ty::BudgetAnswer(a) => a.params(out),
            Ty::Result(a, b) | Ty::Pair(a, b) => {
                a.params(out);
                b.params(out);
            }
            Ty::Data(_, args) | Ty::Std(_, args) => args.iter().for_each(|a| a.params(out)),
            Ty::Fn(f) => {
                f.params.iter().for_each(|a| a.params(out));
                f.ret.params(out);
            }
            Ty::SharedVar(_, a) => a.params(out),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Text
            | Ty::Unit
            | Ty::Never
            | Ty::Float
            | Ty::Float32
            | Ty::Buf
            | Ty::Union(_)
            | Ty::Shown => {}
        }
    }
}

/// How a struct or enum's field is stored when its type holds itself: behind
/// an indirection, unique for an affine data and shared for a shared one
/// (Rust: `Box<T>` and `Rc<T>`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Indirect {
    None,
    /// Shared by every copy of the value; reading it copies the content.
    Shared,
    /// Owned by the value alone; reading it moves the content out.
    Unique,
}

impl Indirect {
    pub fn is_indirect(self) -> bool {
        self != Indirect::None
    }
}

#[derive(Debug, Clone)]
pub struct FieldDef {
    pub name: Option<String>,
    pub ty: Ty,
    pub indirect: Indirect,
}

#[derive(Debug, Clone)]
pub struct CtorDef {
    pub name: Name,
    pub fields: Vec<FieldDef>,
}

#[derive(Debug, Clone)]
pub struct DataDef {
    pub name: Name,
    pub generics: Vec<String>,
    pub kind: Kind,
    pub is_struct: bool,
    pub ctors: Vec<CtorDef>,
    /// `#[derive(Clone)]`: every kind but `linear` and the opaque affine ones.
    pub clone: bool,
    pub copy: bool,
    /// A `bomb` field in each constructor.
    pub linear: bool,
    /// A type that holds a borrow: its Rust type has a lifetime.
    pub view: bool,
    /// An extern type (`extern { type T }`): the host's type, bound by the
    /// backend's configuration; only extern functions make its values.
    pub host: bool,
    /// The name `show` writes for a value of a `struct`: the type's name as
    /// the source spells it, with the modules below its file's. Empty for
    /// an `enum`.
    pub shown: String,
}

#[derive(Debug, Clone)]
pub struct UnionDef {
    pub id: UnionId,
    /// The members in `types.rs`'s order; variant `Vi` holds member `i`.
    pub members: Vec<Ty>,
    pub kind: Kind,
}

#[derive(Debug, Clone)]
pub struct OpDef {
    /// The constant `OP_<name>` is `Op::new(id, name)`.
    pub id: u32,
    pub name: Name,
    pub quant: Quant,
    pub generics: Vec<String>,
    pub params: Vec<Ty>,
    pub result: Ty,
}

/// What a type parameter must be for the instance to compile.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Bound {
    Clone,
    Show,
    Eq,
    /// Holds no borrow, for a host that needs it: the instance builds a
    /// function value or carries values through an effect. A parameter
    /// without it may stand for a type that holds a borrow.
    Static,
}

#[derive(Debug, Clone)]
pub struct FnInst {
    pub id: InstId,
    /// The name in the tauto source.
    pub source: Name,
    pub tier: Tier,
    pub generics: Vec<(String, BTreeSet<Bound>)>,
    pub params: Vec<Param>,
    pub ret: Ty,
    /// `borrows(m)`: for each parameter, whether the result may borrow from
    /// it. `None` is every borrowed parameter.
    pub lends: Option<Vec<bool>>,
    /// Its function values live for a region of the instance's own (`'f`)
    /// that its type parameters outlive, in place of `'static` on them: it
    /// builds function values but keeps them inside its call (it returns
    /// none, stores none in data and hands them only to such instances).
    pub fn_region: bool,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub local: Local,
    pub ty: Ty,
}

/// How a local is stored.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Repr {
    /// `let x` / `let mut x`, a parameter taken by value.
    Plain,
    /// A `var` captured by a closure that may outlive it: one place shared
    /// with the closure. The flag says whether the content is `copy`
    /// (Rust: `Rc<Cell<T>>` for `copy`, `Rc<RefCell<T>>` otherwise).
    SharedVar(bool),
    /// A parameter or `let &x`: a shared borrow (Rust: `&T`).
    Ref,
    RefMut,
    /// A closure that holds borrows, so it does not outlive them (Rust: a
    /// concrete closure, passed as `&mut f`).
    BorrowClosure,
    /// A parameter `&f` of function type (Rust: `&mut dyn FnMut`).
    FnRef,
}

/// What a `Repr` means for a backend that does not distinguish how the
/// content of a shared `var` is stored: a backend other than Rust reads
/// `Local::storage`, not `Repr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Storage {
    Owned,
    /// A `var` captured by a closure that may outlive it: one place shared
    /// by the function and its closures.
    SharedVar,
    Borrow,
    BorrowMut,
    /// A borrowed function (`&f` of function type).
    BorrowedFn,
    /// A closure that holds borrows, so it does not outlive them.
    BorrowingClosure,
}

impl Storage {
    pub fn is_borrow(self) -> bool {
        matches!(
            self,
            Storage::Borrow | Storage::BorrowMut | Storage::BorrowedFn
        )
    }
}

impl Repr {
    pub fn storage(self) -> Storage {
        match self {
            Repr::Plain => Storage::Owned,
            Repr::SharedVar(_) => Storage::SharedVar,
            Repr::Ref => Storage::Borrow,
            Repr::RefMut => Storage::BorrowMut,
            Repr::FnRef => Storage::BorrowedFn,
            Repr::BorrowClosure => Storage::BorrowingClosure,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Local {
    pub id: u32,
    pub name: String,
    pub repr: Repr,
}

impl Local {
    pub fn storage(&self) -> Storage {
        self.repr.storage()
    }

    pub fn rust(&self) -> String {
        format!("{}_{}", self.name, self.id)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Use {
    Move,
    Copy,
    Clone,
    /// Not a use of the value: the name is a place, as the base of a field.
    Place,
}

#[derive(Debug, Clone)]
pub struct Place {
    pub local: Local,
    pub path: Vec<FieldRef>,
    /// The type of the value at the place (not of a borrow of it).
    pub ty: Ty,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldRef {
    pub name: String,
    /// For a `Pair`: the tuple index.
    pub index: Option<usize>,
    /// How the field is stored in its record: a place that goes on
    /// through a shared field has to unshare it before it is written.
    pub indirect: Indirect,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Option<Box<Expr>>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let {
        local: Local,
        ty: Ty,
        init: Expr,
        span: Span,
        /// `let(stack)`: the local is placed in the frame's slot, with no
        /// allocation made for it ([`crate::stack`] checks that it can be).
        stack: bool,
    },
    /// A `var`; `local.repr` says how it is stored.
    Var {
        local: Local,
        ty: Ty,
        init: Expr,
        span: Span,
    },
    Assign {
        target: Place,
        value: Expr,
        span: Span,
    },
    Expr(Expr),
    While {
        cond: Expr,
        body: Block,
        tick: Tick,
        span: Span,
    },
    Return {
        value: Option<Expr>,
        span: Span,
    },
}

/// A place where fuel is counted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tick {
    None,
    /// The host's step limit.
    Host,
    /// A budget's: `tauto_rt::budget::tick(..).await`.
    Budget,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arith {
    Add,
    Sub,
    Mul,
    Neg,
    /// `/`, of `Float` only; by zero, a run-time error.
    Div,
}

/// The numbers an arithmetic operation is on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Num {
    /// Integers of a width: a result outside it is a run-time error.
    Int(Width),
    Float,
    Float32,
}

impl Num {
    /// The type of the operation's operands and result.
    pub fn ty(self) -> Ty {
        match self {
            Num::Int(w) => Ty::Int(w),
            Num::Float => Ty::Float,
            Num::Float32 => Ty::Float32,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cmp {
    Lt,
    Gt,
    Le,
    Ge,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// An index in the package declaration capability table.
    Declaration(usize),
    Unit,
    Int(i128),
    Float(f64),
    Bool(bool),
    Text(String),
    Read {
        local: Local,
        how: Use,
    },
    FnValue {
        inst: InstId,
        /// The checked arguments in the declaration's generic order.
        targs: Vec<Ty>,
    },
    Call(Box<CallNode>),
    Arith {
        op: Arith,
        args: Vec<Expr>,
        num: Num,
    },
    Cmp {
        op: Cmp,
        args: Vec<Expr>,
    },
    Eq {
        negate: bool,
        args: Vec<Expr>,
    },
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    /// The fields in the order written, with the name of a named one.
    Ctor {
        ctor: CtorRef,
        fields: Vec<(Option<String>, Expr)>,
    },
    Field {
        base: Box<Expr>,
        field: FieldRef,
        how: Use,
        indirect: Indirect,
    },
    Match(Box<MatchNode>),
    If {
        cond: Box<Expr>,
        then: Box<Expr>,
        otherwise: Option<Box<Expr>>,
    },
    Block(Block),
    Closure(Box<ClosureNode>),
    Perform(Box<PerformNode>),
    Handle(Box<HandleNode>),
    /// `A` to the union holding it (`Union::V<variant>(value)`).
    Inject {
        union: UnionId,
        variant: usize,
        value: Box<Expr>,
    },
    /// A union to a union with more members, or to one member's type.
    Remap {
        from: UnionId,
        to: Ty,
        value: Box<Expr>,
    },
    Ref(Place),
    RefMut(Place),
    /// A borrow of a value that is not a place: `&(e)`.
    TempRef(Box<Expr>),
    /// `*e` of a borrow, or the value `e` borrows, copied or cloned.
    Deref {
        value: Box<Expr>,
        how: Use,
    },
    Shown(Box<Expr>),
    Budget(Box<BudgetNode>),
    Unreachable(Box<Expr>),
    /// A function value represented at its expected kind and effect tier.
    FnCast(Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct BudgetNode {
    pub id: u32,
    /// `perform budget_memory(n, f)`: `steps` is a count of cells.
    pub memory: bool,
    pub steps: Expr,
    pub body: Expr,
    /// In code of the M tier: a budget among the handlers in place, with
    /// its body in continuation-passing style.
    pub m: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CtorRef {
    pub data: DataRef,
    /// The constructor's name.
    pub name: Name,
    pub index: usize,
    /// The constructor's fields, which are stored boxed.
    pub indirect: Vec<Indirect>,
    pub linear: bool,
    /// Field names, `None` for a positional constructor.
    pub fields: Vec<Option<String>>,
    pub nullary: bool,
}

/// The cells a memory budget counts for making a value: one for the
/// constructor and one for each field, and one for a closure that owns
/// its environment. This is the one cost model every backend charges by.
pub fn cells_made(kind: &ExprKind) -> Option<u64> {
    match kind {
        ExprKind::Ctor { fields, .. } => Some(1 + fields.len() as u64),
        ExprKind::Closure(c) if !c.borrowed => Some(1),
        _ => None,
    }
}

impl CtorRef {
    /// The declared position of the `i`-th field as written, which is by
    /// name for a named field: a backend lays fields out by this and never
    /// compares names itself.
    pub fn slot(&self, i: usize, name: Option<&str>) -> usize {
        name.and_then(|n| self.fields.iter().position(|x| x.as_deref() == Some(n)))
            .unwrap_or(i)
    }

    /// Which constructor of the library's `Option` or `Result` this is, by
    /// its declared index (`None`, `Some` and `Ok`, `Err` in the prelude's
    /// order), so that no backend reads it from the name.
    pub fn library(&self) -> Option<LibraryCtor> {
        Some(match (&self.data, self.index) {
            (DataRef::Option, 0) => LibraryCtor::None,
            (DataRef::Option, _) => LibraryCtor::Some,
            (DataRef::Result, 0) => LibraryCtor::Ok,
            (DataRef::Result, _) => LibraryCtor::Err,
            _ => return None,
        })
    }
}

/// A constructor of the library's `Option` or `Result`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LibraryCtor {
    None,
    Some,
    Ok,
    Err,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DataRef {
    /// A generated type, by name.
    Gen(Name),
    Option,
    Result,
    Pair,
}

#[derive(Debug, Clone)]
pub struct CallNode {
    pub callee: Callee,
    pub args: Vec<Expr>,
    /// The callee's tier; a call to `A` propagates an abort.
    pub tier: Tier,
    /// The explicit type arguments (a turbofish), when they are all known.
    pub targs: Vec<Ty>,
    /// Fuel is counted before the call (the callee may not stop).
    pub tick: Tick,
    /// A call of the function itself in tail position whose frame may be
    /// discarded (`tail.rs`): a backend may give the arguments to the
    /// parameters and run the body again, counting `tick` at the jump. A
    /// backend that does not reads it as an ordinary call.
    pub recur: bool,
    /// What the call's frame drops if the call aborts (a call of the tier
    /// `A` or above), the latest first: the owned values still alive here
    /// that are not given to the call and were made inside the innermost
    /// `handle` around it in the function (or anywhere in the function).
    /// `ownership::insert` writes it; it is on the abort path only, so
    /// `Expr::walk` and `children` do not visit it. Empty before that pass.
    pub unwind: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Callee {
    Inst(InstId),
    Builtin(String),
    /// An `extern` of the program: its wrapper in `externs`, by name.
    Extern(Name),
    Local(Local),
    /// The continuation `k` of an arm of a suspending operation.
    Cont(Local),
    /// A function value written in place. A value the expression makes (a
    /// copy of a field, a closure) is taken by the call: it ends when the
    /// call does, whether the call returns or aborts.
    Value(Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct ClosureNode {
    pub params: Vec<(Local, Ty)>,
    pub ret: Ty,
    pub body: Expr,
    pub fn_ty: FnTy,
    /// Written where a borrowed function is expected (`&f`): not `move`, and
    /// `&mut |…| …`.
    pub borrowed: bool,
    /// The duplicable locals it captures, cloned before the closure is made
    /// (`move`), and the cells it shares.
    pub clones: Vec<Local>,
    /// It captures nothing, so one value of it serves every time it is made.
    pub pure: bool,
    /// A borrowing closure of the O tier is passed what it uses as
    /// references: the name it has inside, the local it stands for, and
    /// whether the reference is `&mut`.
    pub refs: Vec<CapturedRef>,
    /// The shared borrows of duplicable values an owned closure captures:
    /// it may outlive what they borrow, so it holds a copy of each and
    /// reads the copy through a borrow.
    pub owned_refs: Vec<Local>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CapturedRef {
    pub inner: Local,
    pub outer: Local,
    pub mutable: bool,
}

/// A complete checked formal operation signature and its admission boundary.
/// JavaScript may erase representations that Rust must diagnose explicitly.
#[derive(Debug, Clone)]
pub struct OperationInstance {
    pub type_args: Vec<Ty>,
    pub params: Vec<Ty>,
    pub answer: Ty,
    pub admission: OperationAdmission,
}

#[derive(Debug, Clone)]
pub struct PerformNode {
    pub op: OpIndex,
    pub instance: Option<OperationInstance>,
    pub quant: Quant,
    /// A `direct` operation in code that holds no handler from around it
    /// (`Cx::detached`): the handlers it was started under answer it, or
    /// those of whoever runs it now.
    pub detached: bool,
    /// What the perform's frame drops if an abort arm takes it, the latest
    /// first, as `CallNode::unwind` says.
    pub unwind: Vec<Stmt>,
    pub args: Vec<Expr>,
    pub result: Ty,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Pat {
    Wild,
    Bind(Local, Ty),
    Int(i64),
    /// A literal pattern on a `nat`, which Rust cannot match on directly.
    Nat(i64),
    Bool(bool),
    Text(String),
    Ctor {
        ctor: CtorRef,
        fields: Vec<Pat>,
    },
    /// A value of the union `union` injected at `variant`, with `pat` on what was injected:
    /// the converse of `ExprKind::Inject`.
    Variant {
        union: UnionId,
        variant: usize,
        pat: Box<Pat>,
    },
}

#[derive(Debug, Clone)]
pub struct MatchNode {
    pub scrut: Expr,
    /// The scrutinee is a borrow (`match &v`, or a borrowed name): the arms'
    /// names borrow.
    pub by_ref: bool,
    pub arms: Vec<MatchArm>,
    pub exhaustive: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct HandleNode {
    pub id: u32,
    pub body: Expr,
    pub body_ty: Ty,
    pub result: Ty,
    pub ret: Option<ReturnArm>,
    pub direct: Vec<OpArm>,
    pub aborts: Vec<OpArm>,
    /// The arms of operations that resume at most once or once.
    pub susp: Vec<OpArm>,
    /// The locals of the enclosing function that the arms mention, and the
    /// ones among them that a copy is made of for each handler call.
    pub captures: Vec<Local>,
    pub clones: Vec<Local>,
    /// The body's tier: from `O` on it is a future.
    pub body_tier: Tier,
    /// Written in continuation-passing style: the body may resume more
    /// than once, or suspends inside code that does.
    pub m: bool,
    /// For an `m` handle that starts the M tier in a function of another
    /// tier, whose code `return`s: the function's return type. The driver
    /// ends with the returned value, and the function returns it.
    pub host_ret: Option<Ty>,
    /// An arm keeps `k` as a value: the body and the arms hold no handler
    /// from around the `handle`, and an operation they do not answer goes
    /// to whoever runs the continuation.
    pub kept: bool,
    /// In code that holds no `direct` handler from around it (a `kept`
    /// handle, or inside one): the `direct` arms are a handler of the M
    /// tier, which a kept continuation rebuilds.
    pub detached: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ReturnArm {
    pub pat: Pat,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct OpArm {
    pub op: OpIndex,
    pub instance: Option<OperationInstance>,
    /// The operation's payload type (a product of its parameters).
    pub params: Vec<Ty>,
    pub pats: Vec<Pat>,
    pub guard: Option<Expr>,
    /// For a `direct` operation: the arm with each `k(e)` replaced by `e`.
    pub body: Expr,
    /// For an arm of an operation that resumes: the continuation `k`, and the
    /// type of the answer it takes.
    pub k: Option<Local>,
    pub k_ans: Ty,
    /// One of the copies `arms::instantiate` wrote of an arm for every
    /// instance, at one payload type the program performs.
    pub instantiated: bool,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pass {
    Value,
    Ref,
    RefMut,
}

#[derive(Debug, Clone)]
pub struct ExternDef {
    pub name: Name,
    pub generics: Vec<String>,
    pub params: Vec<(String, Ty, Pass)>,
    pub ret: Ty,
    /// `borrows(m)`: for each parameter, whether the result may borrow
    /// from it. `None` is every borrowed parameter.
    pub lends: Option<Vec<bool>>,
    /// The row is `{wait}`: a call waits on the host (a JavaScript Promise,
    /// a Rust Future) before it answers.
    pub waits: bool,
    pub span: Span,
}

/// A replaceable `extern` block: Tauto bodies are always checked; host
/// bindings may replace the whole block's runtime representation.
#[derive(Debug, Clone)]
pub struct ReplaceableExternBlock {
    /// Stable id: sorted member spellings joined by `\0`.
    pub id: String,
    pub fn_names: Vec<Name>,
    /// Whether each member's written row includes `wait`, in `fn_names` order.
    pub fn_waits: Vec<bool>,
    pub data_names: Vec<Name>,
    pub span: Span,
}

/// The program: what the generator writes.
#[derive(Debug, Clone, Default)]
pub struct Package {
    pub declarations: Vec<tauto_surface::identity::DeclRef>,
    /// File boundaries and macro origins for compiled totes.
    pub sources: Option<tauto_surface::sources::SourceMap>,
    /// Runtime syntax parsers with validated, self-contained tables.
    pub syntax_parsers: Vec<SyntaxParser>,
    pub datas: Vec<DataDef>,
    pub unions: Vec<UnionDef>,
    pub ops: Vec<OpDef>,
    pub fns: Vec<FnInst>,
    pub top: Option<InstId>,
    /// The functions a Rust crate may call (`compile_with` `lib`).
    pub exports: Vec<Export>,
    pub externs: Vec<ExternDef>,
    /// Replaceable blocks still using Tauto bodies until host selection.
    pub replaceable_externs: Vec<ReplaceableExternBlock>,
    /// Function instances only the replaced Tauto fallback reached after host
    /// selection. Generators omit them; `InstId`s stay valid for the rest.
    pub host_omitted_fns: BTreeSet<InstId>,
    /// Data types only the replaced Tauto fallback reached after host
    /// selection (including ordinary structs/enums that name omitted hosts).
    pub host_omitted_datas: BTreeSet<Name>,
    /// Unions only the replaced Tauto fallback reached after host selection.
    pub host_omitted_unions: BTreeSet<UnionId>,
    /// The program starts tasks (`perform spawn`): what a task body holds
    /// may cross threads, so shared values are `Arc`s and function values
    /// are `Send + Sync`.
    pub sync: bool,
    /// The permissions (`read`, `write`, `env`, `net`) of the standard effects
    /// that reach the top level (`docs/design/host-effects.md`): a run without
    /// one of them does not start.
    pub permissions: Vec<String>,
    /// What only the Rust backend rejects: a row variable carried by a
    /// record that a call specializes to a suspending tier (a record's
    /// function fields have one tier), or a continuation kept as a value in
    /// code of the M tier. The JavaScript backend runs every function with
    /// explicit continuations.
    pub rust_unsupported: Option<Unsupported>,
    /// The `handle` that answers a `direct` operation where the program
    /// says it alone (`evidence.rs`).
    pub evidence: evidence::Evidence,
}

/// A runtime parser whose syntax name and grammar identity are known at build time.
#[derive(Debug, Clone)]
pub struct SyntaxParser {
    /// Schema type labels bound to the declarations validated during lowering.
    pub data_bindings: std::collections::BTreeMap<String, Name>,
    pub constructor_bindings: std::collections::BTreeMap<(String, String), Name>,
    pub name: String,
    pub sha: String,
    pub tables: String,
    pub result: Ty,
}

#[derive(Debug, Clone)]
pub struct Export {
    pub inst: InstId,
    pub name: String,
    pub row: Vec<String>,
    /// The effects of `row` that are not the library's `show`, `div`, `wait`
    /// or `spawn`: decided by identity when lowering, since the spelling of a
    /// user effect may equal a library one.
    pub foreign_row: Vec<String>,
    /// Parameters declared as shared borrows of functions with an empty row.
    /// Recorded before representation optimizations can introduce borrows.
    pub pure_borrow_callbacks: Vec<usize>,
}

impl Expr {
    /// The operands evaluated before the expression itself, in the order
    /// they are evaluated: the ones a continuation-passing generator binds
    /// to names. A node whose parts are not all evaluated (`&&`, `if`, a
    /// closure) has none.
    pub fn operands_mut(&mut self) -> Vec<&mut Expr> {
        match &mut self.kind {
            ExprKind::Call(c) => {
                let mut v: Vec<&mut Expr> = Vec::new();
                if let Callee::Value(f) = &mut c.callee {
                    v.push(f);
                }
                v.extend(c.args.iter_mut());
                v
            }
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => args.iter_mut().collect(),
            ExprKind::Not(a)
            | ExprKind::TempRef(a)
            | ExprKind::Shown(a)
            | ExprKind::Unreachable(a)
            | ExprKind::FnCast(a) => vec![&mut **a],
            ExprKind::Ctor { fields, .. } => fields.iter_mut().map(|(_, e)| e).collect(),
            ExprKind::Field { base, .. } => vec![&mut **base],
            ExprKind::Perform(p) => p.args.iter_mut().collect(),
            ExprKind::Inject { value, .. }
            | ExprKind::Remap { value, .. }
            | ExprKind::Deref { value, .. } => {
                vec![&mut **value]
            }
            ExprKind::Declaration(_)
            | ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Text(_)
            | ExprKind::Read { .. }
            | ExprKind::FnValue { .. }
            | ExprKind::Ref(_)
            | ExprKind::RefMut(_)
            | ExprKind::Match(_)
            | ExprKind::If { .. }
            | ExprKind::Block(_)
            | ExprKind::Closure(_)
            | ExprKind::Handle(_)
            | ExprKind::And(..)
            | ExprKind::Or(..)
            | ExprKind::Budget(_) => Vec::new(),
        }
    }

    /// Calls `f` on this expression and its value subexpressions, outer first,
    /// including closure bodies. Assignment places and suspending handler arms
    /// are excluded; callers that need them must traverse them separately.
    pub fn walk(&self, f: &mut dyn FnMut(&Expr)) {
        f(self);
        self.children(&mut |child| child.walk(f));
    }

    /// Like `walk`, but also enters the guards and bodies of suspending
    /// handler arms.
    pub fn walk_with_handlers(&self, f: &mut dyn FnMut(&Expr)) {
        self.walk(&mut |node| {
            f(node);
            if let ExprKind::Handle(h) = &node.kind {
                for arm in &h.susp {
                    if let Some(g) = &arm.guard {
                        g.walk_with_handlers(f);
                    }
                    arm.body.walk_with_handlers(f);
                }
            }
        });
    }

    /// Calls `f` on immediate value subexpressions, with the same exclusions
    /// as `walk`. A while body is presented as a block expression.
    pub fn children(&self, f: &mut dyn FnMut(&Expr)) {
        let block = |b: &Block, f: &mut dyn FnMut(&Expr)| {
            for s in &b.stmts {
                match s {
                    Stmt::Let { init, .. } | Stmt::Var { init, .. } => f(init),
                    Stmt::Assign { value, .. } => f(value),
                    Stmt::Expr(e) => f(e),
                    Stmt::While { cond, body, .. } => {
                        f(cond);
                        f(&Expr {
                            kind: ExprKind::Block(body.clone()),
                            ty: Ty::Unit,
                            span: cond.span,
                        });
                    }
                    Stmt::Return { value, .. } => {
                        if let Some(v) = value {
                            f(v)
                        }
                    }
                }
            }
            if let Some(t) = &b.tail {
                f(t);
            }
        };
        match &self.kind {
            ExprKind::Call(c) => {
                if let Callee::Value(v) = &c.callee {
                    f(v);
                }
                c.args.iter().for_each(|a| f(a));
            }
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => args.iter().for_each(|a| f(a)),
            ExprKind::Not(a)
            | ExprKind::TempRef(a)
            | ExprKind::Shown(a)
            | ExprKind::Unreachable(a)
            | ExprKind::FnCast(a) => f(a),
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                f(a);
                f(b);
            }
            ExprKind::Budget(b) => {
                f(&b.steps);
                f(&b.body);
            }
            ExprKind::Ctor { fields, .. } => fields.iter().for_each(|(_, e)| f(e)),
            ExprKind::Field { base, .. } => f(base),
            ExprKind::Match(m) => {
                f(&m.scrut);
                for a in &m.arms {
                    if let Some(g) = &a.guard {
                        f(g);
                    }
                    f(&a.body);
                }
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                f(cond);
                f(then);
                if let Some(o) = otherwise {
                    f(o);
                }
            }
            ExprKind::Block(b) => block(b, f),
            ExprKind::Closure(c) => f(&c.body),
            ExprKind::Perform(p) => p.args.iter().for_each(|a| f(a)),
            ExprKind::Handle(h) => {
                f(&h.body);
                if let Some(r) = &h.ret {
                    f(&r.body);
                }
                for a in h.direct.iter().chain(&h.aborts) {
                    if let Some(g) = &a.guard {
                        f(g);
                    }
                    f(&a.body);
                }
            }
            ExprKind::Inject { value, .. }
            | ExprKind::Remap { value, .. }
            | ExprKind::Deref { value, .. } => f(value),
            ExprKind::Declaration(_)
            | ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Text(_)
            | ExprKind::Read { .. }
            | ExprKind::FnValue { .. }
            | ExprKind::Ref(_)
            | ExprKind::RefMut(_) => {}
        }
    }
}

/// A hash of what code calling the package from outside depends on: each
/// exported function's name and type, and each data type with its
/// constructors and fields, in order. Two compilations of the same source
/// have the same fingerprint; a change to any of these, a new one or a new
/// order changes it.
pub fn interface_fingerprint(pkg: &Package) -> u64 {
    use std::fmt::Write;
    let mut text = String::new();
    for e in &pkg.exports {
        let f = &pkg.fns[e.inst];
        let params: Vec<&Ty> = f.params.iter().map(|p| &p.ty).collect();
        let params: Vec<String> = params.into_iter().map(ty_text).collect();
        let _ = writeln!(
            text,
            "fn {} {:?} {} {:?}",
            e.name,
            params,
            ty_text(&f.ret),
            e.row
        );
    }
    for x in &pkg.externs {
        let params: Vec<String> = x
            .params
            .iter()
            .map(|(_, t, pass)| format!("{pass:?} {}", ty_text(t)))
            .collect();
        let _ = writeln!(
            text,
            "extern {} {:?} {}",
            x.name.as_str(),
            params,
            ty_text(&x.ret)
        );
    }
    for d in &pkg.datas {
        let _ = write!(
            text,
            "data {} {:?} {}",
            d.name.as_str(),
            d.generics,
            d.is_struct
        );
        for c in &d.ctors {
            let _ = write!(text, " | {}", c.name.as_str());
            for field in &c.fields {
                let _ = write!(text, " {:?}:{}", field.name, ty_text(&field.ty));
            }
        }
        text.push('\n');
    }
    content_hash(text.as_bytes())
}

/// FNV-1a of `bytes`: the same on every build of the compiler, so a build
/// and a run of what it built agree on it.
pub fn content_hash(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0100_0000_01b3);
    }
    h
}

/// A type as the fingerprint reads it: declarations by name, without the
/// number a compilation gives them (`DeclRef(Name#12)` is `DeclRef(Name)`).
fn ty_text(t: &Ty) -> String {
    let text = format!("{t:?}");
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '#' && chars.peek().is_some_and(|d| d.is_ascii_digit()) {
            while chars.peek().is_some_and(|d| d.is_ascii_digit()) {
                chars.next();
            }
        } else {
            out.push(c);
        }
    }
    out
}

impl Ty {
    /// Calls `f` on this type and on each type inside it, outermost first;
    /// a type `f` changes is not looked into again.
    pub fn each_mut(&mut self, f: &mut dyn FnMut(&mut Ty)) {
        f(self);
        match self {
            Ty::Vec(a)
            | Ty::Array(a)
            | Ty::Slice(a)
            | Ty::Option(a)
            | Ty::Ref(a)
            | Ty::RefMut(a)
            | Ty::Info(a)
            | Ty::BudgetAnswer(a)
            | Ty::SharedVar(_, a) => a.each_mut(f),
            Ty::Result(a, b) | Ty::Pair(a, b) => {
                a.each_mut(f);
                b.each_mut(f);
            }
            Ty::Data(_, args) | Ty::Std(_, args) => args.iter_mut().for_each(|a| a.each_mut(f)),
            Ty::Fn(t) => t.each_mut(f),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Text
            | Ty::Unit
            | Ty::Never
            | Ty::Float
            | Ty::Float32
            | Ty::Buf
            | Ty::Union(_)
            | Ty::Param(_)
            | Ty::Shown => {}
        }
    }
}

impl FnTy {
    fn each_mut(&mut self, f: &mut dyn FnMut(&mut Ty)) {
        self.params.iter_mut().for_each(|p| p.each_mut(f));
        self.ret.each_mut(f);
    }
}

impl Pat {
    /// Calls `f` on the type of each name the pattern binds.
    pub fn tys_mut(&mut self, f: &mut dyn FnMut(&mut Ty)) {
        match self {
            Pat::Bind(_, t) => t.each_mut(f),
            Pat::Ctor { fields, .. } => fields.iter_mut().for_each(|p| p.tys_mut(f)),
            Pat::Variant { pat, .. } => pat.tys_mut(f),
            Pat::Wild | Pat::Int(_) | Pat::Nat(_) | Pat::Bool(_) | Pat::Text(_) => {}
        }
    }
}

impl OperationInstance {
    fn tys_mut(&mut self, f: &mut dyn FnMut(&mut Ty)) {
        self.type_args.iter_mut().for_each(|t| t.each_mut(f));
        self.params.iter_mut().for_each(|t| t.each_mut(f));
        self.answer.each_mut(f);
    }
}

impl OpArm {
    /// Calls `f` on every type the arm writes (`Expr::tys_mut`).
    pub fn tys_mut(&mut self, f: &mut dyn FnMut(&mut Ty)) {
        if let Some(i) = &mut self.instance {
            i.tys_mut(f);
        }
        self.params.iter_mut().for_each(|t| t.each_mut(f));
        self.pats.iter_mut().for_each(|p| p.tys_mut(f));
        if let Some(g) = &mut self.guard {
            g.tys_mut(f);
        }
        self.body.tys_mut(f);
        self.k_ans.each_mut(f);
    }
}

impl Block {
    fn tys_mut(&mut self, f: &mut dyn FnMut(&mut Ty)) {
        for s in &mut self.stmts {
            s.tys_mut(f);
        }
        if let Some(t) = &mut self.tail {
            t.tys_mut(f);
        }
    }
}

impl Stmt {
    fn tys_mut(&mut self, f: &mut dyn FnMut(&mut Ty)) {
        match self {
            Stmt::Let { ty, init, .. } | Stmt::Var { ty, init, .. } => {
                ty.each_mut(f);
                init.tys_mut(f);
            }
            Stmt::Assign { target, value, .. } => {
                target.ty.each_mut(f);
                value.tys_mut(f);
            }
            Stmt::Expr(e) => e.tys_mut(f),
            Stmt::While { cond, body, .. } => {
                cond.tys_mut(f);
                body.tys_mut(f);
            }
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    v.tys_mut(f);
                }
            }
        }
    }
}

impl Expr {
    /// Calls `f` on every type written in `self`: of each expression, local,
    /// pattern, place, closure and arm in it (`Ty::each_mut` on each).
    pub fn tys_mut(&mut self, f: &mut dyn FnMut(&mut Ty)) {
        self.ty.each_mut(f);
        match &mut self.kind {
            ExprKind::FnValue { targs, .. } => targs.iter_mut().for_each(|t| t.each_mut(f)),
            ExprKind::Call(c) => {
                if let Callee::Value(v) = &mut c.callee {
                    v.tys_mut(f);
                }
                c.args.iter_mut().for_each(|a| a.tys_mut(f));
                c.targs.iter_mut().for_each(|t| t.each_mut(f));
                c.unwind.iter_mut().for_each(|s| s.tys_mut(f));
            }
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => args.iter_mut().for_each(|a| a.tys_mut(f)),
            ExprKind::Not(a)
            | ExprKind::TempRef(a)
            | ExprKind::Shown(a)
            | ExprKind::Unreachable(a)
            | ExprKind::FnCast(a) => a.tys_mut(f),
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                a.tys_mut(f);
                b.tys_mut(f);
            }
            ExprKind::Ctor { fields, .. } => fields.iter_mut().for_each(|(_, e)| e.tys_mut(f)),
            ExprKind::Field { base, .. } => base.tys_mut(f),
            ExprKind::Match(m) => {
                m.scrut.tys_mut(f);
                for a in &mut m.arms {
                    a.pat.tys_mut(f);
                    if let Some(g) = &mut a.guard {
                        g.tys_mut(f);
                    }
                    a.body.tys_mut(f);
                }
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                cond.tys_mut(f);
                then.tys_mut(f);
                if let Some(o) = otherwise {
                    o.tys_mut(f);
                }
            }
            ExprKind::Block(b) => b.tys_mut(f),
            ExprKind::Closure(c) => {
                c.params.iter_mut().for_each(|(_, t)| t.each_mut(f));
                c.ret.each_mut(f);
                c.fn_ty.each_mut(f);
                c.body.tys_mut(f);
            }
            ExprKind::Perform(p) => {
                if let Some(i) = &mut p.instance {
                    i.tys_mut(f);
                }
                p.args.iter_mut().for_each(|a| a.tys_mut(f));
                p.result.each_mut(f);
                p.unwind.iter_mut().for_each(|s| s.tys_mut(f));
            }
            ExprKind::Handle(h) => {
                h.body.tys_mut(f);
                h.body_ty.each_mut(f);
                h.result.each_mut(f);
                if let Some(t) = &mut h.host_ret {
                    t.each_mut(f);
                }
                if let Some(r) = &mut h.ret {
                    r.pat.tys_mut(f);
                    r.body.tys_mut(f);
                }
                for a in h.direct.iter_mut().chain(&mut h.aborts).chain(&mut h.susp) {
                    a.tys_mut(f);
                }
            }
            ExprKind::Inject { value, .. } | ExprKind::Deref { value, .. } => value.tys_mut(f),
            ExprKind::Remap { to, value, .. } => {
                to.each_mut(f);
                value.tys_mut(f);
            }
            ExprKind::Ref(p) | ExprKind::RefMut(p) => p.ty.each_mut(f),
            ExprKind::Budget(b) => {
                b.steps.tys_mut(f);
                b.body.tys_mut(f);
            }
            ExprKind::Declaration(_)
            | ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Text(_)
            | ExprKind::Read { .. } => {}
        }
    }
}
