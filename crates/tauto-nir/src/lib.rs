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

pub use tauto::types::{Kind, OperationAdmission, Quant, Width};
pub use tauto_parol::Span;

mod borrow;
pub mod cps;
mod last_use;
mod lower;
mod tail;
pub use lower::{
    CompileError, CompilePhase, LowerInput, Lowered, compile, compile_javascript,
    compile_javascript_with_observer, compile_loaded_with_observer, compile_with,
    compile_with_observer, lower,
};
pub use tail::{mark as mark_tail_calls, passed_on, recurs};

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

/// A form the generator does not write.
#[derive(Debug, Clone, PartialEq)]
pub struct Unsupported {
    pub what: String,
    pub span: Option<Span>,
}

impl std::fmt::Display for Unsupported {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let m = msg!("nir-unsupported", what = self.what.as_str());
        write!(f, "{m}")
    }
}

/// The Rust shape of a tauto type.
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
    Std(String, Vec<Ty>),
    /// `HashMap(K, V)`: `tauto_rt::stdlib::HashMap`, in insertion order as
    /// the evaluator's is.
    HashMap(Box<Ty>, Box<Ty>),
    /// `Slice(A)`, behind a borrow only: `[A]`.
    Slice(Box<Ty>),
    Option(Box<Ty>),
    Result(Box<Ty>, Box<Ty>),
    /// `Pair(A, B)`: a tuple.
    Pair(Box<Ty>, Box<Ty>),
    /// A struct or enum the generator writes (the program's and the
    /// library's: `List`, `Map`).
    Data(String, Vec<Ty>),
    /// A union's enum.
    Union(UnionId),
    /// A product: a tuple of its members in `types.rs`'s order, each with
    /// its type as `types.rs` writes it, by which the members are told apart
    /// (tags are not in the Rust type).
    Product(Vec<(String, Ty)>),
    /// A type parameter.
    Param(String),
    Fn(Box<FnTy>),
    /// `&A` and `&mut A`.
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
    /// Left to Rust to infer: `_`.
    Infer,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FnTy {
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub kind: Kind,
    pub tier: Tier,
}

impl Ty {
    /// The content of a `var` shared with closures.
    pub fn shared_var(&self) -> Option<&Ty> {
        match self {
            Ty::SharedVar(_, a) => Some(a),
            _ => None,
        }
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Ty::Unit)
    }

    /// Whether the type mentions a type that Rust cannot infer.
    pub fn has_infer(&self) -> bool {
        match self {
            Ty::Infer => true,
            Ty::Vec(a)
            | Ty::Array(a)
            | Ty::Slice(a)
            | Ty::Option(a)
            | Ty::Ref(a)
            | Ty::RefMut(a)
            | Ty::Info(a)
            | Ty::BudgetAnswer(a) => a.has_infer(),
            Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => a.has_infer() || b.has_infer(),
            Ty::Product(ms) => ms.iter().any(|(_, m)| m.has_infer()),
            Ty::Data(_, args) | Ty::Std(_, args) => args.iter().any(Ty::has_infer),
            Ty::Fn(f) => f.params.iter().any(Ty::has_infer) || f.ret.has_infer(),
            _ => false,
        }
    }

    /// The type parameters it mentions.
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
            Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => {
                a.params(out);
                b.params(out);
            }
            Ty::Product(ms) => ms.iter().for_each(|(_, m)| m.params(out)),
            Ty::Data(_, args) | Ty::Std(_, args) => args.iter().for_each(|a| a.params(out)),
            Ty::Fn(f) => {
                f.params.iter().for_each(|a| a.params(out));
                f.ret.params(out);
            }
            _ => {}
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
    /// Whether the field is stored behind an indirection.
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
    pub name: String,
    pub fields: Vec<FieldDef>,
}

#[derive(Debug, Clone)]
pub struct DataDef {
    pub name: String,
    pub generics: Vec<String>,
    pub kind: Kind,
    pub is_struct: bool,
    pub ctors: Vec<CtorDef>,
    /// `#[derive(Clone)]`: every kind but `linear` and the opaque affine ones.
    pub clone: bool,
    /// `#[derive(Clone, Copy)]`.
    pub copy: bool,
    /// A `bomb` field in each constructor.
    pub linear: bool,
    /// A `view struct`: its Rust type has a lifetime.
    pub view: bool,
    /// An extern type (`extern { type T }`): the host's type, bound by the
    /// backend's configuration; only extern functions make its values.
    pub host: bool,
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
    pub name: String,
    pub quant: Quant,
    pub generics: Vec<String>,
    pub params: Vec<Ty>,
    pub result: Ty,
}

/// What a type parameter must be, besides `'static`, for the instance to
/// compile.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Bound {
    Clone,
    Show,
    Eq,
    /// A key of `HashMap`: `DecEq` and `Hash`.
    Hash,
}

#[derive(Debug, Clone)]
pub struct FnInst {
    pub id: InstId,
    /// The name in the tauto source.
    pub source: String,
    pub rust_name: String,
    pub tier: Tier,
    pub generics: Vec<(String, BTreeSet<Bound>)>,
    pub params: Vec<Param>,
    pub ret: Ty,
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
    /// A mutable borrow (Rust: `&mut T`).
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
    /// The value itself, owned by the local.
    Owned,
    /// A `var` captured by a closure that may outlive it: one place shared
    /// by the function and its closures.
    SharedVar,
    /// A shared borrow of a value the local does not own.
    Borrow,
    /// A mutable borrow.
    BorrowMut,
    /// A borrowed function (`&f` of function type).
    BorrowedFn,
    /// A closure that holds borrows, so it does not outlive them.
    BorrowingClosure,
}

impl Storage {
    /// Whether the local refers to a value it does not own.
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

/// How a name is used as a value.
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cmp {
    Lt,
    Gt,
    Le,
    Ge,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Unit,
    Int(i128),
    /// A `Float` literal's value.
    Float(f64),
    Bool(bool),
    Text(String),
    Read {
        local: Local,
        how: Use,
    },
    /// A named function used as a value.
    FnValue {
        inst: InstId,
        /// The checked arguments in the declaration's generic order.
        targs: Vec<Ty>,
    },
    Call(Box<CallNode>),
    Arith {
        op: Arith,
        args: Vec<Expr>,
        width: Width,
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
    /// A product: the members are evaluated in the order written, and the
    /// tuple takes, for each of its members in order, `members[i]` or, with
    /// `Some(j)`, member `j` of the product `members[i]`.
    Product {
        members: Vec<Expr>,
        picks: Vec<(usize, Option<usize>)>,
    },
    /// Member `index` of a product, moved out of a temporary, or copied or
    /// cloned out of a place.
    Member {
        value: Box<Expr>,
        index: usize,
        how: Use,
    },
    /// A union to a union with more members, or to one member's type.
    Remap {
        from: UnionId,
        to: Ty,
        value: Box<Expr>,
    },
    /// `&place` and `&mut place`.
    Ref(Place),
    RefMut(Place),
    /// A borrow of a value that is not a place: `&(e)`.
    TempRef(Box<Expr>),
    /// `*e` of a borrow, or the value `e` borrows, copied or cloned.
    Deref {
        value: Box<Expr>,
        how: Use,
    },
    /// A shown value (`Shown`) made of `value`.
    Shown(Box<Expr>),
    /// `budget(steps: n) { body }`.
    Budget(Box<BudgetNode>),
    /// A value of type `Never`.
    Unreachable(Box<Expr>),
    /// A function that may be called any number of times, as one that is
    /// called once.
    FnCast(Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct BudgetNode {
    pub id: u32,
    /// `budget(memory: n)`: `steps` is a count of cells.
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
    pub name: String,
    pub index: usize,
    /// The constructor's fields, which are stored boxed.
    pub indirect: Vec<Indirect>,
    pub linear: bool,
    /// Field names, `None` for a positional constructor.
    pub fields: Vec<Option<String>>,
    pub nullary: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DataRef {
    /// A generated type, by name.
    Gen(String),
    Option,
    Result,
    Pair,
    /// A product, matched by `#(…)`: its members in the product's order.
    Product,
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
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Callee {
    Inst(InstId),
    /// A function of `tauto_rt::stdlib`, by name.
    Builtin(String),
    /// An `extern` of the program: its wrapper in `externs`, by name.
    Extern(String),
    Local(Local),
    /// The continuation `k` of an arm of a suspending operation.
    Cont(Local),
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
    /// The operation's payload type (a tuple of its parameters).
    pub params: Vec<Ty>,
    pub pats: Vec<Pat>,
    pub guard: Option<Expr>,
    /// For a `direct` operation: the arm with each `k(e)` replaced by `e`.
    pub body: Expr,
    /// For an arm of an operation that resumes: the continuation `k`, and the
    /// type of the answer it takes.
    pub k: Option<Local>,
    pub k_ans: Ty,
    pub span: Span,
}

/// How an extern's parameter is passed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pass {
    Value,
    Ref,
    RefMut,
}

#[derive(Debug, Clone)]
pub struct ExternDef {
    pub name: String,
    pub generics: Vec<String>,
    pub params: Vec<(String, Ty, Pass)>,
    pub ret: Ty,
    pub span: Span,
}

/// The program: what the generator writes.
#[derive(Debug, Clone, Default)]
pub struct Package {
    /// File boundaries and macro origins for compiled totes.
    pub sources: Option<tauto::program::SourceMap>,
    /// Runtime syntax parsers with validated, self-contained tables.
    pub syntax_parsers: Vec<SyntaxParser>,
    pub datas: Vec<DataDef>,
    pub unions: Vec<UnionDef>,
    pub ops: Vec<OpDef>,
    pub fns: Vec<FnInst>,
    pub top: Option<InstId>,
    /// The functions a Rust crate may call (`compile_with` `lib`).
    pub exports: Vec<Export>,
    /// The `extern` functions the program declares, in the order written.
    pub externs: Vec<ExternDef>,
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
}

/// A runtime parser whose syntax name and grammar identity are known at build time.
#[derive(Debug, Clone)]
pub struct SyntaxParser {
    pub name: String,
    pub sha: String,
    pub tables: String,
    pub result: Ty,
}

/// A function of a tote that Rust may call.
#[derive(Debug, Clone)]
pub struct Export {
    pub inst: InstId,
    pub name: String,
    /// The effects the function performs.
    pub row: Vec<String>,
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
            ExprKind::Product { members, .. } => members.iter_mut().collect(),
            ExprKind::Field { base, .. } => vec![&mut **base],
            ExprKind::Perform(p) => p.args.iter_mut().collect(),
            ExprKind::Inject { value, .. }
            | ExprKind::Remap { value, .. }
            | ExprKind::Member { value, .. }
            | ExprKind::Deref { value, .. } => {
                vec![&mut **value]
            }
            _ => Vec::new(),
        }
    }

    /// Calls `f` on this expression and its value subexpressions, outer first,
    /// including closure bodies. Assignment places and suspending handler arms
    /// are excluded; callers that need them must traverse them separately.
    pub fn walk(&self, f: &mut dyn FnMut(&Expr)) {
        f(self);
        self.children(&mut |child| child.walk(f));
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
            ExprKind::Product { members, .. } => members.iter().for_each(|e| f(e)),
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
            | ExprKind::Member { value, .. }
            | ExprKind::Deref { value, .. } => f(value),
            _ => {}
        }
    }
}
