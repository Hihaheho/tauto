//! NIR as text: `print` writes a package, `parse` reads one back.
//!
//! The text says everything a package holds except where its nodes came
//! from (`Span`, `Package::sources`): a package read back prints as the
//! same text, and a node read from text has the span it is written at.
//! `docs/design/nir-text.md` defines the form.
//!
//! The printer's output is the one way to write a package. `parse` reads
//! any layout of it; a test that takes text as its input asks that printing
//! what it read gives the text again.

mod lex;
mod parse;
mod print;
mod same;

pub use parse::{ParseError, parse, parse_blocks};
pub use print::{print, print_blocks, print_data, print_evidence, print_expr, print_fn};
pub use same::{same, same_blocks};

use crate::*;

/// The words the text reserves: a name spelled as one of them is quoted.
/// They are the words a type, an expression or a statement starts with, and
/// the ones written before a name where the name may be left out.
pub(crate) const KEYWORDS: &[&str] = &[
    // Types.
    "i8",
    "i16",
    "u8",
    "u16",
    "u32",
    "u64",
    "uhost",
    "i32",
    "i64",
    "nat",
    "Bool",
    "Text",
    "Unit",
    "Never",
    "Float",
    "Float32",
    "Buf",
    "Shown",
    "Vec",
    "Array",
    "Slice",
    "Option",
    "Info",
    "BudgetAnswer",
    "Result",
    "Pair",
    "SharedVar",
    "std",
    "union",
    "fn",
    // Expressions.
    "true",
    "false",
    "nan",
    "inf",
    "declaration",
    "add",
    "sub",
    "mul",
    "neg",
    "div",
    "lt",
    "gt",
    "le",
    "ge",
    "eq",
    "ne",
    "not",
    "and",
    "or",
    "extern",
    "builtin",
    "resume",
    "match",
    "if",
    "closure",
    "perform",
    "handle",
    "inject",
    "remap",
    "tempref",
    "deref",
    "shown",
    "budget",
    "unreachable",
    "fncast",
    "move",
    "copy",
    "clone",
    // Statements.
    "let",
    "var",
    "set",
    "while",
    "return",
    // Before a name.
    "shared",
    "unique",
    "ref",
    "refmut",
];

/// Whether a character continues an identifier.
pub(crate) fn ident_continue(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

pub(crate) fn ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_ident(s: &str) -> bool {
    let mut cs = s.chars();
    cs.next().is_some_and(ident_start) && cs.all(ident_continue) && s != "_"
}

/// Whether a name is written as it is: identifiers joined by `::`, not a
/// reserved word. Any other name is written as a string.
pub(crate) fn is_bare(name: &str) -> bool {
    name.split("::").all(is_ident) && !KEYWORDS.contains(&name)
}

pub(crate) fn width_word(w: Width) -> &'static str {
    match w {
        Width::W8 => "i8",
        Width::W16 => "i16",
        Width::W32 => "i32",
        Width::W64 => "i64",
        Width::U8 => "u8",
        Width::U16 => "u16",
        Width::U32 => "u32",
        Width::U64 => "u64",
        Width::Host => "uhost",
        Width::Nat => "nat",
    }
}

pub(crate) fn width_of(word: &str) -> Option<Width> {
    Some(match word {
        "i8" => Width::W8,
        "i16" => Width::W16,
        "i32" => Width::W32,
        "i64" => Width::W64,
        "u8" => Width::U8,
        "u16" => Width::U16,
        "u32" => Width::U32,
        "u64" => Width::U64,
        "uhost" => Width::Host,
        "nat" => Width::Nat,
        _ => return None,
    })
}

/// The numbers of an arithmetic operation, spelled as their type.
pub(crate) fn num_word(n: Num) -> &'static str {
    match n {
        Num::Int(w) => width_word(w),
        Num::Float => "Float",
        Num::Float32 => "Float32",
    }
}

pub(crate) fn num_of(word: &str) -> Option<Num> {
    Some(match word {
        "Float" => Num::Float,
        "Float32" => Num::Float32,
        w => Num::Int(width_of(w)?),
    })
}

pub(crate) fn tier_word(t: Tier) -> &'static str {
    match t {
        Tier::S => "S",
        Tier::A => "A",
        Tier::O => "O",
        Tier::M => "M",
    }
}

pub(crate) fn tier_of(word: &str) -> Option<Tier> {
    Some(match word {
        "S" => Tier::S,
        "A" => Tier::A,
        "O" => Tier::O,
        "M" => Tier::M,
        _ => return None,
    })
}

pub(crate) const STD_TYPES: &[StdType] = &[
    StdType::SynDeclaration,
    StdType::Ref,
    StdType::Weak,
    StdType::Mutex,
    StdType::MutexGuard,
    StdType::Atomic,
    StdType::Bytes,
    StdType::Pending,
    StdType::Secret,
    StdType::Signal,
    StdType::CancelSource,
    StdType::Region,
    StdType::Place,
    StdType::RcRegion,
    StdType::RcPlace,
    StdType::Slots,
    StdType::OpaqueHost,
];

pub(crate) fn repr_word(r: Repr) -> &'static str {
    match r {
        Repr::Plain => "plain",
        Repr::SharedVar(false) => "sharedvar",
        Repr::SharedVar(true) => "sharedvar_copy",
        Repr::Ref => "ref",
        Repr::RefMut => "refmut",
        Repr::BorrowClosure => "borrowclosure",
        Repr::FnRef => "fnref",
    }
}

pub(crate) fn repr_of(word: &str) -> Option<Repr> {
    Some(match word {
        "plain" => Repr::Plain,
        "sharedvar" => Repr::SharedVar(false),
        "sharedvar_copy" => Repr::SharedVar(true),
        "ref" => Repr::Ref,
        "refmut" => Repr::RefMut,
        "borrowclosure" => Repr::BorrowClosure,
        "fnref" => Repr::FnRef,
        _ => return None,
    })
}

pub(crate) fn use_word(u: Use) -> Option<&'static str> {
    match u {
        Use::Move => Some("move"),
        Use::Copy => Some("copy"),
        Use::Clone => Some("clone"),
        Use::Place => None,
    }
}

pub(crate) fn use_of(word: &str) -> Option<Use> {
    Some(match word {
        "move" => Use::Move,
        "copy" => Use::Copy,
        "clone" => Use::Clone,
        _ => return None,
    })
}

pub(crate) fn bound_word(b: Bound) -> &'static str {
    match b {
        Bound::Clone => "Clone",
        Bound::Show => "Show",
        Bound::Eq => "Eq",
        Bound::Static => "Static",
    }
}

pub(crate) fn bound_of(word: &str) -> Option<Bound> {
    Some(match word {
        "Clone" => Bound::Clone,
        "Show" => Bound::Show,
        "Eq" => Bound::Eq,
        "Static" => Bound::Static,
        _ => return None,
    })
}

pub(crate) const ADMISSIONS: &[(OperationAdmission, &str)] = &[
    (OperationAdmission::Legacy, "legacy"),
    (OperationAdmission::Unique, "unique"),
    (OperationAdmission::Incomplete, "incomplete"),
    (OperationAdmission::ExplicitReturn, "explicit_return"),
    (OperationAdmission::Missing, "missing"),
    (OperationAdmission::Indeterminate, "indeterminate"),
    (OperationAdmission::Distinct, "distinct"),
    (OperationAdmission::Unresolved, "unresolved"),
];

pub(crate) fn arith_word(op: Arith) -> &'static str {
    match op {
        Arith::Add => "add",
        Arith::Sub => "sub",
        Arith::Mul => "mul",
        Arith::Neg => "neg",
        Arith::Div => "div",
    }
}

pub(crate) fn cmp_word(op: Cmp) -> &'static str {
    match op {
        Cmp::Lt => "lt",
        Cmp::Gt => "gt",
        Cmp::Le => "le",
        Cmp::Ge => "ge",
    }
}

/// The constructors of the library's `Option`, `Result` and `Pair`, which
/// no data type of a package declares: the name of each, the data it
/// belongs to and its index.
pub(crate) const LIBRARY_CTORS: &[(&str, DataRef, usize)] = &[
    ("Option::None", DataRef::Option, 0),
    ("Option::Some", DataRef::Option, 1),
    ("Result::Ok", DataRef::Result, 0),
    ("Result::Err", DataRef::Result, 1),
    ("Pair::Mk", DataRef::Pair, 0),
];

/// The type a use of a local shows: the type the local was bound with, and
/// for a local that is a borrow, what it borrows.
pub(crate) fn local_ty(repr: Repr, bound: &Ty) -> Ty {
    match (repr, bound) {
        (Repr::Ref | Repr::RefMut | Repr::FnRef, Ty::Ref(t) | Ty::RefMut(t)) => (**t).clone(),
        _ => bound.clone(),
    }
}

/// The type an expression has when the text writes none for it: what the
/// text of the expression itself shows. `bound` gives the type a use of a
/// local shows (`local_ty`).
pub(crate) fn default_ty(kind: &ExprKind, bound: &dyn Fn(&Local) -> Option<Ty>) -> Option<Ty> {
    Some(match kind {
        ExprKind::Unit => Ty::Unit,
        ExprKind::Bool(_) | ExprKind::Cmp { .. } | ExprKind::Eq { .. } => Ty::Bool,
        ExprKind::Not(_) | ExprKind::And(..) | ExprKind::Or(..) => Ty::Bool,
        ExprKind::Text(_) => Ty::Text,
        ExprKind::Float(_) => Ty::Float,
        ExprKind::Read { local, .. } => return bound(local),
        ExprKind::Arith { num, .. } => num.ty(),
        ExprKind::Match(m) => m.arms.first()?.body.ty.clone(),
        ExprKind::If { then, .. } => then.ty.clone(),
        ExprKind::Block(b) => match &b.tail {
            Some(t) => t.ty.clone(),
            None => Ty::Unit,
        },
        ExprKind::Closure(c) => Ty::Fn(Box::new(c.fn_ty.clone())),
        ExprKind::Perform(p) => p.result.clone(),
        ExprKind::Handle(h) => h.result.clone(),
        ExprKind::Inject { union, .. } => Ty::Union(*union),
        ExprKind::Remap { to, .. } => to.clone(),
        ExprKind::Ref(p) => Ty::Ref(Box::new(p.ty.clone())),
        ExprKind::RefMut(p) => Ty::RefMut(Box::new(p.ty.clone())),
        ExprKind::TempRef(e) => Ty::Ref(Box::new(e.ty.clone())),
        ExprKind::Shown(_) => Ty::Shown,
        ExprKind::Budget(b) => b.body.ty.clone(),
        // These write their type themselves.
        ExprKind::Int(_)
        | ExprKind::Declaration(_)
        | ExprKind::FnValue { .. }
        | ExprKind::Call(_)
        | ExprKind::Ctor { .. }
        | ExprKind::Field { .. }
        | ExprKind::Deref { .. }
        | ExprKind::Unreachable(_)
        | ExprKind::FnCast(_) => return None,
    })
}

/// Whether the text of the node ends with its type (`…: T`).
pub(crate) fn writes_ty(kind: &ExprKind) -> bool {
    matches!(
        kind,
        ExprKind::Declaration(_)
            | ExprKind::FnValue { .. }
            | ExprKind::Call(_)
            | ExprKind::Ctor { .. }
            | ExprKind::Field { .. }
            | ExprKind::Deref { .. }
            | ExprKind::Unreachable(_)
            | ExprKind::FnCast(_)
    )
}
