//! Value types of executable code, by the rules of `docs/design/nib.md`: sized
//! integers (`i32`, `i64`, `u8`, `u32`, `u64`), `Bool`, `Text`, `Unit`,
//! `Never`, functions, unions, tags, and `struct`s and `enum`s. Directly
//! determined operation instances share inference; `rows.rs` checks effect rows.
//!
//! Inference is by unification. An integer literal is an integer of a width
//! not yet known, `i64` unless something fixes it. Where a value meets a
//! written type (a parameter, a result, a `let` with a type) it must *fit*
//! it: be equivalent to it, forget tags, or be injected into a union. Nothing
//! is converted: `i32` does not fit `i64`.
//!
//! - Integer `/` is a type error; `div(a, b)` and `mod(a, b)` divide.
//! - A `handle` gives the union of the types of its arms and of its `return`
//!   arm (or of its body when there is none).
//! - `budget(steps: n) { body }` has the body's type `T`; an `exceeded(info), k`
//!   arm gets `k: (T) -> H` and `info.more(m)`, `info.unbounded()` of type `H`,
//!   `H` the handle's result type.
//! - `show<A>(name: Text, value: A): Unit` is the host's operation, declared
//!   everywhere.
//!
//! Kinds, borrows and resume quantities:
//! every type has a [`Kind`]; a declaration may bound it (`affine struct
//! File {}`), never loosen it. A function type carries its kind (`affine
//! (A) -> B`, `shared` when none is written), a closure the join of what it
//! captures, and a continuation the one its operation's [`Quant`] gives. A
//! borrow (`&A`, `&mut A`) is a type only of parameters, of what `: &A`
//! returns and of the names `let &x` binds; where a borrow may stand is
//! checked here when it is a matter of types, and by `lin.rs` when it is a
//! matter of use.
//!
//! Not checked here: `Decimal` and `Float` arithmetic beyond `+ - * /`, and
//! `budget`s whose `exceeded` escapes through a call.

use crate::surface::Name;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::OnceLock;

use crate::surface::qualify::written;
use tauto_message::{Message, msg};
use tauto_parol::Span;

mod operation_instances;
mod references;
mod type_functions;
use operation_instances::{ArmObservation, BodyOperations};
pub use operation_instances::{CheckedOperationInstance, OperationAdmission, OperationFacts};
pub use type_functions::expand_type_functions;

use crate::surface::{
    BudgetLimit, DataDecl, EffectDecl, FnDecl, Handler, MatchArm, Pattern, Program, Stmt,
    SurfaceTerm, TermId, TermKind,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Width {
    W32,
    W64,
    U8,
    U32,
    U64,
    Nat,
}

impl Width {
    pub fn fits(self, n: i128) -> bool {
        match self {
            Width::W32 => i32::try_from(n).is_ok(),
            Width::W64 => i64::try_from(n).is_ok(),
            Width::U8 => u8::try_from(n).is_ok(),
            Width::U32 => u32::try_from(n).is_ok(),
            Width::U64 => u64::try_from(n).is_ok(),
            Width::Nat => n >= 0,
        }
    }
}

/// How freely a value may be copied and dropped: `copy ⊑ shared ⊑ affine ⊑
/// linear`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Kind {
    Copy,
    Shared,
    Affine,
    Linear,
}

impl Kind {
    pub fn join(self, other: Kind) -> Kind {
        self.max(other)
    }

    /// Copied and dropped freely: `copy` or `shared`.
    pub fn dup(self) -> bool {
        self <= Kind::Shared
    }

    pub fn parse(word: &str) -> Option<Kind> {
        Some(match word {
            "copy" => Kind::Copy,
            "shared" => Kind::Shared,
            "affine" => Kind::Affine,
            "linear" => Kind::Linear,
            _ => return None,
        })
    }

    /// `(k₁)->k₂`, the bound of a type constructor variable: what it takes
    /// and what it makes.
    pub fn parse_ctor(word: &str) -> Option<(Kind, Kind)> {
        let rest = word.strip_prefix('(')?;
        let (arg, result) = rest.split_once(")->")?;
        Some((Kind::parse(arg)?, Kind::parse(result)?))
    }

    /// `self` may stand where `bound` is expected; the two duplicable kinds
    /// differ only in their run-time cost.
    pub fn fits(self, bound: Kind) -> bool {
        self <= bound || (self.dup() && bound.dup())
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Kind::Copy => "copy",
            Kind::Shared => "shared",
            Kind::Affine => "affine",
            Kind::Linear => "linear",
        })
    }
}

/// How many times an arm may call its continuation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Quant {
    /// `resume 0`: the arm has no `k`.
    Zero,
    /// `resume <=1`, the default.
    AtMostOne,
    /// `resume 1`.
    One,
    /// `resume ω`.
    Many,
    /// `direct`: the arm continues with `k(e)` at the end of every path.
    Direct,
}

impl Quant {
    pub fn parse(written: &str) -> Option<Quant> {
        Some(match written {
            "0" => Quant::Zero,
            "<=1" => Quant::AtMostOne,
            "1" => Quant::One,
            "ω" => Quant::Many,
            "direct" => Quant::Direct,
            _ => return None,
        })
    }

    /// The kind of `k`: `<=1` an affine function, `1` a linear one, `ω` a
    /// duplicable one.
    pub fn continuation_kind(self) -> Kind {
        match self {
            Quant::Zero | Quant::AtMostOne => Kind::Affine,
            Quant::One | Quant::Direct => Kind::Linear,
            Quant::Many => Kind::Shared,
        }
    }
}

impl fmt::Display for Quant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Quant::Zero => "0",
            Quant::AtMostOne => "<=1",
            Quant::One => "1",
            Quant::Many => "ω",
            Quant::Direct => "direct",
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Ty {
    Int(Width),
    Bool,
    Text,
    Unit,
    Never,
    Decimal,
    Float,
    Float32,
    /// Parameters (a borrowed one is a [`Ty::Borrow`]), result, and the
    /// function's kind.
    Fn(Vec<Ty>, Box<Ty>, Kind),
    /// Two or more members, flattened, sorted and without repeats.
    Union(Vec<Ty>),
    /// A non-empty set of tags on a type that is not tagged itself.
    Tagged(BTreeSet<String>, Box<Ty>),
    /// A declared type, or a type nothing declares.
    Named(Name, Vec<Ty>),
    /// A type parameter inside its declaration, with its bound.
    Param(Param, Kind),
    /// What an `exceeded` arm receives; `more` and `unbounded` give the type.
    Info(Box<Ty>),
    /// `&A` (`false`) or `&mut A` (`true`): a borrowed parameter, what
    /// `: &A` returns, a name `let &x` binds.
    Borrow(Box<Ty>, bool),
    Var(usize),
    /// `<A, B>(…) -> …`: a function that takes its type parameters at each
    /// call. Only the expansion makes one: the
    /// dictionary of a method that has generics of its own.
    Poly(Vec<(Param, Kind)>, Box<Ty>),
    /// `F(X)`: a type constructor that is not known yet (a variable, or a
    /// parameter of the declaration) applied to its last argument. It reads
    /// as `Named` once the constructor is.
    App(Box<Ty>, Box<Ty>),
}

impl Ty {
    pub fn unborrowed(&self) -> &Ty {
        match self {
            Ty::Borrow(t, _) => t.unborrowed(),
            t => t,
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = |f: &mut fmt::Formatter<'_>, ts: &[Ty], sep: &str| {
            for (i, t) in ts.iter().enumerate() {
                if i > 0 {
                    write!(f, "{sep}")?;
                }
                write!(f, "{t}")?;
            }
            Ok(())
        };
        match self {
            Ty::Int(Width::W32) => write!(f, "i32"),
            Ty::Int(Width::W64) => write!(f, "i64"),
            Ty::Int(Width::U8) => write!(f, "u8"),
            Ty::Int(Width::U32) => write!(f, "u32"),
            Ty::Int(Width::U64) => write!(f, "u64"),
            Ty::Int(Width::Nat) => write!(f, "nat"),
            Ty::Bool => write!(f, "Bool"),
            Ty::Text => write!(f, "Text"),
            Ty::Unit => write!(f, "Unit"),
            Ty::Never => write!(f, "Never"),
            Ty::Decimal => write!(f, "Decimal"),
            Ty::Float => write!(f, "Float"),
            Ty::Float32 => write!(f, "Float32"),
            Ty::Fn(ps, r, k) => {
                if matches!(k, Kind::Affine | Kind::Linear) {
                    write!(f, "{k} ")?;
                }
                write!(f, "(")?;
                list(f, ps, ", ")?;
                write!(f, ") -> {r}")
            }
            Ty::Union(ts) => list(f, ts, " | "),
            // `Pair(A, B)` is `A × B`, and `Pair(A, Pair(B, C))` is `A × B × C`.
            Ty::Named(n, args) if is_pair_name(n) && args.len() == 2 => {
                let mut members = vec![&args[0]];
                let mut rest = &args[1];
                while let Ty::Named(n, args) = rest
                    && is_pair_name(n)
                    && args.len() == 2
                {
                    members.push(&args[0]);
                    rest = &args[1];
                }
                members.push(rest);
                for (i, t) in members.iter().enumerate() {
                    if i > 0 {
                        write!(f, " × ")?;
                    }
                    match t {
                        Ty::Union(_) | Ty::Fn(..) => write!(f, "({t})")?,
                        Ty::Named(n, args) if is_pair_name(n) && args.len() == 2 => {
                            write!(f, "({t})")?
                        }
                        _ => write!(f, "{t}")?,
                    }
                }
                Ok(())
            }
            Ty::Tagged(tags, t) => {
                for tag in tags {
                    write!(f, "@{tag} ")?;
                }
                write!(f, "{t}")
            }
            // A record without a name, `@record.a.b(A, B)`, as it is written: `{ a: A, b: B }`.
            Ty::Named(n, args)
                if let Some(fields) = tauto_surface::records::fields_of(&written(n))
                    && fields.len() == args.len() =>
            {
                write!(f, "{{ ")?;
                for (i, (field, t)) in fields.iter().zip(args).enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{field}: {t}")?;
                }
                write!(f, " }}")
            }
            Ty::Named(n, args) if args.is_empty() => write!(f, "{}", written(n)),
            Ty::Named(n, args) => {
                write!(f, "{}(", written(n))?;
                list(f, args, ", ")?;
                write!(f, ")")
            }
            Ty::Param(n, _) => write!(f, "{n}"),
            Ty::Info(t) => write!(f, "Info({t})"),
            Ty::Borrow(t, false) => write!(f, "&{t}"),
            Ty::Borrow(t, true) => write!(f, "&mut {t}"),
            Ty::Var(_) => write!(f, "_"),
            Ty::Poly(gs, t) => {
                let names: Vec<&str> = gs.iter().map(|(n, _)| n.name()).collect();
                write!(f, "<{}>{t}", names.join(", "))
            }
            Ty::App(h, x) => write!(f, "{h}({x})"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeError {
    pub message: tauto_message::Message,
    pub span: Span,
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (byte {})", self.message, self.span.start)
    }
}

/// A declared `struct` (one constructor, named as the type) or `enum`.
#[derive(Debug, Clone)]
pub struct Data {
    pub name: Name,
    pub declared: Option<Kind>,
    pub generics: Vec<Name>,
    pub constructors: Vec<DataCtor>,
    pub is_struct: bool,
    /// It holds itself, directly or through other declarations.
    pub recursive: bool,
    /// `kind(D(args))` is `base` joined with the kinds of the arguments for
    /// the generics in `holds` ([`Datas::summarize`]).
    pub base: Kind,
    pub holds: Vec<Name>,
    /// Declared by the prelude and implemented by the evaluator (`Buf`,
    /// `Vec`, `HashMap`): its clone copies what it holds.
    pub builtin: bool,
    /// A `view struct`: an extern type that holds a borrow.
    pub view: bool,
}

#[derive(Debug, Clone)]
pub struct DataCtor {
    pub name: Name,
    /// Field types over the declaration's generics, as [`Ty::Param`]s.
    pub fields: Vec<(Option<String>, Ty)>,
}

#[derive(Debug, Clone, Default)]
pub struct Datas {
    pub decls: HashMap<Name, Data>,
    /// A constructor's name (`Some`, `Shape::Circle`) to its type and index.
    pub ctors: HashMap<Name, (Name, usize)>,
    /// All owners of an ambiguous unqualified constructor name.
    pub ambiguous_ctors: HashMap<Name, Vec<(Name, usize)>>,
}

impl Datas {
    /// Resolve a constructor by its owning result type, never declaration order.
    pub fn resolve_ctor(
        &self,
        name: &Name,
        expected: Option<&Ty>,
    ) -> Result<&(Name, usize), Message> {
        fn owner(t: &Ty) -> Option<&Name> {
            match t.unborrowed() {
                Ty::Named(n, _) => Some(n),
                Ty::Fn(_, r, _) => owner(r),
                _ => None,
            }
        }
        if let Some(c) = self.ctors.get(name) {
            return Ok(c);
        }
        if let Name::Selection(selection) = name {
            let candidates = selection
                .candidates()
                .iter()
                .filter_map(|reference| self.ctors.get(&Name::Global(reference.clone())))
                .collect::<Vec<_>>();
            let candidates: Vec<_> = match expected.and_then(owner) {
                Some(expected) => candidates
                    .into_iter()
                    .filter(|(family, _)| family == expected)
                    .collect(),
                None => candidates,
            };
            return match candidates.as_slice() {
                [candidate] => Ok(candidate),
                [] => Err(msg!("nibcheck-not-a-constructor", name = name.to_string())),
                _ => {
                    let mut names: Vec<_> = candidates
                        .iter()
                        .map(|(owner, index)| {
                            self.decls[owner].constructors[*index].name.to_string()
                        })
                        .collect();
                    names.sort();
                    names.dedup();
                    Err(msg!(
                        "nibcheck-ambiguous-constructor",
                        name = name.to_string(),
                        candidates = names.join(" or ")
                    ))
                }
            };
        }
        // A constructor written alone is one of the expected type's, as the kernel reads it: a
        // type declared in a module (`m::T`) has its constructors under its full name, `m::T::C`.
        if matches!(name, Name::Spelled(_)) && !name.contains("::") {
            if let Some(c) = expected
                .and_then(owner)
                .and_then(|n| self.ctors.get(&format!("{n}::{name}").into()))
            {
                return Ok(c);
            }
        }
        let Some(candidates) = self.ambiguous_ctors.get(name) else {
            return Err(msg!("nibcheck-not-a-constructor", name = name.to_string()));
        };
        if let Some(n) = expected.and_then(owner) {
            if let Some(c) = candidates.iter().find(|(d, _)| d == n) {
                return Ok(c);
            }
        }
        let mut names: Vec<_> = candidates
            .iter()
            .map(|(d, _)| format!("{}::{name}", written(d)))
            .collect();
        names.sort();
        Err(msg!(
            "nibcheck-ambiguous-constructor",
            name = name.to_string(),
            candidates = names.join(" or ")
        ))
    }

    pub fn has_ctor(&self, name: &Name) -> bool {
        self.ctors.contains_key(name)
            || self.ambiguous_ctors.contains_key(name)
            || matches!(name, Name::Selection(selection) if selection.candidates().iter().any(|reference| self.ctors.contains_key(&Name::Global(reference.clone()))))
    }

    pub fn nullary(&self, name: &Name, expected: Option<&Ty>) -> bool {
        let is_nullary = |(d, c): &(Name, usize)| {
            self.decls[d].constructors[*c].fields.is_empty() && !self.decls[d].is_struct
        };
        match self.resolve_ctor(name, expected) {
            Ok(c) => is_nullary(c),
            Err(_) => match name {
                Name::Selection(selection) => selection.candidates().iter().any(|reference| {
                    self.ctors
                        .get(&Name::Global(reference.clone()))
                        .is_some_and(is_nullary)
                }),
                _ => self
                    .ambiguous_ctors
                    .get(name)
                    .is_some_and(|cs| cs.iter().any(is_nullary)),
            },
        }
    }

    /// Every constructor `name` may be is one without fields: `name()` is
    /// then its value, as `name` is.
    pub fn only_nullary(&self, name: &Name) -> bool {
        let is_nullary = |(d, c): &(Name, usize)| {
            self.decls[d].constructors[*c].fields.is_empty() && !self.decls[d].is_struct
        };
        if let Name::Selection(selection) = name {
            let candidates: Vec<_> = selection
                .candidates()
                .iter()
                .filter_map(|reference| self.ctors.get(&Name::Global(reference.clone())))
                .collect();
            return !candidates.is_empty() && candidates.into_iter().all(is_nullary);
        }
        match self.ambiguous_ctors.get(name) {
            Some(cs) => cs.iter().all(is_nullary),
            None => self.ctors.get(name).is_some_and(is_nullary),
        }
    }

    fn register_ctor(&mut self, name: Name, owner: Name, index: usize) {
        let c = (owner, index);
        if let Some(cs) = self.ambiguous_ctors.get_mut(&name) {
            if let Some(old) = cs.iter_mut().find(|(d, _)| d == &c.0) {
                *old = c;
            } else {
                cs.push(c);
            }
        } else if let Some(old) = self.ctors.get(&name) {
            if old.0 != c.0 {
                self.ambiguous_ctors
                    .insert(name.clone(), vec![old.clone(), c]);
                self.ctors.remove(&name);
            } else {
                self.ctors.insert(name, c);
            }
        } else {
            self.ctors.insert(name, c);
        }
    }

    /// Whether a type holds a borrow of something that is not duplicable (a
    /// shared borrow of a duplicable value is the value): `Some(true)` when
    /// the borrow is `&mut`.
    pub fn view_borrow(&self, t: &Ty) -> Option<bool> {
        match t {
            Ty::Borrow(inner, m) => (*m || !self.kind(inner).dup()).then_some(*m),
            Ty::Named(n, args) => {
                if self.decls.get(n).is_some_and(|d| d.view) {
                    return Some(true);
                }
                if ["Option", "Result", "Pair"]
                    .iter()
                    .any(|native| tauto_surface::bindings::is_library(n, native))
                {
                    let mut found = None;
                    for a in args {
                        if let Some(m) = self.view_borrow(a) {
                            found = Some(found.unwrap_or(false) || m);
                        }
                    }
                    return found;
                }
                None
            }
            _ => None,
        }
    }

    /// `kind(T)` of `docs/design/ownership.md`, for a resolved type.
    pub fn kind(&self, t: &Ty) -> Kind {
        self.kind_in(t)
    }

    /// Whether `class` (a structural one: `PartialEq`, `DecEq`, `Hash`) holds
    /// of `t`, given the `(class, parameter)` pairs that are assumed.
    pub fn structural(&self, class: &str, t: &Ty, assume: &[(Name, Param)]) -> bool {
        self.structural_in(class, t, assume, &mut Vec::new())
    }

    fn structural_in(
        &self,
        class: &str,
        t: &Ty,
        assume: &[(Name, Param)],
        visiting: &mut Vec<Ty>,
    ) -> bool {
        match t {
            Ty::Int(_) | Ty::Bool | Ty::Text | Ty::Unit | Ty::Never => true,
            // NaN is not equal to itself, and a decimal's representation is
            // not settled.
            Ty::Decimal | Ty::Float | Ty::Float32 => class == "PartialEq",
            Ty::Fn(..) | Ty::Info(_) | Ty::Poly(..) => false,
            // `F(X)`: nothing is known of what `F` makes.
            Ty::App(..) => false,
            Ty::Union(ts) => ts
                .iter()
                .all(|t| self.structural_in(class, t, assume, visiting)),
            Ty::Tagged(_, t) | Ty::Borrow(t, _) => self.structural_in(class, t, assume, visiting),
            Ty::Param(n, _) => assume.iter().any(|(c, g)| {
                g == n
                    && (tauto_surface::bindings::is_library(c, class)
                        || (class == "PartialEq"
                            && tauto_surface::bindings::is_library(&c, "DecEq")))
            }),
            // Not known yet: checked when it is.
            Ty::Var(_) => true,
            Ty::Named(n, args) => {
                if tauto_surface::bindings::is_library(&n, "Buf") {
                    return true;
                }
                let Some(d) = self.decls.get(n) else {
                    return false;
                };
                let opaque = d.builtin
                    || (matches!(d.declared, Some(Kind::Affine | Kind::Linear))
                        && d.constructors.iter().all(|c| c.fields.is_empty()));
                if d.view || opaque {
                    return false;
                }
                // A type that holds itself is taken to have the class while
                // its fields are checked.
                if visiting.contains(t) {
                    return true;
                }
                visiting.push(t.clone());
                let map = d.instance(args);
                let ok = d.constructors.iter().all(|c| {
                    c.fields.iter().all(|(_, f)| {
                        self.structural_in(class, &substitute(f, &map), assume, visiting)
                    })
                });
                visiting.pop();
                ok
            }
        }
    }

    fn kind_in(&self, t: &Ty) -> Kind {
        match t {
            // A `nat` may be large: shared, as `Text` is.
            Ty::Int(Width::Nat) | Ty::Text => Kind::Shared,
            Ty::Int(_)
            | Ty::Bool
            | Ty::Unit
            | Ty::Never
            | Ty::Decimal
            | Ty::Float
            | Ty::Float32 => Kind::Copy,
            Ty::Fn(_, _, k) => *k,
            Ty::Poly(..) => Kind::Shared,
            // What `F` makes is bounded by the kind `F` is declared with.
            Ty::App(h, _) => match &**h {
                Ty::Param(_, k) => *k,
                _ => Kind::Copy,
            },
            Ty::Union(ts) => ts.iter().fold(Kind::Copy, |k, t| k.join(self.kind_in(t))),
            Ty::Tagged(_, t) | Ty::Borrow(t, _) => self.kind_in(t),
            Ty::Param(_, k) => *k,
            Ty::Info(_) => Kind::Affine,
            // Not known yet: nothing is said of it.
            Ty::Var(_) => Kind::Copy,
            Ty::Named(n, args) => match self.decls.get(n) {
                None => Kind::Shared,
                Some(d) => d
                    .generics
                    .iter()
                    .zip(args)
                    .filter(|(g, _)| d.holds.contains(g))
                    .fold(d.base, |k, (_, a)| k.join(self.kind_in(a))),
            },
        }
    }

    /// The possible kinds of a type whose inference variables may remain
    /// unresolved. Only a declaration's held arguments affect its kind.
    fn kind_range(&self, t: &Ty) -> (Kind, Kind) {
        let join = |(a, b): (Kind, Kind), (c, d): (Kind, Kind)| (a.join(c), b.join(d));
        match t {
            Ty::Var(_) => (Kind::Copy, Kind::Linear),
            Ty::App(h, _) => match &**h {
                Ty::Param(_, k) => (*k, *k),
                _ => (Kind::Copy, Kind::Linear),
            },
            Ty::Union(ts) => ts
                .iter()
                .fold((Kind::Copy, Kind::Copy), |k, t| join(k, self.kind_range(t))),
            Ty::Tagged(_, t) | Ty::Borrow(t, _) => self.kind_range(t),
            Ty::Named(n, args) => match self.decls.get(n) {
                None => (Kind::Shared, Kind::Shared),
                Some(d) => d
                    .generics
                    .iter()
                    .zip(args)
                    .filter(|(g, _)| d.holds.contains(g))
                    .fold((d.base, d.base), |k, (_, a)| join(k, self.kind_range(a))),
            },
            // A function's arguments and result do not affect its own kind.
            _ => {
                let k = self.kind_in(t);
                (k, k)
            }
        }
    }

    /// Each declaration's `base` and `holds`: the least solution of
    /// `kind(D(args)) = join(declared(D), floor(D), kind(each field at args))`
    /// of `docs/design/ownership.md`, as a kind and the generics whose
    /// arguments count. A generic no field mentions is held all the same:
    /// `Vec(A)` holds its `A`s. A recursive declaration may meet itself at
    /// other arguments (`enum W(A) { Leaf(A), Node(W(F)) }`), which the least
    /// solution counts.
    pub fn summarize(&mut self) {
        let mut names: Vec<Name> = self.decls.keys().cloned().collect();
        names.sort();
        for d in self.decls.values_mut() {
            let mut base = d.declared.unwrap_or(Kind::Copy);
            if d.recursive {
                base = base.join(Kind::Shared);
            }
            d.base = base;
            d.holds = d
                .generics
                .iter()
                .filter(|g| !d.mentions(g))
                .cloned()
                .collect();
        }
        loop {
            let mut changed = false;
            for n in &names {
                let d = &self.decls[n];
                let mut base = d.base;
                let mut holds = d.holds.clone();
                for c in &d.constructors {
                    for (_, f) in &c.fields {
                        base = base.join(self.field_kind(f, &d.parameters(), &mut holds));
                    }
                }
                let d = self.decls.get_mut(n).expect("a declared name");
                if base != d.base || holds.len() != d.holds.len() {
                    d.base = base;
                    d.holds = holds;
                    changed = true;
                }
            }
            if !changed {
                return;
            }
        }
    }

    /// The kind of field type `t` over `generics`, but for the arguments:
    /// the generics whose arguments count go into `holds`.
    fn field_kind(&self, t: &Ty, generics: &[Param], holds: &mut Vec<Name>) -> Kind {
        match t {
            Ty::Param(n, k) => {
                if !generics.contains(n) {
                    return *k;
                }
                if !holds.contains(&n.name) {
                    holds.push(n.name.clone());
                }
                Kind::Copy
            }
            // `F(X)`: what `F` makes holds at most what `F` and `X` do.
            Ty::App(h, x) => self
                .field_kind(h, generics, holds)
                .join(self.field_kind(x, generics, holds)),
            Ty::Union(ts) => ts.iter().fold(Kind::Copy, |k, t| {
                k.join(self.field_kind(t, generics, holds))
            }),
            Ty::Tagged(_, t) | Ty::Borrow(t, _) => self.field_kind(t, generics, holds),
            Ty::Named(n, args) => match self.decls.get(n) {
                None => Kind::Shared,
                Some(d) => d
                    .generics
                    .iter()
                    .zip(args)
                    .filter(|(g, _)| d.holds.contains(g))
                    .fold(d.base, |k, (_, a)| {
                        k.join(self.field_kind(a, generics, holds))
                    }),
            },
            _ => self.kind_in(t),
        }
    }

    /// Why `t` has no `clone`, when it has none: a `linear` type, an opaque
    /// one (declared `affine` and holding nothing affine of its own), or a
    /// function or `Info` that is not duplicable.
    pub fn no_clone(&self, t: &Ty) -> Option<String> {
        self.no_clone_in(t, &mut Vec::new())
    }

    fn no_clone_in(&self, t: &Ty, visiting: &mut Vec<Ty>) -> Option<String> {
        if visiting.contains(t) {
            return None;
        }
        let k = self.kind(t);
        if k == Kind::Linear {
            return Some(format!("{t} is linear"));
        }
        if k.dup() {
            return None;
        }
        match t {
            Ty::Named(n, args) => {
                let d = self.decls.get(n)?;
                visiting.push(t.clone());
                let why = if d.builtin {
                    args.iter().find_map(|a| self.no_clone_in(a, visiting))
                } else {
                    let map = d.instance(args);
                    let fields: Vec<Ty> = d
                        .constructors
                        .iter()
                        .flat_map(|c| c.fields.iter().map(|(_, f)| substitute(f, &map)))
                        .collect();
                    if d.declared == Some(Kind::Affine) && fields.iter().all(|f| self.kind(f).dup())
                    {
                        Some(format!("{t} has no clone"))
                    } else {
                        fields.iter().find_map(|f| self.no_clone_in(f, visiting))
                    }
                };
                visiting.pop();
                why
            }
            Ty::Union(ts) => ts.iter().find_map(|t| self.no_clone_in(t, visiting)),
            Ty::Tagged(_, t) => self.no_clone_in(t, visiting),
            Ty::Param(..) => Some(format!("{t} has no clone")),
            _ => Some(format!("{t} has no clone")),
        }
    }

    /// A record pattern's patterns in the order of the struct's fields.
    pub fn positional(
        &self,
        name: &Name,
        fields: &[(String, Pattern)],
        expected: Option<&Ty>,
    ) -> Result<Vec<Pattern>, Message> {
        let (d, c) = self.resolve_ctor(name, expected)?;
        let declared = &self.decls[d].constructors[*c].fields;
        for (f, _) in fields {
            if !declared.iter().any(|(n, _)| n.as_deref() == Some(f)) {
                return Err(msg!(
                    "nibcheck-no-field",
                    name = name.to_string(),
                    field = f.as_str()
                ));
            }
        }
        declared
            .iter()
            .map(|(n, _)| {
                let n = n.as_deref().unwrap_or("");
                fields
                    .iter()
                    .find(|(f, _)| f == n)
                    .map(|(_, p)| p.clone())
                    .ok_or_else(|| msg!("nibcheck-pattern-field-missing", field = n))
            })
            .collect()
    }

    /// The field types of constructor `c` of `d` at the type arguments.
    pub fn fields(&self, d: &Name, c: usize, args: &[Ty]) -> Vec<(Option<String>, Ty)> {
        let Some(data) = self.decls.get(d) else {
            return Vec::new();
        };
        let map = data.instance(args);
        data.constructors[c]
            .fields
            .iter()
            .map(|(n, t)| (n.clone(), substitute(t, &map)))
            .collect()
    }
}

impl Data {
    pub fn parameter(&self, index: usize) -> Param {
        Param::data(&self.name, index, &self.generics[index])
    }

    pub fn parameters(&self) -> Vec<Param> {
        (0..self.generics.len())
            .map(|i| self.parameter(i))
            .collect()
    }

    fn mentions(&self, generic: &Name) -> bool {
        let Some(index) = self.generics.iter().position(|g| g == generic) else {
            return false;
        };
        let param = self.parameter(index);
        self.constructors
            .iter()
            .any(|c| c.fields.iter().any(|(_, f)| param_in(f, &param)))
    }

    fn instance(&self, args: &[Ty]) -> HashMap<ParamId, Ty> {
        self.parameters()
            .into_iter()
            .map(|g| g.id)
            .zip(args.iter().cloned())
            .collect()
    }
}

/// What the checker found: the errors, the width of every integer
/// operation, keyed by the operation's identity, for the evaluator, and the
/// types `lin.rs` reads.
#[derive(Debug, Default)]
pub struct TypeReport {
    pub errors: Vec<TypeError>,
    pub widths: HashMap<TermId, Width>,
    pub lets: Vec<(String, String)>,
    /// The type of each name a program binds, keyed by the name and where it
    /// is bound (see [`site`]).
    pub locals: HashMap<(Name, TermId), Ty>,
    /// The type of each expression, by occurrence identity.
    pub terms: HashMap<TermId, Ty>,
    /// The declaration selected at each type reference occurrence.
    pub type_references: HashMap<TermId, Name>,
    /// The declaration's own type arguments at each named function use.
    /// Captured outer parameters are not instantiated by that use.
    pub instantiations: HashMap<TermId, HashMap<ParamId, Ty>>,
    /// The type arguments of an indexed effect (`indices.rs`) at each
    /// `perform` (by the term) and each arm (by the arm's body).
    pub effect_args: HashMap<TermId, Vec<Ty>>,
    /// The generics of functions that a handler arm in their body gives a
    /// value to (the `E` of `catch`): what a caller performs fixes them.
    pub effect_generics: HashSet<ParamId>,
    pub datas: Datas,
    /// Each operation's resume quantity.
    pub quants: HashMap<Name, Quant>,
    /// Every function's type (the prelude's, the `extern`s', the program's).
    pub schemes: HashMap<Name, Scheme>,
    /// The functions written inside a body whose name no other function
    /// has (not scoped: for a backend that lifts them to the top).
    pub local_schemes: HashMap<Name, Scheme>,
    /// Every operation's signature.
    pub effects: HashMap<Name, EffectSig>,
    /// For each use of a function that has class constraints, the evidence
    /// for each of them in the order of the function's `preds`, by the identity
    /// of the use.
    pub evidence: HashMap<TermId, Vec<Ev>>,
    /// The classes, as declared, by name.
    pub classes: HashMap<Name, crate::surface::ClassDecl>,
    /// The terms, by their spans, whose product value is taken to fewer
    /// members (`A × B <: A`), with the type it is taken to. Taking one twice
    /// gives the same value.
    pub product_fits: HashMap<Span, Ty>,
    /// The `(e: T)` whose `e` is a `Pair` (nested to the right, as `A × B`
    /// reads in the prelude) and whose `T` takes some of its members: the
    /// members taken, by their place in the pair, in the order `T` writes
    /// them, and how many members the pair has. The expansion writes them
    /// as `.fst` and `.snd`.
    pub pair_members: HashMap<TermId, (Vec<usize>, usize)>,
    /// The `match` arms that no value reaches, by the arm's body, with where
    /// the body is: the arms before them take every value they would. A
    /// backend need not write them.
    pub redundant_arms: HashMap<TermId, Span>,
    /// Successful nominal projections, sealed to their checked source.
    nominal_facts: Option<NominalFacts>,
    operation_facts: Option<OperationFacts>,
}

#[derive(Debug)]
struct NominalFacts {
    program: Program,
    occurrences: Vec<TermId>,
    owners: HashMap<TermId, Name>,
}

fn value_occurrences(program: &Program) -> Vec<TermId> {
    let mut ids = Vec::new();
    for stmt in &program.stmts {
        crate::surface::walk::values_stmt(stmt, &mut |node| {
            if let crate::surface::walk::Node::Term(t) = node {
                ids.push(t.id());
            }
        });
    }
    ids
}

#[derive(Debug, Clone, PartialEq)]
pub enum Ev {
    /// The `where` of the function the use is in: the class and the generic.
    Assume(Name, Param),
    /// An instance of the class for the type constructor, the types its
    /// generics were matched to, and the evidence for its `where`.
    Inst(Name, Name, Vec<Ty>, Vec<Ev>),
    /// A structural predicate: no run-time value.
    Structural,
    /// Not found: an error was reported.
    Missing,
}

/// The prelude's own report: the types inside its functions, whose spans
/// (from [`crate::surface::PRELUDE_BASE`]) never meet a program's.
pub fn prelude_report() -> &'static TypeReport {
    static REPORT: OnceLock<TypeReport> = OnceLock::new();
    REPORT.get_or_init(|| {
        CHECKING_PRELUDE.set(true);
        let report = check_program(prelude());
        CHECKING_PRELUDE.set(false);
        report
    })
}

pub fn prelude_report_for(program: &Program) -> &'static TypeReport {
    let library = prelude_for(program);
    if std::ptr::eq(library, prelude()) {
        return prelude_report();
    }
    static REPORT: OnceLock<TypeReport> = OnceLock::new();
    REPORT.get_or_init(|| {
        CHECKING_PRELUDE.set(true);
        let report = check_program(library);
        CHECKING_PRELUDE.set(false);
        report
    })
}

thread_local! {
    /// Set while [`prelude_report`] is being made, which cannot read itself.
    static CHECKING_PRELUDE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

impl TypeReport {
    /// Nominal result owners sealed by [`check_program`] for this exact program.
    /// Function types contribute only their nominal result owner, never a
    /// callable contract or an effect row. Reused expression IDs contribute
    /// no owner. Public type-table edits cannot alter these sealed facts.
    pub fn nominal_owners_for(&self, program: &Program) -> Option<&HashMap<TermId, Name>> {
        let facts = self.nominal_facts.as_ref()?;
        if !self.errors.is_empty()
            || &facts.program != program
            || facts.occurrences != value_occurrences(program)
        {
            return None;
        }
        Some(&facts.owners)
    }

    fn seal_nominal_owners(&mut self, program: &Program) {
        if !self.errors.is_empty() {
            return;
        }
        let occurrences = value_occurrences(program);
        let mut counts = HashMap::<TermId, usize>::new();
        for id in &occurrences {
            *counts.entry(*id).or_default() += 1;
        }
        let owners = self
            .terms
            .iter()
            .filter_map(|(id, ty)| {
                if counts.get(id) != Some(&1) {
                    return None;
                }
                let result = match ty {
                    Ty::Fn(_, result, _) => &**result,
                    ty => ty,
                };
                match result {
                    Ty::Named(name, _) => Some((*id, name.clone())),
                    _ => None,
                }
            })
            .collect();
        self.nominal_facts = Some(NominalFacts {
            program: program.clone(),
            occurrences,
            owners,
        });
    }

    /// A function's scheme: a top-level function's, or a local one's whose
    /// name is not used twice.
    pub fn scheme(&self, name: &Name) -> Option<&Scheme> {
        self.schemes
            .get(name)
            .or_else(|| self.local_schemes.get(name))
    }

    /// Adds what the prelude's report knows of its own functions.
    pub fn with_prelude(self) -> Self {
        self.with_library_report(prelude_report())
    }

    pub fn with_prelude_for(self, program: &Program) -> Self {
        self.with_library_report(prelude_report_for(program))
    }

    fn with_library_report(mut self, lib: &TypeReport) -> Self {
        self.type_references.extend(
            lib.type_references
                .iter()
                .map(|(id, name)| (*id, name.clone())),
        );
        self.terms
            .extend(lib.terms.iter().map(|(k, v)| (*k, v.clone())));
        self.locals
            .extend(lib.locals.iter().map(|(k, v)| (k.clone(), v.clone())));
        self.instantiations
            .extend(lib.instantiations.iter().map(|(k, v)| (*k, v.clone())));
        self.widths.extend(lib.widths.iter().map(|(k, v)| (*k, *v)));
        self.product_fits
            .extend(lib.product_fits.iter().map(|(k, v)| (*k, v.clone())));
        self
    }

    /// The type of the name `name` bound at `site`.
    pub fn local(&self, name: &Name, site: TermId) -> Option<&Ty> {
        self.locals.get(&(name.clone(), site))
    }

    pub fn term(&self, t: &SurfaceTerm) -> Option<&Ty> {
        self.terms.get(&t.id())
    }

    pub fn kind(&self, t: &Ty) -> Kind {
        self.datas.kind(t)
    }
}

/// Where a name is bound, for [`TypeReport::locals`]: a `let`, `var` or a
/// local `fn` by its value (or body) occurrence, a parameter by its function's
/// body, a pattern's names and `k` by their arm's body.
pub fn site(t: &SurfaceTerm) -> TermId {
    t.id()
}

/// What the class-aware check found in a program whose classes could not be
/// expanded (`expand_loaded`), or `None` for one that expanded.
pub fn unexpanded_errors(program: &Program) -> Option<&[(tauto_message::Message, Span)]> {
    match program.errors.split_first() {
        Some(((m, _), rest)) if m.as_text() == Some(expand::UNEXPANDED) => Some(rest),
        _ => None,
    }
}

pub fn check_program(program: &Program) -> TypeReport {
    // A program that did not expand carries what the class-aware check found
    // (`expand_loaded`): that is the report.
    if let Some(errors) = unexpanded_errors(program) {
        let mut c = Checker::default();
        for (message, span) in errors {
            c.error(message.clone(), *span);
        }
        return c.finish();
    }
    let mut report = check_program_in(program, prelude_for(program));
    // A program still using a class did not expand: what the class-aware
    // check finds kept it from expanding, and the rest (`Ord is not defined`)
    // follows from that.
    if !report.errors.is_empty() {
        let found = expansion_errors(program);
        if !found.is_empty() {
            let mut c = Checker::default();
            for e in found {
                c.error(e.message, e.span);
            }
            return c.finish();
        }
    }
    report.seal_nominal_owners(program);
    report
}

/// [`check_program`] against the given prelude. Only [`check_program`] seals
/// nominal-owner facts for the standard-prelude row check.
pub fn check_program_in(program: &Program, prelude: &Program) -> TypeReport {
    let mut c = Checker::default();
    c.run(program, prelude);
    let mut report = c.finish();
    report.seal_operation_instances(program);
    report
}

/// [`check_program_in`] reading the rows given to row parameters as types
/// (`Checker::rows_as_types`), for the index expansion to infer from. Its
/// errors are not the program's.
pub(crate) fn check_program_rows_as_types(program: &Program, prelude: &Program) -> TypeReport {
    let mut c = Checker {
        rows_as_types: true,
        ..Checker::default()
    };
    c.run(program, prelude);
    let mut report = c.finish();
    report.seal_operation_instances(program);
    report
}

/// The report as text, for `totes/nibcheck` to write the same: the errors in
/// order, the top-level lets, and then the locals, terms, widths, quantities,
/// declarations and constructors, each sorted. A type is written with
/// everything in it (`dump_ty`); the "not supported yet: {term:?}" of an
/// unread term is cut to the name of the term.
pub fn dump_types(report: &TypeReport) -> String {
    let mut out = String::new();
    for e in &report.errors {
        let mut message = e.message.to_string();
        if let Some(rest) = message.clone().strip_prefix("not supported yet: ") {
            let name = rest.split(['(', ' ']).next().unwrap_or("");
            message = format!("not supported yet: {name}");
        }
        out.push_str(&format!(
            "error {} {} {message}\n",
            e.span.start, e.span.end
        ));
    }
    for (name, ty) in &report.lets {
        out.push_str(&format!("let {name} {ty}\n"));
    }
    let mut locals: Vec<_> = report.locals.iter().collect();
    locals.sort_by_key(|((name, id), t)| (name.as_str(), id.span().start, dump_ty(t)));
    for ((name, id), t) in locals {
        let site = id.span().start;
        out.push_str(&format!("local {name} {site} {}\n", dump_ty(t)));
    }
    let mut terms: Vec<_> = report.terms.iter().collect();
    terms.sort_by_key(|(id, t)| (id.span().start, id.span().end, dump_ty(t)));
    for (id, t) in terms {
        let Span { start, end } = id.span();
        out.push_str(&format!("term {start} {end} {}\n", dump_ty(t)));
    }
    let mut widths: Vec<_> = report.widths.iter().collect();
    widths.sort_by_key(|(id, w)| (id.span().start, id.span().end, **w));
    for (id, w) in widths {
        let Span { start, end } = id.span();
        out.push_str(&format!("width {start} {end} {}\n", Ty::Int(*w)));
    }
    let mut quants: Vec<_> = report.quants.iter().collect();
    quants.sort_by(|a, b| a.0.cmp(b.0));
    for (effect, q) in quants {
        out.push_str(&format!("quant {effect} {q:?}\n"));
    }
    let mut decls: Vec<_> = report.datas.decls.values().collect();
    decls.sort_by(|a, b| a.name.cmp(&b.name));
    for d in decls {
        let declared = d.declared.map_or("-".to_string(), |k| k.to_string());
        let ctors: Vec<String> = d
            .constructors
            .iter()
            .map(|c| {
                let fields: Vec<String> = c
                    .fields
                    .iter()
                    .map(|(n, t)| format!("{}:{}", n.as_deref().unwrap_or("_"), dump_ty(t)))
                    .collect();
                format!("{}({})", c.name, fields.join(","))
            })
            .collect();
        out.push_str(&format!(
            "data {} {declared} {} {} {} {} {}\n",
            d.name,
            d.recursive,
            d.is_struct,
            d.builtin,
            d.generics
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(","),
            ctors.join(";")
        ));
    }
    let mut ctors: Vec<_> = report.datas.ctors.iter().collect();
    ctors.sort_by(|a, b| a.0.cmp(b.0));
    for (name, (d, i)) in ctors {
        // The report writes the struct's single name, not its canonical alias.
        if report.datas.decls[d].is_struct && name != &report.datas.decls[d].constructors[*i].name {
            continue;
        }
        out.push_str(&format!("ctor {name} {d} {i}\n"));
    }
    out
}

/// A type with everything in it: the variables, the kinds, the borrows.
pub fn dump_ty(t: &Ty) -> String {
    let list = |ts: &[Ty]| {
        let parts: Vec<String> = ts.iter().map(dump_ty).collect();
        format!("[{}]", parts.join(","))
    };
    match t {
        Ty::Int(w) => format!("Int({})", Ty::Int(*w)),
        Ty::Bool => "Bool".into(),
        Ty::Text => "Text".into(),
        Ty::Unit => "Unit".into(),
        Ty::Never => "Never".into(),
        Ty::Decimal => "Decimal".into(),
        Ty::Float => "Float".into(),
        Ty::Float32 => "Float32".into(),
        Ty::Fn(ps, r, k) => format!("Fn({},{},{k})", list(ps), dump_ty(r)),
        Ty::Union(ts) => format!("Union({})", list(ts)),
        Ty::Tagged(tags, t) => {
            let tags: Vec<&str> = tags.iter().map(|s| s.as_str()).collect();
            format!("Tagged([{}],{})", tags.join(","), dump_ty(t))
        }
        Ty::Named(n, args) => format!("Named({n},{})", list(args)),
        Ty::Param(n, k) => format!("Param({n},{k})"),
        Ty::Info(t) => format!("Info({})", dump_ty(t)),
        Ty::Borrow(t, m) => format!("Borrow({},{})", dump_ty(t), if *m { "mut" } else { "ref" }),
        Ty::Var(v) => format!("Var({v})"),
        Ty::Poly(gs, t) => {
            let names: Vec<String> = gs.iter().map(|(n, k)| format!("{n}:{k}")).collect();
            format!("Poly([{}],{})", names.join(","), dump_ty(t))
        }
        Ty::App(h, x) => format!("App({},{})", dump_ty(h), dump_ty(x)),
    }
}

/// The declarations every program sees before its own: `std/prelude/Std.taut`
/// and the affine standard library. A program's own
/// declaration of a name hides the prelude's.
static PRELUDE: OnceLock<Program> = OnceLock::new();

fn has_references(program: &Program) -> bool {
    let mut resolved = tauto_surface::bindings::declared_names(&program.stmts)
        .iter()
        .any(|n| n.is_resolved());
    if !resolved {
        for statement in &program.stmts {
            let mut statement = statement.clone();
            crate::surface::walk::stmt(&mut statement, &mut |term| match &*term.kind {
                TermKind::Var(name) | TermKind::Perform { effect: name, .. } => {
                    resolved |= name.is_resolved()
                }
                _ => {}
            });
            if resolved {
                break;
            }
        }
    }
    resolved
}

pub fn prelude_for(program: &Program) -> &'static Program {
    let resolved = has_references(program);
    if !resolved {
        return prelude();
    }
    static RESOLVED: OnceLock<Program> = OnceLock::new();
    RESOLVED.get_or_init(|| {
        let mut program = expand::expand_prelude(
            resolved_prelude_source().clone(),
            crate::surface::PRELUDE_BASE + (1 << 30),
        );
        tauto_surface::resolve::Resolver::new(
            tauto_surface::bindings::library_definition_bindings(),
        )
        .statements(&mut program.stmts);
        program
    })
}

pub fn prelude() -> &'static Program {
    PRELUDE.get_or_init(|| {
        let program = expand::expand_prelude(
            prelude_source().clone(),
            crate::surface::PRELUDE_BASE + (1 << 30),
        );
        // A prelude that does not check keeps its classes unexpanded, and
        // every program would read its class methods as calls whose effects
        // no row describes. The prelude ships with the checker: say where
        // it fails, as a prelude that does not parse does.
        if let Some(errors) = unexpanded_errors(&program) {
            let found: Vec<String> = errors
                .iter()
                .take(50)
                .map(|(message, span)| {
                    crate::nibstd::locate_error(
                        format!("{message} at byte {}", span.start),
                        crate::surface::PRELUDE_BASE,
                        crate::nibstd::PRELUDE_FILES,
                    )
                })
                .collect();
            panic!(
                "the prelude does not check ({} errors):\n{}",
                errors.len(),
                found.join("\n")
            );
        }
        program
    })
}

/// The prelude as written, its classes and instances still in it: what a
/// program that uses a class is checked against before it is expanded.
pub fn prelude_source() -> &'static Program {
    static SOURCE: OnceLock<Program> = OnceLock::new();
    SOURCE.get_or_init(|| {
        let mut program = crate::surface::parse_program_as_written_at(
            crate::nibstd::PRELUDE,
            crate::surface::PRELUDE_BASE,
        )
        .expect("the prelude parses");
        crate::surface::qualify::lower_prelude_names(&mut program.stmts);
        program
    })
}

fn resolved_prelude_source() -> &'static Program {
    static SOURCE: OnceLock<Program> = OnceLock::new();
    SOURCE.get_or_init(|| {
        let mut program = prelude_source().clone();
        for statement in &mut program.stmts {
            crate::surface::walk::stmt(statement, &mut SurfaceTerm::freshen);
        }
        tauto_surface::resolve::Resolver::new(
            tauto_surface::bindings::library_definition_bindings(),
        )
        .statements(&mut program.stmts);
        program
    })
}

pub(super) fn prelude_source_for(program: &Program) -> &'static Program {
    if has_references(program) {
        resolved_prelude_source()
    } else {
        prelude_source()
    }
}

const OPERATORS: &[&str] = &[
    "+", "-", "*", "/", "==", "!=", "<", ">", "<=", ">=", "&&", "||",
];

/// The binder of a type parameter. Occurrence identities are internal keys,
/// not names for diagnostics or generated code.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ParamId {
    Function {
        owner: FunctionOwner,
        index: usize,
    },
    Data {
        data: Name,
        index: usize,
    },
    Effect {
        owner: EffectOwner,
        index: usize,
    },
    Instance {
        class: Name,
        head: TermId,
        index: usize,
    },
    Poly {
        occurrence: TermId,
        index: usize,
    },
    Skolem {
        serial: usize,
    },
    KindWitness(Kind),
}

/// A named function occurrence and its lexical declaration site. The parent
/// and path distinguish declarations even when their bodies share a term.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionOwner {
    name: Name,
    body: TermId,
    parent: Option<Box<FunctionOwner>>,
    site: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EffectOwner {
    name: Name,
    occurrence: TermId,
    function: Option<FunctionOwner>,
    site: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct StableFunctionOwner {
    name: Name,
    parent: Option<Box<StableFunctionOwner>>,
    site: Vec<usize>,
}

impl FunctionOwner {
    fn stable_key(&self) -> StableFunctionOwner {
        StableFunctionOwner {
            name: self.name.clone(),
            parent: self.parent.as_ref().map(|p| Box::new(p.stable_key())),
            site: self.site.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum StableParamKey {
    Function(StableFunctionOwner, usize),
    Data(Name, usize),
    Effect(Option<StableFunctionOwner>, Name, Vec<usize>, usize),
    Instance(Name, u32, usize),
    Poly(u32, usize),
    Skolem(Name),
    KindWitness(Kind),
}

/// A parameter's binder identity and its source spelling. Equality uses only
/// the binder; distinct declarations may use the same spelling and kind.
#[derive(Debug, Clone)]
pub struct Param {
    id: ParamId,
    name: Name,
}

impl Param {
    fn new(id: ParamId, name: impl Into<Name>) -> Self {
        Self {
            id,
            name: name.into(),
        }
    }

    pub fn id(&self) -> &ParamId {
        &self.id
    }
    pub fn reference(&self) -> &Name {
        &self.name
    }
    pub fn name(&self) -> &str {
        &self.name
    }

    fn data(data: &Name, index: usize, name: &Name) -> Self {
        Self::new(
            ParamId::Data {
                data: data.into(),
                index,
            },
            name,
        )
    }

    fn effect(owner: &EffectOwner, index: usize, name: &Name) -> Self {
        Self::new(
            ParamId::Effect {
                owner: owner.clone(),
                index,
            },
            name,
        )
    }

    fn kind_witness(kind: Kind) -> Self {
        Self::new(ParamId::KindWitness(kind), kind.to_string())
    }

    fn stable_key(&self) -> StableParamKey {
        match &self.id {
            ParamId::Function { owner, index } => {
                StableParamKey::Function(owner.stable_key(), *index)
            }
            ParamId::Data { data, index } => StableParamKey::Data(data.clone(), *index),
            ParamId::Effect { owner, index } => StableParamKey::Effect(
                owner.function.as_ref().map(FunctionOwner::stable_key),
                owner.name.clone(),
                owner.site.clone(),
                *index,
            ),
            ParamId::Instance { class, head, index } => {
                StableParamKey::Instance(class.clone(), head.span().start, *index)
            }
            ParamId::Poly { occurrence, index } => {
                StableParamKey::Poly(occurrence.span().start, *index)
            }
            ParamId::Skolem { .. } => StableParamKey::Skolem(self.name.clone()),
            ParamId::KindWitness(kind) => StableParamKey::KindWitness(*kind),
        }
    }
}

impl PartialEq for Param {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Param {}
impl Hash for Param {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl PartialOrd for Param {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Param {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.name)
    }
}

/// A function's type with its type parameters and their bounds,
/// instantiated at each use.
#[derive(Debug, Clone)]
pub struct Scheme {
    /// Identity of this declaration, shared by its signature and body.
    pub owner: FunctionOwner,
    /// The type parameters, and the kind each is bounded by. A row variable
    /// is not among them.
    pub generics: Vec<(Param, Kind)>,
    /// A [`Ty::Fn`]: the parameters (a borrowed one a [`Ty::Borrow`]), the
    /// result.
    pub ty: Ty,
    /// The `where` constraints: the class and the generic it constrains.
    pub preds: Vec<(Name, Param)>,
    /// The generics that are type constructors, with the kind each takes;
    /// the kind in `generics` is the one it makes.
    pub ctors: Vec<(Param, Kind)>,
}

mod classes;
mod expand;
pub(crate) mod indices;
pub(crate) use classes::Unresolved;
pub use expand::{expand_classes, expand_loaded, expansion_errors, index_expansion_errors};

/// The classes whose instances follow from a type's structure.
pub const STRUCTURAL: &[&str] = &["PartialEq", "DecEq", "Hash"];

/// A constraint to check once the types are known: `ty` has the `class` the
/// use of `what` asks for, given what the enclosing function assumes.
struct Pending {
    class: Name,
    ty: Ty,
    what: String,
    assume: Vec<(Name, Param)>,
    span: Span,
    /// Which constraint of which use this is: the occurrence, its index
    /// among the function's constraints, and how many there are.
    slot: Option<(TermId, usize, usize)>,
}

#[derive(Debug, Clone)]
pub struct EffectSig {
    pub generics: Vec<Param>,
    pub params: Vec<Ty>,
    pub result: Ty,
}

#[derive(Clone, Copy)]
enum Instantiation {
    Fresh,
    /// An incomplete local self signature keeps its declaration's binders
    /// until the body has been checked, including through nested scopes.
    SelfSignature,
}

#[derive(Clone)]
struct Local {
    name: Name,
    /// A named local function is instantiated at each use; other values are not.
    scheme: Option<Scheme>,
    instantiation: Instantiation,
    ty: Ty,
    mutable: bool,
    /// A `var &x`: it is advanced through `&mut x`, never assigned.
    view: bool,
}

/// The name of the type a row is read as (`Checker::rows_as_types`). No
/// program can write it.
pub(crate) const ROW_TYPE: &str = "!row";
/// A row's tail inside a [`ROW_TYPE`] type.
pub(crate) const ROW_TAIL: &str = "!tail";

#[derive(Default)]
struct Checker {
    /// Whether the program being checked names its declarations by reference.
    resolved_names: bool,
    type_references: HashMap<TermId, Name>,
    classes: HashMap<Name, classes::ClassInfo>,
    /// By class and the constructor at the head of the instance.
    instances: HashMap<(Name, Name), classes::InstanceInfo>,
    subst: Vec<Option<Ty>>,
    /// While an argument is checked against a general type: the first variable
    /// made for the argument itself; none otherwise.
    local_from: Option<usize>,
    ints: HashSet<usize>,
    /// A type constructor variable at a use: what it takes and makes, and
    /// the function it was for.
    ctor_bounds: Vec<(Ty, Kind, Kind, String, Span)>,
    /// Writing a type where a constructor is wanted: an instance's head.
    constructor_position: bool,
    /// How many rigid generics `fits` has made, for their names.
    rigids: usize,
    fns: HashMap<Name, Scheme>,
    /// The prelude's functions that only its own code calls: the externs
    /// that answer the standard effects, each marked by the effect in its
    /// row, and the functions of `module Host` that wrap them
    /// (`std/prelude/Os.taut`).
    host_only: HashSet<Name>,
    local_fns: Vec<(Name, Scheme)>,
    effects: HashMap<Name, EffectSig>,
    builtin_show_owner: Option<EffectOwner>,
    operation_performs: Vec<(TermId, CheckedOperationInstance)>,
    operation_arms: Vec<ArmObservation>,
    quants: HashMap<Name, Quant>,
    datas: Datas,
    errors: Vec<TypeError>,
    constructor_uses: Vec<(Name, Ty, Span)>,
    /// What each `$x` and `$(e)` of a `quote` fills an expression with
    /// (`Syn::expr_of`'s argument): checked in [`Checker::finish`] to be
    /// a `SynExpr`, a `SynIdent` or a `Judgement`.
    splices: Vec<(TermId, Span)>,
    constructor_records: Vec<(Name, Ty, Vec<(String, Ty, Span)>, Span)>,
    ops: Vec<(TermId, Ty)>,
    literals: Vec<(Span, i128, Ty)>,
    /// The result type a `return` gives, innermost function last.
    returns: Vec<Ty>,
    /// The body type of the budgets the nearest `exceeded` arm answers.
    exceeded: Vec<Ty>,
    lets: Vec<(Name, Ty)>,
    /// A type that must fit a bound: an instantiated type parameter.
    bounds: Vec<(Ty, Kind, Span)>,
    /// What the function being checked may assume: its `where`.
    assume: Vec<(Name, Param)>,
    /// The current function's own type binders for local annotations.
    type_params: HashMap<Name, Ty>,
    function_owner: Option<FunctionOwner>,
    declaration_path: Vec<usize>,
    term_path: Vec<usize>,
    term_children: Vec<usize>,
    /// Constraints of the uses, checked in [`Checker::finish`].
    pending: Vec<Pending>,
    locals: Vec<((Name, TermId), Ty)>,
    terms: Vec<(TermId, Ty)>,
    instantiations: Vec<(TermId, HashMap<ParamId, Ty>)>,
    /// The effects a row names with type arguments, and the arguments each
    /// `perform` and arm of one of them is checked with.
    indexed: HashSet<Name>,
    effect_args: Vec<(TermId, Vec<Ty>)>,
    /// By function, the generics its rows use as an index.
    index_generics: HashMap<Name, HashSet<Name>>,
    /// The generics a function's own row names as its tail (`! e`): rows,
    /// which these types do not follow, even where a type mentions them as
    /// an argument (`Handlers(e)`).
    row_generics: HashSet<ParamId>,
    /// Each use of a generic function with the type arguments it was given,
    /// by the generics' names: checked in [`Checker::finish`] to be determined.
    undetermined: Vec<(TermId, Name, Vec<(Param, Ty)>)>,
    /// The variables a handler arm stands for its operation's generics with.
    arm_generics: Vec<usize>,
    /// The positions of each data type's row parameters. The row check
    /// (`rows`) reads what is given there; to the types it is `()`, so that a
    /// row says nothing a type must agree on.
    row_params: HashMap<Name, Vec<usize>>,
    /// Read a row given to a row parameter as a type (`ROW_TYPE`) instead of
    /// `()`. Only the index expansion's inference (`indices.rs`) asks for it.
    rows_as_types: bool,
    /// The generics of effects that are declared row variables, `<!e>`.
    effect_rows: HashSet<ParamId>,
    /// [`TypeReport::effect_generics`] of the prelude, whose bodies are not
    /// checked with the program.
    prelude_effect_generics: HashSet<ParamId>,
    /// Each closure's result type, which may not be a borrow: checked once
    /// the types are known.
    closure_results: Vec<(Ty, Span)>,
    /// Owned captures and the function kind fixed at their declaration.
    /// Inference may not later grant the function weaker ownership.
    capture_kinds: Vec<(Vec<(Name, Ty)>, Kind, Span)>,
    /// The expected type of the lambda being checked.
    hint: Option<Ty>,
    /// The type the next term is checked against, when it is in a result
    /// position: a function's body, a `return`, and their tails. A call
    /// reads it to fix its type arguments before its arguments are checked.
    result_hint: Option<Ty>,
    /// The type being written is the one directly under a `&`: `Slice(A)`
    /// may be written there only.
    under_borrow: bool,
    /// A product may forget members here: only where [`Checker::expect`]
    /// fits a term's type at the top, so that the place is recorded.
    widen_products: bool,
    /// Where a product forgot members, and the type it was fitted to.
    product_fits: Vec<(Span, Ty)>,
    pair_members: HashMap<TermId, (Vec<usize>, usize)>,
    /// Why a product did not fit by the types of its members, for the next error.
    product_note: Option<ProductNote>,
    redundant_arms: Vec<(TermId, Span)>,
}

impl Checker {
    fn error(&mut self, message: impl Into<tauto_message::Message>, span: Span) {
        self.errors.push(TypeError {
            message: message.into(),
            span,
        });
    }

    fn fresh(&mut self) -> Ty {
        self.subst.push(None);
        Ty::Var(self.subst.len() - 1)
    }

    fn fresh_int(&mut self) -> Ty {
        let v = self.fresh();
        if let Ty::Var(i) = v {
            self.ints.insert(i);
        }
        v
    }

    fn resolve(&self, t: &Ty) -> Ty {
        match t {
            Ty::Var(i) => match &self.subst[*i] {
                Some(t) => self.resolve(t),
                None => t.clone(),
            },
            Ty::Fn(ps, r, k) => Ty::Fn(
                ps.iter().map(|p| self.resolve(p)).collect(),
                Box::new(self.resolve(r)),
                *k,
            ),
            Ty::Union(ts) => union(ts.iter().map(|t| self.resolve(t)).collect()),
            Ty::Tagged(tags, t) => tagged(tags.clone(), self.resolve(t)),
            Ty::Named(n, args) => {
                Ty::Named(n.clone(), args.iter().map(|a| self.resolve(a)).collect())
            }
            Ty::Info(t) => Ty::Info(Box::new(self.resolve(t))),
            Ty::Borrow(t, m) => Ty::Borrow(Box::new(self.resolve(t)), *m),
            Ty::Poly(gs, t) => Ty::Poly(gs.clone(), Box::new(self.resolve(t))),
            Ty::App(h, x) => apply(self.resolve(h), self.resolve(x)),
            other => other.clone(),
        }
    }

    fn kind(&self, t: &Ty) -> Kind {
        self.datas.kind(&self.resolve(t))
    }

    fn occurs(&self, v: usize, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Var(i) => i == v,
            Ty::Fn(ps, r, _) => ps.iter().any(|p| self.occurs(v, p)) || self.occurs(v, &r),
            Ty::Union(ts) => ts.iter().any(|t| self.occurs(v, t)),
            Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Poly(_, t) => {
                self.occurs(v, &t)
            }
            Ty::App(h, x) => self.occurs(v, &h) || self.occurs(v, &x),
            Ty::Named(_, args) => args.iter().any(|a| self.occurs(v, a)),
            _ => false,
        }
    }

    fn bind(&mut self, v: usize, t: Ty) -> Result<(), ()> {
        if let Ty::Var(w) = t {
            if w == v {
                return Ok(());
            }
            if self.ints.contains(&v) {
                self.ints.insert(w);
            }
            self.subst[v] = Some(Ty::Var(w));
            return Ok(());
        }
        if self.ints.contains(&v) && !matches!(t, Ty::Int(_)) {
            return Err(());
        }
        if self.occurs(v, &t) {
            return Err(());
        }
        self.subst[v] = Some(t);
        Ok(())
    }

    /// Makes `a` and `b` the same type. The two duplicable kinds of a
    /// function are the same here: they differ only at run time.
    fn unify(&mut self, a: &Ty, b: &Ty) -> Result<(), ()> {
        let (a, b) = (self.resolve(a), self.resolve(b));
        match (&a, &b) {
            (Ty::Var(v), _) => self.bind(*v, b),
            (_, Ty::Var(v)) => self.bind(*v, a),
            // `F(X) ~ H(U₁, …, Uₙ)`: `F := H(U₁, …, Uₙ₋₁)` and `X ~ Uₙ`.
            // The solution is the only one.
            (Ty::App(h, x), Ty::Named(n, args)) | (Ty::Named(n, args), Ty::App(h, x))
                if !args.is_empty() =>
            {
                let mut init = args.clone();
                let last = init.pop().unwrap();
                self.unify(h, &Ty::Named(n.clone(), init))?;
                self.unify(x, &last)
            }
            (Ty::App(h1, x1), Ty::App(h2, x2)) => {
                self.unify(h1, h2)?;
                self.unify(x1, x2)
            }
            (Ty::Poly(ga, ta), Ty::Poly(gb, tb))
                if ga.len() == gb.len() && ga.iter().zip(gb).all(|(x, y)| x.1 == y.1) =>
            {
                let rigid = self.rigid(ga);
                let (ta, tb) = (
                    substitute(ta, &rigid),
                    substitute(tb, &poly_map(ga, gb, &rigid)),
                );
                self.unify(&ta, &tb)?;
                self.rigid_kept(&rigid, &a, &b)
            }
            (Ty::Fn(pa, ra, ka), Ty::Fn(pb, rb, kb))
                if pa.len() == pb.len() && (ka == kb || (ka.dup() && kb.dup())) =>
            {
                for (x, y) in pa.iter().zip(pb) {
                    self.unify(x, y)?;
                }
                self.unify(ra, rb)
            }
            (Ty::Named(na, xa), Ty::Named(nb, xb))
                if (na == nb || (is_pair_name(na) && is_pair_name(nb))) && xa.len() == xb.len() =>
            {
                for (x, y) in xa.iter().zip(xb) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (Ty::Info(x), Ty::Info(y)) => self.unify(x, y),
            (Ty::Borrow(x, ma), Ty::Borrow(y, mb)) if ma == mb => self.unify(x, y),
            (Ty::Tagged(ta, x), Ty::Tagged(tb, y)) if ta == tb => self.unify(x, y),
            (Ty::Union(xa), Ty::Union(xb)) if xa.len() == xb.len() => {
                for (x, y) in xa.iter().zip(xb) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            _ if a == b => Ok(()),
            _ => Err(()),
        }
    }

    /// The generics of a `Poly` as types no other is equal to.
    fn rigid(&mut self, gs: &[(Param, Kind)]) -> HashMap<ParamId, Ty> {
        gs.iter()
            .map(|(n, k)| {
                self.rigids += 1;
                (
                    n.id.clone(),
                    Ty::Param(
                        Param::new(
                            ParamId::Skolem {
                                serial: self.rigids,
                            },
                            n.name(),
                        ),
                        *k,
                    ),
                )
            })
            .collect()
    }

    /// After `a` and `b` were made the same with generics read as `rigid`:
    /// none of the rigid types got into `a` or `b` (through a variable bound
    /// to one).
    fn rigid_kept(&self, rigid: &HashMap<ParamId, Ty>, a: &Ty, b: &Ty) -> Result<(), ()> {
        let names: Vec<&ParamId> = rigid
            .values()
            .filter_map(|t| match t {
                Ty::Param(n, _) => Some(n.id()),
                _ => None,
            })
            .collect();
        // Variables made since `local_from` belong to the value being checked
        // (a name instantiated for the argument): they may be the rigid
        // type. An older variable bound to one has let it escape.
        let escaped = match self.local_from {
            None => self.mentions(&names, a) || self.mentions(&names, b),
            Some(from) => self.subst[..from.min(self.subst.len())]
                .iter()
                .flatten()
                .any(|t| self.mentions(&names, t)),
        };
        if escaped { Err(()) } else { Ok(()) }
    }

    fn mentions(&self, names: &[&ParamId], t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Param(n, _) => names.contains(&n.id()),
            Ty::Fn(ps, r, _) => {
                ps.iter().any(|p| self.mentions(names, p)) || self.mentions(names, &r)
            }
            Ty::Union(ts) => ts.iter().any(|t| self.mentions(names, t)),
            Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Poly(_, t) => {
                self.mentions(names, &t)
            }
            Ty::App(h, x) => self.mentions(names, &h) || self.mentions(names, &x),
            Ty::Named(_, args) => args.iter().any(|a| self.mentions(names, a)),
            _ => false,
        }
    }

    fn instance_of(&mut self, gs: &[(Param, Kind)]) -> HashMap<ParamId, Ty> {
        gs.iter()
            .map(|(n, k)| {
                let v = self.fresh();
                self.bounds.push((v.clone(), *k, Span::new(0, 0)));
                (n.id.clone(), v)
            })
            .collect()
    }

    fn has_open_vars(&self, t: &Ty, except: &HashSet<usize>) -> bool {
        match self.resolve(t) {
            Ty::Var(v) => !except.contains(&v),
            Ty::Fn(ps, r, _) => {
                ps.iter().any(|p| self.has_open_vars(p, except)) || self.has_open_vars(&r, except)
            }
            Ty::Union(ts) => ts.iter().any(|t| self.has_open_vars(t, except)),
            Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Poly(_, t) => {
                self.has_open_vars(&t, except)
            }
            Ty::App(h, x) => self.has_open_vars(&h, except) || self.has_open_vars(&x, except),
            Ty::Named(_, args) => args.iter().any(|a| self.has_open_vars(a, except)),
            _ => false,
        }
    }

    fn has_vars(&self, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Var(_) => true,
            Ty::Fn(ps, r, _) => ps.iter().any(|p| self.has_vars(p)) || self.has_vars(&r),
            Ty::Union(ts) => ts.iter().any(|t| self.has_vars(t)),
            Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Poly(_, t) => self.has_vars(&t),
            Ty::App(h, x) => self.has_vars(&h) || self.has_vars(&x),
            Ty::Named(_, args) => args.iter().any(|a| self.has_vars(a)),
            _ => false,
        }
    }

    /// Whether `f` succeeds, undoing what it bound either way.
    fn probe(&mut self, f: impl FnOnce(&mut Self) -> Result<(), ()>) -> bool {
        let (subst, ints) = (self.subst.clone(), self.ints.clone());
        let note = self.product_note.take();
        let r = f(self);
        self.subst = subst;
        self.ints = ints;
        self.product_note = note;
        r.is_ok()
    }

    /// Tries `f`, undoing what it bound when it fails.
    fn attempt(&mut self, f: impl FnOnce(&mut Self) -> Result<(), ()>) -> Result<(), ()> {
        let (subst, ints) = (self.subst.clone(), self.ints.clone());
        let r = f(self);
        if r.is_err() {
            self.subst = subst;
            self.ints = ints;
        }
        r
    }

    /// A value of type `a` may stand where `b` is expected.
    fn fits(&mut self, a: &Ty, b: &Ty) -> Result<(), ()> {
        let (a, b) = (self.resolve(a), self.resolve(b));
        match (&a, &b) {
            (Ty::Never, _) => Ok(()),
            (Ty::Var(_), _) | (_, Ty::Var(_)) => self.unify(&a, &b),
            // What is wanted is general: `a` has to be as general. What is
            // given is general: some instance of it will do.
            (_, Ty::Poly(gs, t)) => {
                let rigid = self.rigid(gs);
                self.fits(&a, &substitute(t, &rigid))?;
                self.rigid_kept(&rigid, &a, &b)
            }
            (Ty::Poly(gs, t), _) => {
                let fresh = self.instance_of(gs);
                self.fits(&substitute(t, &fresh), &b)
            }
            // A `&mut` borrow may be lent as a `&` one.
            (Ty::Borrow(x, ma), Ty::Borrow(y, mb)) if ma == mb || !mb => self.fits(x, y),
            // A borrow used as a value: `lin.rs` says whether it may be.
            (Ty::Borrow(x, _), _) => self.fits(x, &b),
            // `&A ≡ A` when `A` is duplicable.
            (_, Ty::Borrow(y, _)) if self.kind(&a).dup() => self.fits(&a, y),
            // A function lent for a call is called, never copied or kept: an
            // affine closure may be lent, and `lin.rs` checks that its body
            // does not consume what it captured.
            (Ty::Fn(pa, ra, ka), Ty::Borrow(y, false))
                if *ka == Kind::Affine
                    && matches!(self.resolve(y), Ty::Fn(ref pb, _, _) if pb.len() == pa.len()) =>
            {
                let Ty::Fn(pb, rb, _) = self.resolve(y) else {
                    unreachable!()
                };
                for (x, y) in pa.iter().zip(&pb) {
                    self.fits(y, x)?;
                }
                self.fits(ra, &rb)
            }
            (Ty::Union(xs), _) => {
                let widen = std::mem::replace(&mut self.widen_products, false);
                let fitted = xs.iter().try_for_each(|x| self.fits(x, &b));
                self.widen_products = widen;
                fitted
            }
            (_, Ty::Union(_)) if self.widen_products => {
                self.widen_products = false;
                let fitted = self.fits(&a, &b);
                self.widen_products = true;
                fitted
            }
            (_, Ty::Union(ys)) => {
                if self.attempt(|c| c.unify(&a, &b)).is_ok() {
                    return Ok(());
                }
                for y in ys {
                    if self.attempt(|c| c.fits(&a, y)).is_ok() {
                        return Ok(());
                    }
                }
                Err(())
            }
            // Tags are forgotten, never added.
            (Ty::Tagged(ta, x), Ty::Tagged(tb, y)) if tb.is_subset(ta) => self.fits(x, y),
            (Ty::Tagged(_, x), _) if !matches!(b, Ty::Tagged(..)) => self.fits(x, &b),
            // A product is a `Pair` nested to the right. Where a type is expected, its members
            // are matched to that type's by their types (`A × B <: A`, `A × B <: B × A`), but
            // only where both sides are closed and the members of each side differ.
            (Ty::Named(n, args), _)
                if is_pair_name(n)
                    && args.len() == 2
                    && self.widen_products
                    && !matches!(b, Ty::Union(_)) =>
            {
                if self.attempt(|c| c.unify(&a, &b)).is_ok() {
                    return Ok(());
                }
                let xs = self.product_members(&a);
                let ys = self.product_members(&b);
                self.fit_by_types(&xs, &ys)
            }
            (Ty::Fn(pa, ra, ka), Ty::Fn(pb, rb, kb)) if pa.len() == pb.len() && ka.fits(*kb) => {
                // Inside a function type a product keeps its members: nothing
                // would take them out where the function is called.
                let widen = std::mem::replace(&mut self.widen_products, false);
                let fitted = pa
                    .iter()
                    .zip(pb)
                    .try_for_each(|(x, y)| self.fits(y, x))
                    .and_then(|()| self.fits(ra, rb));
                self.widen_products = widen;
                fitted
            }
            _ => self.unify(&a, &b),
        }
    }

    /// The members `xs` of a product fitted to `ys` by their types: each of `ys` is exactly one
    /// of `xs`. Only closed members that differ within each side are matched this way; a
    /// side that is not closed or repeats a type is noted for [`Checker::expect`] to report.
    /// An integer literal of unknown width is closed: it stands for some integer type, so it
    /// is matched to the one integer member on the other side, and two integer members
    /// of which one is a literal are not told apart.
    fn fit_by_types(&mut self, xs: &[Ty], ys: &[Ty]) -> Result<(), ()> {
        let xs: Vec<Ty> = xs.iter().map(|t| self.resolve(t)).collect();
        let ys: Vec<Ty> = ys.iter().map(|t| self.resolve(t)).collect();
        // A label does not change what its member is made of.
        fn bare(t: &Ty) -> &Ty {
            match t {
                Ty::Tagged(_, under) => bare(under),
                t => t,
            }
        }
        fn labels(t: &Ty) -> BTreeSet<String> {
            match t {
                Ty::Tagged(tags, under) => tags.iter().cloned().chain(labels(under)).collect(),
                _ => BTreeSet::new(),
            }
        }
        let literal = |c: &Self, t: &Ty| matches!(bare(t), Ty::Var(v) if c.ints.contains(v));
        let integer = |c: &Self, t: &Ty| matches!(bare(t), Ty::Int(_)) || literal(c, t);
        let same = |c: &Self, x: &Ty, y: &Ty| {
            x == y
                || (integer(c, x)
                    && integer(c, y)
                    && (literal(c, x) || literal(c, y))
                    && labels(x) == labels(y))
        };
        if xs
            .iter()
            .chain(&ys)
            .any(|t| !literal(&*self, t) && self.has_vars(t))
        {
            self.product_note = Some(ProductNote::Open);
            return Err(());
        }
        for side in [&xs, &ys] {
            for (i, t) in side.iter().enumerate() {
                if side[..i].iter().any(|u| same(&*self, u, t)) {
                    self.product_note = Some(ProductNote::Clash(t.clone()));
                    return Err(());
                }
            }
        }
        let mut taken = Vec::new();
        let mut found = Vec::new();
        for y in &ys {
            match xs.iter().position(|x| same(&*self, x, y)) {
                Some(i) if !taken.contains(&i) => {
                    taken.push(i);
                    found.push((xs[i].clone(), y.clone()));
                }
                _ => return Err(()),
            }
        }
        for (x, y) in found {
            self.unify(&x, &y)?;
        }
        Ok(())
    }

    fn expect(&mut self, a: &Ty, b: &Ty, span: Span, what: Message) {
        self.product_note = None;
        let widen = std::mem::replace(&mut self.widen_products, true);
        let mut fitted = self.fits(a, b);
        // `T` where `@a T` is expected: the value is wrapped (`T` written as `@a T`), which a
        // label, a mark of the type, leaves as it is.
        if fitted.is_err()
            && let Ty::Tagged(_, under) = self.resolve(b).unborrowed()
            && !matches!(self.resolve(a).unborrowed(), Ty::Tagged(..))
        {
            fitted = self.fits(a, under);
        }
        self.widen_products = widen;
        if fitted.is_ok()
            && is_pair_ty(self.resolve(a).unborrowed())
            && self.resolve(a).unborrowed() != self.resolve(b).unborrowed()
        {
            let have = self.product_members(&self.resolve(a).unborrowed().clone());
            let want = self.product_members(&self.resolve(b).unborrowed().clone());
            for m in have.iter().filter(|m| !want.contains(m)) {
                if self.kind(m) == Kind::Linear {
                    let m = self.shown(m);
                    self.error(
                        msg!(
                            "nibcheck-forgets-linear-member",
                            what = what.clone(),
                            member = m.to_string()
                        ),
                        span,
                    );
                }
            }
            self.product_fits.push((span, b.clone()));
        }
        let note = self.product_note.take();
        if fitted.is_err() {
            let (a, b) = (self.shown(a), self.shown(b));
            let message = match (a.unborrowed(), b.unborrowed()) {
                (p, _) if is_pair_ty(p) && matches!(note, Some(ProductNote::Open)) => msg!(
                    "nibcheck-mismatch-open-product",
                    what = what,
                    found = a.to_string(),
                    expected = b.to_string()
                ),
                (p, _) if is_pair_ty(p) && matches!(note, Some(ProductNote::Clash(_))) => {
                    let Some(ProductNote::Clash(m)) = &note else {
                        unreachable!()
                    };
                    let m = self.shown(m);
                    msg!(
                        "nibcheck-mismatch-product-clash",
                        what = what,
                        member = m.to_string()
                    )
                }
                (Ty::Fn(pa, _, ka), Ty::Fn(pb, _, kb)) if pa.len() == pb.len() && !ka.fits(*kb) => {
                    msg!(
                        "nibcheck-mismatch-closure-kind",
                        what = what,
                        found = ka.to_string(),
                        expected = kb.to_string()
                    )
                }
                (Ty::App(..), other) | (other, Ty::App(..))
                    if !matches!(other, Ty::App(..) | Ty::Var(_) | Ty::Named(..)) =>
                {
                    msg!("nibcheck-not-an-application", ty = other.to_string())
                }
                // `nat` and a machine integer are two types, not one type
                // of two sizes: the kernel's `Nat` is `nat`, and the type of
                // the width it sees is `U64` of `std::UInt` (`I64` of
                // `std::SInt`), which runs as `u64`.
                (Ty::Int(x), Ty::Int(y)) if (*x == Width::Nat) != (*y == Width::Nat) => {
                    let machine = if *x == Width::Nat { y } else { x };
                    let (checked, module) = match machine {
                        Width::U8 => ("U8", "UInt"),
                        Width::U32 => ("U32", "UInt"),
                        Width::U64 => ("U64", "UInt"),
                        Width::W32 => ("I32", "SInt"),
                        Width::W64 | Width::Nat => ("I64", "SInt"),
                    };
                    msg!(
                        "nibcheck-mismatch-number",
                        what = what,
                        found = a.to_string(),
                        expected = b.to_string(),
                        checked = checked,
                        module = module
                    )
                }
                _ if matches!(b, Ty::Borrow(..)) && !matches!(a, Ty::Borrow(..)) => {
                    msg!(
                        "nibcheck-mismatch-lend",
                        what = what,
                        found = a.to_string(),
                        expected = b.to_string()
                    )
                }
                _ => msg!(
                    "nibcheck-mismatch",
                    what = what,
                    found = a.to_string(),
                    expected = b.to_string()
                ),
            };
            self.error(message, span);
        }
    }

    /// `t` for a message: an integer of unknown width reads as `i64`.
    fn shown(&self, t: &Ty) -> Ty {
        match self.resolve(t) {
            Ty::Var(v) if self.ints.contains(&v) => Ty::Int(Width::W64),
            Ty::Fn(ps, r, k) => Ty::Fn(
                ps.iter().map(|p| self.shown(p)).collect(),
                Box::new(self.shown(&r)),
                k,
            ),
            Ty::Union(ts) => union(ts.iter().map(|t| self.shown(t)).collect()),
            Ty::Tagged(tags, t) => tagged(tags, self.shown(&t)),
            Ty::Named(n, args) => Ty::Named(n, args.iter().map(|a| self.shown(a)).collect()),
            Ty::Info(t) => Ty::Info(Box::new(self.shown(&t))),
            Ty::Borrow(t, m) => Ty::Borrow(Box::new(self.shown(&t)), m),
            other => other,
        }
    }

    /// The type of two branches: the same type, or their union.
    fn join(&mut self, a: &Ty, b: &Ty) -> Ty {
        if (self.has_vars(a) || self.has_vars(b)) && self.attempt(|c| c.unify(a, b)).is_ok() {
            return self.resolve(a);
        }
        let (a, b) = (self.resolve(a), self.resolve(b));
        if a == b || b == Ty::Never {
            return a;
        }
        if a == Ty::Never {
            return b;
        }
        // A borrow of a duplicable value is the value (`&A ≡ A`).
        match (&a, &b) {
            (Ty::Borrow(x, _), y) | (y, Ty::Borrow(x, _))
                if !matches!(y, Ty::Borrow(..)) && self.kind(x).dup() =>
            {
                let (x, y) = ((**x).clone(), y.clone());
                if self.attempt(|c| c.unify(&x, &y)).is_ok() {
                    return self.resolve(&x);
                }
            }
            _ => {}
        }
        union(vec![a, b])
    }

    /// A `quote` fills an expression only with a `SynExpr`, a `SynIdent` or
    /// a `Judgement`: anything else is a type error where it is written,
    /// not a failure when the macro runs.
    fn check_splices(&mut self) {
        let splices = std::mem::take(&mut self.splices);
        if splices.is_empty() {
            return;
        }
        let types: HashMap<TermId, Ty> = self.terms.iter().cloned().collect();
        for (id, span) in splices {
            let Some(t) = types.get(&id) else { continue };
            let t = self.resolve(t);
            let fits = matches!(&t, Ty::Named(name, args) if args.is_empty()
                && ["SynExpr", "SynIdent", "Judgement"]
                    .iter()
                    .any(|n| tauto_surface::bindings::is_library(name, n)));
            if !fits {
                let shown = self.shown(&t);
                self.error(
                    format!("a `$` in an expression of a `quote` takes a SynExpr, a SynIdent or a Judgement, not {shown}"),
                    span,
                );
            }
        }
    }

    fn finish(mut self) -> TypeReport {
        let mut pending = std::mem::take(&mut self.constructor_uses);
        let mut records = std::mem::take(&mut self.constructor_records);
        loop {
            let mut remaining_records = Vec::new();
            let before_records = records.len();
            for (name, ty, values, span) in records {
                let expected = self.resolve(&ty);
                match self.datas.resolve_ctor(&name, Some(&expected)).cloned() {
                    Ok((d, c)) => {
                        let args: Vec<Ty> = self.datas.decls[&d]
                            .generics
                            .clone()
                            .iter()
                            .map(|_| self.fresh())
                            .collect();
                        let declared = self.datas.fields(&d, c, &args);
                        self.check_record_fields(&name, &values, &declared, span);
                        self.expect(
                            &Ty::Named(d, args),
                            &ty,
                            span,
                            msg!("nibcheck-what-record-constructor"),
                        );
                    }
                    Err(_) => remaining_records.push((name, ty, values, span)),
                }
            }
            records = remaining_records;
            let mut next = Vec::new();
            let before = pending.len();
            for (name, ty, span) in pending {
                let expected = self.resolve(&ty);
                match self.datas.resolve_ctor(&name, Some(&expected)).cloned() {
                    Ok((d, c)) => {
                        let actual = self.constructor(&d, c, span, &name);
                        self.expect(&actual, &ty, span, msg!("nibcheck-what-constructor"));
                    }
                    Err(_) => next.push((name, ty, span)),
                }
            }
            if next.len() == before && records.len() == before_records {
                for (name, ty, span) in next {
                    let message = self
                        .datas
                        .resolve_ctor(&name, Some(&self.resolve(&ty)))
                        .unwrap_err();
                    self.error(message, span);
                }
                for (name, ty, _, span) in records {
                    let message = self
                        .datas
                        .resolve_ctor(&name, Some(&self.resolve(&ty)))
                        .unwrap_err();
                    self.error(message, span);
                }
                break;
            }
            pending = next;
        }
        // An integer of unknown width is an `i64`.
        let unknown: Vec<usize> = self.ints.iter().copied().collect();
        for v in unknown {
            if let Ty::Var(w) = self.resolve(&Ty::Var(v)) {
                self.subst[w] = Some(Ty::Int(Width::W64));
            }
        }
        let mut report = TypeReport::default();
        for (span, ty) in std::mem::take(&mut self.ops) {
            if let Ty::Int(w) = self.resolve(&ty) {
                report.widths.insert(span, w);
            }
        }
        for (span, n, ty) in std::mem::take(&mut self.literals) {
            match self.resolve(&ty) {
                Ty::Int(w) => {
                    if !w.fits(n) {
                        self.error(
                            msg!(
                                "nibcheck-literal-does-not-fit",
                                literal = n.to_string(),
                                ty = Ty::Int(w).to_string()
                            ),
                            span,
                        );
                    }
                }
                _ => self.error("an integer literal has no integer type", span),
            }
        }
        // A closure returns no borrow but of a duplicable value (`&A ≡ A`);
        // a type still unknown might not be one.
        for (r, span) in std::mem::take(&mut self.closure_results) {
            let t = self.resolve(&r);
            if self.is_view(&t) && (self.has_vars(&t) || self.view_value(&t).is_none()) {
                self.error("a closure cannot return a borrow", span);
            }
        }
        // A capture inferred after its function was declared must still fit
        // that function's fixed ownership. This validates the origin rather
        // than silently changing kinds already used by aliases or bounds.
        for (captures, kind, span) in std::mem::take(&mut self.capture_kinds) {
            for (name, ty) in captures {
                let ty = self.resolve(&ty);
                if matches!(ty, Ty::Borrow(..)) {
                    continue;
                }
                let (least, most) = self.datas.kind_range(&ty);
                if most.fits(kind) {
                    continue;
                }
                let message = if least == most {
                    format!(
                        "capture `{name}` is inferred as {most} after its function kind was fixed; add a type annotation to the captured binding"
                    )
                } else {
                    format!(
                        "the kind of capture `{name}` is not determined; add a type annotation to the captured binding"
                    )
                };
                if !self
                    .errors
                    .iter()
                    .any(|e| e.span == span && e.message.as_text() == Some(message.as_str()))
                {
                    self.error(message, span);
                }
                break;
            }
        }
        for (t, bound, span) in std::mem::take(&mut self.bounds) {
            if self.is_view(&t) {
                self.error("a view cannot be a type argument", span);
                continue;
            }
            let k = self.kind(&t);
            if !k.fits(bound) {
                let t = self.shown(&t);
                self.error(
                    msg!(
                        "nibcheck-kind-does-not-fit-bound",
                        kind = k.to_string(),
                        bound = bound.to_string(),
                        ty = t.to_string()
                    ),
                    span,
                );
            }
        }
        for (t, arg, result, what, span) in std::mem::take(&mut self.ctor_bounds) {
            let t = self.resolve(&t);
            let made = match &t {
                Ty::Named(..) => apply(t.clone(), Ty::Param(Param::kind_witness(arg), arg)),
                Ty::Param(..) => t.clone(),
                _ => continue,
            };
            let k = self.kind(&made);
            if !k.fits(result) {
                let shown = self.shown(&made);
                self.error(
                    format!("{what} takes constructors from {arg} to {result}, and {shown} is {k}"),
                    span,
                );
            }
        }
        self.check_splices();
        let mut evidence: HashMap<TermId, Vec<Ev>> = HashMap::new();
        for p in std::mem::take(&mut self.pending) {
            let t = self.resolve(&p.ty);
            let ev = if STRUCTURAL.contains(&p.class.as_str()) {
                if self.datas.structural(&p.class, &t, &p.assume) {
                    Ev::Structural
                } else {
                    let shown = self.shown(&t);
                    let class = written(&p.class);
                    let hint = match t {
                        Ty::Param(..) => format!(": add where {class}({shown})"),
                        _ => String::new(),
                    };
                    self.error(
                        format!("{} needs {class}({shown}){hint}", written(&p.what)),
                        p.span,
                    );
                    Ev::Missing
                }
            } else {
                match self.resolve_class(&p.class, &t, &p.assume) {
                    Ok(ev) => ev,
                    Err(why) => {
                        let class = written(&p.class);
                        let message = match why {
                            Unresolved::Undetermined => {
                                format!("the type in {class}(?) is not determined")
                            }
                            Unresolved::Assumption(shown) => format!(
                                "{} needs {class}({shown}): add where {class}({shown})",
                                written(&p.what)
                            ),
                            Unresolved::NoInstance(shown) => {
                                format!("no instance {class}({shown})")
                            }
                        };
                        self.error(message, p.span);
                        Ev::Missing
                    }
                }
            };
            if let Some((span, n, total)) = p.slot {
                let slots = evidence
                    .entry(span)
                    .or_insert_with(|| vec![Ev::Missing; total]);
                slots[n] = ev;
            }
        }
        report.evidence = evidence;
        report.classes = self
            .classes
            .iter()
            .map(|(n, c)| (n.clone(), c.decl.clone()))
            .collect();
        report.lets = self
            .lets
            .iter()
            .map(|(n, t)| (n.to_string(), self.resolve(t).to_string()))
            .collect();
        report.locals = std::mem::take(&mut self.locals)
            .into_iter()
            .map(|(k, t)| (k, self.resolve(&t)))
            .collect();
        report.redundant_arms = std::mem::take(&mut self.redundant_arms)
            .into_iter()
            .collect();
        report.pair_members = std::mem::take(&mut self.pair_members);
        report.product_fits = std::mem::take(&mut self.product_fits)
            .into_iter()
            .map(|(span, t)| (span, self.resolve(&t)))
            .collect();
        report.type_references = std::mem::take(&mut self.type_references);
        report.terms = std::mem::take(&mut self.terms)
            .into_iter()
            .map(|(k, t)| (k, self.resolve(&t)))
            .collect();
        // Every use of a generic function settles its type arguments: one
        // that nothing fixes would leave each backend to pick its own.
        // An arm answers whatever instance of its operation is performed, so
        // nothing at the arm fixes the operation's generics. A function's
        // generic that such an arm gives a value to (the `E` of a `catch`
        // that answers `fail`) is fixed by what its caller performs, which
        // these types do not follow.
        let mut arm = HashSet::new();
        let mut by_effects = std::mem::take(&mut self.prelude_effect_generics);
        for v in &self.arm_generics {
            match self.resolve(&Ty::Var(*v)) {
                Ty::Var(w) => {
                    arm.insert(w);
                }
                Ty::Param(p, _) => {
                    by_effects.insert(p.id.clone());
                }
                _ => {}
            }
        }
        for (id, name, generics) in std::mem::take(&mut self.undetermined) {
            let open: Vec<&str> = generics
                .iter()
                .filter(|(g, t)| {
                    !by_effects.contains(g.id())
                        && !self
                            .index_generics
                            .get(&name)
                            .is_some_and(|gs| gs.contains(&g.name))
                        && self.has_open_vars(t, &arm)
                })
                .map(|(g, _)| g.name.as_str())
                .collect();
            if !open.is_empty() {
                self.error(
                    format!(
                        "the type {} of `{name}` is not determined here: give the value a type, as in `let x: T = ...`",
                        open.iter().map(|g| format!("`{g}`")).collect::<Vec<_>>().join(", ")
                    ),
                    id.span(),
                );
            }
        }
        report.effect_generics = by_effects;
        report.instantiations = std::mem::take(&mut self.instantiations)
            .into_iter()
            .map(|(site, args)| {
                (
                    site,
                    args.into_iter()
                        .map(|(id, ty)| (id, self.resolve(&ty)))
                        .collect(),
                )
            })
            .collect();
        report.effect_args = std::mem::take(&mut self.effect_args)
            .into_iter()
            .map(|(site, args)| (site, args.iter().map(|t| self.resolve(t)).collect()))
            .collect();
        report.schemes = std::mem::take(&mut self.fns)
            .into_iter()
            .map(|(n, s)| {
                let ty = self.resolve(&s.ty);
                (n, Scheme { ty, ..s })
            })
            .collect();
        let mut counts: HashMap<Name, usize> = HashMap::new();
        for (n, _) in &self.local_fns {
            *counts.entry(n.clone()).or_insert(0) += 1;
        }
        let local_fns = std::mem::take(&mut self.local_fns);
        for (n, s) in local_fns {
            if counts[&n] == 1 && !report.schemes.contains_key(&n) {
                let ty = self.resolve(&s.ty);
                report.local_schemes.insert(n, Scheme { ty, ..s });
            }
        }
        report.operation_facts = Some(self.finish_operation_facts());
        report.errors = self.errors;
        report.datas = self.datas;
        report.quants = self.quants;
        report.effects = self.effects;
        report
    }

    /// A declared type is written with all its arguments, except where a
    /// type constructor is wanted.
    fn arity(&mut self, name: &Name, given: usize, span: Span) {
        if self.constructor_position {
            return;
        }
        if let Some(d) = self.datas.decls.get(name)
            && given != d.generics.len()
        {
            let want = d.generics.len();
            self.error(format!("{name} takes {want} arguments"), span);
        }
    }

    /// A row given to a row parameter as a type: `Named(ROW_TYPE, entries)`
    /// with the entries sorted, or the row variable's own type. An entry
    /// `res(A)` is `Named(res, [A])`; a tail `| e` is `Named(ROW_TAIL, [e])`.
    fn row_as_type(&mut self, a: &SurfaceTerm, generics: &HashMap<Name, Ty>) -> Ty {
        let TermKind::Row(names) = &*a.kind else {
            return self.written(a, generics);
        };
        let mut members: Vec<Ty> = names
            .iter()
            .map(|n| {
                match n
                    .strip_prefix('|')
                    .map(Name::from)
                    .or_else(|| generics.contains_key(n).then(|| n.clone()))
                {
                    Some(var) => match generics.get(&var) {
                        Some(t) => Ty::Named(Name::from(ROW_TAIL), vec![t.clone()]),
                        None => Ty::Named(Name::from(ROW_TAIL), vec![self.fresh()]),
                    },
                    None => match indices::application(n) {
                        Some((head, args)) => Ty::Named(
                            head,
                            args.iter().map(|a| self.row_as_type(a, generics)).collect(),
                        ),
                        None => Ty::Named(n.clone(), Vec::new()),
                    },
                }
            })
            .collect();
        members.sort_by_key(|m| format!("{m}"));
        members.dedup();
        match members.as_slice() {
            [Ty::Named(tail, only)] if tail.as_str() == ROW_TAIL => only[0].clone(),
            _ => Ty::Named(Name::from(ROW_TYPE), members),
        }
    }

    fn written(&mut self, t: &SurfaceTerm, generics: &HashMap<Name, Ty>) -> Ty {
        let head = match &*t.kind {
            TermKind::App { function, .. } => function.as_ref(),
            _ => t,
        };
        if let TermKind::Var(Name::Selection(selection)) = &*head.kind {
            let families: Vec<_> = selection
                .candidates()
                .iter()
                .map(|r| Name::Global(r.clone()))
                .filter(|name| self.datas.decls.contains_key(name))
                .collect();
            if let [family] = families.as_slice() {
                self.type_references.insert(head.id(), family.clone());
                let kind = match &*t.kind {
                    TermKind::App {
                        function,
                        arguments,
                    } => TermKind::App {
                        function: Box::new(
                            function.with_kind(TermKind::Var(family.clone()), function.span),
                        ),
                        arguments: arguments.clone(),
                    },
                    _ => TermKind::Var(family.clone()),
                };
                return self.written(&t.with_kind(kind, t.span), generics);
            }
        }
        let under_borrow = std::mem::take(&mut self.under_borrow);
        match &*t.kind {
            TermKind::Var(n) => match if tauto_surface::bindings::is_library(n, n.as_str()) {
                n.as_str()
            } else {
                ""
            } {
                "i32" => Ty::Int(Width::W32),
                "i64" => Ty::Int(Width::W64),
                "u8" => Ty::Int(Width::U8),
                "u32" => Ty::Int(Width::U32),
                "u64" => Ty::Int(Width::U64),
                "nat" => Ty::Int(Width::Nat),
                "Bool" => Ty::Bool,
                "Text" => Ty::Text,
                "Unit" => Ty::Unit,
                "Never" => Ty::Never,
                "Decimal" => Ty::Decimal,
                "Float" => Ty::Float,
                "Float32" => Ty::Float32,
                _ => match generics.get(n) {
                    Some(t) => t.clone(),
                    None => {
                        self.arity(n, 0, t.span);
                        Ty::Named(n.clone(), Vec::new())
                    }
                },
            },
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(n)
                    if tauto_surface::bindings::is_library(&n, "Tuple") && arguments.is_empty() =>
                {
                    Ty::Unit
                }
                TermKind::Var(n)
                    if tauto_surface::bindings::is_library(&n, "Info") && arguments.len() == 1 =>
                {
                    Ty::Info(Box::new(self.written(&arguments[0], generics)))
                }
                TermKind::Var(n) if generics.contains_key(n) => {
                    if arguments.len() != 1 {
                        self.error(
                            format!("{n} is a type constructor variable and takes one argument"),
                            t.span,
                        );
                        return self.fresh();
                    }
                    let x = self.written(&arguments[0], generics);
                    apply(generics[n].clone(), x)
                }
                // `Result(E)(A)`: the arguments of both.
                TermKind::App {
                    function: inner,
                    arguments: first,
                } => {
                    let mut merged = first.clone();
                    merged.extend(arguments.iter().cloned());
                    let flat = SurfaceTerm::new(
                        TermKind::App {
                            function: inner.clone(),
                            arguments: merged,
                        },
                        t.span,
                    );
                    self.written(&flat, generics)
                }
                TermKind::Var(n) if !tauto_surface::bindings::is_library(n, "Tuple") => {
                    if tauto_surface::bindings::is_library(&n, "Slice") && !under_borrow {
                        self.error("Slice(A) can only be borrowed", t.span);
                    }
                    let rows = self.row_params.get(n).cloned().unwrap_or_default();
                    let args: Vec<Ty> = arguments
                        .iter()
                        .enumerate()
                        .map(|(i, a)| match &*a.kind {
                            _ if rows.contains(&i) => {
                                // A name is a row variable; whether it is one
                                // is the row check's to say.
                                if !matches!(&*a.kind, TermKind::Row(_) | TermKind::Var(_)) {
                                    self.error(
                                        format!("{n} takes an effect row here, as in `{n}(!{{a | e}})`"),
                                        a.span,
                                    );
                                }
                                if self.rows_as_types {
                                    self.row_as_type(a, generics)
                                } else {
                                    Ty::Unit
                                }
                            }
                            TermKind::Row(_) => {
                                self.error(
                                    format!("an effect row is given only to a row parameter, and this one of {n} is not"),
                                    a.span,
                                );
                                Ty::Unit
                            }
                            _ => self.written(a, generics),
                        })
                        .collect();
                    self.arity(n, args.len(), t.span);
                    Ty::Named(n.clone(), args)
                }
                _ => {
                    self.error("not a type", t.span);
                    self.fresh()
                }
            },
            TermKind::Pi { params, result, .. } => {
                // `(A: Shared, B: Type, …)` first: the expansion's
                // `<A: Shared, B: Type>(…) -> …`.
                let binders: Vec<(Param, Kind)> = params
                    .iter()
                    .enumerate()
                    .map_while(|(index, (n, p))| match (n, &*p.kind) {
                        (Some(n), TermKind::Var(k)) => Some((
                            Param::new(
                                ParamId::Poly {
                                    occurrence: t.id(),
                                    index,
                                },
                                n.clone(),
                            ),
                            Kind::parse(k)?,
                        )),
                        _ => None,
                    })
                    .collect();
                let mut inner = generics.clone();
                for (n, k) in &binders {
                    inner.insert(n.name.clone(), Ty::Param(n.clone(), *k));
                }
                let fun = Ty::Fn(
                    params[binders.len()..]
                        .iter()
                        .map(|(_, p)| self.written(p, &inner))
                        .collect(),
                    Box::new(self.written(result, &inner)),
                    Kind::Shared,
                );
                if binders.is_empty() {
                    fun
                } else {
                    Ty::Poly(binders, Box::new(fun))
                }
            }
            TermKind::FnKind { kind, ty } => match self.written(ty, generics) {
                Ty::Fn(ps, r, _) => Ty::Fn(ps, r, Kind::parse(kind).unwrap_or(Kind::Shared)),
                other => {
                    self.error(format!("`{kind}` is the kind of a function type"), t.span);
                    other
                }
            },
            TermKind::Borrow { mutable, term } => {
                self.under_borrow = true;
                Ty::Borrow(Box::new(self.written(term, generics)), *mutable)
            }
            TermKind::Union(ts) => union(ts.iter().map(|t| self.written(t, generics)).collect()),
            TermKind::Product(ts) => {
                let members = ts.iter().map(|t| self.written(t, generics)).collect();
                self.product(members)
            }
            TermKind::Tagged { tag, term } => {
                tagged(BTreeSet::from([tag.clone()]), self.written(term, generics))
            }
            // What the reader could not read, said as it says it (`a record writes …`).
            TermKind::Other(what) if what.starts_with('`') => {
                self.error(what.clone(), t.span);
                self.fresh()
            }
            _ => {
                self.error("not a type of a program", t.span);
                self.fresh()
            }
        }
    }

    // ---------------------------------------------------------------------
    // Declarations

    fn effect_owner(&self, name: &Name, span: Span) -> EffectOwner {
        EffectOwner {
            name: name.into(),
            occurrence: TermId::fresh(span),
            function: self.function_owner.clone(),
            site: self.declaration_path.clone(),
        }
    }

    fn declare_effect(&mut self, e: &EffectDecl) {
        let owner = self.effect_owner(&e.name, e.span);
        let generics: HashMap<Name, Ty> = e
            .generics
            .iter()
            .enumerate()
            .map(|(index, g)| {
                (
                    g.clone(),
                    Ty::Param(Param::effect(&owner, index, g), Kind::Linear),
                )
            })
            .collect();
        for (index, g) in e.generics.iter().enumerate() {
            if e.rows.get(index) == Some(&true) {
                self.effect_rows.insert(Param::effect(&owner, index, g).id);
            }
        }
        let params = e
            .params
            .iter()
            .map(|p| match p {
                Some(p) => self.written(p, &generics),
                None => {
                    self.error(format!("a parameter of `{}` has no type", e.name), e.span);
                    Ty::Never
                }
            })
            .collect();
        let result = match &e.result {
            Some(r) => self.written(r, &generics),
            None => Ty::Unit,
        };
        let quant = match &e.resume {
            None => Quant::AtMostOne,
            Some(q) => Quant::parse(q).unwrap_or_else(|| {
                self.error(format!("`resume {q}`: write 0, <=1, 1 or ω"), e.span);
                Quant::AtMostOne
            }),
        };
        self.quants.insert(e.name.clone(), quant);
        self.effects.insert(
            e.name.clone(),
            EffectSig {
                generics: e
                    .generics
                    .iter()
                    .enumerate()
                    .map(|(i, g)| Param::effect(&owner, i, g))
                    .collect(),
                params,
                result,
            },
        );
    }

    /// Records a `struct` or `enum`; field types are checked again after
    /// all declarations are known.
    fn declare_data(&mut self, d: &DataDecl, is_struct: bool, builtin: bool) {
        let view = d.kind.as_deref() == Some("view");
        let declared = if view {
            Some(Kind::Affine)
        } else {
            d.kind.as_deref().and_then(Kind::parse)
        };
        if view && (!is_struct || d.constructors.iter().any(|c| !c.fields.is_empty())) {
            self.error("a view struct has no fields: it is an opaque type", d.span);
        }
        // Still here: it could not be the `inductive` it says it is.
        if d.kind.as_deref() == Some(tauto_surface::inductive_data::KIND) {
            for (why, at) in tauto_surface::inductive_data::problems(d, is_struct) {
                self.error(why, at);
            }
        }
        let generics: HashMap<Name, Ty> = d
            .generics
            .iter()
            .enumerate()
            .map(|(index, g)| {
                (
                    g.clone(),
                    Ty::Param(Param::data(&d.name, index, g), Kind::Linear),
                )
            })
            .collect();
        let constructors = d
            .constructors
            .iter()
            .map(|c| DataCtor {
                name: c.name.clone(),
                fields: c
                    .fields
                    .iter()
                    .map(|(n, t)| {
                        if term_has_borrow(t) {
                            self.error("a borrow cannot be a field", t.span);
                        }
                        (n.clone(), self.written(t, &generics))
                    })
                    .collect(),
            })
            .collect::<Vec<_>>();
        for (i, c) in constructors.iter().enumerate() {
            self.datas.register_ctor(c.name.clone(), d.name.clone(), i);
            if c.name.is_resolved() {
                continue;
            }
            self.datas.ctors.insert(
                format!("{}::{}", d.name, c.name).into(),
                (d.name.clone(), i),
            );
            // `T::C` for a constructor renamed to its full name (`m.T.C`).
            let written = c.name.rsplit("::").next().unwrap_or(&c.name);
            if written != c.name.as_str() {
                self.datas
                    .ctors
                    .insert(format!("{}::{written}", d.name).into(), (d.name.clone(), i));
            }
        }
        if is_struct && constructors.len() == 1 {
            self.datas.ctors.insert(d.name.clone(), (d.name.clone(), 0));
        }
        self.datas.decls.insert(
            d.name.clone(),
            Data {
                name: d.name.clone(),
                declared,
                generics: d.generics.clone(),
                constructors,
                is_struct,
                recursive: false,
                base: Kind::Linear,
                holds: d.generics.clone(),
                builtin,
                view,
            },
        );
    }

    /// Which declarations hold themselves, and whether a written kind is
    /// looser than what the fields give.
    fn finish_datas(&mut self, program: &Program) {
        let names: Vec<Name> = self.datas.decls.keys().cloned().collect();
        for n in &names {
            let recursive = reaches(&self.datas, n, n, &mut HashSet::new());
            if let Some(d) = self.datas.decls.get_mut(n) {
                d.recursive = recursive;
            }
        }
        self.datas.summarize();
        for s in &program.stmts {
            let (Stmt::Struct(d) | Stmt::Enum(d)) = s else {
                continue;
            };
            let Some(data) = self.datas.decls.get(&d.name).cloned() else {
                continue;
            };
            let Some(declared) = data.declared else {
                continue;
            };
            if data.recursive && declared < Kind::Shared {
                self.error(
                    format!(
                        "declared {declared} but `{}` holds itself, so it is shared",
                        d.name
                    ),
                    d.span,
                );
                continue;
            }
            // The declaration's own fields, whatever its type parameters
            // are instantiated with.
            let least: HashMap<ParamId, Ty> = data
                .parameters()
                .into_iter()
                .map(|g| (g.id.clone(), Ty::Param(g, Kind::Copy)))
                .collect();
            'fields: for c in &data.constructors {
                for (i, (n, f)) in c.fields.iter().enumerate() {
                    let k = self.datas.kind(&substitute(f, &least));
                    if !k.fits(declared) || (declared == Kind::Copy && k != Kind::Copy) {
                        let field = n.clone().unwrap_or_else(|| format!("{} of {}", i, c.name));
                        self.error(
                            format!("declared {declared} but field {field} is {k}"),
                            d.span,
                        );
                        break 'fields;
                    }
                }
            }
        }
    }

    fn signature(&mut self, f: &FnDecl) -> Scheme {
        let owner = FunctionOwner {
            name: f.name.clone(),
            body: f.body.id(),
            parent: self.function_owner.clone().map(Box::new),
            // Top-level names are unique; keeping their owner independent of
            // registration phase makes cached prelude facts use the same IDs.
            site: if self.function_owner.is_some() {
                self.declaration_path.clone()
            } else {
                Vec::new()
            },
        };
        self.signature_in(f, owner)
    }

    fn signature_in(&mut self, f: &FnDecl, owner: FunctionOwner) -> Scheme {
        let mut generics: Vec<(Param, Kind)> = Vec::new();
        let mut ctors: Vec<(Param, Kind)> = Vec::new();
        let mut map: HashMap<Name, Ty> = HashMap::new();
        for (i, g) in f.generics.iter().enumerate() {
            // Native Nib has type and row generics only. A checked term
            // telescope must first be lowered to ordinary value parameters;
            // ignoring its domain here would silently erase an argument.
            fn native_kind(ty: &SurfaceTerm) -> bool {
                match &*ty.kind {
                    TermKind::Var(name) => name.sort_symbol().is_some_and(|sort| {
                        matches!(sort, tauto_surface::identity::SortSymbol::Type(_))
                    }),
                    TermKind::App { function, .. } => matches!(&*function.kind,
                        TermKind::Var(name) if name.sort_symbol().is_some_and(|sort| matches!(sort, tauto_surface::identity::SortSymbol::Type(_)))),
                    TermKind::Pi {
                        params,
                        result,
                        effects,
                    } => {
                        effects.as_ref().is_none_or(Vec::is_empty)
                            && params.iter().all(|(_, ty)| native_kind(ty))
                            && native_kind(result)
                    }
                    _ => false,
                }
            }
            if f.rows.get(i) != Some(&true)
                && (f.generic_types.get(i).is_some_and(|ty| !native_kind(ty))
                    || f.bounds
                        .get(i)
                        .and_then(|bound| bound.as_deref())
                        .is_some_and(|bound| {
                            Kind::parse(bound).is_none() && Kind::parse_ctor(bound).is_none()
                        }))
            {
                self.error(
                    format!(
                        "term generic `{g}` requires checked extraction before native compilation"
                    ),
                    f.bound_spans.get(i).copied().unwrap_or(f.span),
                );
            }
            let param = Param::new(
                ParamId::Function {
                    owner: owner.clone(),
                    index: i,
                },
                g.clone(),
            );
            let bound = f.bounds.get(i).cloned().flatten();
            if let Some((arg, result)) = bound.as_deref().and_then(Kind::parse_ctor) {
                generics.push((param.clone(), result));
                ctors.push((param.clone(), arg));
                map.insert(g.clone(), Ty::Param(param, result));
                continue;
            }
            let bound = match bound.as_deref() {
                None => Some(Kind::Affine),
                Some(b) => Kind::parse(b),
            };
            if f.effects
                .iter()
                .flatten()
                .any(|e| e.strip_prefix('|') == Some(g.as_str()))
            {
                self.row_generics.insert(param.id.clone());
            }
            // A bound that is not a kind (`<!e: <=1>`, `<!h: Host>`) makes a row variable;
            // the reader gives `Shared` as `shared` and a bare `Type` as no bound.
            if let Some(k) = bound {
                generics.push((param.clone(), k));
                map.insert(g.clone(), Ty::Param(param, k));
            }
        }
        let params = f
            .param_types
            .iter()
            .zip(f.borrows.iter().chain(std::iter::repeat(&None)))
            .map(|(p, b)| {
                self.under_borrow = b.is_some();
                let t = match p {
                    Some(p) => self.written(p, &map),
                    None => self.fresh(),
                };
                // An inferred parameter has no written type to consume this flag.
                self.under_borrow = false;
                match b {
                    Some(m) if !matches!(t, Ty::Borrow(..)) => Ty::Borrow(Box::new(t), *m),
                    _ => t,
                }
            })
            .collect::<Vec<_>>();
        let result = match &f.result {
            Some(r) => self.written(r, &map),
            None => self.fresh(),
        };
        if self.is_view(&result) {
            let span = f.result.as_ref().map_or(f.span, |r| r.span);
            let shown = self.shown(&result);
            if self.has_mut_borrow(&result) {
                if !params.iter().any(|p| matches!(p, Ty::Borrow(_, true))) {
                    self.error(format!("-> {shown} needs a &mut parameter"), span);
                }
            } else if !params.iter().any(|p| matches!(p, Ty::Borrow(..))) {
                self.error(format!("-> {shown} needs a borrowed parameter"), span);
            }
        }
        let mut preds: Vec<(Name, Param)> = Vec::new();
        for c in &f.where_ {
            if !c.arguments.is_empty() {
                self.error(
                    "value-indexed constraints require checked dictionary extraction",
                    c.span,
                );
                continue;
            }
            if !STRUCTURAL.contains(&c.class.as_str()) && !self.classes.contains_key(&c.class) {
                self.error(format!("{} is not a class", c.class), c.span);
                continue;
            }
            let generic = match &*c.ty.kind {
                TermKind::Var(g) if generics.iter().any(|(n, _)| &n.name == g) => generics
                    .iter()
                    .find(|(n, _)| &n.name == g)
                    .unwrap()
                    .0
                    .clone(),
                _ => {
                    self.error(
                        format!("where constrains only generics of {}", f.name),
                        c.span,
                    );
                    continue;
                }
            };
            let pred = (c.class.clone(), generic);
            if preds.contains(&pred) {
                self.error(format!("{}({}) is written twice", pred.0, pred.1), c.span);
                continue;
            }
            preds.push(pred);
        }
        Scheme {
            owner,
            generics,
            ty: Ty::Fn(params, Box::new(result), Kind::Shared),
            preds,
            ctors,
        }
    }

    /// A function's type at a use, its constraints left to be checked once
    /// the types are known.
    fn instantiate_scheme(
        &mut self,
        name: &Name,
        s: &Scheme,
        id: TermId,
        instantiation: Instantiation,
    ) -> Ty {
        let span = id.span();
        let mut arguments = HashMap::new();
        for (g, k) in &s.generics {
            let v = match instantiation {
                Instantiation::Fresh => self.fresh(),
                Instantiation::SelfSignature => Ty::Param(g.clone(), *k),
            };
            match s.ctors.iter().find(|(c, _)| c == g) {
                Some((_, arg)) => {
                    self.ctor_bounds
                        .push((v.clone(), *arg, *k, name.to_string(), span))
                }
                None => self.bounds.push((v.clone(), *k, span)),
            }
            arguments.insert(g.id.clone(), v);
        }
        if matches!(instantiation, Instantiation::Fresh) {
            // A generic the type does not mention (a row of effects) is not
            // a type argument any backend writes.
            let ty = self.resolve(&s.ty);
            let generics = s
                .generics
                .iter()
                .filter(|(g, _)| param_in(&ty, g) && !self.row_generics.contains(g.id()))
                .map(|(g, _)| (g.clone(), arguments[g.id()].clone()))
                .collect();
            self.undetermined.push((id, name.clone(), generics));
        }
        self.instantiations.push((id, arguments.clone()));
        for (n, (class, g)) in s.preds.iter().enumerate() {
            self.pending.push(Pending {
                class: class.clone(),
                ty: arguments[g.id()].clone(),
                what: name.to_string(),
                assume: self.assume.clone(),
                span,
                slot: Some((id, n, s.preds.len())),
            });
        }
        // An inferred result can already refer to the declaration's binders.
        substitute(&self.resolve(&s.ty), &arguments)
    }

    /// A type that holds a borrow, received as one is: a borrow, a
    /// `view struct`, or an `Option`, `Result` or `Pair` of one.
    fn is_view(&self, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Borrow(..) => true,
            Ty::Named(n, args) => {
                self.datas.decls.get(&n).is_some_and(|d| d.view)
                    || (["Option", "Result", "Pair"]
                        .iter()
                        .any(|native| tauto_surface::bindings::is_library(&n, native))
                        && args.iter().any(|a| self.is_view(a)))
            }
            _ => false,
        }
    }

    /// Whether a borrow is anywhere in `t`, or may be: an unknown part may
    /// turn out to be one.
    fn holds_borrow(&self, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Borrow(..) | Ty::Var(_) => true,
            Ty::Fn(..) => false,
            Ty::Union(ts) => ts.iter().any(|t| self.holds_borrow(t)),
            Ty::Tagged(_, t) | Ty::Info(t) | Ty::Poly(_, t) => self.holds_borrow(&t),
            Ty::App(h, x) => self.holds_borrow(&h) || self.holds_borrow(&x),
            Ty::Named(_, args) => args.iter().any(|a| self.holds_borrow(a)),
            _ => false,
        }
    }

    fn has_mut_borrow(&self, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Borrow(_, true) => true,
            Ty::Borrow(inner, false) => self.has_mut_borrow(&inner),
            Ty::Named(_, args) => args.iter().any(|a| self.has_mut_borrow(a)),
            _ => false,
        }
    }

    /// The value a view of duplicable things stands for (`&A ≡ A`), or
    /// `None` when something in it is not duplicable or is a `&mut`.
    fn view_value(&self, t: &Ty) -> Option<Ty> {
        match self.resolve(t) {
            Ty::Borrow(_, true) => None,
            Ty::Borrow(inner, false) => {
                let v = self.view_value(&inner)?;
                self.kind(&v).dup().then_some(v)
            }
            Ty::Named(n, args) => {
                if self.datas.decls.get(&n).is_some_and(|d| d.view) {
                    return None;
                }
                let args: Option<Vec<Ty>> = args.iter().map(|a| self.view_value(a)).collect();
                Some(Ty::Named(n, args?))
            }
            other => Some(other),
        }
    }

    fn bind_local(
        &mut self,
        env: &mut Vec<Local>,
        name: &Name,
        ty: Ty,
        mutable: bool,
        site: TermId,
    ) {
        self.locals.push(((name.clone(), site), ty.clone()));
        env.push(Local {
            name: name.clone(),
            scheme: None,
            instantiation: Instantiation::Fresh,
            ty,
            mutable,
            view: false,
        });
    }

    fn check_fn(&mut self, f: &FnDecl, scheme: &Scheme, env: &[Local]) {
        let Ty::Fn(params, result, _) = &scheme.ty else {
            return;
        };
        let outer_owner = self.function_owner.replace(scheme.owner.clone());
        let outer_path = std::mem::take(&mut self.declaration_path);
        let outer_terms = std::mem::take(&mut self.term_path);
        let outer_children = std::mem::take(&mut self.term_children);
        let mut env = env.to_vec();
        if !scheme.generics.is_empty() && self.has_vars(&scheme.ty) {
            for local in &mut env {
                if local
                    .scheme
                    .as_ref()
                    .is_some_and(|own| own.owner == scheme.owner)
                {
                    local.instantiation = Instantiation::SelfSignature;
                }
            }
        }
        for (name, ty) in f.params.iter().zip(params) {
            self.bind_local(&mut env, name, ty.clone(), false, site(&f.body));
        }
        self.returns.push((**result).clone());
        let outer = std::mem::replace(&mut self.assume, scheme.preds.clone());
        let type_params = scheme
            .generics
            .iter()
            .map(|(g, k)| (g.name.clone(), Ty::Param(g.clone(), *k)))
            .collect();
        let outer_types = std::mem::replace(&mut self.type_params, type_params);
        self.result_hint = Some((**result).clone());
        let body = self.infer(&f.body, &mut env);
        self.type_params = outer_types;
        self.function_owner = outer_owner;
        self.declaration_path = outer_path;
        self.term_path = outer_terms;
        self.term_children = outer_children;
        self.assume = outer;
        self.returns.pop();
        self.expect(
            &body,
            result,
            f.body.span,
            msg!("nibcheck-what-result-of", name = f.name.to_string()),
        );
    }

    fn run(&mut self, program: &Program, prelude: &Program) {
        for (message, span) in &program.errors {
            self.error(message.clone(), *span);
        }
        self.resolved_names = has_references(program);
        let resolved = tauto_surface::bindings::declared_names(&prelude.stmts)
            .iter()
            .any(|n| n.is_resolved());
        let intrinsic = |name: &str| {
            if resolved {
                tauto_surface::bindings::library_name(name)
            } else {
                Name::from(name)
            }
        };
        let show = intrinsic("show");
        let show_owner = self.effect_owner(&show, Span::new(0, 0));
        self.builtin_show_owner = Some(show_owner.clone());
        self.effects.insert(
            show.clone(),
            EffectSig {
                generics: vec![Param::effect(&show_owner, 0, &"A".into())],
                params: vec![
                    Ty::Text,
                    Ty::Param(Param::effect(&show_owner, 0, &"A".into()), Kind::Linear),
                ],
                result: Ty::Unit,
            },
        );
        self.quants.insert(show, Quant::Direct);
        self.quants.insert(intrinsic("exceeded"), Quant::AtMostOne);
        self.row_params = crate::surface::row_parameters_of(
            prelude
                .stmts
                .iter()
                .chain(&program.stmts)
                .filter_map(|s| match s {
                    Stmt::Struct(d) | Stmt::Enum(d) => Some(d),
                    _ => None,
                }),
        );
        for stmt in &program.stmts {
            if let Stmt::Struct(d) | Stmt::Enum(d) = stmt {
                for var in d.undeclared_rows() {
                    self.error(
                        format!(
                            "the row variable `{var}` is not declared; write `{}(!{var})`",
                            d.name
                        ),
                        d.span,
                    );
                }
            }
        }
        self.indexed = indices::indexed_effects(program);
        self.indexed.extend(indices::indexed_effects(prelude));
        self.index_generics = indices::index_generics(prelude);
        self.index_generics.extend(indices::index_generics(program));
        // The prelude's declarations, unless the program declares the name.
        let own: HashSet<&Name> = program
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Struct(d) | Stmt::Enum(d) => Some(&d.name),
                Stmt::Fn(f) => Some(&f.name),
                Stmt::Effect(e) => Some(&e.name),
                _ => None,
            })
            .collect();
        for s in &prelude.stmts {
            match s {
                // An extern whose row names a standard effect is how the host
                // answers that effect (`HOST_EFFECTS`).
                Stmt::Extern { fns, .. } => {
                    for f in fns {
                        if crate::host::is_host_primitive(f) && !own.contains(&f.name) {
                            self.host_only.insert(f.name.clone());
                        }
                    }
                }
                // `module Host` wraps those externs with the permission
                // check and the waiting.
                Stmt::Fn(f)
                    if tauto_surface::bindings::is_host_module_fn(&f.name)
                        && !own.contains(&f.name) =>
                {
                    self.host_only.insert(f.name.clone());
                }
                _ => {}
            }
        }
        for s in &prelude.stmts {
            match s {
                Stmt::Struct(d) if !own.contains(&d.name) => {
                    let opaque = d.constructors.iter().all(|c| c.fields.is_empty());
                    self.declare_data(d, true, opaque)
                }
                Stmt::Enum(d) if !own.contains(&d.name) => self.declare_data(d, false, false),
                Stmt::Effect(e) if !own.contains(&e.name) => self.declare_effect(e),
                _ => {}
            }
        }
        // A type declared again is an error (below); the first declaration
        // keeps the name, so no constructor is read against another's fields.
        let mut declared = HashSet::new();
        for s in &program.stmts {
            match s {
                Stmt::Struct(d) if declared.insert(&d.name) => self.declare_data(d, true, false),
                Stmt::Enum(d) if declared.insert(&d.name) => self.declare_data(d, false, false),
                _ => {}
            }
        }
        self.finish_datas(program);
        let mut data_names = HashSet::new();
        let duplicate_data = program
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Struct(d) | Stmt::Enum(d) => Some(d),
                _ => None,
            })
            .find(|d| !data_names.insert(&d.name));
        if let Some(d) = duplicate_data {
            self.error(format!("type {} is declared twice", d.name), d.span);
        }
        let mut function_names = HashSet::new();
        let duplicate = program
            .stmts
            .iter()
            .flat_map(|s| match s {
                Stmt::Fn(f) => vec![f],
                Stmt::Extern { fns, .. } => fns.iter().collect(),
                _ => Vec::new(),
            })
            .find(|f| !function_names.insert(&f.name));
        if let Some(f) = duplicate {
            self.error(format!("function {} is declared twice", f.name), f.span);
        }
        // At this point every declaration is available, including forward and recursive references.
        for stmt in &program.stmts {
            let (Stmt::Struct(d) | Stmt::Enum(d)) = stmt else {
                continue;
            };
            let generics: HashMap<Name, Ty> = d
                .generics
                .iter()
                .enumerate()
                .map(|(index, g)| {
                    (
                        g.clone(),
                        Ty::Param(Param::data(&d.name, index, g), Kind::Linear),
                    )
                })
                .collect();
            for ctor in &d.constructors {
                for (_, field) in &ctor.fields {
                    self.written(field, &generics);
                }
            }
        }
        if !CHECKING_PRELUDE.get() && PRELUDE.get().is_some_and(|p| std::ptr::eq(prelude, p)) {
            self.prelude_effect_generics = prelude_report_for(program).effect_generics.clone();
        }
        let synthesized = self.declare_classes(program, prelude);
        for (i, s) in prelude.stmts.iter().enumerate() {
            let fns = match s {
                Stmt::Extern { fns, .. } => fns.iter().collect(),
                Stmt::Fn(f) => vec![f],
                _ => Vec::new(),
            };
            for (j, f) in fns
                .into_iter()
                .enumerate()
                .filter(|(_, f)| !own.contains(&f.name))
            {
                self.declaration_path = vec![0, i, j];
                let scheme = self.signature(f);
                self.fns.insert(f.name.clone(), scheme);
            }
        }
        let mut fns = Vec::new();
        for (i, s) in program.stmts.iter().enumerate() {
            self.declaration_path = vec![1, i];
            match s {
                Stmt::Effect(e) => self.declare_effect(e),
                Stmt::Fn(f) => {
                    let scheme = self.signature(f);
                    self.fns.insert(f.name.clone(), scheme.clone());
                    fns.push((f, scheme));
                }
                Stmt::Extern { fns: externs, .. } => {
                    for (j, f) in externs.iter().enumerate() {
                        self.declaration_path = vec![1, i, j];
                        let scheme = self.signature(f);
                        self.fns.insert(f.name.clone(), scheme);
                    }
                }
                _ => {}
            }
        }
        for f in &synthesized {
            let scheme = self.fns[&f.name].clone();
            fns.push((f, scheme));
        }
        for (f, scheme) in fns {
            self.check_fn(f, &scheme, &[]);
        }
        let mut env = Vec::new();
        for (i, s) in program.stmts.iter().enumerate() {
            self.declaration_path = vec![1, i];
            if matches!(
                s,
                Stmt::Fn(_)
                    | Stmt::Effect(_)
                    | Stmt::Struct(_)
                    | Stmt::Enum(_)
                    | Stmt::Extern { .. }
            ) {
                continue;
            }
            let before = env.len();
            self.stmt(s, &mut env);
            if let (Stmt::Let { name, .. }, Some(local)) = (s, env.get(before)) {
                self.lets.push((name.clone(), local.ty.clone()));
            }
        }
    }

    /// Checks a statement, adding what it binds to `env`; its type is the
    /// block's value when it is the last one.
    fn stmt(&mut self, s: &Stmt, env: &mut Vec<Local>) -> Ty {
        match s {
            Stmt::Let {
                name,
                ty,
                value,
                borrow,
                borrow_mut,
            } => {
                // The written type is what the value is checked against (`let n: Nat := 1`).
                let written = ty
                    .as_ref()
                    .map(|ty| self.written(ty, &self.type_params.clone()));
                self.result_hint = written.clone();
                let v = self.infer(value, env);
                let mut t = match written {
                    Some(t) => {
                        self.expect(
                            &v,
                            &t,
                            value.span,
                            msg!("nibcheck-what-named", name = name.to_string()),
                        );
                        t
                    }
                    None => v,
                };
                let resolved = self.resolve(&t);
                let view = self.is_view(&resolved);
                match (*borrow, view) {
                    (true, true) => {
                        if *borrow_mut && !self.has_mut_borrow(&resolved) {
                            self.error(
                                format!(
                                    "`let &mut {name}` binds what a function returns as `-> &mut A`"
                                ),
                                value.span,
                            );
                        }
                    }
                    (true, false) => self.error(
                        if *borrow_mut {
                            format!(
                                "`let &mut {name}` binds what a function returns as `-> &mut A`"
                            )
                        } else {
                            format!("`let &{name}` binds what a function returns as `-> &A`")
                        },
                        value.span,
                    ),
                    (false, true) => match self.view_value(&resolved) {
                        Some(plain) if !matches!(&*value.kind, TermKind::Borrow { .. }) => {
                            // `&A ≡ A`: a duplicable value is copied out.
                            t = plain;
                        }
                        _ => self.error(
                            format!(
                                "a borrow cannot be stored: `{name}` would hold {}",
                                self.shown(&resolved)
                            ),
                            value.span,
                        ),
                    },
                    (false, false) => {}
                }
                self.bind_local(env, name, t, false, site(value));
                Ty::Unit
            }
            Stmt::Var {
                name,
                ty,
                value,
                borrow,
            } => {
                let v = self.infer(value, env);
                let t = match ty {
                    Some(ty) => {
                        let t = self.written(ty, &self.type_params.clone());
                        self.expect(
                            &v,
                            &t,
                            value.span,
                            msg!("nibcheck-what-named", name = name.to_string()),
                        );
                        t
                    }
                    None => v,
                };
                let resolved = self.resolve(&t);
                if *borrow {
                    if !self.is_view(&resolved) {
                        self.error(
                            format!("`var &{name}` binds what a function returns as a view"),
                            value.span,
                        );
                    }
                } else if self.is_view(&resolved) {
                    self.error(
                        format!("a borrow cannot be stored in `var {name}`"),
                        value.span,
                    );
                } else if self.kind(&resolved) == Kind::Linear {
                    self.error(
                        format!(
                            "a var cannot hold a linear value: `{name}` is {}",
                            self.shown(&resolved)
                        ),
                        value.span,
                    );
                }
                self.bind_local(env, name, t, true, site(value));
                if *borrow && let Some(l) = env.last_mut() {
                    l.view = true;
                }
                Ty::Unit
            }
            Stmt::Assign {
                name,
                place: Some(place),
                value,
            } => {
                let v = self.infer(value, env);
                let target = msg!(
                    "nibcheck-what-named",
                    name = crate::surface::print::print_term(place)
                );
                match env.iter().rev().find(|l| l.name == *name) {
                    Some(l) if l.view => {
                        self.error("a field of a view var cannot be assigned", value.span);
                        return Ty::Unit;
                    }
                    Some(_) if self.mutable_place(place, env) => {}
                    Some(_) => {
                        self.error(
                            format!("{target} assigns a field of a `var` or a `&mut` parameter"),
                            place.span,
                        );
                        return Ty::Unit;
                    }
                    None => {
                        self.error(format!("{name} is not defined"), place.span);
                        return Ty::Unit;
                    }
                }
                // The place's type, not the borrow a read through `&mut`
                // would give.
                let ty = self.infer(place, env);
                let ty = self.resolve(&ty).unborrowed().clone();
                self.expect(&v, &ty, value.span, target);
                Ty::Unit
            }
            Stmt::Assign { name, value, .. } => {
                let v = self.infer(value, env);
                let found = env
                    .iter()
                    .rev()
                    .find(|l| l.name == *name)
                    .cloned()
                    .map(|mut l| {
                        l.ty = self.resolve(&l.ty);
                        l
                    });
                match found {
                    Some(l) if l.view => self.error("a view var cannot be reassigned", value.span),
                    Some(l) if l.mutable => self.expect(
                        &v,
                        &l.ty,
                        value.span,
                        msg!("nibcheck-what-named", name = name.to_string()),
                    ),
                    Some(Local {
                        ty: Ty::Borrow(inner, true),
                        ..
                    }) => self.expect(
                        &v,
                        &inner,
                        value.span,
                        msg!("nibcheck-what-named", name = name.to_string()),
                    ),
                    Some(_) => self.error(format!("`{name}` is not a var"), value.span),
                    None => self.error(format!("{name} is not defined"), value.span),
                }
                Ty::Unit
            }
            Stmt::Fn(f) => {
                let mut scheme = self.signature(f);
                let lam = SurfaceTerm::new(
                    TermKind::Lam {
                        params: f.params.clone(),
                        body: Box::new(f.body.clone()),
                        types: Vec::new(),
                    },
                    f.span,
                );
                let mut free = crate::lin::free_vars(&lam);
                free.retain(|name| name != &f.name);
                let captured = self.capture_kind(&free, env, Kind::Shared, f.span);
                if let Ty::Fn(_, _, kind) = &mut scheme.ty {
                    *kind = captured;
                }
                self.local_fns.push((f.name.clone(), scheme.clone()));
                self.bind_local(env, &f.name, scheme.ty.clone(), false, site(&f.body));
                env.last_mut().expect("a bound function").scheme = Some(scheme.clone());
                self.check_fn(f, &scheme, env);
                Ty::Unit
            }
            Stmt::Effect(e) => {
                self.declare_effect(e);
                Ty::Unit
            }
            Stmt::While { condition, body } => {
                let c = self.infer(condition, env);
                self.expect(
                    &c,
                    &Ty::Bool,
                    condition.span,
                    msg!("nibcheck-what-while-condition"),
                );
                self.infer(body, &mut env.clone());
                Ty::Unit
            }
            Stmt::Return(e) => {
                let (t, span) = match e {
                    Some(e) => {
                        self.result_hint = self.returns.last().cloned();
                        (self.infer(e, env), e.span)
                    }
                    None => (Ty::Unit, Span::new(0, 0)),
                };
                match self.returns.last().cloned() {
                    Some(r) => self.expect(&t, &r, span, msg!("nibcheck-what-returned-value")),
                    None => self.error("`return` outside a function", span),
                }
                Ty::Never
            }
            Stmt::Expr(e) => self.infer(e, env),
            Stmt::Theorem(_)
            | Stmt::Def(_)
            | Stmt::Import { .. }
            | Stmt::Module { .. }
            | Stmt::Mutual { .. }
            | Stmt::Attributed { .. }
            | Stmt::Called { .. }
            | Stmt::Class(_)
            | Stmt::Instance(_)
            | Stmt::Inductive(_) => Ty::Unit,
            Stmt::Struct(d) | Stmt::Enum(d) => {
                self.error("declare a type at the top level", d.span);
                Ty::Unit
            }
            Stmt::Extern { span, .. } => {
                self.error("declare an `extern` block at the top level", *span);
                Ty::Unit
            }
            Stmt::Other(what, span) => {
                self.error(format!("not supported yet: {what}"), *span);
                Ty::Unit
            }
            Stmt::Syntax { span, .. } | Stmt::Macro { span, .. } => {
                self.error("a syntax or a macro is declared at the top level", *span);
                Ty::Unit
            }
        }
    }

    fn lookup(&mut self, name: &Name, env: &[Local], id: TermId) -> Ty {
        let span = id.span();
        if let Some(l) = env.iter().rev().find(|l| l.name == *name) {
            if let Name::Selection(selection) = name {
                if let Some(binding) = selection.binding() {
                    self.type_references.insert(id, binding.clone().into());
                }
            }
            return match &l.scheme {
                Some(scheme) => self.instantiate_scheme(name, scheme, id, l.instantiation),
                None => l.ty.clone(),
            };
        }
        if let Some(s) = self.fns.get(name).cloned() {
            if span.start < crate::surface::PRELUDE_BASE && self.host_only.contains(name) {
                self.error(
                    format!(
                        "{name} is how the host answers the standard effects; perform the effect instead"
                    ),
                    span,
                );
            }
            return self.instantiate_scheme(name, &s, id, Instantiation::Fresh);
        }
        if tauto_surface::bindings::is_library(&name, "div")
            || tauto_surface::bindings::is_library(&name, "mod")
        {
            let i = self.fresh_int();
            // Its width decides where `div` overflows.
            self.ops.push((id, i.clone()));
            return Ty::Fn(vec![i.clone(), i.clone()], Box::new(i), Kind::Shared);
        }
        if let Some((d, c)) = self.datas.resolve_ctor(name, None).ok().cloned() {
            if matches!(name, Name::Selection(_)) {
                self.type_references
                    .insert(id, self.datas.decls[&d].constructors[c].name.clone());
            }
            return self.constructor(&d, c, span, name);
        }
        if self.datas.has_ctor(name) {
            let t = self.fresh();
            self.constructor_uses.push((name.clone(), t.clone(), span));
            return t;
        }
        self.error(format!("{name} is not defined"), span);
        self.fresh()
    }

    /// A constructor used as a value: a nullary one is its value, one with
    /// fields a function from them.
    fn constructor(&mut self, d: &Name, c: usize, span: Span, name: &Name) -> Ty {
        let data = self.datas.decls[d].clone();
        let args: Vec<Ty> = data.generics.iter().map(|_| self.fresh()).collect();
        let fields = self.datas.fields(d, c, &args);
        let result = Ty::Named(d.clone(), args);
        if data.is_struct {
            self.error(struct_value_message(name), span);
        }
        if fields.is_empty() {
            result
        } else {
            Ty::Fn(
                fields.into_iter().map(|(_, t)| t).collect(),
                Box::new(result),
                Kind::Shared,
            )
        }
    }

    fn infer(&mut self, term: &SurfaceTerm, env: &mut Vec<Local>) -> Ty {
        let child = self.term_children.last_mut().map_or(0, |n| {
            let child = *n;
            *n += 1;
            child
        });
        self.term_path.push(child);
        self.term_children.push(0);
        let hint = self.result_hint.take();
        let t = self.infer_term(term, env, hint);
        self.term_children.pop();
        self.term_path.pop();
        self.terms.push((term.id(), t.clone()));
        t
    }

    fn infer_term(&mut self, term: &SurfaceTerm, env: &mut Vec<Local>, hint: Option<Ty>) -> Ty {
        let span = term.span;
        match &*term.kind {
            TermKind::Nat(n) => {
                // Where a `Nat` is expected, a numeral is a `Nat`, as on the proof side.
                if let Some(h) = &hint
                    && let Ty::Named(name, args) = self.resolve(h)
                    && args.is_empty()
                    && tauto_surface::bindings::is_library(&name, "Nat")
                {
                    if n.parse::<u128>().is_err() {
                        self.error(format!("{n} is not a Nat"), span);
                    }
                    return Ty::Named(name, args);
                }
                let t = self.fresh_int();
                match n.parse::<i128>() {
                    Ok(v) => self.literals.push((span, v, t.clone())),
                    Err(_) => self.error(format!("{n} is too large"), span),
                }
                t
            }
            TermKind::Float(x) => {
                if !x.parse::<f64>().is_ok_and(f64::is_finite) {
                    self.error(format!("{x} is too large for a Float"), span);
                }
                Ty::Float
            }
            TermKind::Declaration(_) => Ty::Named(
                tauto_surface::bindings::library_name("SynDeclaration"),
                vec![],
            ),
            TermKind::Text(_) => Ty::Text,
            TermKind::Bool(_) => Ty::Bool,
            TermKind::Var(name) => self.lookup(name, env, term.id()),
            TermKind::Lam { .. } => self.lambda(term, &[], env),
            TermKind::BorrowLam { borrows, lam } => self.lambda(lam, borrows, env),
            TermKind::Borrow {
                mutable,
                term: inner,
            } => {
                if *mutable && !self.mutable_place(inner, env) {
                    let what = place_name(inner).unwrap_or_else(|| "this".into());
                    self.error(
                        format!("{what} is not a var: only a var lends `&mut`"),
                        span,
                    );
                }
                let t = self.infer(inner, env);
                match self.resolve(&t) {
                    // Lending a borrow lends what it borrows.
                    Ty::Borrow(t, _) => Ty::Borrow(t, *mutable),
                    t => Ty::Borrow(Box::new(t), *mutable),
                }
            }
            TermKind::Record { name, fields, .. } => self.record(name, fields, env, span),
            TermKind::App {
                function,
                arguments,
            } => {
                if let TermKind::Var(name) = &*function.kind
                    && !env.iter().any(|l| l.name == *name)
                {
                    if tauto_surface::bindings::is_library(&name, "Tuple") && arguments.is_empty() {
                        return Ty::Unit;
                    }
                    if OPERATORS.contains(&name.as_str()) {
                        return self.operator(name, arguments, env, term.id());
                    }
                    if tauto_surface::bindings::is_library(&name, "Syn::expr_of")
                        && let [filled] = arguments.as_slice()
                    {
                        self.splices.push((filled.id(), filled.span));
                    }
                    if tauto_surface::bindings::is_library(&name, "clone")
                        && !self.fns.contains_key(name)
                    {
                        return self.clone_of(arguments, env, span);
                    }
                    // A constructor without fields is written without
                    // `()`: `Start`, not `Start()`.
                    if arguments.is_empty()
                        && !self.fns.contains_key(name)
                        && self.datas.only_nullary(name)
                    {
                        self.error(
                            format!("`{name}` is a constructor without fields: write `{name}`, without `()`"),
                            span,
                        );
                        self.result_hint = hint;
                        return self.infer(function, env);
                    }
                }
                let mut f = self.infer(function, env);
                if let Ty::Poly(gs, t) = self.resolve(&f) {
                    let fresh = self.instance_of(&gs);
                    f = substitute(&t, &fresh);
                    // What the call sees of the callee is the instance.
                    self.terms.push((function.id(), f.clone()));
                }
                // The type the call is checked against fixes the
                // instance first, so that an argument meets the type it
                // is given at: `Some(r)` with `r: &A` for an `Option(A)`
                // copies `A` (`&A ≡ A`) instead of making a view. A
                // wanted type that holds a borrow is left to the
                // arguments, which are what a borrow comes from. A wanted
                // union is left to them too: the call gives one member, and
                // the union is the place it widens into, not its instance.
                if let (Some(h), Ty::Fn(_, r, _)) = (&hint, self.resolve(&f))
                    && !self.holds_borrow(h)
                    && !matches!(self.resolve(h), Ty::Union(_))
                {
                    let _ = self.attempt(|c| c.unify(&r, h));
                }
                // A lambda argument learns its parameters' types from the
                // callee's, once the arguments before it are checked.
                let known = match self.resolve(&f).unborrowed().clone() {
                    Ty::Fn(ps, _, _) if ps.len() == arguments.len() => Some(ps),
                    _ => None,
                };
                let mut args = Vec::new();
                for (i, a) in arguments.iter().enumerate() {
                    if matches!(&*a.kind, TermKind::Lam { .. } | TermKind::BorrowLam { .. }) {
                        self.hint = known.as_ref().map(|ps| ps[i].clone());
                    } else {
                        // The parameter's type is what the argument is checked
                        // against, so a call in the argument fixes its instance
                        // from it first: in `JArr(Cons(q, Nil))` with `q: Text`,
                        // `Cons` is a `List(Json)` one, and the mismatch is at
                        // `q`, the part that does not fit, not at the whole
                        // `Cons(…)` (which may be a macro's, `q` the user's).
                        self.result_hint = known.as_ref().map(|ps| ps[i].clone());
                    }
                    let mark = self.subst.len();
                    let t = self.infer(a, env);
                    self.hint = None;
                    if let Some(ps) = &known {
                        self.local_from = Some(mark);
                        self.expect(&t, &ps[i], a.span, msg!("nibcheck-what-argument"));
                        self.local_from = None;
                    }
                    args.push(t);
                }
                match self.resolve(&f).unborrowed().clone() {
                    Ty::Fn(_, r, _) if known.is_some() => *r,
                    Ty::Fn(ps, r, _) => {
                        if ps.len() != args.len() {
                            self.error(
                                format!(
                                    "a function of {} values is given {}",
                                    ps.len(),
                                    args.len()
                                ),
                                span,
                            );
                        } else {
                            for ((a, p), at) in args.iter().zip(&ps).zip(arguments) {
                                self.expect(a, p, at.span, msg!("nibcheck-what-argument"));
                            }
                        }
                        *r
                    }
                    Ty::Var(_) => {
                        let r = self.fresh();
                        if self
                            .unify(&f, &Ty::Fn(args, Box::new(r.clone()), Kind::Shared))
                            .is_err()
                        {
                            self.error("cannot infer a function type for this call", function.span);
                        }
                        r
                    }
                    other => {
                        self.error(format!("{other} is not a function"), function.span);
                        self.fresh()
                    }
                }
            }
            TermKind::Field { base, name } => {
                if let TermKind::Var(c) = &*base.kind
                    && !env.iter().any(|l| &l.name == c)
                    && self.classes.contains_key(c)
                {
                    let class = &self.classes[c].decl;
                    if class
                        .methods
                        .iter()
                        .any(|method| method.name.as_str() == name)
                    {
                        let full = classes::member_fn(class, name);
                        return self.lookup(&full, env, term.id());
                    }
                    self.error(format!("{c} has no method {name}"), span);
                    return self.fresh();
                }
                // `T::C`: the constructor `C` of the type `T`, as written
                // before its names are qualified.
                if let TermKind::Var(d) = &*base.kind
                    && !env.iter().any(|l| &l.name == d)
                    && self.datas.decls.contains_key(d)
                {
                    let selected = self.datas.decls[d]
                        .constructors
                        .iter()
                        .enumerate()
                        .find(|(_, constructor)| {
                            constructor.name.rsplit("::").next() == Some(name.as_str())
                        })
                        .map(|(index, constructor)| (index, constructor.name.clone()));
                    if let Some((index, reference)) = selected {
                        return self.constructor(d, index, span, &reference);
                    }
                }
                let b = self.infer(base, env);
                let resolved = self.resolve(&b);
                let borrowed = matches!(resolved, Ty::Borrow(..));
                match (resolved.unborrowed().clone(), name.as_str()) {
                    (Ty::Info(h), "more") => Ty::Fn(vec![Ty::Int(Width::W64)], h, Kind::Shared),
                    (Ty::Info(h), "unbounded") => Ty::Fn(vec![], h, Kind::Shared),
                    (Ty::Named(d, args), _)
                        if self.datas.decls.get(&d).is_some_and(|d| d.is_struct) =>
                    {
                        let fields = self.datas.fields(&d, 0, &args);
                        match fields.into_iter().find(|(n, _)| n.as_deref() == Some(name)) {
                            // A field of a `&mut` is lent as `&mut` where the
                            // function returns it (`-> &mut A { s.f }`).
                            Some((_, t)) if borrowed && !self.kind(&t).dup() => {
                                Ty::Borrow(Box::new(t), matches!(resolved, Ty::Borrow(_, true)))
                            }
                            Some((_, t)) => t,
                            None => {
                                self.error(format!("{d} has no field `{name}`"), span);
                                self.fresh()
                            }
                        }
                    }
                    (other, _) => {
                        self.error(format!("{other} has no field `{name}`"), span);
                        self.fresh()
                    }
                }
            }
            // `#(a, b)`: the product of its members' types, as [`product`] puts them:
            // `#(a, #(b, c))` is an `A × B × C`, `#(#(a, b), c)` an `(A × B) × C`, and
            // `#(a, #())` an `A`.
            TermKind::Tuple(members) => {
                // Where a product of as many members is expected, each member is checked
                // against the member in its place (`#(1, 2)` where `Nat × Nat` is expected).
                let hints = match hint.as_ref().map(|h| self.resolve(h)) {
                    Some(h) if is_pair_ty(&h) => {
                        Some(self.product_members(&h)).filter(|hs| hs.len() == members.len())
                    }
                    _ => None,
                };
                let mut types = Vec::new();
                for (i, m) in members.iter().enumerate() {
                    self.result_hint = hints.as_ref().map(|hs| hs[i].clone());
                    let t = self.infer(m, env);
                    types.push(self.resolve(&t));
                }
                // A member that fits neither the member expected in its place nor the
                // place of another member that does not fit its own is the part that
                // does not fit: the mismatch is at it (`#(k, q)` with `q: Text` where
                // `Text × Json` is expected), not at the whole `#(…)`, which may be a
                // macro's and `q` the user's. Members that only trade places are left
                // to the product's match by member types.
                if let Some(hs) = &hints {
                    let misfits: Vec<usize> = (0..types.len())
                        .filter(|&i| !self.probe(|c| c.fits(&types[i], &hs[i])))
                        .collect();
                    for &i in &misfits {
                        let elsewhere = misfits
                            .iter()
                            .any(|&j| j != i && self.probe(|c| c.fits(&types[i], &hs[j])));
                        if !elsewhere {
                            self.expect(
                                &types[i],
                                &hs[i],
                                members[i].span,
                                msg!("nibcheck-what-product-member"),
                            );
                            types[i] = self.resolve(&hs[i]);
                        }
                    }
                }
                self.product(types)
            }
            // `×` is a type operator: a product value is `#(…)`.
            TermKind::Product(members) => {
                for m in members {
                    self.infer(m, env);
                }
                self.error(
                    "`×` builds a type, not a value: write the product as `#(…)`",
                    span,
                );
                self.fresh()
            }
            // `(e: T)`: `e` fits `T`, which may take fewer members of a
            // product (`A × B <: A`, `A × B × C <: A × C`, `@a T <: T`).
            TermKind::Ascribe { term: base, ty } => {
                let b = self.infer(base, env);
                let want = self.written(ty, &self.type_params.clone());
                match self.resolve(&b) {
                    // A member of a borrowed product is borrowed, but a copy.
                    Ty::Borrow(inner, _) if !matches!(want, Ty::Borrow(..)) => {
                        self.expect(&inner, &want, base.span, msg!("nibcheck-what-ascription"));
                        let want = self.resolve(&want);
                        if self.kind(&want).dup() {
                            want
                        } else {
                            Ty::Borrow(Box::new(want), false)
                        }
                    }
                    _ => {
                        self.expect(&b, &want, base.span, msg!("nibcheck-what-ascription"));
                        want
                    }
                }
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                let c = self.infer(condition, env);
                self.expect(
                    &c,
                    &Ty::Bool,
                    condition.span,
                    msg!("nibcheck-what-if-condition"),
                );
                self.result_hint = hint.clone();
                let t = self.infer(then, &mut env.clone());
                match otherwise {
                    Some(o) => {
                        self.result_hint = hint;
                        let o = self.infer(o, &mut env.clone());
                        self.join(&t, &o)
                    }
                    None => Ty::Unit,
                }
            }
            TermKind::Block(stmts) => {
                let mut inner = env.clone();
                let mut last = Ty::Unit;
                let mut stopped = false;
                for (i, s) in stmts.iter().enumerate() {
                    let outer_path =
                        std::mem::replace(&mut self.declaration_path, self.term_path.clone());
                    self.declaration_path.push(i);
                    if i + 1 == stmts.len() && matches!(s, Stmt::Expr(_)) {
                        self.result_hint = hint.clone();
                    }
                    let t = self.stmt(s, &mut inner);
                    self.declaration_path = outer_path;
                    stopped |= t == Ty::Never;
                    last = if i + 1 == stmts.len() && matches!(s, Stmt::Expr(_) | Stmt::Return(_)) {
                        t
                    } else {
                        Ty::Unit
                    };
                }
                if stopped { Ty::Never } else { last }
            }
            // `match e: G { C => ⊢ G' from p }`: the written type is the type of the whole
            // `match`, and an arm's goal the type of its body. A type that depends on a value
            // (it names a local) is a proof's, which Nib does not check, so it is rejected.
            TermKind::Match {
                scrutinee,
                result,
                arms,
                ..
            } if result.is_some() || arms.iter().any(|a| a.goal.is_some()) => {
                let want = result.as_deref().and_then(|r| self.match_type(r, env));
                let goals: Vec<Option<Ty>> = arms
                    .iter()
                    .map(|a| a.goal.as_ref().and_then(|g| self.match_type(g, env)))
                    .collect();
                if let Some(want) = &want {
                    for (g, arm) in goals.iter().zip(arms) {
                        if let (Some(g), Some(written)) = (g, &arm.goal) {
                            self.expect(g, want, written.span, msg!("nibcheck-what-arm-goal"));
                        }
                    }
                }
                let (got, bodies) =
                    self.match_arms(scrutinee, arms, env, span, want.clone().or(hint));
                for ((g, arm), body) in goals.iter().zip(arms).zip(bodies) {
                    if let Some(g) = g {
                        self.expect(&body, g, arm.body.span, msg!("nibcheck-what-arm-body"));
                    }
                }
                match want {
                    Some(want) => {
                        self.expect(&got, &want, span, msg!("nibcheck-what-match-result"));
                        want
                    }
                    None => got,
                }
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => self.match_expr(scrutinee, arms, env, span, hint),
            TermKind::Perform { effect, args } => {
                let types: Vec<Ty> = args.iter().map(|a| self.infer(a, env)).collect();
                let Some(sig) = self.effects.get(effect).cloned() else {
                    self.error(format!("no effect `{effect}` is declared"), span);
                    return self.fresh();
                };
                let instance = self.instantiate_operation(&sig);
                if self.indexed.contains(effect) {
                    self.effect_args
                        .push((site(term), instance.type_args.clone()));
                }
                let ps = instance.params.clone();
                let r = instance.answer.clone();
                self.operation_performs.push((term.id(), instance));
                if ps.len() != types.len() {
                    self.error(
                        format!(
                            "`{effect}` takes {} values, given {}",
                            ps.len(),
                            types.len()
                        ),
                        span,
                    );
                } else {
                    for ((a, p), at) in types.iter().zip(&ps).zip(args) {
                        self.expect(a, p, at.span, msg!("nibcheck-what-argument"));
                    }
                }
                r
            }
            TermKind::Handle { body, handlers } => self.handle(body, handlers, env),
            TermKind::Budget { limit, steps, body } => {
                let s = self.infer(steps, env);
                let what = match limit {
                    BudgetLimit::Steps => msg!("nibcheck-what-budget-steps"),
                    BudgetLimit::Memory => msg!("nibcheck-what-budget-memory"),
                };
                self.expect(&s, &Ty::Int(Width::W64), steps.span, what);
                let t = self.infer(body, env);
                if let Some(x) = self.exceeded.last().cloned()
                    && self.unify(&x, &t).is_err()
                {
                    self.error(
                        "budgets answered by one `exceeded` arm give different types",
                        span,
                    );
                }
                t
            }
            TermKind::Tagged { tag, term } => {
                let t = self.infer(term, env);
                let t = self.resolve(&t);
                tagged(BTreeSet::from([tag.clone()]), t)
            }
            // `syntax::expand` reported why it is still here.
            TermKind::SyntaxLit(_)
            | TermKind::MacroCall { .. }
            | TermKind::Quote { .. }
            | TermKind::Splice(_) => self.fresh(),
            // What the surface reader refused (`a = b = c`) says why.
            TermKind::Other(what) if what.starts_with('`') => {
                self.error(what.clone(), span);
                self.fresh()
            }
            other => {
                self.error(format!("not supported yet: {other:?}"), span);
                self.fresh()
            }
        }
    }

    /// A lambda: its parameters (borrowed where `borrows` says), its
    /// result, and its kind, the join of the kinds of what it captures by
    /// value. What it borrows and the `var`s whose cells it shares do not
    /// count: a closure that holds a borrow or a `var` whose content is not
    /// duplicable is a borrow itself, which `lin.rs` keeps in place.
    fn lambda(&mut self, lam: &SurfaceTerm, borrows: &[Option<bool>], env: &[Local]) -> Ty {
        let hint = self.hint.take();
        let TermKind::Lam {
            params,
            body,
            types,
        } = &*lam.kind
        else {
            return self.fresh();
        };
        let ps: Vec<Ty> = params
            .iter()
            .enumerate()
            .map(|(i, _)| {
                let t = self.fresh();
                // A written parameter type is held to, when it names no
                // generic of the enclosing declaration.
                if let Some(Some(w)) = types.get(i) {
                    let before = self.errors.len();
                    let w = self.written(w, &self.type_params.clone());
                    if self.errors.len() == before {
                        let _ = self.attempt(|c| c.unify(&t, &w));
                    } else {
                        self.errors.truncate(before);
                    }
                }
                match borrows.get(i).copied().flatten() {
                    Some(m) => Ty::Borrow(Box::new(t), m),
                    None => t,
                }
            })
            .collect();
        if let Some(Ty::Fn(hs, _, _)) = hint.map(|h| self.resolve(&h).unborrowed().clone())
            && hs.len() == ps.len()
        {
            for (p, h) in ps.iter().zip(&hs) {
                let _ = self.attempt(|c| c.unify(p, h));
            }
        }
        let kind = self.capture_kind(&crate::lin::free_vars(lam), env, Kind::Copy, lam.span);
        let mut inner = env.to_vec();
        for (name, t) in params.iter().zip(&ps) {
            self.bind_local(&mut inner, name, t.clone(), false, site(body));
        }
        let r = self.fresh();
        self.returns.push(r.clone());
        let b = self.infer(body, &mut inner);
        self.returns.pop();
        self.expect(&b, &r, body.span, msg!("nibcheck-what-function-result"));
        self.closure_results.push((r.clone(), body.span));
        Ty::Fn(ps, Box::new(r), kind)
    }

    /// The join of owned captures. Borrowed values and mutable cells are
    /// tracked by the lifetime and ownership checks instead.
    fn capture_kind(&mut self, free: &[Name], env: &[Local], floor: Kind, span: Span) -> Kind {
        let mut kind = floor;
        let mut captures = Vec::new();
        for name in free {
            let Some(l) = env.iter().rev().find(|l| l.name == *name) else {
                continue;
            };
            if l.mutable {
                continue;
            }
            captures.push((name.clone(), l.ty.clone()));
            let ty = self.resolve(&l.ty);
            if !matches!(ty, Ty::Borrow(..)) {
                kind = kind.join(self.datas.kind(&ty));
            }
        }
        if !captures.is_empty() {
            self.capture_kinds.push((captures, kind, span));
        }
        kind
    }

    fn mutable_place(&self, p: &SurfaceTerm, env: &[Local]) -> bool {
        match &*p.kind {
            TermKind::Var(n) => {
                env.iter().rev().find(|l| &l.name == n).is_some_and(|l| {
                    l.mutable || matches!(self.resolve(&l.ty), Ty::Borrow(_, true))
                })
            }
            TermKind::Field { base, .. } => self.mutable_place(base, env),
            _ => false,
        }
    }

    fn clone_of(&mut self, arguments: &[SurfaceTerm], env: &mut Vec<Local>, span: Span) -> Ty {
        let [arg] = arguments else {
            self.error("`clone` takes one borrow, `clone(&x)`", span);
            return self.fresh();
        };
        let t = self.infer(arg, env);
        let t = match self.resolve(&t) {
            Ty::Borrow(t, _) => *t,
            other => {
                self.error("`clone` takes a borrow: write `clone(&x)`", arg.span);
                other
            }
        };
        if let Some(why) = self.datas.no_clone(&t) {
            self.error(why, span);
        }
        t
    }

    fn record(
        &mut self,
        name: &Name,
        fields: &[(String, SurfaceTerm)],
        env: &mut Vec<Local>,
        span: Span,
    ) -> Ty {
        // `Pair { fst: a, snd: b }` written by its name is a value of the inductive `Pair`,
        // not the product `#(a, b)`: a member that is a `Pair` or `Unit` stays one member.
        if tauto_surface::bindings::is_pair_record(name, fields.iter().map(|f| f.0.as_str())) {
            let a = self.infer(&fields[0].1, env);
            let b = self.infer(&fields[1].1, env);
            let (a, b) = (self.resolve(&a), self.resolve(&b));
            let args = vec![a, b];
            let d = self
                .datas
                .ctors
                .get(name)
                .map(|(family, _)| family.clone())
                // `Pair` written by its spelling is the declared `Pair`, which the written
                // type `Pair(nat, nat)` names.
                .or_else(|| self.datas.decls.keys().find(|d| is_pair_name(d)).cloned())
                .unwrap_or_else(|| name.clone());
            return Ty::Named(d, args);
        }
        // Report an unknown constructor before inferring fields without a schema.
        let ctor = self.datas.ctors.get(name).cloned();
        if ctor.is_none() && !self.datas.has_ctor(name) {
            self.error(format!("{name} is not a struct"), span);
            return self.fresh();
        }
        // As with a call's arguments, the fields are checked in the order
        // written, and a lambda learns its parameters' types from its
        // field's, with what the fields before it fixed.
        let schema = ctor.clone().map(|(d, c)| {
            let generics = self.datas.decls[&d].generics.clone();
            let args: Vec<Ty> = generics.iter().map(|_| self.fresh()).collect();
            let declared = self.datas.fields(&d, c, &args);
            (d, args, declared)
        });
        let mut values = Vec::new();
        for (field, value) in fields {
            let want = schema.as_ref().and_then(|(_, _, declared)| {
                declared
                    .iter()
                    .find(|(n, _)| n.as_deref() == Some(field))
                    .map(|(_, t)| t.clone())
            });
            if matches!(
                &*value.kind,
                TermKind::Lam { .. } | TermKind::BorrowLam { .. }
            ) {
                self.hint = want.clone();
            }
            let v = self.infer(value, env);
            self.hint = None;
            if matches!(&*value.kind, TermKind::Borrow { .. }) {
                self.error("a borrow cannot be a field", value.span);
            }
            // A mismatch is reported once, with the others, below.
            if let Some(want) = &want {
                let _ = self.attempt(|c| c.unify(&v, want));
            }
            values.push((field.clone(), v, value.span));
        }
        let Some((d, args, declared)) = schema else {
            let ty = self.fresh();
            self.constructor_records
                .push((name.clone(), ty.clone(), values, span));
            return ty;
        };
        self.check_record_fields(name, &values, &declared, span);
        Ty::Named(d, args)
    }

    fn check_record_fields(
        &mut self,
        name: &str,
        values: &[(String, Ty, Span)],
        declared: &[(Option<String>, Ty)],
        span: Span,
    ) {
        let mut seen = HashSet::new();
        for (field, v, at) in values {
            if !seen.insert(field.clone()) {
                self.error(format!("field `{field}` is given twice"), *at);
            }
            match declared.iter().find(|(n, _)| n.as_deref() == Some(field)) {
                Some((_, t)) => self.expect(
                    v,
                    t,
                    *at,
                    msg!("nibcheck-what-field", field = field.to_string()),
                ),
                None => self.error(format!("{name} has no field `{field}`"), *at),
            }
        }
        for (n, _) in declared {
            if let Some(n) = n
                && !seen.contains(n)
            {
                self.error(format!("field `{n}` of {name} is missing"), span);
            }
        }
    }

    fn operator(
        &mut self,
        op: &str,
        arguments: &[SurfaceTerm],
        env: &mut Vec<Local>,
        id: TermId,
    ) -> Ty {
        let span = id.span();
        let args: Vec<Ty> = arguments
            .iter()
            .map(|a| {
                let t = self.infer(a, env);
                // Operands are duplicable: a borrow of one is the value.
                match self.resolve(&t) {
                    Ty::Borrow(t, _) => *t,
                    t => t,
                }
            })
            .collect();
        match (op, args.as_slice()) {
            ("-" | "+", [a]) => {
                self.number(a, span, op);
                self.ops.push((id, a.clone()));
                a.clone()
            }
            ("&&" | "||", [a, b]) => {
                self.expect(
                    a,
                    &Ty::Bool,
                    arguments[0].span,
                    msg!("nibcheck-what-named", name = op.to_string()),
                );
                self.expect(
                    b,
                    &Ty::Bool,
                    arguments[1].span,
                    msg!("nibcheck-what-named", name = op.to_string()),
                );
                Ty::Bool
            }
            (_, [a, b]) => {
                if self.unify(a, b).is_err() {
                    let (a, b) = (self.shown(a), self.shown(b));
                    let mut message = format!("`{op}` of {a} and {b}: the operands differ");
                    // A label binds tighter than a binary operator, so
                    // `@tag a + b` labels only `a`.
                    if let Some(tag) = arguments.iter().find_map(|t| match &*t.kind {
                        TermKind::Tagged { tag, .. } => Some(tag),
                        _ => None,
                    }) {
                        message.push_str(&format!(
                            "; `@{tag}` labels only its operand, since it binds tighter than `{op}`\
                             ; to label the result, write `@{tag} (a {op} b)`"
                        ));
                    }
                    self.error(message, span);
                    return if matches!(op, "+" | "-" | "*" | "/") {
                        a
                    } else {
                        Ty::Bool
                    };
                }
                match op {
                    "==" | "!=" => {
                        self.pending.push(Pending {
                            class: "PartialEq".into(),
                            ty: a.clone(),
                            what: op.into(),
                            assume: self.assume.clone(),
                            span,
                            slot: None,
                        });
                        Ty::Bool
                    }
                    "<" | ">" | "<=" | ">=" => {
                        self.number(a, span, op);
                        Ty::Bool
                    }
                    "/" => {
                        match self.resolve(a) {
                            Ty::Decimal | Ty::Float | Ty::Float32 => {}
                            Ty::Var(v) if !self.ints.contains(&v) => self.error(
                                "the operands of `/` have no known type: write it",
                                span,
                            ),
                            _ => self.error(
                                "integer `/` is a type error: write div(a, b), mod(a, b), or decimal(a) / decimal(b)",
                                span,
                            ),
                        }
                        a.clone()
                    }
                    _ => {
                        self.number(a, span, op);
                        self.ops.push((id, a.clone()));
                        a.clone()
                    }
                }
            }
            _ => {
                self.error(format!("`{op}` takes other operands"), span);
                self.fresh()
            }
        }
    }

    /// `t` must be a number; a type not known yet becomes an integer.
    fn number(&mut self, t: &Ty, span: Span, op: &str) {
        match self.resolve(t) {
            Ty::Int(_) | Ty::Decimal | Ty::Float | Ty::Float32 => {}
            Ty::Var(v) => {
                self.ints.insert(v);
            }
            other => self.error(format!("`{op}` of {other}: not a number"), span),
        }
    }

    /// Binds a pattern's names; literals must have the scrutinee's type. A
    /// name that is a constructor without fields is that constructor. Over a
    /// borrow, what a pattern binds is borrowed too.
    fn pattern(&mut self, p: &Pattern, t: &Ty, env: &mut Vec<Local>, span: Span, at: TermId) {
        // `#(p, #())` is `p` and `#(#(p, q), r)` is `#(p, q, r)`, as the value is.
        if let Some(flat) = crate::surface::qualify::flatten_pair_pattern(p) {
            return self.pattern(&flat, t, env, span, at);
        }
        let resolved = self.resolve(t);
        let borrowed = match &resolved {
            Ty::Borrow(_, m) => Some(*m),
            _ => None,
        };
        let lit = match p {
            Pattern::Wild => return,
            Pattern::Bind(name) if self.datas.nullary(name, Some(&resolved)) => {
                self.ctor_pattern(name, &[], t, borrowed, env, span, at);
                return;
            }
            Pattern::Bind(name) => {
                self.bind_local(env, name, t.clone(), false, at);
                return;
            }
            Pattern::Int(n) => {
                let i = self.fresh_int();
                self.literals.push((span, i128::from(*n), i.clone()));
                i
            }
            Pattern::Bool(_) => Ty::Bool,
            Pattern::Text(_) => Ty::Text,
            // `@a p`: `p` on the value under the label `a`, which the value's type has.
            Pattern::Ctor { .. } if let Some((tag, inner)) = p.label() => {
                let under = match resolved.unborrowed() {
                    // The other labels of the set stay on the value: `@a p` on `@a @b T`
                    // matches `p` against `@b T`.
                    Ty::Tagged(tags, under) if tags.contains(tag) => {
                        let mut rest = tags.clone();
                        rest.remove(tag);
                        Some(tagged(rest, (**under).clone()))
                    }
                    Ty::Var(_) => {
                        let under = self.fresh();
                        let labelled = tagged(BTreeSet::from([tag.to_string()]), under.clone());
                        self.unify(resolved.unborrowed(), &labelled)
                            .is_ok()
                            .then_some(under)
                    }
                    _ => None,
                };
                match under {
                    Some(under) => {
                        let under = match borrowed {
                            Some(m) => Ty::Borrow(Box::new(under), m),
                            None => under,
                        };
                        self.pattern(inner, &under, env, span, at);
                    }
                    None => self.error(format!("the label `@{tag}` is not on {resolved}"), span),
                }
                return;
            }
            // `#()`: the unit, which `Unit` has as its one value.
            Pattern::Ctor { name, args }
                if args.is_empty()
                    && (tauto_surface::bindings::is_library(name, "Star")
                        || name
                            .spelling()
                            .is_some_and(|n| n == "Unit::Star" || n.ends_with("::Unit::Star"))) =>
            {
                if self.unify(&Ty::Unit, &resolved).is_err() {
                    self.error(format!("`#()` does not match {resolved}"), span);
                }
                return;
            }
            Pattern::Ctor { name, args } => {
                self.ctor_pattern(name, args, t, borrowed, env, span, at);
                return;
            }
            // `#(p, q)` on a product: each member by its label, or else by
            // position.
            Pattern::Record { name, .. }
                if is_pair_name(name) && !matches!(resolved.unborrowed(), Ty::Named(..)) =>
            {
                self.pair_pattern(p, t, borrowed, env, span, at);
                return;
            }
            Pattern::Tuple(_)
                if !matches!(resolved.unborrowed(), Ty::Named(..))
                    || is_pair_ty(resolved.unborrowed()) =>
            {
                self.pair_pattern(p, t, borrowed, env, span, at);
                return;
            }
            // `#(p, q)` on a `Pair` kept as a type of its own: its record.
            Pattern::Tuple(_) => {
                let pair = crate::surface::qualify::tuple_pattern_as_pairs(p, "Pair");
                self.pattern(&pair, t, env, span, at);
                return;
            }
            Pattern::Record { name, fields } => {
                match self.datas.positional(name, fields, Some(&resolved)) {
                    Ok(args) => self.ctor_pattern(name, &args, t, borrowed, env, span, at),
                    Err(e) => self.error(e, span),
                }
                return;
            }
            Pattern::Other(what) => {
                self.error(format!("this pattern is not supported yet: {what}"), span);
                return;
            }
        };
        let target = resolved.unborrowed().clone();
        if self.unify(&lit, &target).is_err() {
            let target = self.resolve(&target);
            let lit = self.resolve(&lit);
            self.error(format!("a pattern of {lit} cannot match {target}"), span);
        }
    }

    /// `#(p₁, …, pₙ)` (`Pair { fst, snd }` nested to the right) on the product `t`.
    fn pair_pattern(
        &mut self,
        p: &Pattern,
        t: &Ty,
        borrowed: Option<bool>,
        env: &mut Vec<Local>,
        span: Span,
        at: TermId,
    ) {
        let pats = pair_pattern_members(p);
        let target = self.resolve(t).unborrowed().clone();
        let labelled = pats.iter().all(|q| q.label().is_some());
        let members: Vec<Ty> = match &target {
            t if is_pair_ty(t) => {
                let mut ms = self.product_members(t);
                // `#(p, q)` on `A × B × C` takes `A` and `B × C`, as `Pair { fst, snd }` does.
                if !labelled && pats.len() >= 2 && pats.len() < ms.len() {
                    let rest = self.product(ms.split_off(pats.len() - 1));
                    ms.push(rest);
                }
                ms
            }
            Ty::Var(_) => {
                let ms: Vec<Ty> = pats.iter().map(|_| self.fresh()).collect();
                let product = self.product(ms.clone());
                let _ = self.unify(&target, &product);
                ms
            }
            other => {
                let other = self.shown(other);
                self.error(format!("a pattern of a product cannot match {other}"), span);
                return;
            }
        };
        if members.len() != pats.len() {
            let shown = self.shown(&target);
            self.error(
                format!("a pattern of {} members cannot match {shown}", pats.len()),
                span,
            );
            return;
        }
        let tags: Option<Vec<&str>> = pats.iter().map(|q| q.label().map(|(l, _)| l)).collect();
        let order: Vec<usize> = match tags {
            Some(tags) => {
                let mut order = Vec::new();
                for tag in &tags {
                    match members
                        .iter()
                        .position(|m| matches!(m, Ty::Tagged(ts, _) if ts.contains(*tag)))
                    {
                        Some(i) if !order.contains(&i) => order.push(i),
                        _ => {
                            let shown = self.shown(&target);
                            self.error(format!("the label `@{tag}` is not on {shown}"), span);
                            return;
                        }
                    }
                }
                order
            }
            None => (0..pats.len()).collect(),
        };
        for (q, i) in pats.iter().zip(order) {
            let m = match borrowed {
                Some(b) => Ty::Borrow(Box::new(members[i].clone()), b),
                None => members[i].clone(),
            };
            self.pattern(q, &m, env, span, at);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn ctor_pattern(
        &mut self,
        name: &Name,
        args: &[Pattern],
        t: &Ty,
        borrowed: Option<bool>,
        env: &mut Vec<Local>,
        span: Span,
        at: TermId,
    ) {
        let target = self.resolve(t).unborrowed().clone();
        let (d, c) = match self.datas.resolve_ctor(name, Some(&target)).cloned() {
            Ok(c) => c,
            Err(_) if !self.datas.has_ctor(name) => {
                // As the kernel says it (`kernel-match-not-ctor`), with a near
                // spelling of one of the matched type's constructors.
                let hint = match &target {
                    Ty::Named(d, _) => self.datas.decls.get(d).and_then(|data| {
                        tauto_surface::suggest::closest_name(
                            name,
                            data.constructors.iter().map(|c| c.name.as_str()),
                        )
                    }),
                    _ => None,
                };
                let message = match hint {
                    Some(hint) => format!("`{name}` is not a constructor; did you mean `{hint}`?"),
                    None => format!("`{name}` is not a constructor"),
                };
                self.error(message, span);
                return;
            }
            Err(e) => {
                self.error(e, span);
                return;
            }
        };
        let generics = self.datas.decls[&d].generics.len();
        let targs: Vec<Ty> = (0..generics).map(|_| self.fresh()).collect();
        let target = self.resolve(t).unborrowed().clone();
        if self
            .unify(&target, &Ty::Named(d.clone(), targs.clone()))
            .is_err()
        {
            let target = self.shown(&target);
            self.error(format!("a pattern of {d} cannot match {target}"), span);
            return;
        }
        let fields = self.datas.fields(&d, c, &targs);
        if fields.len() != args.len() {
            self.error(
                format!(
                    "{name} has {} fields, the pattern {}",
                    fields.len(),
                    args.len()
                ),
                span,
            );
            return;
        }
        for (p, (_, ft)) in args.iter().zip(fields) {
            let ft = match borrowed {
                Some(m) => Ty::Borrow(Box::new(ft), m),
                None => ft,
            };
            self.pattern(p, &ft, env, span, at);
        }
    }

    /// The type a `match` or its arm is written to have, or `None` (after an error) where
    /// it names a local: a type that depends on a value is a proof's.
    fn match_type(&mut self, t: &SurfaceTerm, env: &[Local]) -> Option<Ty> {
        let mut named = None;
        let mut copy = t.clone();
        crate::surface::walk::term(&mut copy, &mut |u| {
            if let TermKind::Var(n) = &*u.kind
                && named.is_none()
                && env.iter().any(|l| &l.name == n)
            {
                named = Some(n.clone());
            }
        });
        if let Some(n) = named {
            self.error(
                format!("the type of this `match` depends on the value `{n}`, which only a proof can check"),
                t.span,
            );
            return None;
        }
        Some(self.written(t, &self.type_params.clone()))
    }

    fn match_expr(
        &mut self,
        scrutinee: &SurfaceTerm,
        arms: &[MatchArm],
        env: &mut Vec<Local>,
        span: Span,
        hint: Option<Ty>,
    ) -> Ty {
        self.match_arms(scrutinee, arms, env, span, hint).0
    }

    fn match_arms(
        &mut self,
        scrutinee: &SurfaceTerm,
        arms: &[MatchArm],
        env: &mut Vec<Local>,
        span: Span,
        hint: Option<Ty>,
    ) -> (Ty, Vec<Ty>) {
        let mut bodies = Vec::new();
        let s = self.infer(scrutinee, env);
        let mut result: Option<Ty> = None;
        for arm in arms {
            let mut inner = env.clone();
            self.pattern(&arm.pattern, &s, &mut inner, arm.body.span, site(&arm.body));
            if let Some(g) = &arm.guard {
                let gt = self.infer(g, &mut inner);
                self.expect(&gt, &Ty::Bool, g.span, msg!("nibcheck-what-guard"));
            }
            self.result_hint = hint.clone();
            let b = self.infer(&arm.body, &mut inner);
            bodies.push(b.clone());
            result = Some(match result {
                None => b,
                Some(r) => self.join(&r, &b),
            });
        }
        if !self.exhaustive(&s, arms) {
            self.error("the `match` does not cover every value", span);
        } else {
            self.rest_arm(&s, arms, span);
        }
        self.redundant(&s, arms);
        self.default_arm(&s, arms);
        (result.unwrap_or(Ty::Never), bodies)
    }

    /// Literals of a number or a text are a chain of `==` tests: the
    /// values they leave are many, so the last arm names them (`other => …`).
    fn rest_arm(&mut self, t: &Ty, arms: &[MatchArm], span: Span) {
        let t = self.resolve(t);
        if !matches!(t.unborrowed(), Ty::Int(_) | Ty::Text | Ty::Var(_)) {
            return;
        }
        let literal = arms
            .iter()
            .any(|a| matches!(a.pattern, Pattern::Int(_) | Pattern::Text(_)));
        if literal {
            let named = arms.last().is_some_and(|a| {
                a.guard.is_none()
                    && matches!(&a.pattern, Pattern::Bind(n) if !self.datas.nullary(n, None))
            });
            if !named {
                self.error(
                    "a `match` on literals ends with a named rest arm (`other => …`)",
                    span,
                );
            }
        }
    }

    /// Whether the unguarded arms take every value of `t`: a name or `_`,
    /// `true` and `false`, or every constructor of an `enum` with patterns
    /// that take every value of its fields.
    fn exhaustive(&self, t: &Ty, arms: &[MatchArm]) -> bool {
        let open: Vec<&Pattern> = arms
            .iter()
            .filter(|a| a.guard.is_none())
            .map(|a| &a.pattern)
            .collect();
        self.covers(&self.resolve(t), &open)
    }

    /// Records each arm that the unguarded arms before it already take every
    /// value of ([`TypeReport::redundant_arms`]).
    /// The default arm `_ =>` (without a guard) is the last arm, and some value is left for
    /// it by the arms before it, as in a proof's `match`.
    fn default_arm(&mut self, t: &Ty, arms: &[MatchArm]) {
        let t = self.resolve(t);
        let last = arms.len().saturating_sub(1);
        for (i, arm) in arms.iter().enumerate() {
            if !matches!(arm.pattern, Pattern::Wild) || arm.guard.is_some() {
                continue;
            }
            if i != last {
                self.error("the default arm `_ =>` must be the last", arm.body.span);
                return;
            }
            let before: Vec<Vec<Pattern>> = arms[..i]
                .iter()
                .filter(|a| a.guard.is_none())
                .map(|a| vec![a.pattern.clone()])
                .collect();
            if !before.is_empty() && self.covers_within(&[t.clone()], &before, &[Pattern::Wild]) {
                self.error("the default arm `_ =>` matches no value", arm.body.span);
            }
        }
    }

    fn redundant(&mut self, t: &Ty, arms: &[MatchArm]) {
        let t = self.resolve(t);
        let mut before: Vec<Vec<Pattern>> = Vec::new();
        for arm in arms {
            if !before.is_empty()
                && self.covers_within(&[t.clone()], &before, &[arm.pattern.clone()])
            {
                self.redundant_arms.push((arm.body.id(), arm.body.span));
            }
            if arm.guard.is_none() {
                before.push(vec![arm.pattern.clone()]);
            }
        }
    }

    /// Whether `rows` together take every value that `q` takes, `q` and each
    /// row being a pattern per column of `tys`. A pattern this does not read
    /// (`Other`) is taken by no row, so an arm is never called redundant
    /// unless it is.
    fn covers_within(&self, tys: &[Ty], rows: &[Vec<Pattern>], q: &[Pattern]) -> bool {
        let Some((t, rest)) = tys.split_first() else {
            return !rows.is_empty();
        };
        let t = t.unborrowed();
        // A labelled column: `@a p` is `p` on the value under the label.
        if let Ty::Tagged(_, under) = t {
            // The labels are one set on the column: a chain `@a @b p` takes them all off.
            let strip = |p: &Pattern| {
                let mut p = p;
                while let Some((_, inner)) = p.label() {
                    p = inner;
                }
                p.clone()
            };
            let tys = [vec![(**under).clone()], rest.to_vec()].concat();
            let rows: Vec<Vec<Pattern>> = rows
                .iter()
                .map(|r| {
                    let mut r = r.clone();
                    r[0] = strip(&r[0]);
                    r
                })
                .collect();
            let mut q = q.to_vec();
            q[0] = strip(&q[0]);
            return self.covers_within(&tys, &rows, &q);
        }
        if let Some(ms) = self.product_pattern_members(t, rows.iter().map(|r| &r[0]).chain([&q[0]]))
        {
            let ms = &ms;
            let tys = [ms.clone(), rest.to_vec()].concat();
            let spread = |r: &[Pattern]| {
                self.product_columns(ms, &r[0])
                    .map(|h| [h, r[1..].to_vec()].concat())
            };
            let rows: Vec<Vec<Pattern>> = rows.iter().filter_map(|r| spread(r)).collect();
            let Some(q) = spread(q) else { return false };
            return self.covers_within(&tys, &rows, &q);
        }
        // `#(…)` on a `Pair` kept as a type of its own: its record.
        if rows.iter().any(|r| matches!(r[0], Pattern::Tuple(_)))
            || matches!(q[0], Pattern::Tuple(_))
        {
            let rows: Vec<Vec<Pattern>> = rows.iter().map(|r| tuple_head_as_pair(r)).collect();
            return self.covers_within(tys, &rows, &tuple_head_as_pair(q));
        }
        let wild = |p: &Pattern| {
            matches!(p, Pattern::Wild)
                || matches!(p, Pattern::Bind(n) if !self.datas.nullary(n, Some(t)))
        };
        let taking = |p: &Pattern| -> Vec<Vec<Pattern>> {
            rows.iter()
                .filter(|r| wild(&r[0]) || &r[0] == p)
                .map(|r| r[1..].to_vec())
                .collect()
        };
        let data = match t {
            Ty::Named(d, args) => self.datas.decls.get(d).map(|data| (d, args, data)),
            _ => None,
        };
        // The rows for constructor `c` of the data, its fields in place of the column.
        let specialize = |d: &Name, args: &[Ty], c: usize| -> (Vec<Ty>, Vec<Vec<Pattern>>) {
            let fields = self.datas.fields(d, c, args);
            let this = |n: &Name| {
                self.datas
                    .resolve_ctor(n, Some(t))
                    .is_ok_and(|(dd, cc)| dd == d && *cc == c)
            };
            let taken = rows
                .iter()
                .filter_map(|r| {
                    let head = match &r[0] {
                        p if wild(p) => vec![Pattern::Wild; fields.len()],
                        Pattern::Ctor { name: n, args } if this(n) => args.clone(),
                        Pattern::Record { name: n, fields } if this(n) => {
                            self.datas.positional(n, fields, Some(t)).ok()?
                        }
                        Pattern::Bind(n) if this(n) => Vec::new(),
                        _ => return None,
                    };
                    (head.len() == fields.len()).then(|| [head, r[1..].to_vec()].concat())
                })
                .collect();
            let tys = fields
                .iter()
                .map(|(_, ft)| ft.clone())
                .chain(rest.iter().cloned())
                .collect();
            (tys, taken)
        };
        if rows.is_empty() {
            return false;
        }
        let head = &q[0];
        if wild(head) && rows.iter().all(|r| wild(&r[0])) {
            let defaults: Vec<Vec<Pattern>> = rows.iter().map(|r| r[1..].to_vec()).collect();
            return self.covers_within(rest, &defaults, &q[1..]);
        }
        if wild(head) {
            return match (t, data) {
                (Ty::Bool, _) => [true, false]
                    .iter()
                    .all(|b| self.covers_within(rest, &taking(&Pattern::Bool(*b)), &q[1..])),
                (_, Some((d, args, data))) => (0..data.constructors.len()).all(|c| {
                    let (tys, taken) = specialize(d, args, c);
                    let n = tys.len() - rest.len();
                    let q = [vec![Pattern::Wild; n], q[1..].to_vec()].concat();
                    self.covers_within(&tys, &taken, &q)
                }),
                // A column of numbers or texts: no set of literals takes
                // every value, so only the rows that take any value count.
                _ => {
                    let defaults: Vec<Vec<Pattern>> = rows
                        .iter()
                        .filter(|r| wild(&r[0]))
                        .map(|r| r[1..].to_vec())
                        .collect();
                    self.covers_within(rest, &defaults, &q[1..])
                }
            };
        }
        match head {
            Pattern::Bool(_) | Pattern::Int(_) | Pattern::Text(_) => {
                self.covers_within(rest, &taking(head), &q[1..])
            }
            Pattern::Ctor { .. } | Pattern::Record { .. } | Pattern::Bind(_) => {
                let Some((d, args, _)) = data else {
                    return false;
                };
                let (name, fields) = match head {
                    Pattern::Ctor { name, args } => (name, Some(args.clone())),
                    Pattern::Record { name, fields } => {
                        match self.datas.positional(name, fields, Some(t)) {
                            Ok(f) => (name, Some(f)),
                            Err(_) => return false,
                        }
                    }
                    Pattern::Bind(name) => (name, None),
                    _ => unreachable!(),
                };
                let Ok((dd, c)) = self.datas.resolve_ctor(name, Some(t)) else {
                    return false;
                };
                if dd != d {
                    return false;
                }
                let c = *c;
                let (tys, taken) = specialize(d, args, c);
                let n = tys.len() - rest.len();
                let fields = fields.unwrap_or_else(|| vec![Pattern::Wild; n]);
                if fields.len() != n {
                    return false;
                }
                let q = [fields, q[1..].to_vec()].concat();
                self.covers_within(&tys, &taken, &q)
            }
            _ => false,
        }
    }

    /// The patterns, one per member of the product `ms`, that `p` puts on
    /// them: `#(…)` by labels or by position, any other that takes
    /// every value on each.
    fn product_columns(&self, ms: &[Ty], p: &Pattern) -> Option<Vec<Pattern>> {
        match p {
            Pattern::Wild => Some(vec![Pattern::Wild; ms.len()]),
            Pattern::Bind(n) if !self.datas.has_ctor(n) => Some(vec![Pattern::Wild; ms.len()]),
            Pattern::Record { name, .. } if is_pair_ctor(name) => {
                let pats = self.regroup(ms.len(), pair_pattern_members(p));
                self.tuple_columns(ms, pats)
            }
            Pattern::Tuple(_) => {
                self.tuple_columns(ms, self.regroup(ms.len(), pair_pattern_members(p)))
            }
            Pattern::Ctor { name, args } if is_pair_ctor(name) && args.len() == 2 => {
                self.tuple_columns(ms, args.clone())
            }
            _ => None,
        }
    }

    /// The columns the `#(…)` patterns `pats` put their patterns on in the product `t`: its
    /// members read flat where a pattern names them all by labels (`#(@b q, @a p)`), else its
    /// first member and the product of the rest, as the `Pair`s a tuple pattern nests to.
    fn product_pattern_members<'p>(
        &self,
        t: &Ty,
        mut pats: impl Iterator<Item = &'p Pattern>,
    ) -> Option<Vec<Ty>> {
        if !is_pair_ty(t) {
            return None;
        }
        let mut ms = self.product_members(t);
        let labelled = |p: &Pattern| {
            matches!(p, Pattern::Tuple(items)
                if items.len() == ms.len() && items.iter().all(|q| q.label().is_some()))
        };
        if !pats.any(labelled) {
            let rest = self.product(ms.split_off(1));
            ms.push(rest);
        }
        Some(ms)
    }

    /// The patterns `pats` of a tuple put on `columns` columns: where there are more and
    /// the columns are two, the first and `#(…)` of the rest.
    fn regroup(&self, columns: usize, mut pats: Vec<Pattern>) -> Vec<Pattern> {
        if columns == 2 && pats.len() > 2 && !pats.iter().all(|q| q.label().is_some()) {
            let rest = Pattern::Tuple(pats.split_off(1));
            pats.push(rest);
        }
        pats
    }

    fn tuple_columns(&self, ms: &[Ty], pats: Vec<Pattern>) -> Option<Vec<Pattern>> {
        if pats.len() != ms.len() {
            return None;
        }
        // `#()` on a `Unit` member takes its one value.
        let pats: Vec<Pattern> = pats
            .into_iter()
            .zip(ms)
            .map(|(q, m)| match (&q, m) {
                (Pattern::Ctor { args, .. }, Ty::Unit) if args.is_empty() => Pattern::Wild,
                _ => q,
            })
            .collect();
        let tags: Option<Vec<&str>> = pats.iter().map(|q| q.label().map(|(l, _)| l)).collect();
        match tags {
            None => Some(pats),
            Some(tags) => {
                let mut out = vec![Pattern::Wild; ms.len()];
                for (tag, q) in tags.iter().zip(&pats) {
                    let i = ms
                        .iter()
                        .position(|m| matches!(m, Ty::Tagged(ts, _) if ts.contains(*tag)))?;
                    out[i] = q.clone();
                }
                Some(out)
            }
        }
    }

    fn covers(&self, t: &Ty, pats: &[&Pattern]) -> bool {
        let rows: Vec<Vec<Pattern>> = pats
            .iter()
            .map(|p| vec![crate::surface::qualify::flatten_pair_patterns(p)])
            .collect();
        self.covers_rows(&[t.clone()], rows)
    }

    /// Whether `rows`, each a pattern per column of `tys`, together take
    /// every value: a constructor's arms are tried with its fields in place
    /// of the column, so `Cons(x, Cons(y, r))`, `Cons(_, Nil)` and `Nil`
    /// cover a list, as their fields are covered jointly, not one by one.
    fn covers_rows(&self, tys: &[Ty], rows: Vec<Vec<Pattern>>) -> bool {
        let Some((t, rest)) = tys.split_first() else {
            return !rows.is_empty();
        };
        let t = t.unborrowed();
        // A labelled column: `@a p` is `p` on the value under the label.
        if let Ty::Tagged(_, under) = t {
            let tys = [vec![(**under).clone()], rest.to_vec()].concat();
            let rows = rows
                .into_iter()
                .map(|mut r| {
                    while let Some((_, inner)) = r[0].label() {
                        r[0] = inner.clone();
                    }
                    r
                })
                .collect();
            return self.covers_rows(&tys, rows);
        }
        if let Some(ms) = self.product_pattern_members(t, rows.iter().map(|r| &r[0])) {
            let ms = &ms;
            let tys = [ms.clone(), rest.to_vec()].concat();
            let rows: Vec<Vec<Pattern>> = rows
                .iter()
                .filter_map(|r| {
                    self.product_columns(ms, &r[0])
                        .map(|h| [h, r[1..].to_vec()].concat())
                })
                .collect();
            return self.covers_rows(&tys, rows);
        }
        // `#(…)` on a `Pair` kept as a type of its own: its record.
        if rows.iter().any(|r| matches!(r[0], Pattern::Tuple(_))) {
            let rows = rows.iter().map(|r| tuple_head_as_pair(r)).collect();
            return self.covers_rows(tys, rows);
        }
        let wild = |p: &Pattern| {
            matches!(p, Pattern::Wild)
                || matches!(p, Pattern::Bind(n) if !self.datas.nullary(n, Some(t)))
        };
        let defaults = |rows: &[Vec<Pattern>]| -> Vec<Vec<Pattern>> {
            rows.iter()
                .filter(|r| wild(&r[0]))
                .map(|r| r[1..].to_vec())
                .collect()
        };
        if rows.iter().all(|r| wild(&r[0])) {
            return self.covers_rows(rest, defaults(&rows));
        }
        if let Ty::Bool = t {
            return [true, false].iter().all(|b| {
                let mut taken = defaults(&rows);
                taken.extend(
                    rows.iter()
                        .filter(|r| r[0] == Pattern::Bool(*b))
                        .map(|r| r[1..].to_vec()),
                );
                self.covers_rows(rest, taken)
            });
        }
        let data = match t {
            Ty::Named(d, args) => self.datas.decls.get(d).map(|data| (d, args, data)),
            _ => None,
        };
        let Some((d, args, data)) = data else {
            return self.covers_rows(rest, defaults(&rows));
        };
        (0..data.constructors.len()).all(|c| {
            let fields = self.datas.fields(d, c, args);
            let this = |n: &Name| {
                self.datas
                    .resolve_ctor(n, Some(t))
                    .is_ok_and(|(dd, cc)| dd == d && *cc == c)
            };
            let taken: Vec<Vec<Pattern>> = rows
                .iter()
                .filter_map(|r| {
                    let head = match &r[0] {
                        p if wild(p) => vec![Pattern::Wild; fields.len()],
                        Pattern::Ctor { name: n, args } if this(n) => args.clone(),
                        Pattern::Record { name: n, fields } if this(n) => {
                            self.datas.positional(n, fields, Some(t)).ok()?
                        }
                        Pattern::Bind(n) if this(n) => Vec::new(),
                        _ => return None,
                    };
                    (head.len() == fields.len()).then(|| [head, r[1..].to_vec()].concat())
                })
                .collect();
            let tys: Vec<Ty> = fields
                .iter()
                .map(|(_, ft)| ft.clone())
                .chain(rest.iter().cloned())
                .collect();
            self.covers_rows(&tys, taken)
        })
    }

    fn handle(&mut self, body: &SurfaceTerm, handlers: &[Handler], env: &mut Vec<Local>) -> Ty {
        let answers_exceeded = handlers
            .iter()
            .any(|h| matches!(h, Handler::Operation { effect, .. } if tauto_surface::bindings::is_library(&effect, "exceeded")));
        let budget_ty = self.fresh();
        if answers_exceeded {
            self.exceeded.push(budget_ty.clone());
        }
        let request_start = self.operation_performs.len();
        let b = self.infer(body, env);
        let operations = self.body_operations(body, handlers, request_start);
        if answers_exceeded {
            self.exceeded.pop();
        }
        // The result: the `return` arm's type (or the body's), widened by
        // each arm into a union.
        let result = self.fresh();
        let Ty::Var(result_var) = result else {
            unreachable!()
        };
        let ret = handlers.iter().find_map(|h| match h {
            Handler::Return { pattern, body } => Some((pattern, body)),
            _ => None,
        });
        let first = match ret {
            Some((pattern, arm)) => {
                let mut inner = env.clone();
                self.pattern(pattern, &b, &mut inner, arm.span, site(arm));
                self.infer(arm, &mut inner)
            }
            None => b,
        };
        self.subst[result_var] = Some(first);
        self.handle_arms(
            handlers,
            env,
            &result,
            Some(result_var),
            &budget_ty,
            &operations,
        );
        // Earlier arms saw only the result accumulated so far. Check every
        // continuation use again with the complete result, without widening it.
        let complete = self.resolve(&result);
        self.handle_arms(handlers, env, &complete, None, &budget_ty, &operations);
        result
    }

    fn handle_arms(
        &mut self,
        handlers: &[Handler],
        env: &[Local],
        result: &Ty,
        result_var: Option<usize>,
        budget_ty: &Ty,
        operations: &BodyOperations,
    ) {
        for h in handlers {
            let Handler::Operation {
                effect,
                instance,
                patterns,
                cont,
                guard,
                body,
            } = h
            else {
                continue;
            };
            // The arm writes the instance it answers (`res<Pos>()`), or
            // `∀ A. res<A>()` for every one: then it must work for every
            // choice, so it reads the generics as types no other is equal to.
            let mut rigid = HashMap::new();
            let mut bound = Vec::new();
            let (params, answer) = if tauto_surface::bindings::is_library(&effect, "exceeded") {
                (vec![Ty::Info(Box::new(result.clone()))], budget_ty.clone())
            } else {
                match self.effects.get(effect).cloned() {
                    Some(sig) => {
                        let generics: Vec<(Param, Kind)> = sig
                            .generics
                            .iter()
                            .map(|g| (g.clone(), Kind::Linear))
                            .collect();
                        // The generics the values mention; a row's generic
                        // (`test<!e>`) is not written.
                        let typed: Vec<Param> = generics
                            .iter()
                            .map(|(g, _)| g.clone())
                            .filter(|g| {
                                sig.params
                                    .iter()
                                    .chain([&sig.result])
                                    .any(|t| param_in(t, g))
                            })
                            .collect();
                        let row_arm = self.rows_as_types
                            && !typed.is_empty()
                            && instance.args.is_empty()
                            && instance.forall.is_empty()
                            && typed.iter().all(|g| self.effect_rows.contains(&g.id));
                        // Reading rows as types: an arm that writes no instance of an
                        // effect whose generics are all rows answers the one instance
                        // its body requests, which the types then fix.
                        let written = match if row_arm {
                            Ok(Some(&[][..]))
                        } else {
                            arm_instance(effect, instance, &typed)
                        } {
                            Ok(written) => Ok(written),
                            Err(why) => {
                                // Reported once: the arms are checked twice.
                                if result_var.is_some() {
                                    self.error(why, body.span);
                                }
                                Err(())
                            }
                        };
                        let args = match written {
                            // Unknown types, so that nothing else is reported.
                            Err(()) => generics
                                .iter()
                                .map(|(g, _)| (g.id.clone(), self.fresh()))
                                .collect(),
                            // An arm of one instance answers it only: the
                            // expansion (`indices.rs`) gives the instance a
                            // name of its own, which only performs with the
                            // same arguments reach.
                            Ok(Some(args)) => {
                                let scope = self.type_params.clone();
                                let mut given = HashMap::new();
                                for (g, a) in typed.iter().zip(args) {
                                    given.insert(g.id.clone(), self.written(a, &scope));
                                }
                                let fixed: HashMap<ParamId, Ty> = generics
                                    .iter()
                                    .map(|(g, _)| match given.remove(&g.id) {
                                        Some(t) => (g.id.clone(), t),
                                        None => (g.id.clone(), self.fresh()),
                                    })
                                    .collect();
                                let args =
                                    generics.iter().map(|(g, _)| fixed[&g.id].clone()).collect();
                                self.effect_args.push((site(body), args));
                                fixed
                            }
                            Ok(None) => {
                                if !typed.is_empty()
                                    && self.indexed.contains(effect)
                                    && result_var.is_some()
                                    && !instance.forall.is_empty()
                                {
                                    self.error(
                                        format!(
                                            "`{effect}` is told apart by its type arguments: an arm answers one instance, `{effect}<…>(…)`"
                                        ),
                                        body.span,
                                    );
                                }
                                // Unbounded, as a function's generics are.
                                let unbounded: Vec<(Param, Kind)> = generics
                                    .iter()
                                    .map(|(g, _)| (g.clone(), Kind::Affine))
                                    .collect();
                                rigid = self.rigid(&unbounded);
                                for (name, g) in instance.forall.iter().zip(&typed) {
                                    if let Some(t) = rigid.get(&g.id) {
                                        bound.push((name.clone(), t.clone()));
                                    }
                                }
                                rigid.clone()
                            }
                        };
                        let type_args = generics.iter().map(|(g, _)| args[&g.id].clone()).collect();
                        let mut checked = self.instantiate_operation_with(&sig, type_args);
                        if rigid.is_empty() {
                            // The arm writes its instance: it is linked to
                            // the handled body's request as written.
                            self.connect_operation_arm(
                                &mut checked,
                                operations,
                                body.id(),
                                result_var.is_none(),
                                body.span,
                            );
                        } else {
                            // `∀`: the arm is checked at rigid types, but the
                            // backends need the instance it answers here. A
                            // copy with fresh types is linked to the handled
                            // body's one request, leaving the arm's own types
                            // alone.
                            let mut linked = self.instantiate_operation(&sig);
                            self.connect_operation_arm(
                                &mut linked,
                                operations,
                                body.id(),
                                result_var.is_none(),
                                body.span,
                            );
                        }
                        (checked.params, checked.answer)
                    }
                    None => {
                        self.error(format!("no effect `{effect}` is declared"), body.span);
                        continue;
                    }
                }
            };
            if params.len() != patterns.len() {
                self.error(
                    format!(
                        "`{effect}` gives {} values, the arm takes {}",
                        params.len(),
                        patterns.len()
                    ),
                    body.span,
                );
                continue;
            }
            let quant = self.quants.get(effect).copied().unwrap_or(Quant::AtMostOne);
            if quant == Quant::Direct {
                let tail = cont.as_ref().is_some_and(|k| {
                    crate::direct::is_tail_form(body, k)
                        && guard
                            .as_ref()
                            .is_none_or(|g| !crate::direct::mentions(g, k))
                });
                if !tail {
                    self.error(
                        format!("{effect} is direct; every path of its arm must end in k(e)"),
                        body.span,
                    );
                }
            }
            let mut inner = env.to_vec();
            for (p, t) in patterns.iter().zip(&params) {
                self.pattern(p, t, &mut inner, body.span, site(body));
            }
            if let Some(k) = cont {
                if quant == Quant::Zero {
                    self.error(
                        format!("{effect} does not resume (`resume 0`): its arm has no `{k}`"),
                        body.span,
                    );
                }
                self.bind_local(
                    &mut inner,
                    k,
                    Ty::Fn(
                        vec![answer],
                        Box::new(result.clone()),
                        quant.continuation_kind(),
                    ),
                    false,
                    site(body),
                );
            }
            // `∀ A. res<A>(…)`: `A` names the type the arm reads it as.
            let outer = self.type_params.clone();
            self.type_params.extend(bound);
            if let Some(g) = guard {
                let gt = self.infer(g, &mut inner);
                self.expect(&gt, &Ty::Bool, g.span, msg!("nibcheck-what-guard"));
            }
            let a = self.infer(body, &mut inner);
            self.type_params = outer;
            let names: Vec<&ParamId> = rigid
                .values()
                .filter_map(|t| match t {
                    Ty::Param(n, _) => Some(n.id()),
                    _ => None,
                })
                .collect();
            if !names.is_empty()
                && (self.mentions(&names, &a)
                    || self.mentions(&names, result)
                    || env.iter().any(|l| self.mentions(&names, &l.ty)))
            {
                self.error(
                    format!(
                        "the arm of `{effect}` must work for whatever type arguments it is \
                         performed with: they are chosen where it is performed"
                    ),
                    body.span,
                );
                continue;
            }
            let Some(result_var) = result_var else {
                let fits = self.attempt(|c| c.fits(&a, result)).is_ok()
                    || match self.resolve(result) {
                        Ty::Union(choices) => choices
                            .iter()
                            .any(|choice| self.attempt(|c| c.fits(&a, choice)).is_ok()),
                        _ => false,
                    };
                if !fits {
                    self.expect(&a, result, body.span, msg!("nibcheck-what-handler-arm"));
                }
                continue;
            };
            let current = self.resolve(result);
            // Two functions of one shape: the result is the looser kind.
            if let (Ty::Fn(pa, ra, ka), Ty::Fn(pb, rb, kb)) = (self.resolve(&a), current.clone())
                && pa.len() == pb.len()
                && ka != kb
            {
                let wide = Ty::Fn(pb.clone(), rb.clone(), ka.join(kb));
                let probe = Ty::Fn(pa, ra, ka.join(kb));
                if self.attempt(|c| c.unify(&probe, &wide)).is_ok() {
                    let wide = self.resolve(&wide);
                    if !self.occurs(result_var, &wide) {
                        self.subst[result_var] = Some(wide);
                    }
                    continue;
                }
            }
            // A borrow of a duplicable value is the value (`&A ≡ A`).
            if let Ty::Borrow(x, _) = &current
                && !matches!(self.resolve(&a), Ty::Borrow(..))
                && self.kind(x).dup()
                && self.attempt(|c| c.fits(&a, x)).is_ok()
            {
                let x = self.resolve(x);
                if !self.occurs(result_var, &x) {
                    self.subst[result_var] = Some(x);
                }
                continue;
            }
            if let Ty::Borrow(x, _) = self.resolve(&a)
                && !matches!(current, Ty::Borrow(..))
                && self.kind(&x).dup()
                && self.attempt(|c| c.fits(&x, &current)).is_ok()
            {
                continue;
            }
            if self.attempt(|c| c.fits(&a, &current)).is_err() {
                let a = self.resolve(&a);
                self.subst[result_var] = Some(union(vec![current, a]));
            }
        }
    }
}

/// Whether declaration `from` holds `target` through its fields.
fn reaches(datas: &Datas, from: &Name, target: &Name, seen: &mut HashSet<Name>) -> bool {
    let Some(d) = datas.decls.get(from) else {
        return false;
    };
    if !seen.insert(from.clone()) {
        return false;
    }
    let mut names = Vec::new();
    for c in &d.constructors {
        for (_, f) in &c.fields {
            named_in(f, &mut names);
        }
    }
    names
        .iter()
        .any(|n| n == target || reaches(datas, n, target, seen))
}

fn named_in(t: &Ty, out: &mut Vec<Name>) {
    match t {
        Ty::Named(n, args) => {
            out.push(n.clone());
            args.iter().for_each(|a| named_in(a, out));
        }
        Ty::Union(ts) => ts.iter().for_each(|t| named_in(t, out)),
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) => named_in(t, out),
        // A function holds no value of its parameters' or result's types.
        _ => {}
    }
}

/// The type arguments an arm of `effect` is checked with: `Some` of the
/// written ones for an arm of one instance, `None` for `∀ A. res<A>(…)` (and
/// an operation without type arguments), or why the arm is not written so.
fn arm_instance<'a>(
    effect: &str,
    instance: &'a crate::surface::Instance,
    typed: &[Param],
) -> Result<Option<&'a [SurfaceTerm]>, Message> {
    let n = typed.len();
    let args = &instance.args;
    if n == 0 {
        if args.is_empty() && instance.forall.is_empty() {
            return Ok(None);
        }
        return Err(msg!(
            "nibcheck-effect-takes-no-type-arguments",
            effect = effect
        ));
    }
    let every = format!("`∀ {}. {effect}<{}>(…)`", names(typed), names(typed));
    if args.is_empty() {
        return Err(msg!(
            "nibcheck-arm-write-instance",
            effect = effect,
            every = every
        ));
    }
    if args.len() != n {
        return Err(msg!(
            "nibcheck-effect-type-argument-count",
            effect = effect,
            expected = n,
            given = args.len()
        ));
    }
    if instance.forall.is_empty() {
        return Ok(Some(args));
    }
    let binds_each = instance.forall.len() == n
        && args
            .iter()
            .zip(&instance.forall)
            .all(|(a, f)| matches!(&*a.kind, TermKind::Var(v) if v == f))
        && instance.forall.iter().collect::<HashSet<_>>().len() == n;
    if binds_each {
        Ok(None)
    } else {
        Err(msg!("nibcheck-arm-binds-each-type-argument", every = every))
    }
}

fn names(generics: &[Param]) -> String {
    generics
        .iter()
        .map(|g| g.name.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

fn param_in(t: &Ty, generic: &Param) -> bool {
    match t {
        Ty::Param(n, _) => n == generic,
        Ty::Named(_, args) => args.iter().any(|a| param_in(a, generic)),
        Ty::Fn(ps, r, _) => ps.iter().any(|p| param_in(p, generic)) || param_in(r, generic),
        Ty::Union(ts) => ts.iter().any(|t| param_in(t, generic)),
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) => param_in(t, generic),
        _ => false,
    }
}

/// `p`'s name for a message, when it is a name or a field path.
fn place_name(p: &SurfaceTerm) -> Option<String> {
    match &*p.kind {
        TermKind::Var(n) => Some(n.to_string()),
        TermKind::Field { base, name } => Some(format!("{}.{name}", place_name(base)?)),
        _ => None,
    }
}

/// `h(x)`: a `Named` constructor takes `x` as its next argument; any other
/// head stays an application.
pub(super) fn apply(h: Ty, x: Ty) -> Ty {
    match h {
        Ty::Named(n, mut args) => {
            args.push(x);
            Ty::Named(n, args)
        }
        h => Ty::App(Box::new(h), Box::new(x)),
    }
}

/// `gb`'s generics, named as `ga`'s are in `rigid`.
fn poly_map(
    ga: &[(Param, Kind)],
    gb: &[(Param, Kind)],
    rigid: &HashMap<ParamId, Ty>,
) -> HashMap<ParamId, Ty> {
    gb.iter()
        .zip(ga)
        .map(|((b, _), (a, _))| (b.id.clone(), rigid[a.id()].clone()))
        .collect()
}

fn substitute(t: &Ty, map: &HashMap<ParamId, Ty>) -> Ty {
    match t {
        Ty::Param(n, _) if map.contains_key(n.id()) => map[n.id()].clone(),
        Ty::Named(n, args) => {
            Ty::Named(n.clone(), args.iter().map(|a| substitute(a, map)).collect())
        }
        Ty::Fn(ps, r, k) => Ty::Fn(
            ps.iter().map(|p| substitute(p, map)).collect(),
            Box::new(substitute(r, map)),
            *k,
        ),
        Ty::Union(ts) => union(ts.iter().map(|t| substitute(t, map)).collect()),
        Ty::Tagged(tags, t) => tagged(tags.clone(), substitute(t, map)),
        Ty::Info(t) => Ty::Info(Box::new(substitute(t, map))),
        Ty::Borrow(t, m) => Ty::Borrow(Box::new(substitute(t, map)), *m),
        Ty::App(h, x) => apply(substitute(h, map), substitute(x, map)),
        Ty::Poly(gs, t) => {
            let mut inner = map.clone();
            for (g, _) in gs {
                inner.remove(g.id());
            }
            Ty::Poly(gs.clone(), Box::new(substitute(t, &inner)))
        }
        other => other.clone(),
    }
}

/// The union of `ts`: associative, commutative, idempotent; `Never` is its
/// unit.
fn union(ts: Vec<Ty>) -> Ty {
    let mut members = BTreeSet::new();
    for t in ts {
        match t {
            Ty::Union(inner) => members.extend(inner),
            Ty::Never => {}
            t => {
                members.insert(t);
            }
        }
    }
    let mut members: Vec<Ty> = members.into_iter().collect();
    members.sort_by_key(stable_type_key);
    match members.len() {
        0 => Ty::Never,
        1 => members.pop().unwrap(),
        _ => Ty::Union(members),
    }
}

/// The members of `#(p₁, …, pₙ)`, read from `Pair { fst, snd }` nested to the right.
fn pair_pattern_members(p: &Pattern) -> Vec<Pattern> {
    if let Pattern::Tuple(items) = p {
        return items.clone();
    }
    let mut out = Vec::new();
    let mut at = p;
    loop {
        match at {
            Pattern::Record { name, fields }
                if tauto_surface::bindings::is_pair_record(
                    name,
                    fields.iter().map(|f| f.0.as_str()),
                ) =>
            {
                out.push(fields[0].1.clone());
                at = &fields[1].1;
            }
            other => {
                out.push(other.clone());
                return out;
            }
        }
    }
}

/// `r` with its first pattern, when it is `#(…)`, put as the record of the prelude's `Pair`.
fn tuple_head_as_pair(r: &[Pattern]) -> Vec<Pattern> {
    let mut r = r.to_vec();
    if let Some(head @ Pattern::Tuple(_)) = r.first() {
        r[0] = crate::surface::qualify::tuple_pattern_as_pairs(head, "Pair");
    }
    r
}

fn is_pair_name(n: &Name) -> bool {
    tauto_surface::bindings::is_library(n, "Pair")
}

/// `n` names the `Pair` or its one constructor.
fn is_pair_ctor(n: &Name) -> bool {
    is_pair_name(n) || tauto_surface::bindings::is_library(n, "Pair::Mk")
}

/// Why [`Checker::fit_by_types`] did not match the members of two products.
#[derive(Debug, Clone)]
enum ProductNote {
    /// A side mentions a type parameter or an unknown type.
    Open,
    /// A side has two members of one type.
    Clash(Ty),
}

/// The product of `ts`: its members in the order written, and `()` none. `×` nests to the
/// right, so a last member that is a product gives its members (`A × (B × C)` is
/// `A × B × C`, as the kernel's `Prod(A, Prod(B, C))` is one term); any other member that
/// is a product stays one member (`(A × B) × C` is not `A × B × C`), so a product means the
/// same whether its members are written or substituted.
fn product_of(pair: &Name, ts: Vec<Ty>) -> Ty {
    let mut members = ts;
    let Some(mut tail) = members.pop() else {
        return Ty::Unit;
    };
    while let Some(head) = members.pop() {
        tail = Ty::Named(pair.clone(), vec![head, tail]);
    }
    tail
}

impl Checker {
    /// The name `Pair` is declared under, which a `Pair` type is named by.
    fn pair_name(&self) -> Name {
        // The prelude's `Pair` may be declared by spelling and by reference at once (a program
        // checked against the prelude as written and as resolved): the one the program names
        // its declarations by.
        let mut found = self.datas.decls.keys().filter(|d| is_pair_name(d));
        let first = found
            .clone()
            .find(|d| d.is_resolved() == self.resolved_names);
        first
            .or_else(|| found.next())
            .cloned()
            .unwrap_or_else(|| tauto_surface::bindings::library_name("Pair"))
    }

    /// The product of `ts`: its members in the order written, `Pair`s nested to the
    /// right, and `()` none.
    fn product(&self, ts: Vec<Ty>) -> Ty {
        product_of(&self.pair_name(), ts)
    }

    /// The members of the product `t`: its first, then those of its second where that is a
    /// `Pair` too (`A × (B × C)` is `A × B × C`). Another type is the one member.
    fn product_members(&self, t: &Ty) -> Vec<Ty> {
        let mut out = Vec::new();
        let mut at = self.resolve(t);
        loop {
            match at {
                Ty::Named(n, mut args) if is_pair_name(&n) && args.len() == 2 => {
                    let rest = args.pop().unwrap();
                    out.push(self.resolve(&args[0]));
                    at = self.resolve(&rest);
                }
                last => {
                    out.push(last);
                    return out;
                }
            }
        }
    }
}

/// The members of a product already resolved: see [`Checker::product_members`].
pub(crate) fn pair_spine(t: &Ty) -> Vec<Ty> {
    let mut out = Vec::new();
    let mut at = t;
    while let Ty::Named(n, args) = at
        && is_pair_name(n)
        && args.len() == 2
    {
        out.push(args[0].clone());
        at = &args[1];
    }
    out.push(at.clone());
    out
}

pub(crate) fn is_pair_ty(t: &Ty) -> bool {
    matches!(t, Ty::Named(n, args) if is_pair_name(n) && args.len() == 2)
}

/// Canonical presentation order, independent of allocated occurrence identities.
/// Source names alone cannot order two shadowed parameters.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum StableTypeKey {
    Int(Width),
    Bool,
    Text,
    Unit,
    Never,
    Decimal,
    Float,
    Float32,
    Fn(Vec<StableTypeKey>, Box<StableTypeKey>, Kind),
    Union(Vec<StableTypeKey>),
    Tagged(BTreeSet<String>, Box<StableTypeKey>),
    Named(Name, Vec<StableTypeKey>),
    Param(StableParamKey, Kind),
    Info(Box<StableTypeKey>),
    Borrow(Box<StableTypeKey>, bool),
    Var(usize),
    Poly(Vec<(StableParamKey, Kind)>, Box<StableTypeKey>),
    App(Box<StableTypeKey>, Box<StableTypeKey>),
}

fn stable_type_key(t: &Ty) -> StableTypeKey {
    let list = |ts: &[Ty]| ts.iter().map(stable_type_key).collect();
    let boxed = |t: &Ty| Box::new(stable_type_key(t));
    match t {
        Ty::Int(w) => StableTypeKey::Int(*w),
        Ty::Bool => StableTypeKey::Bool,
        Ty::Text => StableTypeKey::Text,
        Ty::Unit => StableTypeKey::Unit,
        Ty::Never => StableTypeKey::Never,
        Ty::Decimal => StableTypeKey::Decimal,
        Ty::Float => StableTypeKey::Float,
        Ty::Float32 => StableTypeKey::Float32,
        Ty::Fn(ps, r, k) => StableTypeKey::Fn(list(ps), boxed(r), *k),
        Ty::Union(ts) => StableTypeKey::Union(list(ts)),
        Ty::Tagged(tags, t) => StableTypeKey::Tagged(tags.clone(), boxed(t)),
        Ty::Named(n, args) => StableTypeKey::Named(n.clone(), list(args)),
        Ty::Param(p, k) => StableTypeKey::Param(p.stable_key(), *k),
        Ty::Info(t) => StableTypeKey::Info(boxed(t)),
        Ty::Borrow(t, m) => StableTypeKey::Borrow(boxed(t), *m),
        Ty::Var(v) => StableTypeKey::Var(*v),
        Ty::Poly(gs, t) => StableTypeKey::Poly(
            gs.iter().map(|(p, k)| (p.stable_key(), *k)).collect(),
            boxed(t),
        ),
        Ty::App(h, x) => StableTypeKey::App(boxed(h), boxed(x)),
    }
}

fn tagged(mut tags: BTreeSet<String>, t: Ty) -> Ty {
    let t = match t {
        Ty::Tagged(inner, t) => {
            tags.extend(inner);
            *t
        }
        t => t,
    };
    if tags.is_empty() {
        t
    } else {
        Ty::Tagged(tags, Box::new(t))
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn view_wrappers_require_the_designated_declaration() {
        let datas = Datas::default();
        for spelling in ["Option", "Result", "Pair"] {
            let args = vec![Ty::Borrow(Box::new(Ty::Unit), true)];
            let native = Ty::Named(
                tauto_surface::bindings::library_name(spelling),
                args.clone(),
            );
            let foreign = Ty::Named(
                tauto_surface::identity::DeclRef::fresh(spelling).into(),
                args,
            );
            assert_eq!(datas.view_borrow(&native), Some(true));
            assert_eq!(datas.view_borrow(&foreign), None);
        }
    }

    #[test]
    fn primitive_type_display_does_not_authorize_a_foreign_declaration() {
        let mut checker = Checker::default();
        for spelling in ["i64", "Bool", "Text", "Unit", "Never", "Decimal", "Float"] {
            let foreign = Name::Global(tauto_surface::identity::DeclRef::fresh(spelling));
            let syntax = SurfaceTerm::var(&foreign, Span::new(0, 1));
            assert_eq!(
                checker.written(&syntax, &HashMap::new()),
                Ty::Named(foreign, vec![])
            );
        }
        let builtin = SurfaceTerm::var(
            &tauto_surface::bindings::library_name("Text"),
            Span::new(0, 1),
        );
        assert_eq!(checker.written(&builtin, &HashMap::new()), Ty::Text);
    }

    #[test]
    fn a_held_parameter_is_not_inserted_again_by_its_display() {
        let owner = Name::Global(tauto_surface::identity::DeclRef::fresh("Container"));
        let name = Name::Local(tauto_surface::identity::LocalRef::fresh("Element"));
        let parameter = Param::data(&owner, 0, &name);
        let mut held = vec![name.clone()];
        let data = Datas::default();
        data.field_kind(
            &Ty::Param(parameter.clone(), Kind::Shared),
            &[parameter],
            &mut held,
        );
        assert_eq!(held, vec![name]);
    }

    fn check_types(source: &str) -> Result<TypeReport, String> {
        let program = expand_classes(crate::surface::parse_program_as_written(source)?, 1 << 30);
        Ok(check_program(&program))
    }
    use super::*;

    /// The prelude's functions check with its classes and expand class methods.
    #[test]
    fn the_prelude_checks_and_expands() {
        let program = prelude();
        let mut left = Vec::new();
        for s in program.stmts.iter().filter(|s| matches!(s, Stmt::Fn(_))) {
            let mut s = s.clone();
            crate::surface::walk::stmt(&mut s, &mut |t| match &*t.kind {
                TermKind::Field { base, name } if matches!(&*base.kind, TermKind::Var(c) if tauto_surface::bindings::is_library(c, "ToText") || tauto_surface::bindings::is_library(c, "Ord")) => {
                    left.push(name.clone())
                }
                TermKind::Var(n)
                    if (n.starts_with("ToText::") || n.starts_with("Ord::"))
                        && !n.contains('@') =>
                {
                    left.push(n.to_string())
                }
                _ => {}
            });
        }
        assert!(left.is_empty(), "{left:?}");
    }

    /// A constructor written alone in a pattern is one of the matched type's, also for a type
    /// declared in a module, whose constructors are under its full name (`m::I::Num_I`).
    #[test]
    fn a_bare_constructor_of_a_type_in_a_module() {
        let report = check_types(
            "module m {\n  enum I {\n    Num_I(Text)\n    Other_I(i64)\n  }\n}\nfn f(a: m::I): i64 { match a { Num_I(t) => 1\n Other_I(n) => n } }\n",
        )
        .unwrap();
        assert!(report.errors.is_empty(), "{:?}", report.errors);
    }

    /// The bodies, as written, of the arms [`TypeReport::redundant_arms`] holds.
    fn redundant(source: &str) -> Vec<String> {
        let report = check_types(source).unwrap();
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        let mut out: Vec<(u32, String)> = report
            .redundant_arms
            .values()
            .map(|sp| {
                (
                    sp.start,
                    source[sp.start as usize..sp.end as usize].to_string(),
                )
            })
            .collect();
        out.sort();
        out.into_iter().map(|(_, s)| s).collect()
    }

    #[test]
    fn redundant_arms() {
        let shape = "enum Shape {\n Dot\n Line(Bool)\n Pair(Bool, Bool)\n}\n";
        // After a name that takes every value.
        assert_eq!(
            redundant(&format!(
                "{shape}fn f(s: Shape): i64 {{ match s {{ Dot => 0\n x => 1\n Line(b) => 2\n }} }}"
            )),
            ["2"]
        );
        // After every constructor, and an arm taken by an earlier one.
        assert_eq!(
            redundant(&format!(
                "{shape}fn f(s: Shape): i64 {{ match s {{ Pair(true, _) => 0\n Dot => 1\n Line(_) => 2\n Pair(_, _) => 3\n Pair(true, false) => 4\n }} }}"
            )),
            ["4"]
        );
        // Jointly: `true` and `false` take every `Bool`.
        assert_eq!(
            redundant(&format!(
                "{shape}fn f(s: Shape): i64 {{ match s {{ Line(true) => 0\n Line(false) => 1\n Line(b) => 2\n _ => 3\n }} }}"
            )),
            ["2"]
        );
        // A guarded arm takes nothing for the arms after it, literal matches retain a named rest arm.
        assert_eq!(
            redundant(
                "fn f(n: i64): i64 { match n { 0 => 0\n 1 => 1\n m if m > 5 => 2\n 0 => 3\n other => 4\n } }"
            ),
            ["3"]
        );
        assert!(redundant(&format!("{shape}fn f(s: Shape): i64 {{ match s {{ Dot => 0\n Line(_) => 1\n Pair(a, b) => 2\n }} }}")).is_empty());
    }

    fn errors(source: &str) -> Vec<String> {
        check_types(source)
            .unwrap()
            .errors
            .into_iter()
            .map(|e| e.message.to_string())
            .collect()
    }

    #[test]
    fn a_rigid_generic_does_not_escape() {
        let generic = |g: &str| Param::data(&Name::from(g), 0, &Name::from(g));
        let poly = |g: &str, t: Ty| Ty::Poly(vec![(generic(g), Kind::Shared)], Box::new(t));
        let param = |g: &str| Ty::Param(generic(g), Kind::Shared);
        let mut c = Checker::default();
        let v = c.fresh();
        // `∀a. ?v` is not `∀b. b`: `?v` would have to be the rigid `b`.
        assert!(
            c.unify(&poly("a", v.clone()), &poly("b", param("b")))
                .is_err()
        );
        // A function of some one type is not one of every type.
        let mut c = Checker::default();
        let w = c.fresh();
        let id = |t: Ty| Ty::Fn(vec![t.clone()], Box::new(t), Kind::Shared);
        assert!(c.fits(&id(w), &poly("b", id(param("b")))).is_err());
        let mut c = Checker::default();
        assert!(
            c.unify(&poly("a", param("a")), &poly("b", param("b")))
                .is_ok()
        );
        // A variable made for the argument itself may become the rigid type.
        let mut c = Checker::default();
        let _outer = c.fresh();
        c.local_from = Some(c.subst.len());
        let w = c.fresh();
        assert!(c.fits(&id(w), &poly("b", id(param("b")))).is_ok());
        let linear = Ty::Poly(vec![(generic("b"), Kind::Linear)], Box::new(param("b")));
        assert!(c.unify(&poly("a", param("a")), &linear).is_err());
    }

    #[test]
    fn local_self_uses_record_declaration_arguments_and_evidence() {
        let source = r#"fn outer<A: Shared>(value: A): A where DecEq(A) {
  fn repeat<A: Shared>(other: A, again: Bool) where DecEq(A) {
    if again {
      let same := other == other
      repeat(other, false)
    } else { other }
  }
  repeat(value, false)
}
perform show("answer", outer("text"))"#
            .to_string();
        let report = check_types(&source).unwrap();
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        let own = &report.local_schemes[&Name::from("repeat")].generics[0].0;
        let outer = &report.schemes[&Name::from("outer")].generics[0].0;
        let self_uses: Vec<_> = report
            .instantiations
            .iter()
            .filter(|(_, args)| args.get(own.id()) == Some(&Ty::Param(own.clone(), Kind::Shared)))
            .collect();
        assert_eq!(self_uses.len(), 1);
        assert_eq!(report.evidence[self_uses[0].0], [Ev::Structural]);
        assert!(
            report.instantiations.values().any(|args| {
                args.get(own.id()) == Some(&Ty::Param(outer.clone(), Kind::Shared))
            })
        );
    }

    #[test]
    fn local_self_uses_keep_user_class_evidence_on_the_own_binder() {
        let source = r#"class Render(A: Shared) { fn render(value: A): Text }
instance Render(Text) { fn render(value: Text): Text { value } }
fn outer<A: Shared>(value: A): Text where Render(A) {
  fn repeat<A: Shared>(other: A, again: Bool) where Render(A) {
    if again { repeat(other, false) } else { Render::render(other) }
  }
  repeat(value, false)
}
perform show("answer", outer("text"))"#
            .to_string();
        let program = crate::surface::parse_program_as_written(&source).unwrap();
        let report = check_program(&program);
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        let own = &report.local_schemes[&Name::from("repeat")].generics[0].0;
        let outer = &report.schemes[&Name::from("outer")].generics[0].0;
        assert_ne!(own.id(), outer.id());
        let self_uses: Vec<_> = report
            .instantiations
            .iter()
            .filter(|(_, args)| args.get(own.id()) == Some(&Ty::Param(own.clone(), Kind::Shared)))
            .collect();
        assert_eq!(self_uses.len(), 1);
        assert_eq!(
            report.evidence[self_uses[0].0],
            [Ev::Assume("Render".into(), own.clone())]
        );
        assert!(report.instantiations.iter().any(|(term, args)| {
            args.get(own.id()) == Some(&Ty::Param(outer.clone(), Kind::Shared))
                && report.evidence[term] == [Ev::Assume("Render".into(), outer.clone())]
        }));
    }

    #[test]
    fn nominal_owners_are_sealed_to_successful_exact_source() {
        let source = r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
let value: Reader := Read("original")"#
            .to_string();
        let program = crate::surface::parse_program_as_written(&source).unwrap();
        let mut report = check_program(&program);
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        let Stmt::Let { value, .. } = &program.stmts[2] else {
            panic!("constructor binding")
        };
        let id = value.id();
        assert_eq!(
            report.nominal_owners_for(&program).unwrap()[&id].as_str(),
            "Reader"
        );
        assert!(report.nominal_owners_for(&program.clone()).is_some());
        report
            .terms
            .insert(id, Ty::Named("Number".into(), Vec::new()));
        assert_eq!(
            report.nominal_owners_for(&program).unwrap()[&id].as_str(),
            "Reader"
        );
        let fresh = crate::surface::parse_program_as_written(&source).unwrap();
        assert_eq!(program, fresh);
        assert!(report.nominal_owners_for(&fresh).is_none());
        let mut edited = program.clone();
        let Stmt::Let { value, .. } = &mut edited.stmts[2] else {
            unreachable!()
        };
        assert_eq!(value.id(), id);
        value.kind = std::sync::Arc::new(TermKind::Text("edited".into()));
        assert!(report.nominal_owners_for(&edited).is_none());
        let report = report.with_prelude();
        assert_eq!(
            report.nominal_owners_for(&program).unwrap()[&id].as_str(),
            "Reader"
        );
        let custom = check_program_in(&program, prelude());
        assert!(custom.errors.is_empty());
        assert!(custom.nominal_owners_for(&program).is_none());
        let source = r#"fn outer<A: Shared>(value: A): Unit {
  fn inner<A: Shared>(other: A): Unit {
    let local: A := value
  }
}"#
        .to_string();
        let failed = crate::surface::parse_program_as_written(&source).unwrap();
        let mut report = check_program(&failed);
        assert!(!report.errors.is_empty());
        report.errors.clear();
        assert!(report.nominal_owners_for(&failed).is_none());
    }

    #[test]
    fn nominal_owners_withhold_reused_expression_occurrences() {
        let source = r#"enum Reader { Read(Text) }
enum Other { Read(Text) }
let first: Reader := Read("original")
let second: Other := Read("original")"#
            .to_string();
        let mut program = crate::surface::parse_program_as_written(&source).unwrap();
        let Stmt::Let { value, .. } = &program.stmts[2] else {
            panic!("first constructor")
        };
        let shared = value.clone();
        let id = shared.id();
        let Stmt::Let { value, .. } = &mut program.stmts[3] else {
            panic!("second constructor")
        };
        *value = shared;
        let report = check_program(&program);
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        assert!(
            report
                .nominal_owners_for(&program)
                .unwrap()
                .get(&id)
                .is_none()
        );
    }

    #[test]
    fn constructor_alias_nominal_projection_has_no_callable_evidence() {
        let source = r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
fn outer(): Reader ! {} {
  let make := Read
  let value := make("ok")
  value
}
"#
        .to_string();
        let program = crate::surface::parse_program_as_written(&source).unwrap();
        let report = check_program(&program);
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        let mut aliases = Vec::new();
        for stmt in &program.stmts {
            crate::surface::walk::values_stmt(stmt, &mut |node| {
                if let crate::surface::walk::Node::Term(t) = node
                    && matches!(&*t.kind, TermKind::Var(name) if name.as_str() == "Read")
                {
                    aliases.push(t.id());
                }
            });
        }
        assert!(!aliases.is_empty());
        for id in aliases {
            assert!(matches!(report.terms.get(&id), Some(Ty::Fn(..))));
            assert_eq!(
                report.nominal_owners_for(&program).unwrap()[&id].as_str(),
                "Reader"
            );
        }
    }

    #[test]
    fn lexical_declarations_distinguish_shared_function_bodies() {
        let source = r#"fn outer<A: Shared>(value: A): A {
  fn inner<A: Shared>(other: A): A {
    perform show("captured", value)
    let local: A := other
    local
  }
  perform show("number", inner(1))
  inner(value)
}
perform show("answer", outer("text"))"#
            .to_string();
        let program = crate::surface::parse_program_as_written(&source).unwrap();
        let Stmt::Fn(outer) = &program.stmts[0] else {
            panic!("outer function")
        };
        let TermKind::Block(stmts) = &*outer.body.kind else {
            panic!("body")
        };
        let Stmt::Fn(inner) = &stmts[0] else {
            panic!("inner function")
        };
        let mut c = Checker::default();
        let outer_scheme = c.signature(outer);
        c.function_owner = Some(outer_scheme.owner);
        c.declaration_path = vec![0, 0];
        let first = c.signature(inner);
        c.declaration_path = vec![0, 1];
        let second = c.signature(&inner.clone());
        let (a, b) = (&first.generics[0].0, &second.generics[0].0);
        assert_eq!(a.name(), b.name());
        assert_eq!(inner.body.id(), inner.clone().body.id());
        assert_ne!(a.id(), b.id());
        assert!(
            c.unify(
                &Ty::Param(a.clone(), Kind::Shared),
                &Ty::Param(b.clone(), Kind::Shared)
            )
            .is_err()
        );
        assert_ne!(a.stable_key(), b.stable_key());
    }

    #[test]
    fn local_function_schemes_keep_captured_and_own_parameters_distinct() {
        let source = r#"fn outer<A: Shared>(value: A): A {
  fn inner<A: Shared>(other: A): A {
    perform show("captured", value)
    let local: A := other
    local
  }
  perform show("number", inner(1))
  inner(value)
}
perform show("answer", outer("text"))"#
            .to_string();
        let report = check_types(&source).unwrap();
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        let outer = &report.schemes[&Name::from("outer")].generics[0].0;
        let inner = &report.local_schemes[&Name::from("inner")].generics[0].0;
        assert_eq!(outer.name(), inner.name());
        assert_ne!(outer.id(), inner.id());
        let locals = |name: &str| {
            report
                .locals
                .iter()
                .filter(|((n, _), _)| n.as_str() == name)
                .map(|(_, t)| t.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(locals("value"), [Ty::Param(outer.clone(), Kind::Shared)]);
        assert_eq!(locals("other"), [Ty::Param(inner.clone(), Kind::Shared)]);
        assert_eq!(locals("local"), [Ty::Param(inner.clone(), Kind::Shared)]);
    }

    #[test]
    fn cached_prelude_facts_use_the_declarations_own_parameter_ids() {
        let source = r#"fn keep<A: Shared>(value: A): A {
  let local: A := value
  local
}
perform show("answer", keep("text"))"#
            .to_string();
        let report = check_types(&source).unwrap();
        for (name, scheme) in &prelude_report().schemes {
            if let Some(ordinary) = report.schemes.get(name) {
                assert_eq!(scheme.generics, ordinary.generics, "{name}");
            }
        }
    }

    #[test]
    fn repeated_effect_declarations_do_not_share_generic_binders() {
        let source = r#"effect identity<A>(value: A): A
let result := handle { perform identity(7) } with {
  ∀ A. identity<A>(value), k => k(value)
}
perform show("answer", result)"#
            .to_string();
        let program = crate::surface::parse_program_as_written(&source).unwrap();
        let Stmt::Effect(effect) = &program.stmts[0] else {
            panic!("effect declaration")
        };
        let mut c = Checker::default();
        c.declare_effect(effect);
        let first = c.effects[&effect.name].clone();
        c.declare_effect(&effect.clone());
        let second = &c.effects[&effect.name];
        assert_eq!(first.generics[0].name(), second.generics[0].name());
        assert_ne!(first.generics[0].id(), second.generics[0].id());
        assert_eq!(
            first.params[0],
            Ty::Param(first.generics[0].clone(), Kind::Linear)
        );
        assert_eq!(
            second.params[0],
            Ty::Param(second.generics[0].clone(), Kind::Linear)
        );
    }

    #[test]
    fn final_capture_kinds_do_not_weaken_declared_function_ownership() {
        // Nothing fixes the element of `vec_new()` either, which is its own error.
        let name = "unresolved-owned-capture-kind-needs-annotation";
        let source = crate::types::case_inputs::source("types/scoped-generics.eure", name);
        let expected =
            crate::types::case_inputs::expected("types/scoped-generics.eure", name, "types");
        assert_eq!(
            errors(&source),
            [
                expected.strip_prefix("error: ").unwrap(),
                VEC_NEW_UNDETERMINED
            ]
        );
    }

    const VEC_NEW_UNDETERMINED: &str = "the type `A` of `Vec::new` is not determined here: give the value a type, as in `let x: T = ...`";

    #[test]
    fn fixed_capture_kinds_keep_shared_and_annotated_affine_uses() {
        let datas = Datas::default();
        assert_eq!(
            datas.kind_range(&Ty::Fn(
                vec![Ty::Var(0)],
                Box::new(Ty::Var(1)),
                Kind::Shared
            )),
            (Kind::Shared, Kind::Shared)
        );
        assert_eq!(
            datas.kind_range(&Ty::Info(Box::new(Ty::Var(0)))),
            (Kind::Affine, Kind::Affine)
        );
        assert_eq!(datas.kind_range(&Ty::Var(0)), (Kind::Copy, Kind::Linear));
    }

    #[test]
    fn capture_kind_ranges_only_follow_ownership_dependencies() {
        let source = r#"struct Phantom(A: Type) { callback: (A) -> i64 }
linear struct LinearBox(A: Type) { item: A }"#
            .to_string();
        let report = check_types(&source).unwrap();
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        assert!(report.datas.decls[&Name::from("Phantom")].holds.is_empty());
        assert_eq!(
            report
                .datas
                .kind_range(&Ty::Named("Phantom".into(), vec![Ty::Var(0)])),
            (Kind::Shared, Kind::Shared)
        );
        assert_eq!(
            report
                .datas
                .kind_range(&Ty::Named("LinearBox".into(), vec![Ty::Var(0)])),
            (Kind::Linear, Kind::Linear)
        );
        let source = r#"linear struct Token {}
fn outer(token: Token): Unit {
  let value := Vec::new()
  fn consume() { Pair { fst: token, snd: value } }
  let result := consume()
}"#
        .to_string();
        // The linear capture fixes the kind: no capture is reported, only
        // the element that nothing determines.
        assert_eq!(errors(&source), [VEC_NEW_UNDETERMINED]);
        let mut checker = Checker::default();
        let head = checker.fresh();
        let applied = Ty::App(Box::new(head), Box::new(Ty::Int(Width::W64)));
        checker.capture_kinds.push((
            vec![("value".into(), applied)],
            Kind::Shared,
            Span::new(0, 0),
        ));
        let report = checker.finish();
        let expected = r#"error: the kind of capture `value` is not determined; add a type annotation to the captured binding"#.to_string();
        assert_eq!(report.errors.len(), 1);
        assert_eq!(
            report.errors[0].message.to_string(),
            expected.strip_prefix("error: ").unwrap()
        );
    }

    #[test]
    fn named_functions_retain_owned_capture_kinds_at_every_use() {
        for name in [
            "named-owned-affine-capture-is-used-once",
            "generic-named-owned-affine-capture-is-used-once",
            "named-owned-affine-capture-single-use",
            "generic-named-owned-affine-capture-single-use",
        ] {
            let source = crate::types::case_inputs::source("types/scoped-generics.eure", name);
            let program = expand_classes(
                crate::surface::parse_program_as_written(&source).unwrap(),
                1 << 30,
            );
            let report = check_program(&program);
            assert!(report.errors.is_empty(), "{name}: {:?}", report.errors);
            assert!(
                matches!(
                    report.local_schemes[&Name::from("consume")].ty,
                    Ty::Fn(_, _, Kind::Affine)
                ),
                "{name}"
            );
            for (_, ty) in report
                .locals
                .iter()
                .filter(|((n, _), _)| n.as_str() == "consume")
            {
                assert!(matches!(ty, Ty::Fn(_, _, Kind::Affine)), "{name}");
            }
            let found = crate::lin::check_lin_program(&program)
                .unwrap()
                .into_iter()
                .map(|e| e.message)
                .collect::<Vec<_>>();
            let expected =
                crate::types::case_inputs::expected("types/scoped-generics.eure", name, "lin");
            if expected == "ok" {
                assert!(found.is_empty(), "{name}: {found:?}");
            } else {
                assert_eq!(found, [expected.strip_prefix("error: ").unwrap()], "{name}");
            }
        }
    }

    #[test]
    fn type_fact_output_does_not_depend_on_occurrence_allocation() {
        let source = r#"fn outer<A: Shared>(value: A): A {
  fn inner<A: Shared>(other: A): A {
    perform show("captured", value)
    let local: A := other
    local
  }
  perform show("number", inner(1))
  inner(value)
}
perform show("answer", outer("text"))"#
            .to_string();
        let first = check_types(&source).unwrap();
        assert!(first.errors.is_empty(), "{:?}", first.errors);
        let noise = r#"class Render(A: Shared) { fn render(value: A): Text }
instance Render(i64) { fn render(value: i64): Text { "number" } }
instance Render(Text) { fn render(value: Text): Text { value } }
fn outer<A: Shared>(value: A): Text where Render(A) {
  fn inner<A: Shared>(item: A): Text where Render(A) {
    let local: A := item
    Render::render(local)
  }
  inner(value)
}
perform show("first", outer(7))
perform show("second", outer("text"))"#
            .to_string();
        let _ = check_types(&noise).unwrap();
        let second = check_types(&source).unwrap();
        assert!(second.errors.is_empty(), "{:?}", second.errors);
        assert_eq!(dump_types(&first), dump_types(&second));
        let ordered = |report: &TypeReport| {
            let outer = report.schemes[&Name::from("outer")].generics[0].0.clone();
            let inner = report.local_schemes[&Name::from("inner")].generics[0]
                .0
                .clone();
            stable_type_key(&union(vec![
                Ty::Param(inner, Kind::Shared),
                Ty::Param(outer, Kind::Shared),
            ]))
        };
        assert_eq!(ordered(&first), ordered(&second));
    }

    #[test]
    fn literal_finalization_rejects_unresolved_and_non_integer_types() {
        for ty in [Ty::Var(0), Ty::Bool] {
            let mut c = Checker::default();
            let _unresolved = c.fresh();
            c.literals.push((Span { start: 0, end: 1 }, 1, ty));
            let report = c.finish();
            assert!(
                report
                    .errors
                    .iter()
                    .any(|e| { e.message.to_string() == "an integer literal has no integer type" })
            );
        }
    }

    #[test]
    fn the_prelude_checks() {
        let e: Vec<String> = check_program(prelude())
            .errors
            .into_iter()
            .map(|e| e.to_string())
            .collect();
        assert!(e.is_empty(), "{e:?}");
    }

    #[test]
    fn kinds_follow_the_fields() {
        let report = check_types(
            r#"affine struct F {}
struct W { f: F }
struct Q { t: Text }
enum L { Nil, Cons(i64, L) }
struct P { x: i64 }"#,
        )
        .unwrap();
        let k = |n: &str| report.kind(&Ty::Named(n.into(), vec![]));
        assert_eq!(k("F"), Kind::Affine);
        assert_eq!(k("W"), Kind::Affine);
        assert_eq!(k("Q"), Kind::Shared);
        assert_eq!(k("L"), Kind::Shared);
        assert_eq!(k("P"), Kind::Copy);
        let e = errors(r#"copy struct Q { t: Text }"#);
        assert!(
            e[0].contains("declared copy but field t is shared"),
            "{e:?}"
        );
    }
}

fn term_has_borrow(t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::Borrow { .. } => true,
        TermKind::App {
            function,
            arguments,
        } => term_has_borrow(function) || arguments.iter().any(term_has_borrow),
        TermKind::Tagged { term, .. } => term_has_borrow(term),
        TermKind::Union(ts) | TermKind::Product(ts) | TermKind::Tuple(ts) => {
            ts.iter().any(term_has_borrow)
        }
        TermKind::Pi { params, result, .. } => {
            params.iter().any(|(_, p)| term_has_borrow(p)) || term_has_borrow(result)
        }
        _ => false,
    }
}

#[cfg(test)]
#[cfg(test)]
/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn source_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
            ("types/scoped-generics.eure", "named-owned-affine-capture-is-used-once") => {
                r#"fn outer(): Unit {
  let text := "text"
  let value := Buf::of(&text)
  fn consume(marker: i64): Text { Text::of(value) }
  perform show("first", consume(1))
  perform show("second", consume(2))
}
outer()"#
            }
            ("types/scoped-generics.eure", "named-owned-affine-capture-single-use") => {
                r#"fn outer(): Text {
  let text := "text"
  let value := Buf::of(&text)
  fn consume(marker: i64): Text { Text::of(value) }
  consume(1)
}
perform show("answer", outer())"#
            }
            ("types/scoped-generics.eure", "generic-named-owned-affine-capture-is-used-once") => {
                r#"fn outer(): Unit {
  let text := "text"
  let value := Buf::of(&text)
  fn consume<A: Shared>(marker: A): Text {
    let local: A := marker
    Text::of(value)
  }
  perform show("first", consume(1))
  perform show("second", consume("again"))
}
outer()"#
            }
            ("types/scoped-generics.eure", "generic-named-owned-affine-capture-single-use") => {
                r#"fn outer(): Text {
  let text := "text"
  let value := Buf::of(&text)
  fn consume<A: Shared>(marker: A): Text {
    let local: A := marker
    Text::of(value)
  }
  consume(1)
}
perform show("answer", outer())"#
            }
            ("types/scoped-generics.eure", "unresolved-owned-capture-kind-needs-annotation") => {
                r#"fn outer(): Unit {
  let value := Vec::new()
  fn consume() { value }
}"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn source(file: &str, name: &str) -> String {
        source_static(file, name).to_string()
    }
    pub fn expected_static(file: &str, name: &str, input: &str) -> &'static str {
        match (file, name, input) {
            ("types/scoped-generics.eure", "named-owned-affine-capture-is-used-once", "types") => {
                r#"ok"#
            }
            ("types/scoped-generics.eure", "named-owned-affine-capture-is-used-once", "lin") => {
                r#"error: consume is used after move"#
            }
            ("types/scoped-generics.eure", "named-owned-affine-capture-single-use", "types") => {
                r#"ok"#
            }
            ("types/scoped-generics.eure", "named-owned-affine-capture-single-use", "lin") => {
                r#"ok"#
            }
            (
                "types/scoped-generics.eure",
                "generic-named-owned-affine-capture-is-used-once",
                "types",
            ) => r#"ok"#,
            (
                "types/scoped-generics.eure",
                "generic-named-owned-affine-capture-is-used-once",
                "lin",
            ) => r#"error: consume is used after move"#,
            (
                "types/scoped-generics.eure",
                "generic-named-owned-affine-capture-single-use",
                "types",
            ) => r#"ok"#,
            (
                "types/scoped-generics.eure",
                "generic-named-owned-affine-capture-single-use",
                "lin",
            ) => r#"ok"#,
            (
                "types/scoped-generics.eure",
                "unresolved-owned-capture-kind-needs-annotation",
                "types",
            ) => {
                r#"error: the kind of capture `value` is not determined; add a type annotation to the captured binding"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn expected(file: &str, name: &str, input: &str) -> String {
        expected_static(file, name, input).to_string()
    }
}

/// A struct used as a value. A record type `{ x: A }` is the struct
/// `@record.x`, which is never written, so it gets its own message.
fn struct_value_message(name: &Name) -> String {
    if name.starts_with("@record.") {
        "a record type `{ … }` is not a value: write a record without a name as `#{ … }`".to_string()
    } else {
        format!("`{name}` is a struct: write `{name} {{ field: value }}`")
    }
}
