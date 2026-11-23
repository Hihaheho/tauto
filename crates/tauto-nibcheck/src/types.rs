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
//! - `perform budget(n, () => { body })` has the body's type `T`; an `exceeded(info), k`
//!   arm gets `k: (T) -> H` and `info.more(m)`, `info.unbounded()` of type `H`,
//!   `H` the handle's result type.
//! - `show<A>(name: Text, value: A): Unit` is the host's operation, declared
//!   everywhere.
//!
//! Kinds, borrows and resume quantities:
//! every type has a [`Kind`]; a declaration may bound it (`struct(affine)
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

use crate::surface::CoerceLevel;
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

pub use tauto_surface::kinds::{Kind, Quant, Width};

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
    /// `&orig T` of a type with `struct &T`: the borrow of the owner, not
    /// through `Lend`. Of another type it is `&T`.
    Orig(Box<Ty>),
    /// `&rc T`: a counted box of a `T`, shared by every copy. It is read
    /// only through a shared borrow of the contents (`&orig T`, then `&T`).
    Rc(Box<Ty>),
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
            Ty::Borrow(t, _) | Ty::Orig(t) => t.unborrowed(),
            t => t,
        }
    }
}

impl Ty {
    /// How tight the written form of the type binds, from the loosest: an arrow, `|`, `×`, a
    /// prefix (`@tag`, `&`) on one operand, and last what stands alone. A type is written in
    /// parentheses where it stands in a place that takes a tighter one, as `@value (Text × u64)`
    /// and not `@value Text × u64`, which reads as `(@value Text) × u64`.
    fn written_binding(&self) -> u8 {
        match self {
            Ty::Fn(..) | Ty::Poly(..) => 0,
            Ty::Union(_) => 1,
            Ty::Named(n, args) if is_pair_name(n) && args.len() == 2 => 2,
            Ty::Tagged(..) | Ty::Borrow(..) | Ty::Orig(_) | Ty::Rc(_) => 3,
            _ => 4,
        }
    }

    /// The written form of the type where it takes a form that binds at least `least`.
    fn write_at(&self, f: &mut fmt::Formatter<'_>, least: u8) -> fmt::Result {
        if self.written_binding() < least {
            write!(f, "({self})")
        } else {
            write!(f, "{self}")
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
            Ty::Int(Width::W8) => write!(f, "i8"),
            Ty::Int(Width::W16) => write!(f, "i16"),
            Ty::Int(Width::U16) => write!(f, "u16"),
            Ty::Int(Width::W32) => write!(f, "i32"),
            Ty::Int(Width::W64) => write!(f, "i64"),
            Ty::Int(Width::U8) => write!(f, "u8"),
            Ty::Int(Width::U32) => write!(f, "u32"),
            Ty::Int(Width::U64) => write!(f, "u64"),
            Ty::Int(Width::Host) => write!(f, "uhost"),
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
            Ty::Union(ts) => {
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    t.write_at(f, 2)?;
                }
                Ok(())
            }
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
                    t.write_at(f, 3)?;
                }
                Ok(())
            }
            Ty::Tagged(tags, t) => {
                for tag in tags {
                    write!(f, "@{tag} ")?;
                }
                t.write_at(f, 3)
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
            Ty::Borrow(t, mutable) => {
                write!(f, "{}", if *mutable { "&mut " } else { "&" })?;
                t.write_at(f, 3)
            }
            Ty::Orig(t) => {
                write!(f, "&orig ")?;
                t.write_at(f, 3)
            }
            Ty::Rc(t) => {
                write!(f, "&rc ")?;
                t.write_at(f, 3)
            }
            Ty::Var(_) => write!(f, "_"),
            Ty::Poly(gs, t) => {
                let names: Vec<&str> = gs.iter().map(|(n, _)| n.name()).collect();
                write!(f, "<{}>{t}", names.join(", "))
            }
            Ty::App(h, x) => {
                h.write_at(f, 4)?;
                write!(f, "({x})")
            }
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
    /// `Vec`): its clone copies what it holds.
    pub builtin: bool,
    /// An extern `type(borrow)`: an opaque type that holds a borrow.
    pub view: bool,
    /// The struct's `coerce` field, by its index, and the level written.
    pub coerce: Option<(usize, crate::surface::CoerceLevel)>,
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
    /// `T` to its `struct &T`.
    pub lent_of: HashMap<Name, Name>,
}

impl Datas {
    /// `&T` as the struct `struct &T` declares, for a type that has one.
    pub fn lent_struct(&self, t: &Ty) -> Option<Ty> {
        let Ty::Borrow(inner, false) = t else {
            return None;
        };
        let Ty::Named(n, args) = &**inner else {
            return None;
        };
        let lent = self.lent_of.get(n)?;
        Some(Ty::Named(lent.clone(), args.clone()))
    }

    /// The constructor `IntOfNat` when `t` is std's `Int`: the type with no
    /// generics and the two constructors `IntOfNat(Nat)` and `IntNegSucc(Nat)`.
    /// A numeral where an `Int` is expected is `IntOfNat` of it, as the kernel
    /// reads it (`3` is `IntOfNat(3)`), so the executable code reads a numeral
    /// as the proofs do and the backends build it with this constructor.
    pub fn int_of_nat(&self, t: &Ty) -> Option<&Name> {
        let Ty::Named(name, args) = t else {
            return None;
        };
        let decl = self.decls.get(name)?;
        // The executable code holds a `Nat` as a `nat`.
        let nat = |c: &DataCtor| match c.fields.as_slice() {
            [(_, Ty::Int(Width::Nat))] => true,
            [(_, Ty::Named(n, a))] => a.is_empty() && tauto_surface::bindings::is_library(n, "Nat"),
            _ => false,
        };
        match decl.constructors.as_slice() {
            [of_nat, neg_succ]
                if args.is_empty()
                    && decl.generics.is_empty()
                    && !decl.is_struct
                    && name.as_str() == "Int"
                    && of_nat.name.as_str().ends_with("IntOfNat")
                    && neg_succ.name.as_str().ends_with("IntNegSucc")
                    && nat(of_nat)
                    && nat(neg_succ) =>
            {
                Some(&of_nat.name)
            }
            _ => None,
        }
    }

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

    /// Marks the declarations that hold a borrow: a field holds a borrow, a
    /// declaration that holds one, or a type applied to
    /// them. Declarations refer to each other, so this runs to a fixpoint.
    pub fn find_views(&mut self) {
        loop {
            let found: Vec<Name> = self
                .decls
                .values()
                .filter(|d| {
                    !d.view
                        && d.constructors
                            .iter()
                            .flat_map(|c| c.fields.iter())
                            .any(|(_, t)| self.field_holds_view(t))
                })
                .map(|d| d.name.clone())
                .collect();
            if found.is_empty() {
                return;
            }
            for n in found {
                if let Some(d) = self.decls.get_mut(&n) {
                    d.view = true;
                }
            }
        }
    }

    fn field_holds_view(&self, t: &Ty) -> bool {
        match t {
            Ty::Borrow(..) | Ty::Orig(_) => true,
            Ty::Named(n, args) => {
                self.decls.get(n).is_some_and(|d| d.view)
                    || args.iter().any(|a| self.field_holds_view(a))
            }
            _ => false,
        }
    }

    /// Whether a type holds a borrow of something that is not duplicable (a
    /// shared borrow of a duplicable value is the value): `Some(true)` when
    /// the borrow is `&mut`.
    /// Whether a value of `t` holds an opaque view (`type(affine, borrow)
    /// Guard` of an `extern`), itself or in a field or a type argument: its
    /// drop may run code that uses what it borrows, so `lin` keeps it live
    /// to the end of its scope. A borrow of one (`&Guard`) drops nothing.
    pub fn holds_opaque_view(&self, t: &Ty) -> bool {
        self.holds_opaque_view_in(t, &mut Vec::new())
    }

    fn holds_opaque_view_in(&self, t: &Ty, visiting: &mut Vec<Ty>) -> bool {
        let Ty::Named(n, args) = t else {
            return false;
        };
        if visiting.contains(t) {
            return false;
        }
        visiting.push(t.clone());
        let found = match self.decls.get(n).filter(|d| d.view) {
            Some(d) => {
                let map = d.instance(args);
                let fields: Vec<Ty> = d
                    .constructors
                    .iter()
                    .flat_map(|c| c.fields.iter().map(|(_, f)| substitute(f, &map)))
                    .collect();
                fields.is_empty()
                    || fields
                        .iter()
                        .any(|f| self.holds_opaque_view_in(f, visiting))
            }
            None => args.iter().any(|a| self.holds_opaque_view_in(a, visiting)),
        };
        visiting.pop();
        found
    }

    pub fn view_borrow(&self, t: &Ty) -> Option<bool> {
        self.view_borrow_in(t, &mut Vec::new())
    }

    /// `view_borrow` with the view types being unfolded: a recursive view
    /// (`enum Tree { Leaf, Branch(Placed(Tree), u64) }`) holds what its
    /// fields hold apart from itself, so a type met again adds nothing (the
    /// least fixed point).
    fn view_borrow_in(&self, t: &Ty, visiting: &mut Vec<Ty>) -> Option<bool> {
        match t {
            // A `&A` is a borrow even of a duplicable `A`: it is copied
            // only where an `A` is wanted (`&A → A`).
            Ty::Borrow(_, m) => Some(*m),
            Ty::Orig(_) => Some(false),
            Ty::Named(n, args) => {
                if let Some(d) = self.decls.get(n).filter(|d| d.view) {
                    // An opaque view may hold anything; a view struct holds
                    // what its fields do.
                    let fields: Vec<&Ty> = d
                        .constructors
                        .iter()
                        .flat_map(|c| c.fields.iter().map(|(_, t)| t))
                        .collect();
                    if fields.is_empty() {
                        return Some(true);
                    }
                    // Borrows of duplicable values only: the value is the
                    // values it borrows (`&A ≡ A`).
                    if visiting.contains(t) {
                        return None;
                    }
                    visiting.push(t.clone());
                    let map = d.instance(args);
                    let mut found = None;
                    for f in fields {
                        if let Some(m) = self.view_borrow_in(&substitute(f, &map), visiting) {
                            found = Some(found.unwrap_or(false) || m);
                        }
                    }
                    visiting.pop();
                    return found;
                }
                // `D(T₁, …)` holds what its type arguments hold.
                let mut found = None;
                for a in args {
                    if let Some(m) = self.view_borrow_in(a, visiting) {
                        found = Some(found.unwrap_or(false) || m);
                    }
                }
                found
            }
            _ => None,
        }
    }

    /// Whether every borrow a type holds is a shared `&` of a duplicable
    /// value: such a holder is copied where its value is wanted.
    pub fn view_value_dup(&self, t: &Ty) -> bool {
        self.nondup_borrow_in(t, &mut Vec::new()).is_none()
    }

    fn nondup_borrow_in(&self, t: &Ty, visiting: &mut Vec<Ty>) -> Option<bool> {
        match t {
            Ty::Borrow(inner, m) => (*m || !self.kind(inner).dup()).then_some(*m),
            Ty::Orig(inner) => (!self.kind(inner).dup()).then_some(false),
            Ty::Named(n, args) => {
                if let Some(d) = self.decls.get(n).filter(|d| d.view) {
                    // An opaque view may hold anything; a view struct holds
                    // what its fields do.
                    let fields: Vec<&Ty> = d
                        .constructors
                        .iter()
                        .flat_map(|c| c.fields.iter().map(|(_, t)| t))
                        .collect();
                    if fields.is_empty() {
                        return Some(true);
                    }
                    // Borrows of duplicable values only: the value is the
                    // values it borrows (`&A ≡ A`).
                    if visiting.contains(t) {
                        return None;
                    }
                    visiting.push(t.clone());
                    let map = d.instance(args);
                    let mut found = None;
                    for f in fields {
                        if let Some(m) = self.nondup_borrow_in(&substitute(f, &map), visiting) {
                            found = Some(found.unwrap_or(false) || m);
                        }
                    }
                    visiting.pop();
                    return found;
                }
                // `D(T₁, …)` holds what its type arguments hold.
                let mut found = None;
                for a in args {
                    if let Some(m) = self.nondup_borrow_in(a, visiting) {
                        found = Some(found.unwrap_or(false) || m);
                    }
                }
                found
            }
            _ => None,
        }
    }

    /// Whether a value of the type may hold a lent function: a `&` or `&mut`
    /// of a function type, in a field of a view struct or in a type argument
    /// (`Some(true)` when `&mut`). The function behind the borrow may be a
    /// closure that borrows, whatever kind its type has, so the copy that
    /// `&A ≡ A` allows is for `lin.rs` to decide from where the value came.
    pub fn lent_function(&self, t: &Ty) -> Option<bool> {
        self.lent_function_in(t, &mut Vec::new())
    }

    fn lent_function_in(&self, t: &Ty, visiting: &mut Vec<Ty>) -> Option<bool> {
        match t {
            Ty::Borrow(inner, m) if matches!(inner.unborrowed(), Ty::Fn(..)) => Some(*m),
            Ty::Borrow(inner, _) => self.lent_function_in(inner, visiting),
            Ty::Named(n, args) => {
                let mut found = None;
                if let Some(d) = self.decls.get(n).filter(|d| d.view) {
                    if visiting.contains(t) {
                        return None;
                    }
                    visiting.push(t.clone());
                    let map = d.instance(args);
                    for c in &d.constructors {
                        for (_, f) in &c.fields {
                            if let Some(m) = self.lent_function_in(&substitute(f, &map), visiting) {
                                found = Some(found.unwrap_or(false) || m);
                            }
                        }
                    }
                    visiting.pop();
                }
                for a in args {
                    if let Some(m) = self.lent_function_in(a, visiting) {
                        found = Some(found.unwrap_or(false) || m);
                    }
                }
                found
            }
            _ => None,
        }
    }

    /// Whether a value of `t` may hold a function, or a type the check does
    /// not read through (a variable, a type constructor not known yet): a
    /// function type in `t`, in a field of a declaration it names, or in a
    /// type argument. A type parameter holds none of its own.
    pub fn may_hold_function(&self, t: &Ty) -> bool {
        self.may_hold_function_in(t, &mut Vec::new())
    }

    fn may_hold_function_in(&self, t: &Ty, visiting: &mut Vec<Ty>) -> bool {
        match t {
            Ty::Fn(..) | Ty::Var(_) | Ty::Poly(..) | Ty::App(..) => true,
            Ty::Borrow(inner, _) | Ty::Tagged(_, inner) | Ty::Info(inner) | Ty::Rc(inner) => {
                self.may_hold_function_in(inner, visiting)
            }
            Ty::Union(ts) => ts.iter().any(|t| self.may_hold_function_in(t, visiting)),
            Ty::Named(n, args) => {
                if args.iter().any(|a| self.may_hold_function_in(a, visiting)) {
                    return true;
                }
                let Some(d) = self.decls.get(n) else {
                    return false;
                };
                // By the declaration, not the instance: a field that names
                // the declaration again at other arguments (`Nest(Pair(A,
                // A))`) would make a new instance at every step. Its
                // arguments were read above, and a parameter holds none.
                //
                // A declaration is read once in a whole query: its arguments
                // hold no function here, so what it holds does not depend on
                // them, and an answer of yes ends the query. Taking it off
                // `visiting` again would read a declaration once for every
                // path to it, exponentially many in a deep program.
                let key = Ty::Named(n.clone(), Vec::new());
                if visiting.contains(&key) {
                    return false;
                }
                visiting.push(key);
                let map = d.instance(args);
                d.constructors.iter().any(|c| {
                    c.fields
                        .iter()
                        .any(|(_, f)| self.may_hold_function_in(&substitute(f, &map), visiting))
                })
            }
            _ => false,
        }
    }

    /// `kind(T)` of `docs/design/ownership.md`, for a resolved type.
    pub fn kind(&self, t: &Ty) -> Kind {
        self.kind_in(t)
    }

    /// Whether `class` (a structural one: `PartialEq`, `DecEq`) holds
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
            Ty::Tagged(_, t) | Ty::Borrow(t, _) | Ty::Orig(t) | Ty::Rc(t) => {
                self.structural_in(class, t, assume, visiting)
            }
            Ty::Param(n, _) => assume.iter().any(|(c, g)| {
                g == n
                    && (tauto_surface::bindings::is_library(c, class)
                        || (class == "PartialEq"
                            && tauto_surface::bindings::is_library(&c, "DecEq")))
            }),
            // The caller settles every variable first (`Checker::settled`):
            // an open one is never taken to have the class.
            Ty::Var(_) => false,
            Ty::Named(n, args) => {
                // `Buf` is the prelude's text buffer, compared as its text
                // (`docs/design/classes.md`「Structural predicates」).
                if tauto_surface::bindings::is_library(&n, "Buf") && args.is_empty() {
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
            Ty::Tagged(_, t) | Ty::Borrow(t, _) | Ty::Orig(t) => self.kind_in(t),
            // Every copy shares the box, whatever the contents' kind.
            Ty::Rc(_) => Kind::Shared,
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
            Ty::Tagged(_, t) | Ty::Borrow(t, _) | Ty::Orig(t) => self.kind_range(t),
            Ty::Rc(_) => (Kind::Shared, Kind::Shared),
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
                // A `struct &T` is a borrow: a shared borrow it
                // holds is copied as a borrow, whatever its contents' kind.
                let lent = self.lent_of.values().any(|l| l == n);
                for c in &d.constructors {
                    for (_, f) in &c.fields {
                        let f = if lent { &unborrow_shared(f) } else { f };
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
            Ty::Tagged(_, t) | Ty::Borrow(t, _) | Ty::Orig(t) => {
                self.field_kind(t, generics, holds)
            }
            Ty::Rc(_) => Kind::Shared,
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
    pub fn no_clone(&self, t: &Ty) -> Option<Message> {
        self.no_clone_in(t, &mut Vec::new())
    }

    fn no_clone_in(&self, t: &Ty, visiting: &mut Vec<Ty>) -> Option<Message> {
        if visiting.contains(t) {
            return None;
        }
        let k = self.kind(t);
        if k == Kind::Linear {
            return Some(msg!("nibcheck-type-is-linear", ty = t.to_string()));
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
                        Some(msg!("nibcheck-type-has-no-clone", ty = t.to_string()))
                    } else {
                        fields.iter().find_map(|f| self.no_clone_in(f, visiting))
                    }
                };
                visiting.pop();
                why
            }
            Ty::Union(ts) => ts.iter().find_map(|t| self.no_clone_in(t, visiting)),
            Ty::Tagged(_, t) => self.no_clone_in(t, visiting),
            // A text is copied by value, whatever its kind: `clone(&t)` always has one.
            Ty::Text => None,
            Ty::Param(..) => Some(msg!("nibcheck-type-has-no-clone", ty = t.to_string())),
            _ => Some(msg!("nibcheck-type-has-no-clone", ty = t.to_string())),
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
#[derive(Debug, Default, Clone)]
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
    /// Each `(e: T)`, by its identity, with the `T` written: a picked member
    /// `(p: @a T)` is a `T`, but which member it picks is `@a T`.
    pub ascribed: HashMap<TermId, Ty>,
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
    /// The terms, by their spans, that are read through `coerce` fields: the
    /// struct and the field of each step, outermost first. `w` read as `T`
    /// is `w.W::value` (`&w` is `&w.W::value`), and the base of `w.x` is
    /// read so too. The coercion expansion writes them as fields.
    pub coercions: HashMap<Span, Vec<(Name, String)>>,
    /// The fields written with their struct's name, `w.Placed::at`, by the
    /// span of the field term, with the field's own name.
    pub qualified_fields: HashMap<Span, String>,
    /// The struct whose field each field term reads, by the span of the
    /// term: the type the value has, past its `coerce` fields. Visibility
    /// asks it where a field's name alone does not tell its type
    /// (`docs/design/visibility.md`).
    pub field_owners: HashMap<Span, Name>,
    /// The coercions that give the value itself (`coerce(owned)`, `W` as
    /// `T`), which the expansion takes apart rather than reads a field of.
    pub coercion_moves: HashSet<Span>,
    /// Where a `&T` is given as `T` (`Lend::owned`), and where a `&orig T`
    /// is given as `&T` (`Lend::lend`), for the lend expansion.
    pub lent_copies: HashSet<Span>,
    pub orig_lends: HashSet<Span>,
    /// Where a `&rc T` is read as a borrow of its contents, and where a
    /// value is moved into a new `&rc T` box.
    pub rc_reads: HashSet<Span>,
    pub rc_boxes: HashSet<Span>,
    pub rc_copies: HashSet<Span>,
    /// Successful nominal projections, sealed to their checked source.
    nominal_facts: Option<NominalFacts>,
    operation_facts: Option<OperationFacts>,
}

#[derive(Debug, Clone)]
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
    /// The `where` of the function the use is in: the class and every generic
    /// it constrains (`Convert(A, B)` → `[A, B]`).
    Assume(Name, Vec<Param>),
    /// An instance of the class for the type constructor, the types its
    /// generics were matched to, and the evidence for its `where`.
    Inst(Name, Name, Vec<Ty>, Vec<Ev>),
    /// `Debug` of a union: the evidence for each member, which a `match`
    /// with a typed arm for each member takes apart.
    Union(Name, Vec<(Ty, Ev)>),
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

    /// The effect `effect` of the row of a call of `callee` as the program
    /// would write it at this use: `fail(E)` of `raise<T, E>` with `E` taken as
    /// `Text` is `fail(Text)`. `None` when the effect names no type argument
    /// of the callee.
    pub fn effect_at_use(&self, callee: &Name, at: TermId, effect: &str) -> Option<String> {
        let split = effect.find(['@', '('])?;
        let (head, arguments) = effect.split_at(split);
        let scheme = self.scheme(callee)?;
        let inst = self.instantiations.get(&at)?;
        let mut out = String::new();
        let mut word = String::new();
        let mut changed = false;
        let mut flush = |word: &mut String, out: &mut String, changed: &mut bool| {
            if word.is_empty() {
                return;
            }
            let found = scheme
                .generics
                .iter()
                .find(|(p, _)| p.name() == word.as_str())
                .and_then(|(p, _)| inst.get(p.id()));
            match found {
                Some(ty) => {
                    out.push_str(&ty.to_string());
                    *changed = true;
                }
                None => out.push_str(word),
            }
            word.clear();
        };
        for c in arguments.chars() {
            if c.is_alphanumeric() || c == '_' {
                word.push(c);
            } else {
                flush(&mut word, &mut out, &mut changed);
                out.push(c);
            }
        }
        flush(&mut word, &mut out, &mut changed);
        changed.then(|| format!("{head}{out}"))
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
        self.ascribed
            .extend(lib.ascribed.iter().map(|(k, v)| (*k, v.clone())));
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
    let inherited = tauto_surface::surface::superclasses::expanded(program);
    let program = inherited.as_ref();
    let mut report = check_program_in(program, prelude_for(program));
    // A program still using a class did not expand, and the expanded prelude
    // has no classes (`Ord is not defined`): the program is checked against
    // the prelude as written, with its classes, and that is the report.
    if !report.errors.is_empty() && expand::uses_classes(program) {
        report = check_program_in(program, prelude_source_for(program));
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

const NOT_SUPPORTED_YET: &str = "nibcheck-not-supported-yet";

/// The report as text, for `totes/nibcheck` to write the same: the errors in
/// order, the top-level lets, and then the locals, terms, widths, quantities,
/// declarations and constructors, each sorted. A type is written with
/// everything in it (`dump_ty`); the "not supported yet: {term:?}" of an
/// unread term is cut to the name of the term.
pub fn dump_types(report: &TypeReport) -> String {
    let mut out = String::new();
    for e in &report.errors {
        let mut message = e.message.clone();
        if let (NOT_SUPPORTED_YET, Some(tauto_message::Value::Text(what))) =
            (&*message.id, message.get("what"))
        {
            let name = what.split(['(', ' ']).next().unwrap_or("");
            message = msg!(NOT_SUPPORTED_YET, what = name.to_string());
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
            "data {} {declared} {} {} {} {} {} {}\n",
            d.name,
            d.recursive,
            d.is_struct,
            d.builtin,
            d.view,
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
        // A product is shown as one, its members in order: the checker
        // holds `A × B` as the prelude's `Pair`, which only the kernel
        // reads (`docs/design/program-data.md`), and a last member that is
        // a product is the rest of it (`A × (B × C)` is `A × B × C`).
        Ty::Named(..) if is_pair_ty(t) => {
            let mut members = Vec::new();
            let mut rest = t;
            while let Ty::Named(_, args) = rest
                && is_pair_ty(rest)
            {
                members.push(args[0].clone());
                rest = &args[1];
            }
            members.push(rest.clone());
            format!("Product({})", list(&members))
        }
        Ty::Named(n, args) => format!("Named({n},{})", list(args)),
        Ty::Param(n, k) => format!("Param({n},{k})"),
        Ty::Info(t) => format!("Info({})", dump_ty(t)),
        Ty::Borrow(t, m) => format!("Borrow({},{})", dump_ty(t), if *m { "mut" } else { "ref" }),
        Ty::Orig(t) => format!("Orig({})", dump_ty(t)),
        Ty::Rc(t) => format!("Rc({})", dump_ty(t)),
        Ty::Var(v) => format!("Var({v})"),
        Ty::Poly(gs, t) => {
            let names: Vec<String> = gs.iter().map(|(n, k)| format!("{n}:{k}")).collect();
            format!("Poly([{}],{})", names.join(","), dump_ty(t))
        }
        Ty::App(h, x) => format!("App({},{})", dump_ty(h), dump_ty(x)),
    }
}

/// The declarations every program sees before its own: `std/prelude/std.taut`
/// and the affine standard library. A program's own
/// declaration of a name hides the prelude's.
static PRELUDE: OnceLock<Program> = OnceLock::new();
/// [`PRELUDE`] read with the library's references ([`prelude_for`]).
static PRELUDE_RESOLVED: OnceLock<Program> = OnceLock::new();
/// The prelude as written ([`prelude_source`]).
static PRELUDE_SOURCE: OnceLock<Program> = OnceLock::new();
/// [`PRELUDE_SOURCE`] read with the library's references.
static PRELUDE_SOURCE_RESOLVED: OnceLock<Program> = OnceLock::new();

/// Which of the preludes this module keeps for the life of the process
/// `prelude` is, by address: what is computed of one of them alone can be
/// kept with it, since it never changes. Any other program (the prelude
/// checked against itself while it is made, a caller's own) is `None`.
/// Whether what the check computes once and reuses ([`kept_prelude`]) is
/// computed again at each use and compared with what was kept, stopping on
/// any difference: on with `TAUTO_VERIFY_REUSE=1` in the environment or
/// [`set_verify_reuse`]. A run with it on gives the same results as one
/// without, only slower, so a test suite can show that the reuse changes
/// nothing.
pub fn verify_reuse() -> bool {
    use std::sync::atomic::Ordering;
    match VERIFY_REUSE.load(Ordering::Relaxed) {
        0 => {
            let on =
                std::env::var_os("TAUTO_VERIFY_REUSE").is_some_and(|v| v != "0" && !v.is_empty());
            VERIFY_REUSE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
        v => v == 2,
    }
}

/// Turns [`verify_reuse`] on or off for the process, whatever the environment says.
pub fn set_verify_reuse(on: bool) {
    VERIFY_REUSE.store(if on { 2 } else { 1 }, std::sync::atomic::Ordering::Relaxed);
}

/// 0: not read yet; 1: off; 2: on.
static VERIFY_REUSE: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

pub(crate) fn kept_prelude(prelude: &Program) -> Option<usize> {
    [
        &PRELUDE,
        &PRELUDE_RESOLVED,
        &PRELUDE_SOURCE,
        &PRELUDE_SOURCE_RESOLVED,
    ]
    .iter()
    .position(|kept| kept.get().is_some_and(|p| std::ptr::eq(p, prelude)))
}

fn has_references(program: &Program) -> bool {
    let mut resolved = tauto_surface::bindings::declared_names(&program.stmts)
        .iter()
        .any(|n| n.is_resolved());
    if !resolved {
        for statement in &program.stmts {
            let mut statement = statement.clone();
            crate::surface::walk::stmt(&mut statement, &mut |term| match &*term.kind {
                // A declaration the reader writes by the library's own reference (`Pair` of
                // `A × B`, `Pair::Mk` of `#(a, b)`, `Star` of `#()`) is so in every program,
                // resolved or not: the parser writes it, so it says nothing of how the
                // program was read.
                TermKind::Var(name)
                    if ["Pair", "Pair::Mk", "Star", "Unit"]
                        .iter()
                        .any(|s| tauto_surface::bindings::is_reader_reference(name, s)) => {}
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
    PRELUDE_RESOLVED.get_or_init(|| {
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
    PRELUDE_SOURCE.get_or_init(|| {
        let mut program = tauto_parse::parse_builtin_as_written_at(
            crate::nibstd::PRELUDE,
            crate::surface::PRELUDE_BASE,
        )
        .expect("the prelude parses");
        debug::add_instances(&mut program, &mut [], None);
        crate::surface::qualify::lower_prelude_names(&mut program.stmts);
        program
    })
}

fn resolved_prelude_source() -> &'static Program {
    PRELUDE_SOURCE_RESOLVED.get_or_init(|| {
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
    /// The `where` constraints: the class and the generics it constrains.
    pub preds: Vec<(Name, Vec<Param>)>,
    /// The associated types (`type_functions::ASSOC`): `(C::t, G, H)` is
    /// `H = C::t(G)`.
    pub equations: Vec<(Name, Param, Param)>,
    /// The generics that are type constructors, with the kind each takes;
    /// the kind in `generics` is the one it makes.
    pub ctors: Vec<(Param, Kind)>,
}

mod classes;
mod coerce;
mod debug;
mod expand;
mod lend;
pub use coerce::expand_coercions;
pub mod indices;
pub(crate) use classes::Unresolved;
pub use expand::{
    InstanceMethod, expand_classes, expand_library, expand_loaded, expand_loaded_reporting,
    expansion_errors, index_expansion_errors, instance_methods,
};

/// Whether `span` belongs to an instance the compiler made, not one the
/// program wrote.
pub fn is_made_instance(span: tauto_parol::Span) -> bool {
    debug::is_made(span)
}

/// The classes whose instances follow from a type's structure.
pub const STRUCTURAL: &[&str] = &["PartialEq", "DecEq"];

/// A constraint to check once the types are known: `tys` have the `class` the
/// use of `what` asks for, given what the enclosing function assumes.
struct Pending {
    class: Name,
    tys: Vec<Ty>,
    what: String,
    assume: Vec<(Name, Vec<Param>)>,
    span: Span,
    /// Which constraint of which use this is: the occurrence, its index
    /// among the function's constraints, and how many there are.
    slot: Option<(TermId, usize, usize)>,
}

#[derive(Debug, Clone)]
pub struct EffectSig {
    pub generics: Vec<Param>,
    /// The kind each generic is bounded by (`Linear` when nothing is written).
    pub kinds: Vec<Kind>,
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

/// One change an `attempt` may undo: a variable's binding before it was
/// set, or a variable marked as an integer.
enum Undo {
    Subst(usize, Option<Ty>),
    Int(usize),
}

#[derive(Default)]
struct Checker {
    /// Whether the program being checked names its declarations by reference.
    resolved_names: bool,
    /// The type each nullary `def Name(): Type := T` of the program names:
    /// where a type is written, the def is the type it names.
    type_defs: HashMap<Name, SurfaceTerm>,
    type_references: HashMap<TermId, Name>,
    classes: HashMap<Name, classes::ClassInfo>,
    /// By class and the constructor at the head of the instance.
    instances: HashMap<(Name, Name), classes::InstanceInfo>,
    /// By a class method that is not executable (`C::child_type`) and the
    /// constructor at the head of an instance: the type the instance gives
    /// it, which `C::child_type(H)` is.
    type_methods: HashMap<(Name, Name), (Ty, Ty)>,
    /// Inside a function with associated types (`Scheme::equations`): `C::t(G)`
    /// is the generic `H`.
    local_projections: Vec<(Name, ParamId, Ty)>,
    /// At the uses of such functions: `C::t(G)` and the type `H` stands for,
    /// made equal once `G` is known.
    deferred_projections: Vec<(Ty, Ty, Span)>,
    subst: Vec<Option<Ty>>,
    /// While an argument is checked against a general type: the first variable
    /// made for the argument itself; none otherwise.
    local_from: Option<usize>,
    ints: HashSet<usize>,
    /// What `set_subst` and `add_int` changed while an `attempt` or a `probe`
    /// runs, to be undone in reverse when it fails: undoing by this record
    /// costs what was changed, where a copy of `subst` costs every variable
    /// of the program.
    trail: Vec<Undo>,
    /// How many `attempt`s and `probe`s are running.
    trying: usize,
    /// A type constructor variable at a use: what it takes and makes, and
    /// the function it was for.
    ctor_bounds: Vec<(Ty, Kind, Kind, String, Span)>,
    /// Writing a type where a constructor is wanted: an instance's head.
    constructor_position: bool,
    /// How many rigid generics `fits` has made, for their names.
    rigids: usize,
    fns: HashMap<Name, Scheme>,
    local_fns: Vec<(Name, Scheme)>,
    effects: HashMap<Name, EffectSig>,
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
    /// A type that must fit a bound: an instantiated type parameter, and
    /// whether the parameter is bounded by `NoBorrow`.
    bounds: Vec<(Ty, Kind, Span, bool)>,
    /// The type parameters bounded by `NoBorrow`: they take no type that
    /// holds a borrow.
    no_borrow: HashSet<ParamId>,
    /// An effect's argument: a type variable in its type must be bounded by
    /// `NoBorrow`.
    effect_values: Vec<(Ty, Span)>,
    /// What a `&rc T` holds, written or built: at most affine, and holding
    /// no borrow.
    rc_contents: Vec<(Ty, Span)>,
    /// The term being inferred: where a bound made by instantiating a
    /// general type is reported.
    at: Span,
    /// What the function being checked may assume: its `where`.
    assume: Vec<(Name, Vec<Param>)>,
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
    /// The generics of a top-level function at a use, by the names a call
    /// writes them with: `f(<A: T>)`.
    instance_names: HashMap<TermId, Vec<(Name, Ty)>>,
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
    /// The `struct &T` declarations, by [`Datas::lent_name`].
    lent_decls: Vec<(Name, Span)>,
    /// Owned captures and the function kind fixed at their declaration.
    /// Inference may not later grant the function weaker ownership.
    capture_kinds: Vec<(Vec<(Name, Ty)>, Kind, Span)>,
    /// The expected type of the lambda being checked.
    hint: Option<Ty>,
    /// The type the next term is checked against, when it is in a result
    /// position: a function's body, a `return`, and their tails. A call
    /// reads it to fix its type arguments before its arguments are checked.
    result_hint: Option<Ty>,
    /// The spans of the text literals, which fit a `&Text` as they are.
    text_literals: HashSet<Span>,
    /// The type being written is the one directly under a `&`: `Slice(A)`
    /// may be written there only.
    under_borrow: bool,
    /// A product may forget members here: only where [`Checker::expect`]
    /// fits a term's type at the top, so that the place is recorded.
    widen_products: bool,
    /// Where a product forgot members, and the type it was fitted to.
    product_fits: Vec<(Span, Ty)>,
    ascribed: Vec<(TermId, Ty)>,
    pair_members: HashMap<TermId, (Vec<usize>, usize)>,
    /// Why a product did not fit by the types of its members, for the next error.
    product_note: Option<ProductNote>,
    redundant_arms: Vec<(TermId, Span)>,
    coercions: Vec<(Span, Vec<(Name, String)>)>,
    qualified_fields: Vec<(Span, String)>,
    field_owners: Vec<(Span, Name)>,
    coercion_moves: Vec<Span>,
    lent_copies: Vec<Span>,
    orig_lends: Vec<Span>,
    /// Where a `&rc T` is read as `&orig T` (`rc_reads`), and where a `T`
    /// is given as a `&rc T` (`rc_boxes`), for the expansion.
    rc_reads: Vec<Span>,
    rc_boxes: Vec<Span>,
    /// Where the duplicable contents of a `&rc T` are copied out.
    rc_copies: Vec<Span>,
    /// The next `fits` is the one `expect` asks.
    rc_top: bool,
    /// The field being read is the place an assignment writes.
    assigning: bool,
    /// Replaceable `extern` blocks: sealed representation is checked here,
    /// not only during lowering.
    extern_blocks: tauto_surface::surface::extern_blocks::ExternBlocks,
}

impl Checker {
    fn error(&mut self, message: impl Into<tauto_message::Message>, span: Span) {
        self.errors.push(TypeError {
            message: message.into(),
            span,
        });
    }

    /// Refuses construction, projection, update, or match on a replaceable
    /// extern type outside its block.
    fn refuse_sealed_repr(&mut self, data_or_ctor: &Name, span: Span) {
        let owner = self
            .datas
            .ctors
            .get(data_or_ctor)
            .map(|(d, _)| d.clone())
            .or_else(|| {
                self.datas
                    .decls
                    .keys()
                    .find(|d| d.as_str() == data_or_ctor.as_str())
                    .cloned()
            })
            .unwrap_or_else(|| data_or_ctor.clone());
        let accessor = self.function_owner.as_ref().map(|o| &o.name);
        if tauto_surface::surface::extern_blocks::may_access_repr(
            &self.extern_blocks,
            &owner,
            accessor,
        ) {
            return;
        }
        self.error(
            msg!("surface-extern-repr-sealed", name = owner.to_string()),
            span,
        );
    }

    fn fresh(&mut self) -> Ty {
        self.subst.push(None);
        Ty::Var(self.subst.len() - 1)
    }

    fn fresh_int(&mut self) -> Ty {
        let v = self.fresh();
        if let Ty::Var(i) = v {
            self.add_int(i);
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
                let args: Vec<Ty> = args.iter().map(|a| self.resolve(a)).collect();
                if let [head] = args.as_slice() {
                    if let Some(ctor) = classes::head_constructor(head, self.resolved_names)
                        && let Some((pattern, given)) = self.type_methods.get(&(n.clone(), ctor))
                    {
                        // The instance's head is its constructor over distinct
                        // generics: each argument is what one generic is.
                        let mut found: HashMap<ParamId, Ty> = HashMap::new();
                        if let (Ty::Named(_, params), Ty::Named(_, args)) = (pattern, head) {
                            for (p, a) in params.iter().zip(args) {
                                if let Ty::Param(g, _) = p {
                                    found.insert(g.id().clone(), a.clone());
                                }
                            }
                        }
                        return self.resolve(&substitute(given, &found));
                    }
                    if let Ty::Param(g, _) = head
                        && let Some((_, _, h)) = self
                            .local_projections
                            .iter()
                            .find(|(m, x, _)| m == n && x == g.id())
                    {
                        return h.clone();
                    }
                }
                Ty::Named(n.clone(), args)
            }
            Ty::Info(t) => Ty::Info(Box::new(self.resolve(t))),
            Ty::Borrow(t, m) => {
                let inner = self.resolve(t);
                // `&A` with `A` a type that has `struct &T` is that struct,
                // also where `A` was a type variable.
                if !*m
                    && let Ty::Named(n, args) = &inner
                    && let Some(lent) = self.datas.lent_of.get(n)
                {
                    return Ty::Named(lent.clone(), args.clone());
                }
                Ty::Borrow(Box::new(inner), *m)
            }
            Ty::Orig(t) => Ty::Orig(Box::new(self.resolve(t))),
            Ty::Rc(t) => Ty::Rc(Box::new(self.resolve(t))),
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
            Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Rc(t) | Ty::Poly(_, t) => {
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
                self.add_int(w);
            }
            self.set_subst(v, Some(Ty::Var(w)));
            return Ok(());
        }
        if self.ints.contains(&v) && !matches!(t, Ty::Int(_)) {
            return Err(());
        }
        if self.occurs(v, &t) {
            return Err(());
        }
        self.set_subst(v, Some(t));
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
            (Ty::Orig(x), Ty::Orig(y)) => self.unify(x, y),
            (Ty::Rc(x), Ty::Rc(y)) => self.unify(x, y),
            (Ty::Tagged(ta, x), Ty::Tagged(tb, y)) if ta == tb => self.unify(x, y),
            (Ty::Union(xa), Ty::Union(xb)) if xa.len() == xb.len() => {
                // Members solved since the union was built are sorted again:
                // `?b | ?a` with `?b = Text`, `?a = i64` is `i64 | Text`.
                if self.resolve(&a) == self.resolve(&b) {
                    return Ok(());
                }
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
            Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Rc(t) | Ty::Poly(_, t) => {
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
                let plain = self.no_borrow.contains(&n.id);
                self.bounds.push((v.clone(), *k, self.at, plain));
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
            Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Rc(t) | Ty::Poly(_, t) => {
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
            Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Rc(t) | Ty::Poly(_, t) => {
                self.has_vars(&t)
            }
            Ty::App(h, x) => self.has_vars(&h) || self.has_vars(&x),
            Ty::Named(_, args) => args.iter().any(|a| self.has_vars(a)),
            _ => false,
        }
    }

    /// Whether `f` succeeds, undoing what it bound either way.
    fn probe(&mut self, f: impl FnOnce(&mut Self) -> Result<(), ()>) -> bool {
        let mark = self.mark();
        let note = self.product_note.take();
        let r = f(self);
        self.undo_to(mark);
        self.product_note = note;
        r.is_ok()
    }

    /// Tries `f`, undoing what it bound when it fails.
    fn attempt(&mut self, f: impl FnOnce(&mut Self) -> Result<(), ()>) -> Result<(), ()> {
        let mark = self.mark();
        let r = f(self);
        if r.is_err() {
            self.undo_to(mark);
        } else {
            self.keep(mark);
        }
        r
    }

    /// Where an `attempt` or a `probe` starts: what it may undo back to.
    fn mark(&mut self) -> (usize, usize) {
        self.trying += 1;
        (self.subst.len(), self.trail.len())
    }

    /// The changes since `mark` stay: they are undone only with an outer
    /// attempt's, so the record is kept while one runs.
    fn keep(&mut self, mark: (usize, usize)) {
        self.trying -= 1;
        if self.trying == 0 {
            self.trail.truncate(mark.1);
        }
    }

    /// `subst` and `ints` as they were at `mark`: the variables made since are
    /// gone, and what was bound or marked since is undone.
    fn undo_to(&mut self, (len, at): (usize, usize)) {
        while self.trail.len() > at {
            match self.trail.pop() {
                Some(Undo::Subst(v, t)) => {
                    if v < self.subst.len() {
                        self.subst[v] = t;
                    }
                }
                Some(Undo::Int(v)) => {
                    self.ints.remove(&v);
                }
                None => {}
            }
        }
        self.subst.truncate(len);
        self.trying -= 1;
    }

    fn set_subst(&mut self, v: usize, t: Option<Ty>) {
        let old = std::mem::replace(&mut self.subst[v], t);
        if self.trying > 0 {
            self.trail.push(Undo::Subst(v, old));
        }
    }

    fn add_int(&mut self, v: usize) {
        if self.ints.insert(v) && self.trying > 0 {
            self.trail.push(Undo::Int(v));
        }
    }

    /// A value of type `a` may stand where `b` is expected.
    fn fits(&mut self, a: &Ty, b: &Ty) -> Result<(), ()> {
        let (a, b) = (self.resolve(a), self.resolve(b));
        // A `&rc T` is read, or a `T` boxed, only where a written type asks
        // for it (`expect`), never inside another type.
        let top = std::mem::take(&mut self.rc_top);
        // A value holding only `&` of duplicables is copied where its value
        // is wanted (`Option(&V)` where an `Option(V)` is): `&A → A`.
        if matches!(a, Ty::Named(..))
            && matches!(b, Ty::Named(..))
            && self.is_view(&a)
            && !self.is_view(&b)
            && let Some(plain) = self.view_value(&a)
        {
            return self.fits(&plain, &b);
        }
        match (&a, &b) {
            (Ty::Never, _) => Ok(()),
            (Ty::Rc(x), Ty::Rc(y)) => self.unify(x, y),
            (Ty::Var(v), Ty::Rc(y))
                if top && self.ints.contains(v) && !self.has_open_vars(y, &HashSet::new()) =>
            {
                let y = (**y).clone();
                self.fits(&a, &y)
            }
            // An integer literal where a union is wanted is the union's
            // integer member: `i64` when the union has it, as a literal
            // nothing fixes is, or else its one integer member. Two other
            // integer members leave it unsettled, which is an error.
            (Ty::Var(v), Ty::Union(ys)) if self.ints.contains(v) => {
                let members: Vec<&Ty> = ys.iter().filter(|y| matches!(y, Ty::Int(_))).collect();
                let member = members
                    .iter()
                    .find(|y| matches!(y, Ty::Int(Width::W64)))
                    .or(match members.as_slice() {
                        [one] => Some(one),
                        _ => None,
                    });
                match member {
                    Some(m) => self.unify(&a, m),
                    None => self.unify(&a, &b),
                }
            }
            (Ty::Var(_), _) | (_, Ty::Var(_)) => self.unify(&a, &b),
            // The contents of a `&rc T` are read through a shared borrow,
            // `&orig T` (`&T` of a type without `struct &T`), and copied
            // from it only when they are duplicable.
            (Ty::Rc(x), _) if top && self.rc_reads_as(&b) => {
                let borrowed =
                    matches!(b, Ty::Borrow(_, false) | Ty::Orig(_)) || self.is_lent_struct(&b);
                if !borrowed && !self.kind(x).dup() {
                    return Err(());
                }
                let read = self.rc_read(x);
                self.fits(&read, &b)
            }
            // A `T` where a `&rc T` is wanted is moved into a new box, when
            // the box's type is known.
            (_, Ty::Rc(y)) if top && !self.has_open_vars(y, &HashSet::new()) => {
                let y = (**y).clone();
                self.unify(&a, &y)
            }
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
            // A `&T` is copied where a duplicable `T` is wanted (`owned`).
            (Ty::Named(l, la), Ty::Named(o, oa))
                if self.datas.lent_of.get(o) == Some(l)
                    && la.len() == oa.len()
                    && self.kind(&b).dup() =>
            {
                for (p, q) in la.clone().iter().zip(oa.clone().iter()) {
                    self.fits(p, q)?;
                }
                Ok(())
            }
            // `&orig T` is lent as `&T` (`lend`), and fits another `&orig T`.
            (Ty::Orig(x), Ty::Orig(y)) => self.fits(x, y),
            (Ty::Orig(x), Ty::Named(l, args)) if matches!(&**x, Ty::Named(n, xa) if self.datas.lent_of.get(n) == Some(l) && xa.len() == args.len()) =>
            {
                let Ty::Named(_, xa) = &**x else {
                    unreachable!()
                };
                for (p, q) in xa.clone().iter().zip(args) {
                    self.fits(p, q)?;
                }
                Ok(())
            }
            (Ty::Orig(x), Ty::Borrow(y, false)) => self.fits(x, y),
            // A copy of the original value (`&orig T → T`).
            (Ty::Orig(x), _) => self.fits(x, &b),
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
            // Tags are forgotten, never added. What is under a label is taken whole
            // (`@a T <: T`): a product under it keeps its members, as the kernel's
            // ascription takes the label off once and does not go on to a member.
            (Ty::Tagged(ta, x), Ty::Tagged(tb, y)) if tb.is_subset(ta) => {
                let widen = std::mem::replace(&mut self.widen_products, false);
                let fitted = self.fits(x, y);
                self.widen_products = widen;
                fitted
            }
            (Ty::Tagged(_, x), _) if !matches!(b, Ty::Tagged(..)) => {
                let widen = std::mem::replace(&mut self.widen_products, false);
                let fitted = self.fits(x, &b);
                self.widen_products = widen;
                fitted
            }
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
                    .try_for_each(|(x, y)| self.fits_param(x, y))
                    .and_then(|()| self.fits(ra, rb));
                self.widen_products = widen;
                fitted
            }
            _ => self.unify(&a, &b),
        }
    }

    /// A function whose parameter is `x` may stand where one whose parameter
    /// is `y` is expected. One that borrows (`&A`) may be given a value (`A`)
    /// of any kind: the caller's value is lent for the call and dropped after
    /// it. One that takes a value may be lent one only when `A` is
    /// duplicable: what is lent is copied for it.
    fn fits_param(&mut self, x: &Ty, y: &Ty) -> Result<(), ()> {
        match (self.resolve(x), self.resolve(y)) {
            (Ty::Borrow(inner, false), y) if !matches!(y, Ty::Borrow(..) | Ty::Var(_)) => {
                self.fits(&y, &inner)
            }
            (x, Ty::Borrow(inner, _)) if !matches!(x, Ty::Borrow(..) | Ty::Var(_)) => {
                if !self.kind(&x).dup() {
                    return Err(());
                }
                self.fits(&inner, &x)
            }
            _ => self.fits(y, x),
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

    /// The struct `t` read through its `coerce` field: the struct, the
    /// field, the field's type and the level written.
    fn coerce_step(&self, t: &Ty) -> Option<(Name, String, Ty, CoerceLevel)> {
        let Ty::Named(d, args) = self.resolve(t) else {
            return None;
        };
        let (index, level) = self.datas.decls.get(&d)?.coerce?;
        let (field, ty) = self.datas.fields(&d, 0, &args).into_iter().nth(index)?;
        Some((d, field?, self.resolve(&ty), level))
    }

    /// `a` where `b` is wanted, read through `coerce` fields: `&W` as `&T`,
    /// `&mut W` as `&mut T`, `W` as `T`. A wanted type that is still a
    /// variable is not one to read into (a type variable takes `W` as it is).
    /// The level each step allows is checked here; the place is recorded for
    /// the expansion.
    fn coerce_fit(&mut self, a: &Ty, b: &Ty, span: Span) -> bool {
        let (a, b) = (self.resolve(a), self.resolve(b));
        let (from, want, mode) = match (&a, &b) {
            (_, Ty::Var(_)) | (_, Ty::Borrow(_, _)) if matches!(b.unborrowed(), Ty::Var(_)) => {
                return false;
            }
            (Ty::Borrow(w, lent), Ty::Borrow(t, wanted)) if *lent || !*wanted => (
                (**w).clone(),
                (**t).clone(),
                if *wanted {
                    CoerceLevel::Mut
                } else {
                    CoerceLevel::Ref
                },
            ),
            (Ty::Borrow(..), _) | (_, Ty::Borrow(..)) => return false,
            _ => (a.clone(), b.clone(), CoerceLevel::Owned),
        };
        let mut current = from.clone();
        let mut steps = Vec::new();
        let mut level = CoerceLevel::Owned;
        loop {
            let Some((d, field, ty, l)) = self.coerce_step(&current) else {
                return false;
            };
            steps.push((d, field));
            level = level.min(l);
            current = ty;
            if self.attempt(|c| c.fits(&current, &want)).is_ok() {
                break;
            }
            if steps.len() > 32 {
                return false;
            }
        }
        let (ty, target) = (self.shown(&from), self.shown(&want));
        let duplicable = mode == CoerceLevel::Ref && self.kind(&want).dup();
        let needed = if duplicable { CoerceLevel::Owned } else { mode };
        if level < needed {
            let allowed = match level {
                CoerceLevel::Ref => "`&`",
                _ => "`&` and `&mut`",
            };
            let message = match mode {
                _ if duplicable => msg!(
                    "nibcheck-coerce-duplicable",
                    ty = ty.to_string(),
                    target = target.to_string()
                ),
                CoerceLevel::Mut => msg!(
                    "nibcheck-coerce-lend-mut",
                    ty = ty.to_string(),
                    target = target.to_string()
                ),
                _ => msg!(
                    "nibcheck-coerce-move",
                    ty = ty.to_string(),
                    target = target.to_string(),
                    allowed = allowed
                ),
            };
            self.error(message, span);
        }
        if mode == CoerceLevel::Owned {
            self.coercion_moves.push(span);
        }
        self.coercions.push((span, steps));
        true
    }

    /// What reading a `&rc T` gives: the borrow of its contents.
    fn rc_read(&self, contents: &Ty) -> Ty {
        match contents {
            Ty::Named(n, _) if self.datas.lent_of.contains_key(n) => {
                Ty::Orig(Box::new(contents.clone()))
            }
            _ => Ty::Borrow(Box::new(contents.clone()), false),
        }
    }

    /// Whether a `&rc T` given where `b` is wanted is read: `b` is a
    /// borrow or a value of one type, not a box, a union or a type not
    /// known yet.
    fn rc_reads_as(&self, b: &Ty) -> bool {
        !matches!(
            b,
            Ty::Rc(_)
                | Ty::Var(_)
                | Ty::Union(_)
                | Ty::Poly(..)
                | Ty::Tagged(..)
                | Ty::App(..)
                | Ty::Never
        ) && !matches!(b, Ty::Borrow(_, true))
    }

    fn expect(&mut self, a: &Ty, b: &Ty, span: Span, what: Message) {
        self.product_note = None;
        // A text literal where a `&Text` is expected: it is a constant, there is nothing to lend.
        if self.text_literals.contains(&span)
            && matches!(self.resolve(a), Ty::Text)
            && matches!(self.resolve(b), Ty::Borrow(inner, false) if *inner == Ty::Text)
        {
            return;
        }
        let widen = std::mem::replace(&mut self.widen_products, true);
        self.rc_top = true;
        let mut fitted = self.fits(a, b);
        self.rc_top = false;
        // `T` where `@a T` is expected: the value is wrapped (`T` written as `@a T`), which a
        // label, a mark of the type, leaves as it is.
        if fitted.is_err()
            && let Ty::Tagged(_, under) = self.resolve(b).unborrowed()
            && !matches!(self.resolve(a).unborrowed(), Ty::Tagged(..))
        {
            fitted = self.fits(a, under);
        }
        self.widen_products = widen;
        if fitted.is_err() && self.coerce_fit(a, b, span) {
            fitted = Ok(());
        }
        if fitted.is_ok() {
            match (self.resolve(a), self.resolve(b)) {
                (Ty::Rc(_), Ty::Rc(_)) | (Ty::Never, _) => {}
                (Ty::Rc(x), want) if self.rc_reads_as(&want) => {
                    let borrowed =
                        matches!(want, Ty::Borrow(..) | Ty::Orig(_)) || self.is_lent_struct(&want);
                    if borrowed {
                        self.rc_reads.push(span);
                    } else {
                        self.rc_copies.push(span);
                    }
                    // `&orig T` given as `&T` is lent.
                    if let (Ty::Named(n, _), Ty::Named(l, _)) = (&*x, &want)
                        && self.datas.lent_of.get(n) == Some(l)
                    {
                        self.orig_lends.push(span)
                    }
                }
                (_, Ty::Rc(_)) => self.rc_boxes.push(span),
                (Ty::Named(l, _), Ty::Named(o, _)) if self.datas.lent_of.get(&o) == Some(&l) => {
                    self.lent_copies.push(span)
                }
                (Ty::Orig(x), Ty::Named(l, _)) if matches!(&*x, Ty::Named(n, _) if self.datas.lent_of.get(n) == Some(&l)) => {
                    self.orig_lends.push(span)
                }
                _ => {}
            }
        }
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
                // The contents of a `&rc T` are only borrowed.
                (Ty::Rc(x), y)
                    if !matches!(y, Ty::Borrow(..) | Ty::Orig(_) | Ty::Rc(_))
                        && x.as_ref() == y =>
                {
                    msg!(
                        "nibcheck-rc-not-owned",
                        what = what,
                        found = a.to_string(),
                        expected = b.to_string()
                    )
                }
                (Ty::Rc(_), Ty::Borrow(_, true)) => msg!("nibcheck-rc-mut", ty = a.to_string()),
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
                // the width it sees is `UInt(64)` of `std::uint` (`SInt(64)` of
                // `std::sint`), which runs as `u64`.
                (Ty::Int(x), Ty::Int(y)) if (*x == Width::Nat) != (*y == Width::Nat) => {
                    let machine = if *x == Width::Nat { y } else { x };
                    let (checked, module) = match machine {
                        Width::U8 => ("UInt(8)", "uint"),
                        Width::U16 => ("UInt(16)", "uint"),
                        Width::W8 => ("SInt(8)", "sint"),
                        Width::W16 => ("SInt(16)", "sint"),
                        Width::U32 => ("UInt(32)", "uint"),
                        Width::U64 => ("UInt(64)", "uint"),
                        Width::Host => ("UHost", "uhost"),
                        Width::W32 => ("SInt(32)", "sint"),
                        Width::W64 | Width::Nat => ("SInt(64)", "sint"),
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

    /// `t` with the variables nothing fixed settled, for a structural
    /// class: an integer literal's is `i64`, as everywhere else, and any
    /// other is `Never`, since nothing fixed the type of a value that has
    /// it (`Nil == Nil`). A structural class is decided on this, never on
    /// an open variable.
    fn settled(&self, t: &Ty) -> Ty {
        match self.resolve(t) {
            Ty::Var(v) if self.ints.contains(&v) => Ty::Int(Width::W64),
            Ty::Var(_) => Ty::Never,
            Ty::Fn(ps, r, k) => Ty::Fn(
                ps.iter().map(|p| self.settled(p)).collect(),
                Box::new(self.settled(&r)),
                k,
            ),
            Ty::Union(ts) => union(ts.iter().map(|t| self.settled(t)).collect()),
            Ty::Tagged(tags, t) => tagged(tags, self.settled(&t)),
            Ty::Named(n, args) => Ty::Named(n, args.iter().map(|a| self.settled(a)).collect()),
            Ty::Info(t) => Ty::Info(Box::new(self.settled(&t))),
            Ty::Borrow(t, m) => Ty::Borrow(Box::new(self.settled(&t)), m),
            Ty::Poly(ps, t) => Ty::Poly(ps, Box::new(self.settled(&t))),
            Ty::App(h, x) => Ty::App(Box::new(self.settled(&h)), Box::new(self.settled(&x))),
            other => other,
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
                    msg!("nibcheck-quote-splice-type", found = shown.to_string()),
                    span,
                );
            }
        }
    }

    /// `C::t(G) = H` for each use whose `G` is now known well enough for
    /// `C::t(G)` to be a type: an instance's, or a generic of the function.
    fn solve_projections(&mut self) {
        loop {
            let mut progress = false;
            for (projection, h, span) in std::mem::take(&mut self.deferred_projections) {
                let reduced = self.resolve(&projection);
                if matches!(&reduced, Ty::Named(n, _) if matches!(&projection, Ty::Named(m, _) if m == n))
                {
                    self.deferred_projections.push((projection, h, span));
                    continue;
                }
                progress = true;
                if self.unify(&reduced, &h).is_err() {
                    let (got, want) = (self.shown(&reduced), self.shown(&h));
                    self.error(
                        msg!(
                            "nibcheck-mismatch",
                            what = "an associated type",
                            expected = want.to_string(),
                            found = got.to_string()
                        ),
                        span,
                    );
                }
            }
            if !progress {
                break;
            }
        }
    }

    fn finish(mut self) -> TypeReport {
        self.solve_projections();
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
                self.set_subst(w, Some(Ty::Int(Width::W64)));
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
                _ => self.error(msg!("nibcheck-int-literal-no-type"), span),
            }
        }
        // A closure returns no bare borrow but of a duplicable value
        // (`&A ≡ A`); a type still unknown might not be one.
        for (r, span) in std::mem::take(&mut self.closure_results) {
            let t = self.resolve(&r);
            // A value that holds a borrow may be returned: lin gives the
            // result the borrows of the borrowed arguments and of what the
            // closure captured. A bare borrow is still not returned.
            let bare = matches!(t, Ty::Borrow(..));
            // A bare borrow of a duplicable value is copied out (`&A → A`).
            if bare && self.is_view(&t) && (self.has_vars(&t) || self.view_value(&t).is_none()) {
                self.error(msg!("nibcheck-closure-returns-borrow"), span);
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
                    msg!(
                        "nibcheck-capture-kind-fixed",
                        name = name.to_string(),
                        kind = most.to_string()
                    )
                } else {
                    msg!(
                        "nibcheck-capture-kind-undetermined",
                        name = name.to_string()
                    )
                };
                if !self
                    .errors
                    .iter()
                    .any(|e| e.span == span && e.message == message)
                {
                    self.error(message, span);
                }
                break;
            }
        }
        for (t, span) in std::mem::take(&mut self.rc_contents) {
            let t = self.resolve(&t);
            let shown = self.shown(&t).to_string();
            if self.kind(&t) == Kind::Linear {
                self.error(msg!("nibcheck-rc-linear", ty = shown), span);
            } else if self.is_view(&t) {
                self.error(msg!("nibcheck-rc-borrow", ty = shown), span);
            } else if let Some(p) = self.borrowing_param(&t) {
                self.error(
                    msg!("nibcheck-rc-generic-borrow", name = p.to_string()),
                    span,
                );
            }
        }
        for (t, span) in std::mem::take(&mut self.effect_values) {
            let t = self.resolve(&t);
            if let Some(p) = self.borrowing_param(&t) {
                self.error(
                    msg!("nibcheck-generic-effect-argument", name = p.to_string()),
                    span,
                );
            }
        }
        for (t, bound, span, plain) in std::mem::take(&mut self.bounds) {
            if plain && self.is_view(&t) {
                self.error(msg!("nibcheck-view-type-argument"), span);
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
                    msg!(
                        "nibcheck-constructor-kind-mismatch",
                        what = what.to_string(),
                        arg = arg.to_string(),
                        result = result.to_string(),
                        shown = shown.to_string(),
                        kind = k.to_string()
                    ),
                    span,
                );
            }
        }
        self.check_splices();
        let mut evidence: HashMap<TermId, Vec<Ev>> = HashMap::new();
        for p in std::mem::take(&mut self.pending) {
            let tys: Vec<Ty> = p.tys.iter().map(|t| self.resolve(t)).collect();
            let t = tys.first().cloned().unwrap_or(Ty::Unit);
            let shown_all = || {
                tys.iter()
                    .map(|t| self.shown(t).to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            let ev = if STRUCTURAL.contains(&p.class.as_str()) {
                let flat: Vec<(Name, Param)> = p
                    .assume
                    .iter()
                    .filter_map(|(c, ps)| Some((c.clone(), ps.first()?.clone())))
                    .collect();
                if tys.len() == 1 && self.datas.structural(&p.class, &self.settled(&t), &flat) {
                    Ev::Structural
                } else {
                    let shown = shown_all();
                    let class = written(&p.class);
                    let what = written(&p.what).to_string();
                    let message = match t {
                        Ty::Param(..) => msg!(
                            "nibcheck-needs-class-add-where",
                            what = what,
                            class = class.to_string(),
                            ty = shown
                        ),
                        _ => msg!(
                            "nibcheck-needs-class",
                            what = what,
                            class = class.to_string(),
                            ty = shown
                        ),
                    };
                    self.error(message, p.span);
                    Ev::Missing
                }
            } else {
                match self.resolve_class(&p.class, &tys, &p.assume) {
                    Ok(ev) => ev,
                    Err(why) => {
                        let class = written(&p.class);
                        let message = match why {
                            Unresolved::Undetermined => msg!(
                                "nibcheck-class-type-undetermined",
                                class = class.to_string()
                            ),
                            Unresolved::Assumption(shown) => msg!(
                                "nibcheck-needs-class-add-where",
                                what = written(&p.what).to_string(),
                                class = class.to_string(),
                                ty = shown
                            ),
                            Unresolved::NoInstance(shown) => msg!(
                                "nibcheck-no-instance",
                                class = class.to_string(),
                                ty = shown
                            ),
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
        report.coercions = std::mem::take(&mut self.coercions).into_iter().collect();
        report.qualified_fields = std::mem::take(&mut self.qualified_fields)
            .into_iter()
            .collect();
        report.field_owners = std::mem::take(&mut self.field_owners).into_iter().collect();
        report.coercion_moves = std::mem::take(&mut self.coercion_moves)
            .into_iter()
            .collect();
        report.lent_copies = std::mem::take(&mut self.lent_copies).into_iter().collect();
        report.orig_lends = std::mem::take(&mut self.orig_lends).into_iter().collect();
        report.rc_reads = std::mem::take(&mut self.rc_reads).into_iter().collect();
        report.rc_boxes = std::mem::take(&mut self.rc_boxes).into_iter().collect();
        report.rc_copies = std::mem::take(&mut self.rc_copies).into_iter().collect();
        report.ascribed = std::mem::take(&mut self.ascribed)
            .into_iter()
            .map(|(id, t)| (id, self.resolve(&t)))
            .collect();
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
        // A generic that indexes an effect (`catch`'s `E`) is given by the
        // expansion from what the argument performs, so a type that waits
        // only for it (the `Result(T, E)` such a call returns, passed on to
        // another generic function) is determined there too.
        let undetermined = std::mem::take(&mut self.undetermined);
        for (_, name, generics) in &undetermined {
            let Some(indices) = self.index_generics.get(name) else {
                continue;
            };
            for (g, t) in generics {
                if indices.contains(&g.name)
                    && let Ty::Var(w) = self.resolve(t)
                {
                    arm.insert(w);
                }
            }
        }
        for (id, name, generics) in undetermined {
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
            // An argument that did not fit leaves the generics it would have fixed open: the
            // mismatch is the error, and this one would only follow from it.
            let after_mismatch = self.errors.iter().any(|e| {
                e.span.start >= id.span().start && e.message.id.starts_with("nibcheck-mismatch")
            });
            if !open.is_empty() && !after_mismatch {
                self.error(
                    msg!(
                        "nibcheck-type-not-determined",
                        generics = open
                            .iter()
                            .map(|g| format!("`{g}`"))
                            .collect::<Vec<_>>()
                            .join(", "),
                        name = name.to_string()
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
            self.error(
                msg!(
                    "nibcheck-takes-arguments",
                    name = name.to_string(),
                    count = want.to_string()
                ),
                span,
            );
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
            // `#()` where a type stands is the unit type.
            _ if t.is_unit() => Ty::Unit,
            TermKind::App { .. } if let Some(ts) = t.product_type_members() => {
                let members = ts.iter().map(|t| self.written(t, generics)).collect();
                self.product(members)
            }
            TermKind::Var(n) => match if tauto_surface::bindings::is_library(n, n.as_str()) {
                n.as_str()
            } else {
                ""
            } {
                "i8" => Ty::Int(Width::W8),
                "i16" => Ty::Int(Width::W16),
                "i32" => Ty::Int(Width::W32),
                "i64" => Ty::Int(Width::W64),
                "u8" => Ty::Int(Width::U8),
                "u16" => Ty::Int(Width::U16),
                "u32" => Ty::Int(Width::U32),
                "u64" => Ty::Int(Width::U64),
                "uhost" => Ty::Int(Width::Host),
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
                    // Taken out while it is read, so that a def that names
                    // itself is a name, not a loop.
                    None if let Some(body) = self.type_defs.remove(n) => {
                        let ty = self.written(&body, &HashMap::new());
                        self.type_defs.insert(n.clone(), body);
                        ty
                    }
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
                    if tauto_surface::bindings::is_library(&n, "Info") && arguments.len() == 1 =>
                {
                    Ty::Info(Box::new(self.written(&arguments[0], generics)))
                }
                TermKind::Var(n) if generics.contains_key(n) => {
                    if arguments.len() != 1 {
                        self.error(
                            msg!(
                                "nibcheck-type-constructor-variable-one-argument",
                                name = n.to_string()
                            ),
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
                TermKind::Var(n) => {
                    if tauto_surface::bindings::is_library(&n, "Slice") && !under_borrow {
                        self.error(msg!("nibcheck-slice-only-borrowed"), t.span);
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
                                        msg!("nibcheck-takes-effect-row", name = n.to_string()),
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
                                    msg!(
                                        "nibcheck-effect-row-only-to-row-parameter",
                                        name = n.to_string()
                                    ),
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
                    self.error(msg!("nibcheck-not-a-type"), t.span);
                    self.fresh()
                }
            },
            TermKind::Pi { params, result, .. } => {
                // `(A: Shared, B: Type, …)` first: the expansion's
                // `<A: Shared, B: Type>(…) -> …`.
                // A binder `shared+noborrow` (a class method's
                // `<T: Shared + NoBorrow>`) keeps its `NoBorrow`.
                let binders: Vec<(Param, Kind, bool)> = params
                    .iter()
                    .enumerate()
                    .map_while(|(index, (n, p))| match (n, &*p.kind) {
                        (Some(n), TermKind::Var(k)) => {
                            let (kind, plain) = without_no_borrow(k.as_str());
                            let kind = match kind {
                                None => Kind::Affine,
                                Some(k) => Kind::parse(&k)?,
                            };
                            let param = Param::new(
                                ParamId::Poly {
                                    occurrence: t.id(),
                                    index,
                                },
                                n.clone(),
                            );
                            Some((param, kind, plain))
                        }
                        _ => None,
                    })
                    .collect();
                for (param, _, plain) in &binders {
                    if *plain {
                        self.no_borrow.insert(param.id.clone());
                    }
                }
                let binders: Vec<(Param, Kind)> =
                    binders.into_iter().map(|(p, k, _)| (p, k)).collect();
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
                    self.error(
                        msg!("nibcheck-kind-of-function-type", kind = kind.to_string()),
                        t.span,
                    );
                    other
                }
            },
            // `&rc T`: what the box holds is checked once the program's
            // types are known (`rc_contents`).
            TermKind::Borrow { rc: true, term, .. } => {
                let inner = self.written(term, generics);
                self.rc_contents.push((inner.clone(), t.span));
                Ty::Rc(Box::new(inner))
            }
            TermKind::Borrow {
                mutable,
                orig,
                term,
                ..
            } => {
                self.under_borrow = true;
                let inner = self.written(term, generics);
                // `&T` of a type with `struct &T` is that struct, which holds
                // borrows; `&orig T` is the borrow of the owner.
                if !*mutable
                    && let Some(lent) = self
                        .datas
                        .lent_struct(&Ty::Borrow(Box::new(inner.clone()), false))
                {
                    if *orig {
                        return Ty::Orig(Box::new(inner));
                    }
                    return lent;
                }
                Ty::Borrow(Box::new(inner), *mutable)
            }
            TermKind::Union(ts) => union(ts.iter().map(|t| self.written(t, generics)).collect()),
            TermKind::Tagged { tag, term } => {
                tagged(BTreeSet::from([tag.clone()]), self.written(term, generics))
            }
            // What the reader could not read, said as it says it (`a record writes …`).
            TermKind::Other(what) if what.starts_with('`') => {
                self.error(what.clone(), t.span);
                self.fresh()
            }
            _ => {
                self.error(msg!("nibcheck-not-a-type-of-program"), t.span);
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
        // A written bound that is a kind (`<A: Shared>`); anything else, or
        // nothing, leaves the generic linear.
        let kinds: Vec<Kind> = (0..e.generics.len())
            .map(|i| {
                e.bounds
                    .get(i)
                    .cloned()
                    .flatten()
                    .as_deref()
                    .map(without_no_borrow)
                    .and_then(|(b, _)| b)
                    .as_deref()
                    .and_then(Kind::parse)
                    .unwrap_or(Kind::Linear)
            })
            .collect();
        let generics: HashMap<Name, Ty> = e
            .generics
            .iter()
            .enumerate()
            .map(|(index, g)| {
                (
                    g.clone(),
                    Ty::Param(Param::effect(&owner, index, g), kinds[index]),
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
                    self.error(
                        msg!("nibcheck-parameter-has-no-type", name = e.name.to_string()),
                        e.span,
                    );
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
                self.error(
                    msg!("nibcheck-resume-quantity", quantity = q.to_string()),
                    e.span,
                );
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
                kinds,
                params,
                result,
            },
        );
    }

    /// Records a `struct` or `enum`; field types are checked again after
    /// all declarations are known.
    /// `struct &T { … }`: declared under [`Datas::lent_name`], beside `T` of
    /// the same module (the same qualified name) and over its type
    /// parameters. Its fields are duplicable values or borrows.
    fn declare_lent(&mut self, d: &DataDecl, stmts: &[Stmt]) {
        let shown = d.name.as_str().trim_start_matches('&').to_string();
        let owners: Vec<&DataDecl> = stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Struct(o) | Stmt::Enum(o) if !o.borrowed && last_segment(o.name.as_str()) == last_segment(&shown) => {
                    Some(o)
                }
                _ => None,
            })
            .collect();
        let [owner] = owners.as_slice() else {
            self.error(
                msg!("nibcheck-lent-struct-without-owner", name = shown),
                d.span,
            );
            return;
        };
        if owner.generics.len() != d.generics.len() {
            self.error(msg!("nibcheck-lent-struct-generics", name = shown), d.span);
            return;
        }
        // `struct &T` asks for `Lend(T)` in the same module.
        let lends = stmts.iter().any(|s| match s {
            Stmt::Instance(i) => {
                i.class.as_str().rsplit("::").next() == Some("Lend")
                    && match &*i.head.kind {
                        TermKind::Var(h) => last_segment(h.as_str()) == shown,
                        TermKind::App { function, .. } => {
                            matches!(&*function.kind, TermKind::Var(h) if last_segment(h.as_str()) == shown)
                        }
                        _ => false,
                    }
            }
            // After the classes are expanded: the dictionary's functions.
            Stmt::Fn(f) => f
                .name
                .as_str()
                .strip_prefix("Lend::lend@")
                .is_some_and(|h| last_segment(h) == shown),
            _ => false,
        });
        if !lends {
            self.error(
                msg!("nibcheck-lent-struct-without-lend", name = shown.clone()),
                d.span,
            );
        }
        self.declare_data(d, true, false);
        self.datas
            .lent_of
            .insert(owner.name.clone(), d.name.clone());
        self.lent_decls.push((d.name.clone(), d.span));
    }

    /// Whether `t` is a `struct &T`.
    fn is_lent_struct(&self, t: &Ty) -> bool {
        matches!(t, Ty::Named(n, _) if self.datas.lent_of.values().any(|l| l == n))
    }

    /// A field of `struct &T` is a duplicable value or a borrow.
    fn check_lent_fields(&mut self) {
        for (name, span) in self.lent_decls.clone() {
            let Some(d) = self.datas.decls.get(&name) else {
                continue;
            };
            let fields: Vec<(Option<String>, Ty)> = d
                .constructors
                .iter()
                .flat_map(|c| {
                    c.fields
                        .iter()
                        .map(|(n, t)| (n.as_ref().map(|n| n.to_string()), t.clone()))
                })
                .collect();
            for (field, t) in fields {
                let ok = self.kind(&unborrow_shared(&t)).dup();
                if !ok {
                    let shown = name.as_str().trim_start_matches('&').to_string();
                    self.error(
                        msg!(
                            "nibcheck-lent-struct-field",
                            name = shown,
                            field = field.unwrap_or_default()
                        ),
                        span,
                    );
                }
            }
        }
    }

    fn declare_data(&mut self, d: &DataDecl, is_struct: bool, builtin: bool) {
        // The words in the parentheses: a kind, and `borrow` on an extern
        // `type` (`type(affine, borrow) Guard`). A type with fields holds a
        // borrow when a field does, with nothing written; only an opaque
        // extern type says so in its declaration, which the grammar keeps to
        // `extern`.
        let mut words: Vec<&str> = d
            .kind
            .as_deref()
            .map(|k| k.split(',').map(str::trim).collect())
            .unwrap_or_default();
        let inductive = words.contains(&tauto_surface::inductive_data::KIND);
        words.retain(|w| *w != tauto_surface::inductive_data::KIND);
        let view = words.contains(&"borrow");
        if view && (!is_struct || d.constructors.iter().any(|c| !c.fields.is_empty())) {
            self.error(msg!("nibcheck-borrow-only-extern-type"), d.span);
        }
        let declared = match words.iter().find(|w| **w != "borrow") {
            Some(k) => Kind::parse(k),
            // A borrow is not copied out of the value that holds it.
            None if view => Some(Kind::Affine),
            None => None,
        };
        // Still here: it could not be the `inductive` it says it is.
        if inductive {
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
                    .map(|(n, t)| (n.clone(), self.written(t, &generics)))
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
        // A variant of another type may share the struct's name: the name then
        // stays ambiguous, whichever of them is declared first.
        if is_struct && constructors.len() == 1 && !self.datas.ambiguous_ctors.contains_key(&d.name)
        {
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
                coerce: d.coerce.as_ref().map(|c| (c.field, c.level)),
            },
        );
    }

    /// Which declarations hold themselves, and whether a written kind is
    /// looser than what the fields give.
    fn finish_datas(&mut self, program: &Program) {
        let names: Vec<Name> = self.datas.decls.keys().cloned().collect();
        self.datas.find_views();
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
                    msg!(
                        "nibcheck-declared-shared-holds-itself",
                        declared = declared.to_string(),
                        name = d.name.to_string()
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
                            msg!(
                                "nibcheck-declared-but-field",
                                declared = declared.to_string(),
                                field = field.to_string(),
                                kind = k.to_string()
                            ),
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
        // A local function's `where` may name a type parameter of the
        // function it is in (`expand.rs` writes the enclosing `where` on it),
        // and so may the dictionary parameters it is given for it. Other
        // outer names are not in its signature.
        let mut named: Vec<&str> = Vec::new();
        for c in &f.where_ {
            if let TermKind::Var(g) = &*c.ty.kind {
                named.push(g.as_str());
            }
        }
        // A dictionary parameter is named `member@A` (`expand.rs`).
        named.extend(
            f.params
                .iter()
                .filter_map(|p| p.as_str().rsplit_once('@').map(|(_, g)| g)),
        );
        for (g, t) in &self.type_params {
            if named.contains(&g.as_str())
                && !f.generics.iter().any(|own| own.as_str() == g.as_str())
            {
                map.insert(g.clone(), t.clone());
            }
        }
        for (i, g) in f.generics.iter().enumerate() {
            // Native Nib has type and row generics only. A checked term
            // telescope must first be lowered to ordinary value parameters;
            // ignoring its domain here would silently erase an argument.
            fn native_kind(ty: &SurfaceTerm) -> bool {
                match &*ty.kind {
                    // `NoBorrow`, alone or beside a kind (`Shared + NoBorrow`).
                    TermKind::Var(name) if name.as_str() == "NoBorrow" => true,
                    TermKind::App {
                        function,
                        arguments,
                    } if matches!(&*function.kind, TermKind::Var(n) if n.as_str() == "+") => {
                        arguments.iter().all(native_kind)
                    }
                    TermKind::Var(name) => name.sort_symbol().is_some_and(|sort| {
                        matches!(sort, tauto_surface::identity::SortSymbol::Type(_))
                    }),
                    TermKind::App { function, .. } => matches!(&*function.kind,
                        TermKind::Var(name) if name.sort_symbol().is_some_and(|sort| matches!(sort, tauto_surface::identity::SortSymbol::Type(_)))),
                    TermKind::Pi {
                        params,
                        result,
                        effects,
                        ..
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
                            let (kind, _) = without_no_borrow(bound);
                            kind.as_deref().is_some_and(|k| {
                                Kind::parse(k).is_none() && Kind::parse_ctor(k).is_none()
                            })
                        }))
            {
                self.error(
                    msg!(
                        "nibcheck-term-generic-needs-extraction",
                        name = g.to_string()
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
            // `NoBorrow` beside the kind (`<A: Shared + NoBorrow>`).
            let (bound, plain) = match bound.as_deref().map(without_no_borrow) {
                Some((b, plain)) => (b, plain),
                None => (None, false),
            };
            if plain {
                self.no_borrow.insert(param.id.clone());
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
                    // `x: &T` of a type with `struct &T` takes that struct.
                    Some(false)
                        if !matches!(t, Ty::Borrow(..))
                            && let Some(lent) = self
                                .datas
                                .lent_struct(&Ty::Borrow(Box::new(t.clone()), false)) =>
                    {
                        lent
                    }
                    // Already written as `&T` and read as its `struct &T`, or
                    // as `&orig T`.
                    Some(false) if self.is_lent_struct(&t) || matches!(t, Ty::Orig(_)) => t,
                    Some(m) if !matches!(t, Ty::Borrow(..)) => Ty::Borrow(Box::new(t), *m),
                    _ => t,
                }
            })
            .collect::<Vec<_>>();
        let result = match &f.result {
            Some(r) => self.written(r, &map),
            None => self.fresh(),
        };
        // A result that may hold a borrow needs a lender only when it is
        // written `&T` or `&mut T` itself. Without a borrowed parameter the
        // result borrows nothing: the body's check sees to that (an extern,
        // which has no body, is trusted to keep it).
        let lends = params.iter().any(|p| matches!(p, Ty::Borrow(..)));
        let direct = matches!(self.resolve(&result), Ty::Borrow(..));
        if self.is_view(&result) && (lends || direct) {
            let span = f.result.as_ref().map_or(f.span, |r| r.span);
            let shown = self.shown(&result);
            if self.has_mut_borrow(&result) {
                if !params.iter().any(|p| matches!(p, Ty::Borrow(_, true))) {
                    self.error(
                        msg!(
                            "nibcheck-return-needs-mut-parameter",
                            ty = shown.to_string()
                        ),
                        span,
                    );
                }
            } else if !lends {
                self.error(
                    msg!(
                        "nibcheck-return-needs-borrowed-parameter",
                        ty = shown.to_string()
                    ),
                    span,
                );
            }
        }
        // `borrows(m, x.f)`: the result holds a borrow, and each path starts
        // at a parameter that lends one.
        if let Some(lends) = &f.lends {
            let span = f.result.as_ref().map_or(f.span, |r| r.span);
            if !self.is_view(&result) {
                let shown = self.shown(&result);
                self.error(
                    msg!(
                        "nibcheck-borrows-result-holds-no-borrow",
                        ty = shown.to_string()
                    ),
                    span,
                );
            }
            let mut lends_mut = false;
            for path in lends {
                let root = path.split('.').next().unwrap_or(path);
                let at = f.params.iter().position(|p| p.as_str() == root);
                // `borrows(place)`: an operation of the written row.
                let in_row = !path.contains('.')
                    && f.effects.iter().flatten().any(|e| {
                        crate::lin::effect_key(&e.to_string()) == crate::lin::effect_key(path)
                    });
                let at = if in_row { None } else { at };
                match at.map(|i| &params[i]) {
                    Some(Ty::Borrow(_, m)) => lends_mut |= *m,
                    Some(t) if self.is_view(t) => lends_mut |= self.has_mut_borrow(t),
                    None if in_row => {}
                    _ => self.error(
                        msg!(
                            "nibcheck-borrows-not-a-borrowed-parameter",
                            name = root.to_string()
                        ),
                        span,
                    ),
                }
            }
            if self.is_view(&result) && self.has_mut_borrow(&result) && !lends_mut {
                let shown = self.shown(&result);
                self.error(
                    msg!(
                        "nibcheck-return-needs-mut-parameter",
                        ty = shown.to_string()
                    ),
                    span,
                );
            }
        }
        let mut preds: Vec<(Name, Vec<Param>)> = Vec::new();
        let mut equations: Vec<(Name, Param, Param)> = Vec::new();
        let generic_param = |n: &Name| {
            generics
                .iter()
                .find(|(g, _)| &g.name == n)
                .map(|(g, _)| g.clone())
        };
        for c in &f.where_ {
            if c.class.as_str() == type_functions::ASSOC {
                if let (TermKind::Var(h), [projection]) = (&*c.ty.kind, c.arguments.as_slice())
                    && let TermKind::App {
                        function,
                        arguments,
                    } = &*projection.kind
                    && let (TermKind::Var(member), [g]) = (&*function.kind, arguments.as_slice())
                    && let TermKind::Var(g) = &*g.kind
                    && let (Some(g), Some(h)) = (generic_param(g), generic_param(h))
                {
                    equations.push((member.clone(), g, h));
                }
                continue;
            }
            let asked = self.classes.get(&c.class).map(|info| info.decl.arity);
            let args: Vec<&SurfaceTerm> = std::iter::once(&c.ty).chain(&c.arguments).collect();
            if let Some(arity) = asked
                && args.len() != arity
            {
                self.error(
                    msg!(
                        "nibcheck-class-argument-arity",
                        name = c.class.to_string(),
                        expected = arity.to_string(),
                        count = args.len().to_string()
                    ),
                    c.span,
                );
                continue;
            }
            if asked.is_none() && !c.arguments.is_empty() {
                // Unknown / structural multi-arg: value index needs extraction.
                if !STRUCTURAL.contains(&c.class.as_str()) {
                    self.error(msg!("nibcheck-value-indexed-constraints"), c.span);
                    continue;
                }
            }
            if !STRUCTURAL.contains(&c.class.as_str()) && !self.classes.contains_key(&c.class) {
                self.error(
                    msg!("nibcheck-not-a-class", name = c.class.to_string()),
                    c.span,
                );
                continue;
            }
            let resolve_generic = |g: &Name| -> Option<Param> {
                if generics.iter().any(|(n, _)| &n.name == g) {
                    return generics
                        .iter()
                        .find(|(n, _)| &n.name == g)
                        .map(|(n, _)| n.clone());
                }
                // A local function's `where` may name a type parameter of
                // the function it is in (`expand.rs` writes the enclosing
                // `where` on it).
                match self.type_params.get(g) {
                    Some(Ty::Param(p, _)) => Some(p.clone()),
                    _ => None,
                }
            };
            let mut params = Vec::new();
            let mut ok = true;
            for a in &args {
                match &*a.kind {
                    TermKind::Var(g) => match resolve_generic(g) {
                        Some(p) => params.push(p),
                        None => {
                            self.error(
                                msg!(
                                    "nibcheck-where-only-generics-of-function",
                                    name = f.name.to_string()
                                ),
                                c.span,
                            );
                            ok = false;
                            break;
                        }
                    },
                    _ => {
                        self.error(
                            msg!(
                                "nibcheck-where-only-generics-of-function",
                                name = f.name.to_string()
                            ),
                            c.span,
                        );
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let pred = (c.class.clone(), params);
            if preds
                .iter()
                .any(|(cls, ps)| cls == &pred.0 && ps == &pred.1)
            {
                self.error(
                    msg!(
                        "nibcheck-predicate-written-twice",
                        class = pred.0.to_string(),
                        argument = pred
                            .1
                            .iter()
                            .map(|p| p.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    c.span,
                );
                continue;
            }
            preds.push(pred);
        }
        Scheme {
            owner,
            generics,
            ty: Ty::Fn(params, Box::new(result), Kind::Shared),
            preds,
            equations,
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
                None => {
                    let plain = self.no_borrow.contains(&g.id);
                    self.bounds.push((v.clone(), *k, span, plain))
                }
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
        self.instance_names.insert(
            id,
            s.generics
                .iter()
                .map(|(g, _)| (g.name.clone(), arguments[g.id()].clone()))
                .collect(),
        );
        for (member, g, h) in &s.equations {
            self.deferred_projections.push((
                Ty::Named(member.clone(), vec![arguments[g.id()].clone()]),
                arguments[h.id()].clone(),
                span,
            ));
        }
        self.solve_projections();
        for (n, (class, gs)) in s.preds.iter().enumerate() {
            // A `where` on a type parameter of the enclosing function (a
            // local function's) is about that parameter as it is.
            let tys: Vec<Ty> = gs
                .iter()
                .map(|g| match arguments.get(g.id()) {
                    Some(t) => t.clone(),
                    None => self
                        .type_params
                        .get(&g.name)
                        .cloned()
                        .unwrap_or(Ty::Param(g.clone(), Kind::Affine)),
                })
                .collect();
            self.pending.push(Pending {
                class: class.clone(),
                tys,
                what: name.to_string(),
                assume: self.assume.clone(),
                span,
                slot: Some((id, n, s.preds.len())),
            });
        }
        // An inferred result can already refer to the declaration's binders.
        substitute(&self.resolve(&s.ty), &arguments)
    }

    /// A type variable in `t` that may stand for a type holding a borrow:
    /// one not bounded by `NoBorrow`.
    fn borrowing_param(&self, t: &Ty) -> Option<Name> {
        match t {
            Ty::Param(p, _) if !self.no_borrow.contains(&p.id) => Some(p.name.clone()),
            Ty::Named(_, args) => args.iter().find_map(|a| self.borrowing_param(a)),
            Ty::Borrow(t, _) | Ty::Tagged(_, t) | Ty::Rc(t) => self.borrowing_param(t),
            Ty::Union(ts) => ts.iter().find_map(|a| self.borrowing_param(a)),
            _ => None,
        }
    }

    /// `let(stack) x := e`: the value of `x` is placed in the frame's slot,
    /// so its type has a size known here and is placed without an
    /// allocation: no type parameter, and not a type that holds itself.
    fn stack_let(&mut self, name: &Name, word: &str, t: &Ty, span: Span) {
        if word != "stack" {
            self.error(
                msg!("nibcheck-let-unknown-prop", word = word.to_string()),
                span,
            );
            return;
        }
        let shown = |s: &Self| s.shown(t).to_string();
        if let Some(param) = self.stack_param(t) {
            let ty = shown(self);
            self.error(
                msg!(
                    "nibcheck-stack-type-param",
                    name = name.to_string(),
                    ty = ty,
                    param = param
                ),
                span,
            );
        } else if let Ty::Named(n, _) = self.resolve(t)
            && self.datas.decls.get(&n).is_some_and(|d| d.recursive)
        {
            let ty = shown(self);
            self.error(
                msg!("nibcheck-stack-recursive", name = name.to_string(), ty = ty),
                span,
            );
        }
    }

    /// A type parameter somewhere in `t`: its size is not known in the frame.
    fn stack_param(&self, t: &Ty) -> Option<String> {
        match self.resolve(t) {
            Ty::Param(p, _) => Some(p.name.to_string()),
            Ty::Union(ts) => ts.iter().find_map(|t| self.stack_param(t)),
            Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Orig(t) | Ty::Rc(t) => {
                self.stack_param(&t)
            }
            Ty::App(h, x) => self.stack_param(&h).or_else(|| self.stack_param(&x)),
            Ty::Named(_, args) => args.iter().find_map(|a| self.stack_param(a)),
            Ty::Fn(ps, r, _) => ps
                .iter()
                .find_map(|p| self.stack_param(p))
                .or_else(|| self.stack_param(&r)),
            _ => None,
        }
    }

    /// A type that holds a borrow, received as one is: a borrow, a
    /// extern `type(borrow)`, or a type applied to one.
    fn is_view(&self, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Borrow(..) => true,
            Ty::Named(n, args) => {
                self.datas.decls.get(&n).is_some_and(|d| d.view)
                    || args.iter().any(|a| self.is_view(a))
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
        // A local function is inside the enclosing function's type
        // parameters, so it may assume their `where` as well as its own.
        // A generic the local function declares again hides the outer one.
        let mut assume = scheme.preds.clone();
        assume.extend(
            self.assume
                .iter()
                .filter(|(_, gs)| {
                    gs.iter().all(|g| {
                        !scheme
                            .generics
                            .iter()
                            .any(|(own, _)| own.name.as_str() == g.name.as_str())
                    })
                })
                .cloned(),
        );
        let outer = std::mem::replace(&mut self.assume, assume);
        let projections = scheme
            .equations
            .iter()
            .map(|(m, g, h)| {
                let kind = scheme
                    .generics
                    .iter()
                    .find(|(x, _)| x == h)
                    .map_or(Kind::Affine, |(_, k)| *k);
                (m.clone(), g.id().clone(), Ty::Param(h.clone(), kind))
            })
            .collect();
        let outer_projections = std::mem::replace(&mut self.local_projections, projections);
        // The enclosing function's type parameters are in scope, under the
        // local function's own.
        let mut type_params = self.type_params.clone();
        type_params.extend(
            scheme
                .generics
                .iter()
                .map(|(g, k)| (g.name.clone(), Ty::Param(g.clone(), *k))),
        );
        let outer_types = std::mem::replace(&mut self.type_params, type_params);
        self.result_hint = Some((**result).clone());
        let body = self.infer(&f.body, &mut env);
        self.type_params = outer_types;
        self.function_owner = outer_owner;
        self.declaration_path = outer_path;
        self.term_path = outer_terms;
        self.term_children = outer_children;
        self.assume = outer;
        self.local_projections = outer_projections;
        self.returns.pop();
        self.expect(
            &body,
            result,
            f.body.span,
            msg!("nibcheck-what-result-of", name = f.name.to_string()),
        );
    }

    fn run(&mut self, program: &Program, prelude: &Program) {
        for s in &program.stmts {
            if let Stmt::Def(t) = s
                && t.params.is_empty()
                && matches!(&*t.ty.kind, TermKind::Var(n) if n.as_str() == "Type")
                && let Some(body) = &t.body
            {
                self.type_defs.insert(t.name.clone(), body.clone());
            }
        }
        // The mark of a program whose classes did not expand is not an error.
        for (message, span) in unexpanded_errors(program).unwrap_or(&program.errors) {
            self.error(message.clone(), *span);
        }
        // Validate replaceable `extern` here too: differentials parse without
        // the loader that already pushed these into `program.errors`. Skip a
        // diagnostic the loader already recorded (same id and span).
        for (message, span) in
            tauto_surface::surface::extern_blocks::validate_extern_blocks(&program.stmts)
        {
            let already = self.errors.iter().any(|e| {
                &*e.message.id == &*message.id
                    && e.span.start == span.start
                    && e.span.end == span.end
            });
            if !already {
                self.error(message, span);
            }
        }
        self.extern_blocks =
            tauto_surface::surface::extern_blocks::ExternBlocks::collect(&program.stmts);
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
                        msg!(
                            "nibcheck-row-variable-not-declared-type",
                            variable = var.to_string(),
                            name = d.name.to_string()
                        ),
                        d.span,
                    );
                }
            }
        }
        let of_prelude = indices::prelude_indices(prelude);
        self.indexed = indices::indexed_effects(program);
        self.indexed.extend(of_prelude.indexed.iter().cloned());
        self.index_generics = of_prelude.generics.clone();
        self.index_generics.extend(indices::index_generics(program));
        // The prelude's declarations, unless the program declares the name.
        // A program's own externs are its own too: the prelude read as a
        // program declares the host primitives it wraps.
        let own: HashSet<&Name> = program
            .stmts
            .iter()
            .flat_map(|s| match s {
                Stmt::Struct(d) | Stmt::Enum(d) => vec![&d.name],
                Stmt::Fn(f) => vec![&f.name],
                Stmt::Effect(e) => vec![&e.name],
                Stmt::Extern { fns, .. } => fns.iter().map(|f| &f.name).collect(),
                _ => vec![],
            })
            .collect();
        for s in &prelude.stmts {
            match s {
                Stmt::Struct(d) if d.borrowed && !own.contains(&d.name) => {
                    self.declare_lent(d, &prelude.stmts)
                }
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
                Stmt::Struct(d) if d.borrowed && declared.insert(&d.name) => {
                    self.declare_lent(d, &program.stmts)
                }
                Stmt::Struct(d) if declared.insert(&d.name) => self.declare_data(d, true, false),
                Stmt::Enum(d) if declared.insert(&d.name) => self.declare_data(d, false, false),
                _ => {}
            }
        }
        self.finish_datas(program);
        self.check_lent_fields();
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
            self.error(
                msg!("nibcheck-type-declared-twice", name = d.name.to_string()),
                d.span,
            );
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
            self.error(
                msg!(
                    "nibcheck-function-declared-twice",
                    name = f.name.to_string()
                ),
                f.span,
            );
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
                Stmt::Extern {
                    fns: externs,
                    instances,
                    types,
                    structs,
                    enums,
                    ..
                } => {
                    let replaceable = tauto_surface::surface::extern_is_replaceable(
                        externs, instances, types, structs, enums,
                    );
                    for (j, f) in externs.iter().enumerate() {
                        self.declaration_path = vec![1, i, j];
                        let scheme = self.signature(f);
                        self.fns.insert(f.name.clone(), scheme.clone());
                        if replaceable {
                            fns.push((f, scheme));
                        }
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
                stack,
                ..
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
                                msg!(
                                    "nibcheck-let-mut-borrow-binds-return",
                                    name = name.to_string()
                                ),
                                value.span,
                            );
                        }
                    }
                    (true, false) => self.error(
                        if *borrow_mut {
                            msg!(
                                "nibcheck-let-mut-borrow-binds-return",
                                name = name.to_string()
                            )
                        } else {
                            msg!("nibcheck-let-borrow-binds-return", name = name.to_string())
                        },
                        value.span,
                    ),
                    // A value that holds a borrow is received as a borrow,
                    // even of duplicable values: an unannotated `let` asks for
                    // no copy (`&A → A` happens only where an `A` is wanted).
                    (false, _) => {}
                }
                if let Some(word) = stack {
                    self.stack_let(name, word, &resolved, value.span);
                }
                self.bind_local(env, name, t, false, site(value));
                Ty::Unit
            }
            Stmt::Var {
                name,
                ty,
                value,
                borrow,
                stack,
                ..
            } => {
                if let Some(word) = stack {
                    let message = if word == "stack" {
                        msg!("nibcheck-stack-var", name = name.to_string())
                    } else {
                        msg!("nibcheck-let-unknown-prop", word = word.clone())
                    };
                    self.error(message, value.span);
                }
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
                let borrow = &(*borrow || self.is_view(&resolved));
                if *borrow {
                    if !self.is_view(&resolved) {
                        self.error(
                            msg!("nibcheck-var-borrow-binds-view", name = name.to_string()),
                            value.span,
                        );
                    }
                } else if self.kind(&resolved) == Kind::Linear {
                    self.error(
                        msg!(
                            "nibcheck-var-holds-linear",
                            name = name.to_string(),
                            ty = self.shown(&resolved).to_string()
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
                deref,
            } => {
                let v = self.infer(value, env);
                let target = msg!(
                    "nibcheck-what-named",
                    name = crate::surface::print::print_term(place)
                );
                match env.iter().rev().find(|l| l.name == *name) {
                    Some(l) if l.view => {
                        self.error(msg!("nibcheck-view-var-field-assigned"), value.span);
                        return Ty::Unit;
                    }
                    Some(_) if self.mutable_place(place, env) => {}
                    Some(_) => {
                        self.error(
                            msg!("nibcheck-assigns-field-of-var", target = target.to_string()),
                            place.span,
                        );
                        return Ty::Unit;
                    }
                    None => {
                        self.error(
                            msg!("nibcheck-not-defined", name = name.to_string()),
                            place.span,
                        );
                        return Ty::Unit;
                    }
                }
                // The place's type, not the borrow a read through `&mut`
                // would give.
                self.assigning = true;
                let ty = self.infer(place, env);
                self.assigning = false;
                let ty = self.resolve(&ty);
                // The field's type as declared: a read through a borrowed
                // root wraps a field that is not copied in one more borrow.
                let root_borrowed = env
                    .iter()
                    .rev()
                    .find(|l| l.name == *name)
                    .is_some_and(|l| matches!(self.resolve(&l.ty), Ty::Borrow(..)));
                let declared = match &ty {
                    Ty::Borrow(inner, _) if root_borrowed && !self.kind(inner).dup() => {
                        (**inner).clone()
                    }
                    t => t.clone(),
                };
                let shown = crate::surface::print::print_term(place);
                match (deref.is_some(), &declared) {
                    // `*p.r := v` writes where the `&mut` in the field points.
                    (true, Ty::Borrow(inner, true)) => {
                        let inner = (**inner).clone();
                        self.expect(&v, &inner, value.span, target);
                    }
                    (true, _) => {
                        self.error(
                            msg!("nibcheck-deref-needs-mut-borrow", place = shown),
                            place.span,
                        );
                    }
                    // `p.r := v` would rebind the borrow the field holds.
                    (false, Ty::Borrow(..)) => {
                        self.error(
                            msg!("nibcheck-assign-through-borrow", place = shown),
                            place.span,
                        );
                    }
                    (false, _) => {
                        let ty = ty.unborrowed().clone();
                        self.expect(&v, &ty, value.span, target);
                    }
                }
                Ty::Unit
            }
            Stmt::Assign {
                name, value, deref, ..
            } => {
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
                    // `*a := v` writes where the `&mut` borrow `a` points.
                    Some(Local {
                        ty: Ty::Borrow(inner, true),
                        mutable: false,
                        ..
                    }) if deref.is_some() => self.expect(
                        &v,
                        &inner,
                        value.span,
                        msg!("nibcheck-what-named", name = name.to_string()),
                    ),
                    Some(_) if deref.is_some() => self.error(
                        msg!("nibcheck-deref-needs-mut-borrow", place = name.to_string()),
                        value.span,
                    ),
                    Some(l) if l.mutable => self.expect(
                        &v,
                        &l.ty,
                        value.span,
                        msg!("nibcheck-what-named", name = name.to_string()),
                    ),
                    // `a := v` rebinds `a`, which a `let` does not allow.
                    Some(Local {
                        ty: Ty::Borrow(_, true),
                        ..
                    }) => self.error(
                        msg!("nibcheck-assign-through-borrow", place = name.to_string()),
                        value.span,
                    ),
                    Some(_) => self.error(
                        msg!("nibcheck-not-a-var", name = name.to_string()),
                        value.span,
                    ),
                    None => self.error(
                        msg!("nibcheck-not-defined", name = name.to_string()),
                        value.span,
                    ),
                }
                Ty::Unit
            }
            Stmt::Fn(f) => {
                let mut scheme = self.signature(f);
                let lam = SurfaceTerm::new(
                    TermKind::Lam {
                        params: f.params.clone(),
                        unused_params: Vec::new(),
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
                    None => self.error(msg!("nibcheck-return-outside-function"), span),
                }
                Ty::Never
            }
            Stmt::Expr(e) => self.infer(e, env),
            // `lower_fors` / `lower_loops` expand them where the program is read.
            Stmt::For { .. } | Stmt::Loop { .. } | Stmt::Break(_) | Stmt::Continue => Ty::Unit,
            Stmt::Theorem(_)
            | Stmt::Def(_)
            | Stmt::Reexport { .. }
            | Stmt::Import { .. }
            | Stmt::Module { .. }
            | Stmt::Mutual { .. }
            | Stmt::Attributed { .. }
            | Stmt::Called { .. }
            | Stmt::Class(_)
            | Stmt::Instance(_)
            | Stmt::Inductive(_) => Ty::Unit,
            Stmt::Struct(d) | Stmt::Enum(d) => {
                self.error(msg!("nibcheck-declare-type-at-top-level"), d.span);
                Ty::Unit
            }
            Stmt::Extern { span, .. } => {
                self.error(msg!("nibcheck-declare-extern-at-top-level"), *span);
                Ty::Unit
            }
            Stmt::Other(what, span) => {
                self.error(
                    msg!("nibcheck-not-supported-yet", what = what.to_string()),
                    *span,
                );
                Ty::Unit
            }
            Stmt::Syntax { span, .. } | Stmt::Macro { span, .. } => {
                self.error(msg!("nibcheck-declare-syntax-at-top-level"), *span);
                Ty::Unit
            }
        }
    }

    /// How many arguments the class of the method `name` (`C::m`) takes, if
    /// `name` is a class's method.
    fn class_member_arity(&self, name: &Name) -> Option<usize> {
        self.classes.values().find_map(|c| {
            c.decl
                .methods
                .iter()
                .any(|m| classes::member_fn(&c.decl, &m.name) == *name)
                .then_some(c.decl.parameters.len())
        })
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
        self.error(msg!("nibcheck-not-defined", name = name.to_string()), span);
        self.fresh()
    }

    /// A constructor used as a value: a nullary one is its value, one with
    /// fields a function from them.
    fn constructor(&mut self, d: &Name, c: usize, span: Span, name: &Name) -> Ty {
        let data = self.datas.decls[d].clone();
        let args: Vec<Ty> = data.generics.iter().map(|_| self.fresh()).collect();
        let fields = self.datas.fields(d, c, &args);
        let result = Ty::Named(d.clone(), args);
        self.refuse_sealed_repr(d, span);
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
        let outer = std::mem::replace(&mut self.at, term.span);
        let t = self.infer_term(term, env, hint);
        self.at = outer;
        self.term_children.pop();
        self.term_path.pop();
        self.terms.push((term.id(), t.clone()));
        t
    }

    fn infer_term(&mut self, term: &SurfaceTerm, env: &mut Vec<Local>, hint: Option<Ty>) -> Ty {
        let span = term.span;
        match &*term.kind {
            // `#()`: the one value of `Unit`.
            _ if term.is_unit() => Ty::Unit,
            // `×` is a type operator: a product value is `#(…)`.
            TermKind::App { .. } if let Some(members) = term.product_type_members() => {
                for m in members {
                    self.infer(m, env);
                }
                self.error(msg!("nibcheck-product-type-as-value"), span);
                self.fresh()
            }
            // `#(a, b)`: the product of its members' types, as [`product`] puts them:
            // `#(a, #(b, c))` is an `A × B × C`, `#(#(a, b), c)` an `(A × B) × C`, and
            // `#(a, #())` an `A × Unit`.
            TermKind::App { .. } if let Some(members) = term.product_value_members() => {
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
            TermKind::Nat(n) => {
                // Where a `Nat` is expected, a numeral is a `Nat`, as on the proof side.
                if let Some(h) = &hint
                    && let Ty::Named(name, args) = self.resolve(h)
                    && args.is_empty()
                    && tauto_surface::bindings::is_library(&name, "Nat")
                {
                    if n.parse::<u128>().is_err() {
                        self.error(msg!("nibcheck-not-a-nat", value = n.to_string()), span);
                    }
                    return Ty::Named(name, args);
                }
                // Where std's `Int` is expected, a numeral is `IntOfNat` of it, as on the
                // proof side (`Datas::int_of_nat`).
                if let Some(h) = &hint
                    && let h = self.resolve(h)
                    && self.datas.int_of_nat(&h).is_some()
                {
                    if n.parse::<u128>().is_err() {
                        self.error(msg!("nibcheck-not-an-int", value = n.to_string()), span);
                    }
                    return h;
                }
                let t = self.fresh_int();
                match n.parse::<i128>() {
                    Ok(v) => self.literals.push((span, v, t.clone())),
                    Err(_) => {
                        self.error(msg!("nibcheck-nat-too-large", value = n.to_string()), span)
                    }
                }
                t
            }
            TermKind::Float(x) => {
                if !x.parse::<f64>().is_ok_and(f64::is_finite) {
                    self.error(
                        msg!("nibcheck-float-too-large", value = x.to_string()),
                        span,
                    );
                }
                Ty::Float
            }
            TermKind::Declaration(_) => Ty::Named(
                tauto_surface::bindings::library_name("SynDeclaration"),
                vec![],
            ),
            // A literal is a constant of the module and freezes nothing, so it fits a `&Text`
            // with no `&` written (`expect` reads `text_literals`).
            TermKind::Text(_) => {
                self.text_literals.insert(span);
                Ty::Text
            }
            TermKind::Bool(_) => Ty::Bool,
            TermKind::Var(name) => self.lookup(name, env, term.id()),
            TermKind::Lam { .. } => self.lambda(term, &[], env),
            TermKind::BorrowLam { borrows, lam } => self.lambda(lam, borrows, env),
            // `&rc e` moves the value of `e` into a new box.
            TermKind::Borrow {
                rc: true,
                term: inner,
                ..
            } => {
                let t = self.infer(inner, env);
                let t = self.resolve(&t);
                self.rc_contents.push((t.clone(), span));
                Ty::Rc(Box::new(t))
            }
            TermKind::Borrow {
                mutable,
                orig,
                term: inner,
                ..
            } => {
                // `&T { f: e }` builds the `struct &T` of `T`.
                if !*mutable
                    && !*orig
                    && let TermKind::Record { name, fields, .. } = &*inner.kind
                    && let Some((family, _)) = self.datas.ctors.get(name).cloned()
                    && let Some(lent) = self.datas.lent_of.get(&family).cloned()
                    && let Some(ctor) = self
                        .datas
                        .decls
                        .get(&lent)
                        .and_then(|d| d.constructors.first())
                        .map(|c| c.name.clone())
                {
                    return self.record(&ctor, fields, env, span);
                }
                if *mutable && !self.mutable_place(inner, env) {
                    let what = place_name(inner).unwrap_or_else(|| "this".into());
                    self.error(
                        msg!("nibcheck-not-a-var-for-lend", what = what.to_string()),
                        span,
                    );
                }
                let t = self.infer(inner, env);
                let t = match self.resolve(&t) {
                    // Lending a borrow lends what it borrows, and a borrow of
                    // a `&rc T` borrows its contents, which are never written.
                    Ty::Borrow(t, _) | Ty::Orig(t) => *t,
                    Ty::Rc(t) => {
                        if *mutable {
                            let shown = self.shown(&Ty::Rc(t.clone()));
                            self.error(msg!("nibcheck-rc-mut", ty = shown.to_string()), span);
                        }
                        *t
                    }
                    t => t,
                };
                // `&orig x` of a type with `struct &T` borrows the owner.
                if *orig
                    && let Ty::Named(n, _) = &t
                    && self.datas.lent_of.contains_key(n)
                {
                    return Ty::Orig(Box::new(t));
                }
                self.resolve(&Ty::Borrow(Box::new(t), *mutable))
            }
            TermKind::Record { name, fields, .. } => self.record(name, fields, env, span),
            // `*a` stands only on the left of `:=`; elsewhere a borrow reads
            // as its value.
            TermKind::App { arguments, .. } if crate::surface::deref_of(term).is_some() => {
                self.error(msg!("nibcheck-deref-outside-assign"), span);
                let inner = arguments[0].clone();
                let t = self.infer(&inner, env);
                self.resolve(&t).unborrowed().clone()
            }
            TermKind::App {
                function,
                arguments,
            } => {
                // `f(<A: T>, x)`: the named implicit arguments are carried first as a record
                // of the generics' names, not an argument of the call.
                let (implicits, arguments) = match arguments.split_first() {
                    Some((first, rest))
                        if matches!(&*first.kind, TermKind::Record { name, .. }
                            if name.spelling() == Some(tauto_surface::IMPLICITS)) =>
                    {
                        (Some(first), rest)
                    }
                    _ => (None, arguments.as_slice()),
                };
                if let TermKind::Var(name) = &*function.kind
                    && !env.iter().any(|l| l.name == *name)
                {
                    if OPERATORS.contains(&name.as_str()) {
                        return self.operator(name, arguments, env, term.id());
                    }
                    if tauto_surface::bindings::is_library(&name, "Syn::expr_of")
                        && let [filled] = arguments
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
                    // `Nil(<A: T>)` names the generic of one: it has no
                    // arguments, and is not `Nil()`.
                    if arguments.is_empty()
                        && implicits.is_none()
                        && !self.fns.contains_key(name)
                        && self.datas.only_nullary(name)
                    {
                        self.error(
                            msg!(
                                "nibcheck-constructor-without-fields",
                                name = name.to_string()
                            ),
                            span,
                        );
                        self.result_hint = hint;
                        return self.infer(function, env);
                    }
                }
                let mut f = self.infer(function, env);
                // The generics a call can name: a `Poly` value's, or a
                // top-level function's, which is instantiated where it is
                // looked up.
                let mut named_generics: Option<Vec<(Name, Ty)>> = None;
                if let Ty::Poly(gs, t) = self.resolve(&f) {
                    let fresh = self.instance_of(&gs);
                    f = substitute(&t, &fresh);
                    // What the call sees of the callee is the instance.
                    self.terms.push((function.id(), f.clone()));
                    named_generics = Some(
                        gs.iter()
                            .map(|(g, _)| (g.name.clone(), fresh[&g.id].clone()))
                            .collect(),
                    );
                } else if let Some(names) = self.instance_names.get(&function.id()) {
                    named_generics = Some(names.clone());
                }
                // A generic named in `<A: T>` is the written type.
                if let (Some(generics), Some(TermKind::Record { fields, .. })) =
                    (&named_generics, implicits.map(|i| &*i.kind))
                {
                    let scope = self.type_params.clone();
                    // `C(T)::m(…)`: the class's arguments, by their places,
                    // lead the generics of its method.
                    let class_arity = match &*function.kind {
                        TermKind::Var(n) => self.class_member_arity(n),
                        _ => None,
                    };
                    for (field, written) in fields {
                        let found = match tauto_surface::class_argument_index(field) {
                            Some(i) if class_arity.is_some_and(|a| i < a) => generics.get(i),
                            _ => generics.iter().find(|(g, _)| g.as_str() == field),
                        };
                        let Some((_, inst)) = found else {
                            self.error(
                                msg!("nibcheck-call-no-type-argument-named", name = field.clone()),
                                written.span,
                            );
                            continue;
                        };
                        let want = self.written(written, &scope);
                        self.expect(&want, inst, written.span, msg!("nibcheck-what-argument"));
                    }
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
                                msg!(
                                    "nibcheck-function-argument-count",
                                    expected = ps.len().to_string(),
                                    given = args.len().to_string()
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
                            self.error(msg!("nibcheck-cannot-infer-function-type"), function.span);
                        }
                        r
                    }
                    // `Nil(<A: T>)`: a constructor without fields, its generics named.
                    other if args.is_empty() && implicits.is_some() => other,
                    other => {
                        self.error(
                            msg!("nibcheck-not-a-function", found = other.to_string()),
                            function.span,
                        );
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
                    self.error(
                        msg!(
                            "nibcheck-no-method",
                            owner = c.to_string(),
                            name = name.to_string()
                        ),
                        span,
                    );
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
                let assigning = std::mem::take(&mut self.assigning);
                self.assigning = assigning;
                let b = self.infer(base, env);
                self.assigning = assigning;
                let mut resolved = self.resolve(&b);
                // A field of a `&rc T` is read through the borrow of its
                // contents.
                if let Ty::Rc(x) = &resolved {
                    self.rc_reads.push(base.span);
                    resolved = self.rc_read(x);
                }
                if let Ty::Named(data, _) = resolved.unborrowed() {
                    self.refuse_sealed_repr(data, span);
                }
                let borrowed = matches!(resolved, Ty::Borrow(..) | Ty::Orig(_));
                // `w.x` reads the field of what `w` coerces to, through every
                // `coerce` field; `w.W::f` the field `f` of `W` on that way.
                let (qualifier, field) = match name.rsplit_once("::") {
                    Some((q, f)) => (Some(q), f),
                    None => (None, name.as_str()),
                };
                let last = |n: &str| n.rsplit("::").next().unwrap_or(n).to_string();
                let mut current = resolved.unborrowed().clone();
                let mut steps: Vec<(Name, String)> = Vec::new();
                let mut passed: Vec<Name> = Vec::new();
                let mut level = CoerceLevel::Owned;
                // A field the coercion expansion wrote is the struct's own.
                let own = term.is_own_field();
                loop {
                    if own {
                        break;
                    }
                    if let (Some(q), Ty::Named(d, _)) = (qualifier, &current)
                        && last(d) == last(q)
                    {
                        break;
                    }
                    let Some((d, f, ty, l)) = self.coerce_step(&current) else {
                        break;
                    };
                    if steps.len() > 32 {
                        break;
                    }
                    passed.push(d.clone());
                    steps.push((d, f));
                    level = level.min(l);
                    current = ty;
                }
                if let Some(q) = qualifier
                    && !matches!(&current, Ty::Named(d, _) if last(d) == last(q))
                {
                    let shown = self.shown(resolved.unborrowed());
                    self.error(
                        msg!(
                            "nibcheck-no-field",
                            name = shown.to_string(),
                            field = name.to_string()
                        ),
                        span,
                    );
                    return self.fresh();
                }
                if qualifier.is_none()
                    && !own
                    && let Ty::Named(here, _) = &current
                    && !self.datas.decls.get(here).is_some_and(|d| {
                        d.is_struct
                            && d.constructors[0]
                                .fields
                                .iter()
                                .any(|(n, _)| n.as_deref() == Some(field))
                    })
                    && let Some(owner) = passed.iter().find(|d| {
                        self.datas.decls[*d].constructors[0]
                            .fields
                            .iter()
                            .any(|(n, _)| n.as_deref() == Some(field))
                    })
                {
                    let place = place_name(base).unwrap_or_else(|| "w".into());
                    self.error(
                        msg!(
                            "nibcheck-coerce-own-field",
                            field = field.to_string(),
                            ty = last(owner),
                            place = place.to_string()
                        ),
                        span,
                    );
                    return self.fresh();
                }
                if !steps.is_empty() {
                    if self.assigning && level < CoerceLevel::Mut {
                        let (ty, target) =
                            (self.shown(resolved.unborrowed()), self.shown(&current));
                        self.error(
                            msg!(
                                "nibcheck-coerce-assign",
                                ty = ty.to_string(),
                                target = target.to_string()
                            ),
                            span,
                        );
                    }
                    self.coercions.push((base.span, steps));
                }
                if qualifier.is_some() {
                    self.qualified_fields.push((span, field.to_string()));
                }
                let name = &field.to_string();
                match (current, name.as_str()) {
                    (Ty::Info(h), "more") => Ty::Fn(vec![Ty::Int(Width::U64)], h, Kind::Shared),
                    (Ty::Info(h), "unbounded") => Ty::Fn(vec![], h, Kind::Shared),
                    (Ty::Named(d, args), _)
                        if self.datas.decls.get(&d).is_some_and(|d| d.is_struct) =>
                    {
                        self.field_owners.push((span, d.clone()));
                        let fields = self.datas.fields(&d, 0, &args);
                        match fields.into_iter().find(|(n, _)| n.as_deref() == Some(name)) {
                            // A field of a `&mut` is lent as `&mut` where the
                            // function returns it (`-> &mut A { s.f }`).
                            Some((_, t)) if borrowed && !self.kind(&t).dup() => {
                                Ty::Borrow(Box::new(t), matches!(resolved, Ty::Borrow(_, true)))
                            }
                            Some((_, t)) => t,
                            None => {
                                self.error(
                                    msg!(
                                        "nibcheck-no-field",
                                        name = d.to_string(),
                                        field = name.to_string()
                                    ),
                                    span,
                                );
                                self.fresh()
                            }
                        }
                    }
                    (other, _) => {
                        self.error(
                            msg!(
                                "nibcheck-no-field",
                                name = other.to_string(),
                                field = name.to_string()
                            ),
                            span,
                        );
                        self.fresh()
                    }
                }
            }
            // `(e: T)`: `e` fits `T`, which may take fewer members of a
            // product (`A × B <: A`, `A × B × C <: A × C`, `@a T <: T`).
            TermKind::Ascribe { term: base, ty } => {
                let b = self.infer(base, env);
                let want = self.written(ty, &self.type_params.clone());
                self.ascribed.push((term.id(), want.clone()));
                match self.resolve(&b) {
                    // A member of a borrowed product is borrowed, but a copy.
                    Ty::Borrow(inner, _) if !matches!(want, Ty::Borrow(..)) => {
                        self.expect(&inner, &want, base.span, msg!("nibcheck-what-ascription"));
                        let want = self.resolve(&want);
                        let want = untagged(want);
                        if self.kind(&want).dup() {
                            want
                        } else {
                            Ty::Borrow(Box::new(want), false)
                        }
                    }
                    _ => {
                        self.expect(&b, &want, base.span, msg!("nibcheck-what-ascription"));
                        // `(p: @a T)` is a `T`, as the kernel types it.
                        untagged(self.resolve(&want))
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
                // `perform e(<T: A>, x)`: the named type arguments are carried
                // first as a record, not a value the operation takes.
                let (implicits, args) = split_implicits(args);
                let types: Vec<Ty> = args.iter().map(|a| self.infer(a, env)).collect();
                let Some(sig) = self.effects.get(effect).cloned() else {
                    self.error(
                        msg!("nibcheck-no-effect-declared", effect = effect.to_string()),
                        span,
                    );
                    return self.fresh();
                };
                let instance = self.instantiate_operation(&sig);
                // A type argument written at the `perform` is the instance's,
                // wherever the `perform` stands (a callback's row need not
                // tell the instance).
                if let Some(fields) = implicits {
                    let scope = self.type_params.clone();
                    for (field, written) in fields {
                        let Some(i) = sig.generics.iter().position(|g| g.name.as_str() == field)
                        else {
                            self.error(
                                msg!(
                                    "nibcheck-effect-no-type-argument-named",
                                    effect = effect.to_string(),
                                    name = field.clone()
                                ),
                                written.span,
                            );
                            continue;
                        };
                        let want = self.written(written, &scope);
                        self.expect(
                            &want,
                            &instance.type_args[i],
                            written.span,
                            msg!("nibcheck-what-argument"),
                        );
                    }
                }
                // Each type argument meets the bound the operation declares.
                for (t, k) in instance.type_args.iter().zip(&sig.kinds) {
                    if *k != Kind::Linear {
                        self.bounds.push((t.clone(), *k, span, false));
                    }
                }
                if self.indexed.contains(effect) {
                    self.effect_args
                        .push((site(term), instance.type_args.clone()));
                }
                let ps = instance.params.clone();
                let r = instance.answer.clone();
                self.operation_performs.push((term.id(), instance));
                if ps.len() != types.len() {
                    self.error(
                        msg!(
                            "nibcheck-effect-value-count",
                            effect = effect.to_string(),
                            expected = ps.len().to_string(),
                            given = types.len().to_string()
                        ),
                        span,
                    );
                } else {
                    for ((a, p), at) in types.iter().zip(&ps).zip(args) {
                        self.expect(a, p, at.span, msg!("nibcheck-what-argument"));
                        self.effect_values.push((a.clone(), at.span));
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
                self.expect(&s, &Ty::Int(Width::U64), steps.span, what);
                let t = self.infer(body, env);
                if let Some(x) = self.exceeded.last().cloned()
                    && self.unify(&x, &t).is_err()
                {
                    self.error(msg!("nibcheck-budget-arms-differ"), span);
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
                self.error(
                    msg!("nibcheck-not-supported-yet", what = format!("{other:?}")),
                    span,
                );
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
            ..
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
        let r = self.fresh();
        if let Some(Ty::Fn(hs, hr, _)) = hint.map(|h| self.resolve(&h).unborrowed().clone())
            && hs.len() == ps.len()
        {
            for (p, h) in ps.iter().zip(&hs) {
                let _ = self.attempt(|c| c.unify(p, h));
            }
            // The expected result asks for a copy of a borrowed result
            // (`&A → A`), so it is known before the body.
            let _ = self.attempt(|c| c.unify(&r, &hr));
        }
        let kind = self.capture_kind(&crate::lin::free_vars(lam), env, Kind::Copy, lam.span);
        let mut inner = env.to_vec();
        for (name, t) in params.iter().zip(&ps) {
            self.bind_local(&mut inner, name, t.clone(), false, site(body));
        }
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
            self.error(msg!("nibcheck-clone-takes-one-borrow"), span);
            return self.fresh();
        };
        let t = self.infer(arg, env);
        let t = match self.resolve(&t) {
            Ty::Borrow(t, _) | Ty::Orig(t) => *t,
            other => {
                self.error(msg!("nibcheck-clone-takes-borrow"), arg.span);
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
            self.error(msg!("nibcheck-not-a-struct", name = name.to_string()), span);
            return self.fresh();
        }
        if let Some((d, _)) = &ctor {
            self.refuse_sealed_repr(d, span);
        } else {
            self.refuse_sealed_repr(name, span);
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
            } else {
                // As a call's argument is, a field is checked against its
                // field's type: a numeral where an `Int` is expected is one.
                self.result_hint = want.clone();
            }
            let v = self.infer(value, env);
            self.hint = None;
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
                self.error(
                    msg!("nibcheck-field-given-twice", field = field.to_string()),
                    *at,
                );
            }
            match declared.iter().find(|(n, _)| n.as_deref() == Some(field)) {
                Some((_, t)) => self.expect(
                    v,
                    t,
                    *at,
                    msg!("nibcheck-what-field", field = field.to_string()),
                ),
                None => self.error(
                    msg!(
                        "nibcheck-no-field",
                        name = name.to_string(),
                        field = field.to_string()
                    ),
                    *at,
                ),
            }
        }
        for (n, _) in declared {
            if let Some(n) = n
                && !seen.contains(n)
            {
                self.error(
                    msg!(
                        "nibcheck-field-missing",
                        field = n.to_string(),
                        name = name.to_string()
                    ),
                    span,
                );
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
                // Operands are duplicable: a borrow of one is the value,
                // and a `&rc T` is read through the borrow of its contents.
                match self.resolve(&t) {
                    Ty::Borrow(t, _) | Ty::Orig(t) => *t,
                    Ty::Rc(t) => {
                        self.rc_reads.push(a.span);
                        *t
                    }
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
                    let mut message = msg!(
                        "nibcheck-operands-differ",
                        op = op.to_string(),
                        left = a.to_string(),
                        right = b.to_string()
                    );
                    // A label binds tighter than a binary operator, so
                    // `@tag a + b` labels only `a`.
                    if let Some(tag) = arguments.iter().find_map(|t| match &*t.kind {
                        TermKind::Tagged { tag, .. } => Some(tag),
                        _ => None,
                    }) {
                        message = msg!(
                            "nibcheck-operands-differ-labeled",
                            op = op.to_string(),
                            left = a.to_string(),
                            right = b.to_string(),
                            tag = tag.to_string()
                        );
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
                            tys: vec![a.clone()],
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
                            Ty::Var(v) if !self.ints.contains(&v) => {
                                self.error(msg!("nibcheck-division-operands-unknown"), span)
                            }
                            _ => self.error(msg!("nibcheck-integer-division"), span),
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
                self.error(
                    msg!("nibcheck-operator-other-operands", op = op.to_string()),
                    span,
                );
                self.fresh()
            }
        }
    }

    /// `t` must be a number; a type not known yet becomes an integer.
    fn number(&mut self, t: &Ty, span: Span, op: &str) {
        match self.resolve(t) {
            Ty::Int(_) | Ty::Decimal | Ty::Float | Ty::Float32 => {}
            Ty::Var(v) => {
                self.add_int(v);
            }
            other => self.error(
                msg!(
                    "nibcheck-operator-not-a-number",
                    op = op.to_string(),
                    ty = other.to_string()
                ),
                span,
            ),
        }
    }

    /// Binds a pattern's names; literals must have the scrutinee's type. A
    /// name that is a constructor without fields is that constructor. Over a
    /// borrow, what a pattern binds is borrowed too.
    fn pattern(&mut self, p: &Pattern, t: &Ty, env: &mut Vec<Local>, span: Span, at: TermId) {
        let resolved = self.resolve(t);
        let borrowed = match &resolved {
            Ty::Borrow(_, m) => Some(*m),
            _ => None,
        };
        // A typed arm is read by `match_arms`; anywhere else it is not a pattern.
        if let Pattern::Typed { name, .. } = p {
            self.error(
                msg!("nibcheck-typed-arm-nested", name = name.to_string()),
                span,
            );
            return;
        }
        // On a union, a constructor or a literal does not apply: the member is narrowed first.
        if matches!(resolved.unborrowed(), Ty::Union(_))
            && matches!(
                p,
                Pattern::Int(_)
                    | Pattern::Bool(_)
                    | Pattern::Text(_)
                    | Pattern::Ctor { .. }
                    | Pattern::Record { .. }
            )
        {
            let shown = self.shown(resolved.unborrowed());
            self.error(
                msg!("nibcheck-pattern-on-union", ty = shown.to_string()),
                span,
            );
            return;
        }
        let lit = match p {
            Pattern::Ctor { .. }
                if p.product_members().is_some()
                    && (!matches!(resolved.unborrowed(), Ty::Named(..))
                        || is_pair_ty(resolved.unborrowed())) =>
            {
                self.pair_pattern(p, t, borrowed, env, span, at);
                return;
            }
            // `#(p, q)` on a `Pair` kept as a type of its own: its record.
            Pattern::Ctor { .. } if let Some(record) = pair_record(p) => {
                self.pattern(&record, t, env, span, at);
                return;
            }
            Pattern::Wild => return,
            Pattern::Bind { name: name, .. } if self.datas.nullary(name, Some(&resolved)) => {
                self.ctor_pattern(name, &[], t, borrowed, env, span, at);
                return;
            }
            Pattern::Bind { name: name, .. } => {
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
                    None => self.error(
                        msg!(
                            "nibcheck-label-not-on",
                            tag = tag.to_string(),
                            ty = resolved.to_string()
                        ),
                        span,
                    ),
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
                    self.error(
                        msg!("nibcheck-unit-pattern-mismatch", ty = resolved.to_string()),
                        span,
                    );
                }
                return;
            }
            // `Zero` and `Succ(p)` on a `Nat`: the executable code holds it as a `nat`,
            // and `Succ(p)` takes a value of at least 1 with `p` on one less.
            Pattern::Ctor { name, args }
                if let Some(inner) = nat_ctor(name, args)
                    && self.takes_nat(name, resolved.unborrowed()) =>
            {
                if let Some(inner) = inner {
                    let nat = self.resolve(resolved.unborrowed());
                    let under = match borrowed {
                        Some(m) => Ty::Borrow(Box::new(nat), m),
                        None => nat,
                    };
                    self.pattern(inner, &under, env, span, at);
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
            Pattern::Record { name, fields } => {
                match self.datas.positional(name, fields, Some(&resolved)) {
                    Ok(args) => self.ctor_pattern(name, &args, t, borrowed, env, span, at),
                    Err(e) => self.error(e, span),
                }
                return;
            }
            Pattern::Other(what) => {
                self.error(
                    msg!("nibcheck-pattern-not-supported", what = what.to_string()),
                    span,
                );
                return;
            }
            Pattern::Typed { .. } => return,
        };
        let target = resolved.unborrowed().clone();
        if self.unify(&lit, &target).is_err() {
            let target = self.resolve(&target);
            let lit = self.resolve(&lit);
            self.error(
                msg!(
                    "nibcheck-pattern-cannot-match",
                    pattern = lit.to_string(),
                    target = target.to_string()
                ),
                span,
            );
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
        let members: Vec<Ty> = match &target {
            t if is_pair_ty(t) => {
                let mut ms = self.product_members(t);
                // `#(p, q)` on `A × B × C` takes `A` and `B × C`, as `Pair { fst, snd }` does.
                if pats.len() >= 2 && pats.len() < ms.len() {
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
                self.error(
                    msg!(
                        "nibcheck-product-pattern-cannot-match",
                        ty = other.to_string()
                    ),
                    span,
                );
                return;
            }
        };
        if members.len() != pats.len() {
            let shown = self.shown(&target);
            self.error(
                msg!(
                    "nibcheck-product-pattern-members",
                    count = pats.len().to_string(),
                    ty = shown.to_string()
                ),
                span,
            );
            return;
        }
        // Members match by position, labelled or not: only a subtyping to a written type
        // reorders by label.
        for (q, m) in pats.iter().zip(&members) {
            let m = match borrowed {
                Some(b) => Ty::Borrow(Box::new(m.clone()), b),
                None => m.clone(),
            };
            self.pattern(q, &m, env, span, at);
        }
    }

    /// Whether the constructor pattern `name` of the library's `Nat` is on a value the
    /// executable code holds as a `nat`: one of that type, or one whose type is still open
    /// and that no data of the program names a constructor `name` of.
    /// Whether `t` is the library's `Nat`: a `nat`, or the type `Nat` that no data
    /// of the program declares the constructors of.
    pub(crate) fn is_nat(&self, t: &Ty) -> bool {
        match t {
            Ty::Int(Width::Nat) => true,
            Ty::Named(d, args) => {
                args.is_empty()
                    && tauto_surface::bindings::is_library(d, "Nat")
                    && !self.datas.decls.contains_key(d)
            }
            _ => false,
        }
    }

    fn takes_nat(&mut self, name: &Name, target: &Ty) -> bool {
        match target {
            t if self.is_nat(t) => true,
            Ty::Var(_) if !self.datas.has_ctor(name) => {
                self.unify(target, &Ty::Int(Width::Nat)).is_ok()
            }
            _ => false,
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
                    Some(hint) => msg!(
                        "nibcheck-not-a-constructor-hint",
                        name = name.to_string(),
                        hint = hint.to_string()
                    ),
                    None => msg!("nibcheck-not-a-constructor-plain", name = name.to_string()),
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
            // A value under a label (`@a T`) is not a `T`: the pattern is written with the
            // label (`@a C(…)`), or the value is annotated as the `T` it holds.
            if let Ty::Tagged(tags, under) = &target
                && let Ty::Named(inner, _) = self.resolve(under).unborrowed()
                && *inner == d
            {
                let labels: Vec<String> = tags.iter().map(|t| format!("@{t}")).collect();
                let shown = self.shown(&target);
                self.error(
                    msg!(
                        "nibcheck-pattern-cannot-match-labelled",
                        pattern = d.to_string(),
                        name = name.to_string(),
                        target = shown.to_string(),
                        label = labels.join(" ")
                    ),
                    span,
                );
                return;
            }
            let target = self.shown(&target);
            self.error(
                msg!(
                    "nibcheck-pattern-cannot-match",
                    pattern = d.to_string(),
                    target = target.to_string()
                ),
                span,
            );
            return;
        }
        let fields = self.datas.fields(&d, c, &targs);
        if fields.len() != args.len() {
            self.error(
                msg!(
                    "nibcheck-pattern-field-count",
                    name = name.to_string(),
                    fields = fields.len().to_string(),
                    pattern = args.len().to_string()
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
                msg!("nibcheck-match-depends-on-value", name = n.to_string()),
                t.span,
            );
            return None;
        }
        Some(self.written(t, &self.type_params.clone()))
    }

    /// A `match` whose patterns are of a type that the scrutinee's struct
    /// coerces to (`match &w { Some(x) => … }` with `w: W` coercing to
    /// `Option(A)`): the scrutinee is read as that type, as an argument
    /// where it is expected (`coerce_fit`).
    fn coerce_scrutinee(&mut self, s: &Ty, arms: &[MatchArm], span: Span) -> Option<Ty> {
        let owner = arms.iter().find_map(|arm| match &arm.pattern {
            Pattern::Ctor { name, .. } | Pattern::Record { name, .. } => {
                self.datas.ctors.get(name).map(|(ty, _)| ty.clone())
            }
            _ => None,
        })?;
        let resolved = self.resolve(s);
        let mut current = resolved.unborrowed().clone();
        if matches!(&current, Ty::Named(d, _) if *d == owner) {
            return None;
        }
        for _ in 0..32 {
            let (_, _, ty, _) = self.coerce_step(&current)?;
            current = ty;
            if matches!(&current, Ty::Named(d, _) if *d == owner) {
                let want = match &resolved {
                    Ty::Borrow(_, m) => Ty::Borrow(Box::new(current), *m),
                    _ => current,
                };
                return self.coerce_fit(&resolved, &want, span).then_some(want);
            }
        }
        None
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
        let mut s = self.infer(scrutinee, env);
        // A `&rc T` is matched as the borrow of its contents: what a
        // pattern binds of it is borrowed.
        if let Ty::Rc(x) = self.resolve(&s) {
            self.rc_reads.push(scrutinee.span);
            s = self.rc_read(&x);
        }
        if let Ty::Named(data, _) = self.resolve(&s).unborrowed() {
            self.refuse_sealed_repr(data, scrutinee.span);
        }
        if let Some(read) = self.coerce_scrutinee(&s, arms, scrutinee.span) {
            s = read;
        }
        let mut result: Option<Ty> = None;
        // Typed arms narrow a union: its members, and for each arm the members it takes.
        let members = arms
            .iter()
            .any(|a| matches!(a.pattern, Pattern::Typed { .. }))
            .then(|| self.narrowed_members(&s, span))
            .flatten();
        let mut taken: Vec<Option<Vec<usize>>> = Vec::new();
        for arm in arms {
            let mut inner = env.clone();
            match &arm.pattern {
                Pattern::Typed { name, ty, .. } => {
                    let picked = self.typed_arm(
                        name,
                        ty,
                        &s,
                        members.as_deref(),
                        &mut inner,
                        arm.body.span,
                        site(&arm.body),
                    );
                    taken.push(picked);
                }
                p => {
                    self.pattern(p, &s, &mut inner, arm.body.span, site(&arm.body));
                    taken.push(None);
                }
            }
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
        if arms
            .iter()
            .any(|a| matches!(a.pattern, Pattern::Typed { .. }))
        {
            if let Some(members) = &members {
                self.narrowed_coverage(members, arms, &taken, span);
            }
            return (result.unwrap_or(Ty::Never), bodies);
        }
        if !self.exhaustive(&s, arms) {
            self.error(msg!("nibcheck-match-not-exhaustive"), span);
        } else {
            self.rest_arm(&s, arms, span);
        }
        self.redundant(&s, arms);
        self.default_arm(&s, arms);
        (result.unwrap_or(Ty::Never), bodies)
    }

    /// The members of the union a `match` with typed arms is on, or `None` after an error:
    /// its type is a union, known in full.
    fn narrowed_members(&mut self, s: &Ty, span: Span) -> Option<Vec<Ty>> {
        let resolved = self.resolve(s);
        if self.has_vars(&resolved) {
            let shown = self.shown(&resolved);
            self.error(
                msg!("nibcheck-typed-arm-unsolved", ty = shown.to_string()),
                span,
            );
            return None;
        }
        match resolved.unborrowed() {
            Ty::Union(members) => Some(members.clone()),
            other => {
                let shown = self.shown(other);
                self.error(
                    msg!("nibcheck-typed-arm-not-union", ty = shown.to_string()),
                    span,
                );
                None
            }
        }
    }

    /// `y: T` on a union of `members`: binds `y` at `T` (a borrow of it over a borrow) and
    /// gives the members `T` takes. `T` is a member or a union of members, and every member
    /// left out has a head no member of `T` has, so the head of a value tells which it is.
    #[allow(clippy::too_many_arguments)]
    fn typed_arm(
        &mut self,
        name: &Name,
        written: &SurfaceTerm,
        s: &Ty,
        members: Option<&[Ty]>,
        env: &mut Vec<Local>,
        span: Span,
        at: TermId,
    ) -> Option<Vec<usize>> {
        let t = self.written(written, &self.type_params.clone());
        let t = self.resolve(&t);
        let borrowed = match self.resolve(s) {
            Ty::Borrow(_, m) => Some(m),
            _ => None,
        };
        let bound = match borrowed {
            Some(m) => Ty::Borrow(Box::new(t.clone()), m),
            None => t.clone(),
        };
        self.bind_local(env, name, bound, false, at);
        let members = members?;
        let picked: Vec<Ty> = match &t {
            Ty::Union(us) => us.clone(),
            other => vec![other.clone()],
        };
        let union_shown = self.shown(&Ty::Union(members.to_vec()));
        let mut indices = Vec::new();
        for p in &picked {
            match members.iter().position(|m| m == p) {
                Some(i) => indices.push(i),
                None => {
                    let shown = self.shown(&t);
                    self.error(
                        msg!(
                            "nibcheck-typed-arm-not-member",
                            arm = shown.to_string(),
                            ty = union_shown.to_string()
                        ),
                        span,
                    );
                    return None;
                }
            }
        }
        let mut ok = true;
        for m in members {
            if matches!(m.unborrowed(), Ty::Param(..))
                || matches!(m, Ty::Tagged(_, under) if matches!(**under, Ty::Param(..)))
            {
                self.error(
                    msg!("nibcheck-typed-arm-type-variable", member = m.to_string()),
                    span,
                );
                ok = false;
            } else if head_of(m).is_none() {
                self.error(
                    msg!("nibcheck-typed-arm-no-head", member = m.to_string()),
                    span,
                );
                ok = false;
            }
        }
        if !ok {
            return None;
        }
        for m in members.iter().filter(|m| !picked.contains(m)) {
            if let Some(p) = picked.iter().find(|p| head_of(p) == head_of(m)) {
                let shown = self.shown(&t);
                self.error(
                    msg!(
                        "nibcheck-typed-arm-same-head",
                        arm = shown.to_string(),
                        member = p.to_string(),
                        other = m.to_string()
                    ),
                    span,
                );
                return None;
            }
        }
        Some(indices)
    }

    /// Exhaustiveness of a `match` with typed arms, member by member: an arm without a guard
    /// takes the members of its type, or all of them when it is a name or `_`. Also the arms
    /// that take only members taken before, and the place of `_ =>`.
    fn narrowed_coverage(
        &mut self,
        members: &[Ty],
        arms: &[MatchArm],
        taken: &[Option<Vec<usize>>],
        span: Span,
    ) {
        let mut covered = vec![false; members.len()];
        let last = arms.len().saturating_sub(1);
        for (i, (arm, picked)) in arms.iter().zip(taken).enumerate() {
            let indices: Vec<usize> = match &arm.pattern {
                Pattern::Typed { .. } => match picked {
                    Some(p) => p.clone(),
                    // After an error: as if it took every member.
                    None => (0..members.len()).collect(),
                },
                Pattern::Wild | Pattern::Bind { .. } => (0..members.len()).collect(),
                _ => (0..members.len()).collect(),
            };
            let before = indices.iter().all(|k| covered[*k]);
            if matches!(arm.pattern, Pattern::Wild) && arm.guard.is_none() {
                if i != last {
                    self.error(msg!("nibcheck-default-arm-last"), arm.body.span);
                } else if before {
                    self.error(msg!("nibcheck-default-arm-unreachable"), arm.body.span);
                }
            } else if before {
                self.redundant_arms.push((arm.body.id(), arm.body.span));
            }
            if arm.guard.is_none() {
                for k in indices {
                    covered[k] = true;
                }
            }
        }
        let missing: Vec<String> = members
            .iter()
            .zip(&covered)
            .filter(|(_, c)| !**c)
            .map(|(m, _)| self.shown(m).to_string())
            .collect();
        if !missing.is_empty() {
            self.error(
                msg!(
                    "nibcheck-match-members-not-covered",
                    members = missing.join(", ")
                ),
                span,
            );
        }
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
                    && matches!(&a.pattern, Pattern::Bind { name: n, .. } if !self.datas.nullary(n, None))
            });
            if !named {
                self.error(msg!("nibcheck-match-literals-need-rest-arm"), span);
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
                self.error(msg!("nibcheck-default-arm-last"), arm.body.span);
                return;
            }
            let before: Vec<Vec<Pattern>> = arms[..i]
                .iter()
                .filter(|a| a.guard.is_none())
                .map(|a| vec![a.pattern.clone()])
                .collect();
            if !before.is_empty() && self.covers_within(&[t.clone()], &before, &[Pattern::Wild]) {
                self.error(msg!("nibcheck-default-arm-unreachable"), arm.body.span);
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
        if let Some(ms) = self.product_pattern_members(t) {
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
        if rows.iter().any(|r| pair_record(&r[0]).is_some()) || pair_record(&q[0]).is_some() {
            let rows: Vec<Vec<Pattern>> = rows.iter().map(|r| pair_head_as_record(r)).collect();
            return self.covers_within(tys, &rows, &pair_head_as_record(q));
        }
        // A column of `nat` that `Succ` is written on: `Zero` and `Succ(n)`, as the
        // kernel's `Nat` has them, with a literal `k` as `Succ` taken `k` times of `Zero`.
        if self.is_nat(t) && rows.iter().any(|r| written_succ(&r[0])) || written_succ(&q[0]) {
            let nat = t.clone();
            let zero_rows: Vec<Vec<Pattern>> = rows
                .iter()
                .filter_map(|r| match nat_head(&r[0]) {
                    NatHead::Zero | NatHead::Any => Some(r[1..].to_vec()),
                    _ => None,
                })
                .collect();
            let succ_rows: Vec<Vec<Pattern>> = rows
                .iter()
                .filter_map(|r| match nat_head(&r[0]) {
                    NatHead::Succ(p) => Some([vec![p], r[1..].to_vec()].concat()),
                    NatHead::Any => Some([vec![Pattern::Wild], r[1..].to_vec()].concat()),
                    _ => None,
                })
                .collect();
            let succ_tys = [vec![nat], rest.to_vec()].concat();
            return match nat_head(&q[0]) {
                NatHead::Zero => self.covers_within(rest, &zero_rows, &q[1..]),
                NatHead::Succ(p) => {
                    self.covers_within(&succ_tys, &succ_rows, &[vec![p], q[1..].to_vec()].concat())
                }
                NatHead::Any => {
                    self.covers_within(rest, &zero_rows, &q[1..])
                        && self.covers_within(
                            &succ_tys,
                            &succ_rows,
                            &[vec![Pattern::Wild], q[1..].to_vec()].concat(),
                        )
                }
                NatHead::None => false,
            };
        }
        let wild = |p: &Pattern| {
            matches!(p, Pattern::Wild)
                || matches!(p, Pattern::Bind { name: n, .. } if !self.datas.nullary(n, Some(t))
                    // The executable code holds a `Nat` as a `nat`, whose `Zero`
                    // is a value, not a name that takes any.
                    && !(self.is_nat(t)
                        && tauto_surface::bindings::is_library_selected(n, "Zero")))
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
                        Pattern::Bind { name: n, .. } if this(n) => Vec::new(),
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
            Pattern::Ctor { .. } | Pattern::Record { .. } | Pattern::Bind { .. } => {
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
                    Pattern::Bind { name: name, .. } => (name, None),
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
            Pattern::Bind { name: n, .. } if !self.datas.has_ctor(n) => {
                Some(vec![Pattern::Wild; ms.len()])
            }
            Pattern::Record { name, .. } if is_pair_ctor(name) => {
                let pats = self.regroup(ms.len(), pair_pattern_members(p));
                self.tuple_columns(ms, pats)
            }
            Pattern::Ctor { name, args } if is_pair_ctor(name) && args.len() == 2 => {
                self.tuple_columns(ms, args.clone())
            }
            _ => None,
        }
    }

    /// The columns the `#(…)` patterns put their patterns on in the product `t`: its first
    /// member and the product of the rest, as the `Pair`s a product pattern nests to. Members
    /// match by position, labelled or not.
    fn product_pattern_members(&self, t: &Ty) -> Option<Vec<Ty>> {
        if !is_pair_ty(t) {
            return None;
        }
        let mut ms = self.product_members(t);
        let rest = self.product(ms.split_off(1));
        ms.push(rest);
        Some(ms)
    }

    /// The patterns `pats` of a product put on `columns` columns: where there are more and
    /// the columns are two, the first and `#(…)` of the rest.
    fn regroup(&self, columns: usize, mut pats: Vec<Pattern>) -> Vec<Pattern> {
        if columns == 2 && pats.len() > 2 {
            let rest = Pattern::product(pats.split_off(1));
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
        Some(pats)
    }

    fn covers(&self, t: &Ty, pats: &[&Pattern]) -> bool {
        let rows: Vec<Vec<Pattern>> = pats.iter().map(|p| vec![(*p).clone()]).collect();
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
        if let Some(ms) = self.product_pattern_members(t) {
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
        if rows.iter().any(|r| pair_record(&r[0]).is_some()) {
            let rows = rows.iter().map(|r| pair_head_as_record(r)).collect();
            return self.covers_rows(tys, rows);
        }
        // A column of `nat` that `Succ` is written on: `Zero` and `Succ(n)`, as the
        // kernel's `Nat` has them, with a literal `k` as `Succ` taken `k` times of `Zero`.
        if self.is_nat(t) && rows.iter().any(|r| written_succ(&r[0])) {
            let nat = t.clone();
            let zero_rows: Vec<Vec<Pattern>> = rows
                .iter()
                .filter_map(|r| match nat_head(&r[0]) {
                    NatHead::Zero | NatHead::Any => Some(r[1..].to_vec()),
                    _ => None,
                })
                .collect();
            let succ_rows: Vec<Vec<Pattern>> = rows
                .iter()
                .filter_map(|r| match nat_head(&r[0]) {
                    NatHead::Succ(p) => Some([vec![p], r[1..].to_vec()].concat()),
                    NatHead::Any => Some([vec![Pattern::Wild], r[1..].to_vec()].concat()),
                    _ => None,
                })
                .collect();
            let succ_tys = [vec![nat], rest.to_vec()].concat();
            return self.covers_rows(rest, zero_rows) && self.covers_rows(&succ_tys, succ_rows);
        }
        let wild = |p: &Pattern| {
            matches!(p, Pattern::Wild)
                || matches!(p, Pattern::Bind { name: n, .. } if !self.datas.nullary(n, Some(t))
                    // The executable code holds a `Nat` as a `nat`, whose `Zero`
                    // is a value, not a name that takes any.
                    && !(self.is_nat(t)
                        && tauto_surface::bindings::is_library_selected(n, "Zero")))
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
                        Pattern::Bind { name: n, .. } if this(n) => Vec::new(),
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
        self.set_subst(result_var, Some(first));
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
                ..
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
                            .cloned()
                            .zip(sig.kinds.iter().copied())
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
                                        msg!(
                                            "nibcheck-arm-told-apart-by-type-arguments",
                                            effect = effect.to_string()
                                        ),
                                        body.span,
                                    );
                                }
                                // With the bound the operation declares, which
                                // the instance performed met; a function's
                                // default when none is written.
                                let unbounded: Vec<(Param, Kind)> = generics
                                    .iter()
                                    .map(|(g, k)| {
                                        (
                                            g.clone(),
                                            if *k == Kind::Linear { Kind::Affine } else { *k },
                                        )
                                    })
                                    .collect();
                                rigid = self.rigid(&unbounded);
                                // The request's payload was checked where it
                                // was performed: an arm may perform it again.
                                for t in rigid.values() {
                                    if let Ty::Param(p, _) = t {
                                        self.no_borrow.insert(p.id.clone());
                                    }
                                }
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
                        // The host answers a budget, as it does `wait`: no
                        // program's `handle` has an arm for it.
                        if tauto_surface::bindings::is_library(&effect, "budget")
                            || tauto_surface::bindings::is_library(&effect, "budget_memory")
                        {
                            self.error(
                                msg!("nibcheck-host-answers", effect = effect.to_string()),
                                body.span,
                            );
                        } else {
                            self.error(
                                msg!("nibcheck-no-effect-declared", effect = effect.to_string()),
                                body.span,
                            );
                        }
                        continue;
                    }
                }
            };
            if params.len() != patterns.len() {
                self.error(
                    msg!(
                        "nibcheck-arm-value-count",
                        effect = effect.to_string(),
                        expected = params.len().to_string(),
                        given = patterns.len().to_string()
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
                        msg!(
                            "nibcheck-direct-arm-must-resume",
                            effect = effect.to_string()
                        ),
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
                        msg!(
                            "nibcheck-arm-does-not-resume",
                            effect = effect.to_string(),
                            k = k.to_string()
                        ),
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
                    msg!("nibcheck-arm-must-be-generic", effect = effect.to_string()),
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
                        self.set_subst(result_var, Some(wide));
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
                    self.set_subst(result_var, Some(x));
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
                self.set_subst(result_var, Some(union(vec![current, a])));
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
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Orig(t) | Ty::Rc(t) => {
            named_in(t, out)
        }
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
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) | Ty::Orig(t) | Ty::Rc(t) => {
            param_in(t, generic)
        }
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

/// `t` with each shared borrow in it read as `Unit`: what a field of a
/// `struct &T` is, for its kind, once its borrows are copies of the borrow.
fn unborrow_shared(t: &Ty) -> Ty {
    match t {
        Ty::Borrow(_, false) => Ty::Unit,
        Ty::Named(n, args) => Ty::Named(n.clone(), args.iter().map(unborrow_shared).collect()),
        Ty::Union(ts) => Ty::Union(ts.iter().map(unborrow_shared).collect()),
        Ty::Tagged(tags, t) => Ty::Tagged(tags.clone(), Box::new(unborrow_shared(t))),
        other => other.clone(),
    }
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
        Ty::Orig(t) => Ty::Orig(Box::new(substitute(t, map))),
        Ty::Rc(t) => Ty::Rc(Box::new(substitute(t, map))),
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

/// What a typed arm tests of a value of a union (`docs/design/nib.md`「Matching on a union」):
/// its width, `Bool`, `Unit`, `Text`, `Decimal`, `Float`, `Float32`, the data type that
/// declares it whatever its type arguments (a product's is `Pair`), or that it is a function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Head {
    Int(Width),
    Bool,
    Unit,
    Text,
    Decimal,
    Float,
    Float32,
    Data(Name),
    Fn,
}

/// The head of the values of `t`; a label does not change a value, so `@a T` has `T`'s.
/// A type variable and what no union holds have none.
pub(crate) fn head_of(t: &Ty) -> Option<Head> {
    match t {
        Ty::Tagged(_, t) => head_of(t),
        Ty::Int(w) => Some(Head::Int(*w)),
        Ty::Bool => Some(Head::Bool),
        Ty::Unit => Some(Head::Unit),
        Ty::Text => Some(Head::Text),
        Ty::Decimal => Some(Head::Decimal),
        Ty::Float => Some(Head::Float),
        Ty::Float32 => Some(Head::Float32),
        Ty::Named(n, _) => Some(Head::Data(n.clone())),
        Ty::Fn(..) => Some(Head::Fn),
        _ => None,
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
    if let Some(items) = p.product_members() {
        return items.into_iter().cloned().collect();
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

/// `#(p, q)` as the record of the prelude's `Pair`, `Pair { fst: p, snd: q }`.
fn pair_record(p: &Pattern) -> Option<Pattern> {
    let (fst, snd) = p.as_pair()?;
    Some(Pattern::Record {
        name: Name::from("Pair"),
        fields: vec![("fst".into(), fst.clone()), ("snd".into(), snd.clone())],
    })
}

/// `r` with its first pattern, when it is `#(…)`, put as the record of the prelude's `Pair`.
fn pair_head_as_record(r: &[Pattern]) -> Vec<Pattern> {
    let mut r = r.to_vec();
    if let Some(record) = r.first().and_then(pair_record) {
        r[0] = record;
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
    Rc(Box<StableTypeKey>),
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
        Ty::Orig(t) => StableTypeKey::Borrow(boxed(t), false),
        Ty::Rc(t) => StableTypeKey::Rc(boxed(t)),
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
    fn a_type_applied_to_a_borrow_holds_it() {
        tauto_parse::install();
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
            assert_eq!(datas.view_borrow(&foreign), Some(true));
        }
    }

    #[test]
    fn primitive_type_display_does_not_authorize_a_foreign_declaration() {
        tauto_parse::install();
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
        let program = expand_classes(tauto_parse::parse_program_as_written(source)?, 1 << 30);
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
            .map(|e| format!("{:?}", e.message))
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
show(&outer("text"))"#
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
show(&outer("text"))"#
            .to_string();
        let program = tauto_parse::parse_program_as_written(&source).unwrap();
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
            [Ev::Assume("Render".into(), vec![own.clone()])]
        );
        assert!(report.instantiations.iter().any(|(term, args)| {
            args.get(own.id()) == Some(&Ty::Param(outer.clone(), Kind::Shared))
                && report.evidence[term] == [Ev::Assume("Render".into(), vec![outer.clone()])]
        }));
    }

    #[test]
    fn nominal_owners_are_sealed_to_successful_exact_source() {
        let source = r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
let value: Reader := Read("original")"#
            .to_string();
        let program = tauto_parse::parse_program_as_written(&source).unwrap();
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
        let fresh = tauto_parse::parse_program_as_written(&source).unwrap();
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
        let failed = tauto_parse::parse_program_as_written(&source).unwrap();
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
        let mut program = tauto_parse::parse_program_as_written(&source).unwrap();
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
        let program = tauto_parse::parse_program_as_written(&source).unwrap();
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
    let seen := value
    let local: A := other
    local
  }
  show(&inner(1))
  inner(value)
}
show(&outer("text"))"#
            .to_string();
        let program = tauto_parse::parse_program_as_written(&source).unwrap();
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
    let seen := value
    let local: A := other
    local
  }
  show(&inner(1))
  inner(value)
}
show(&outer("text"))"#
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
show(&keep("text"))"#
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
show(&result)"#
            .to_string();
        let program = tauto_parse::parse_program_as_written(&source).unwrap();
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
        let source = tauto_case_inputs::source("types/scoped-generics.eure", name);
        let expected = tauto_case_inputs::expected("types/scoped-generics.eure", name, "types");
        let found = check_types(&source).unwrap().errors;
        assert_eq!(found.len(), 2, "{found:?}");
        assert_eq!(
            tauto_messages::english(&found[0].message),
            expected.strip_prefix("error: ").unwrap()
        );
        assert_eq!(format!("{:?}", found[1].message), VEC_NEW_UNDETERMINED);
    }

    const VEC_NEW_UNDETERMINED: &str =
        "nibcheck-type-not-determined(generics: \"`A`\", name: \"Vec::new\")";

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
        // The instances written for the types call the prelude's `concat`.
        let source = r#"fn concat(a: Text, b: Text): Text { a }
struct Phantom(A: Type) { callback: (A) -> i64 }
struct(linear) LinearBox(A: Type) { item: A }"#
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
        let source = r#"struct(linear) Token {}
fn outer(token: Token): Unit {
  let value := Vec::new()
  fn consume() { #(token, value) }
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
        assert_eq!(report.errors.len(), 1);
        assert_eq!(
            report.errors[0].message,
            msg!(
                "nibcheck-capture-kind-undetermined",
                name = "value".to_string()
            )
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
            let source = tauto_case_inputs::source("types/scoped-generics.eure", name);
            let program = expand_classes(
                tauto_parse::parse_program_as_written(&source).unwrap(),
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
                .map(|e| tauto_messages::english(&e.message))
                .collect::<Vec<_>>();
            let expected = tauto_case_inputs::expected("types/scoped-generics.eure", name, "lin");
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
    let seen := value
    let local: A := other
    local
  }
  show(&inner(1))
  inner(value)
}
show(&outer("text"))"#
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
show(&outer(7))
show(&outer("text"))"#
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
                    .any(|e| { e.message == msg!("nibcheck-int-literal-no-type") })
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
            r#"struct(affine) F {}
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
        let e = errors(r#"struct(copy) Q { t: Text }"#);
        assert!(
            e[0].contains(
                "nibcheck-declared-but-field(declared: \"copy\", field: \"t\", kind: \"shared\")"
            ),
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
        TermKind::Union(ts) => ts.iter().any(term_has_borrow),
        TermKind::Pi { params, result, .. } => {
            params.iter().any(|(_, p)| term_has_borrow(p)) || term_has_borrow(result)
        }
        _ => false,
    }
}

/// A struct used as a value. A record type `{ x: A }` is the struct
/// `@record.x`, which is never written, so it gets its own message.
fn struct_value_message(name: &Name) -> tauto_message::Message {
    if name.starts_with("@record.") {
        msg!("nibcheck-record-type-not-a-value")
    } else {
        msg!("nibcheck-struct-as-value", name = name.to_string())
    }
}

/// A bound string with `noborrow` taken out (`shared+noborrow` is `shared`,
/// `noborrow` alone no kind), and whether it was there.
pub(crate) fn without_no_borrow(bound: &str) -> (Option<String>, bool) {
    let parts: Vec<&str> = bound.split('+').collect();
    if !parts.contains(&"noborrow") {
        return (Some(bound.to_string()), false);
    }
    let rest: Vec<&str> = parts.into_iter().filter(|p| *p != "noborrow").collect();
    ((!rest.is_empty()).then(|| rest.join("+")), true)
}

/// `T` for `@a T`: the label of a member picked out of a product is not part
/// of the picked value's type.
fn untagged(ty: Ty) -> Ty {
    match ty {
        Ty::Tagged(_, under) => untagged(*under),
        other => other,
    }
}

/// The named type arguments written first in a call or a `perform`
/// (`<T: A>`, a record of the internal name `IMPLICITS`), and the rest.
pub(crate) fn split_implicits(
    args: &[SurfaceTerm],
) -> (Option<&[(String, SurfaceTerm)]>, &[SurfaceTerm]) {
    match args.split_first() {
        Some((first, rest)) => match &*first.kind {
            TermKind::Record { name, fields, .. }
                if name.spelling() == Some(tauto_surface::IMPLICITS) =>
            {
                (Some(fields.as_slice()), rest)
            }
            _ => (None, args),
        },
        None => (None, args),
    }
}

/// `Zero` (none) or `Succ(p)` (`p`), the library's constructors of `Nat` as a pattern.
pub(crate) fn nat_ctor<'p>(name: &Name, args: &'p [Pattern]) -> Option<Option<&'p Pattern>> {
    match args {
        [] if tauto_surface::bindings::is_library_selected(name, "Zero") => Some(None),
        [inner] if tauto_surface::bindings::is_library_selected(name, "Succ") => Some(Some(inner)),
        _ => None,
    }
}

/// A pattern on a `nat` read as the kernel's `Nat`: `Zero`, `Succ(p)`, one that takes
/// every value, or one that takes none (a negative literal).
enum NatHead {
    Zero,
    Succ(Pattern),
    Any,
    None,
}

fn nat_head(p: &Pattern) -> NatHead {
    match p {
        Pattern::Wild => NatHead::Any,
        Pattern::Int(0) => NatHead::Zero,
        Pattern::Int(k) if *k > 0 => NatHead::Succ(Pattern::Int(k - 1)),
        Pattern::Int(_) => NatHead::None,
        Pattern::Bind { name, .. }
            if tauto_surface::bindings::is_library_selected(name, "Zero") =>
        {
            NatHead::Zero
        }
        Pattern::Bind { .. } => NatHead::Any,
        Pattern::Ctor { name, args } => match nat_ctor(name, args) {
            Some(None) => NatHead::Zero,
            Some(Some(inner)) => NatHead::Succ(inner.clone()),
            None => NatHead::None,
        },
        _ => NatHead::None,
    }
}

/// Whether `p` is `Succ(…)` written on a `nat`.
fn written_succ(p: &Pattern) -> bool {
    matches!(p, Pattern::Ctor { name, args } if matches!(nat_ctor(name, args), Some(Some(_))))
}

/// `T` of `m::T`: a type of a module is written in full where it is declared,
/// and its `struct &T` by the short name.
fn last_segment(name: &str) -> &str {
    name.rsplit_once("::").map_or(name, |(_, n)| n)
}
