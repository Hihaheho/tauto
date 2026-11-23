//! Static checks of what a package promises, run without running it.
//!
//! A pass that writes NIR keeps invariants every backend and every later
//! pass relies on. `check` reads a package and reports where one is broken:
//!
//! - **Scope.** Every local a node uses (read, borrowed, assigned, called,
//!   captured, resumed, dropped on an abort path) is bound around it, on the
//!   path it is reached by.
//! - **Identity.** A use names its local as the binder does: the same name
//!   and the same storage.
//! - **Types.** A read has the type of its binder (a borrowed local shows
//!   what it borrows), a `let` the type of its value, a call the arity of
//!   its callee and, for a callee with no type parameters, its parameter and
//!   result types.
//! - **Tiers.** A call states the tier of the function it calls.
//! - **Continuations.** A function of the tier `O` or `M` split into its
//!   continuations (`kont::split`) is closed: each continuation uses only
//!   its argument, its environment and what it binds.
//!
//! The checks read the block form of a function (`blocks::wf`).
//!
//! Types are compared where NIR writes them in full: a type with
//! `Ty::Never`, a type parameter or `Never` in it is taken as written.

use std::collections::HashMap;

use crate::*;

/// What is broken.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rule {
    /// A local is used where it is not bound.
    Scope,
    /// A use names its local with another name or storage than its binder.
    Identity,
    /// A type differs from the one its binder, callee or value gives.
    Type,
    /// A call passes another number of arguments than its callee takes.
    Arity,
    /// A call states another tier than its callee's.
    Tier,
    /// A continuation uses a local its environment does not hold, or is
    /// passed another environment than it takes.
    Kont,
    /// A block ends in no terminator, or an edge names no block.
    Flow,
    /// A function has a terminator its tier does not allow.
    Terminator,
    /// A `suspend` lists another environment than what its continuation
    /// reads.
    Closed,
    /// The region metadata disagrees with the blocks.
    Region,
}

#[derive(Debug, Clone)]
pub struct Finding {
    pub rule: Rule,
    pub span: Span,
    pub message: String,
}

impl std::fmt::Display for Finding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}: {} at {:?}", self.rule, self.message, self.span)
    }
}

/// Every finding in the package, with the function it is in.
pub fn check(pkg: &Package) -> Vec<(InstId, Finding)> {
    let mut out = Vec::new();
    for f in &pkg.fns {
        out.extend(check_fn(pkg, f).into_iter().map(|x| (f.id, x)));
    }
    out
}

/// The findings in one function, its continuations included when it is of
/// the tier `O` or `M` and in the form `kont::split` reads.
pub fn check_fn(pkg: &Package, f: &FnInst) -> Vec<Finding> {
    crate::blocks::wf::check_fn(pkg, f)
}

#[derive(Clone, Default)]
pub(crate) struct Scope(pub(crate) HashMap<u32, (Local, Ty)>);

impl Scope {
    pub(crate) fn bind(&mut self, l: &Local, t: &Ty) {
        self.0.insert(l.id, (l.clone(), t.clone()));
    }

    pub(crate) fn with(&self, bound: &[(Local, Ty)]) -> Scope {
        let mut s = self.clone();
        for (l, t) in bound {
            s.bind(l, t);
        }
        s
    }
}

/// Whether a type is written in full, so that it can be compared.
pub(crate) fn written(t: &Ty) -> bool {
    let mut ps = std::collections::BTreeSet::new();
    t.params(&mut ps);
    ps.is_empty() && !t.has_arm_generic() && !has_never(t)
}

/// A value of `have` stands where `want` is expected: the same type, up to
/// function values of a kind copied more freely (`copy ⊑ shared ⊑ affine ⊑
/// linear`), anywhere in it. Behind a borrow the kind is not read (a
/// borrowed function is only called), and a `&mut` lends a `&`.
pub(crate) fn fits(want: &Ty, have: &Ty) -> bool {
    fits_in(want, have, false)
}

pub(crate) fn fits_in(want: &Ty, have: &Ty, lent: bool) -> bool {
    let all = |w: &[Ty], h: &[Ty], lent| {
        w.len() == h.len() && w.iter().zip(h).all(|(w, h)| fits_in(w, h, lent))
    };
    match (want, have) {
        (Ty::Fn(w), Ty::Fn(h)) => {
            (lent || h.kind <= w.kind)
                && w.tier == h.tier
                && all(&w.params, &h.params, false)
                && fits_in(&w.ret, &h.ret, false)
        }
        (Ty::Ref(w), Ty::Ref(h) | Ty::RefMut(h)) | (Ty::RefMut(w), Ty::RefMut(h)) => {
            fits_in(w, h, true)
        }
        (Ty::Vec(w), Ty::Vec(h))
        | (Ty::Array(w), Ty::Array(h))
        | (Ty::Slice(w), Ty::Slice(h))
        | (Ty::Option(w), Ty::Option(h)) => fits_in(w, h, lent),
        (Ty::Result(w1, w2), Ty::Result(h1, h2))
        | (Ty::Pair(w1, w2), Ty::Pair(h1, h2)) => {
            fits_in(w1, h1, lent) && fits_in(w2, h2, lent)
        }
        (Ty::Data(w, wa), Ty::Data(h, ha)) => w == h && all(wa, ha, lent),
        _ => want == have,
    }
}

fn has_never(t: &Ty) -> bool {
    match t {
        Ty::Never => true,
        Ty::Vec(a)
        | Ty::Array(a)
        | Ty::Slice(a)
        | Ty::Option(a)
        | Ty::Ref(a)
        | Ty::RefMut(a)
        | Ty::Info(a)
        | Ty::BudgetAnswer(a)
        | Ty::SharedVar(_, a) => has_never(a),
        Ty::Result(a, b) | Ty::Pair(a, b) => has_never(a) || has_never(b),
        Ty::Data(_, args) | Ty::Std(_, args) => args.iter().any(has_never),
        Ty::Fn(f) => f.params.iter().any(has_never) || has_never(&f.ret),
        _ => false,
    }
}
