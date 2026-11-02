//! A function's calls to itself in tail position whose frame may be
//! discarded (`CallNode::recur`). After such a call the caller only returns
//! its value, so a backend can give the arguments to the parameters and run
//! the body again: recursion that walks its input one step per call does not
//! grow the stack with the input. The marks are made here once, and every
//! backend reads the same ones.
//!
//! A call is marked when
//! - it is in tail position: the body, a block's tail, the value of a
//!   `return` among a block's statements, a `match` arm, an `if` branch. A
//!   `handle`, a `budget` and a closure end the tail position: the frame
//!   around their body is still needed;
//! - it calls the same instance at the function's own type arguments;
//! - each parameter that holds a borrow or a function is passed on
//!   unchanged, or, for a shared borrow, takes a borrow reached through the
//!   function's shared borrow parameters (a name a `match` on one of them
//!   binds, and so on): the value it points at lives outside the frame, so
//!   running the body again never keeps a borrow of a value the body made;
//! - no value the function's names hold is of an `extern` type: running the
//!   body again drops what the frame owns before the call instead of after
//!   it, and only an `extern` type's drop is observable;
//! - the function is not of the M tier: its continuations may be resumed more
//!   than once, and parameters that take new values would be one place shared
//!   by every resumption.

use std::collections::BTreeSet;

use crate::{
    Block, CallNode, Callee, Expr, ExprKind, FnInst, Local, Package, Param, Pat, Repr, Stmt, Tier,
    Ty, Use,
};

/// Marks the self calls in tail position of every function. Lowering does
/// this last; a package built by hand is marked by calling it.
pub fn mark(pkg: &mut Package) {
    let shapes: Vec<Option<Shape>> = pkg
        .fns
        .iter()
        .map(|f| {
            (f.tier != Tier::M && !holds_host_value(pkg, f)).then(|| Shape {
                id: f.id,
                outside: reached_through_params(f),
                generics: f.generics.iter().map(|(g, _)| g.clone()).collect(),
                params: f
                    .params
                    .iter()
                    .map(|p| (p.local.clone(), loops_owned(pkg, p)))
                    .collect(),
            })
        })
        .collect();
    for (f, shape) in pkg.fns.iter_mut().zip(shapes) {
        if let Some(shape) = shape {
            shape.tail(&mut f.body);
        }
    }
}

pub fn recurs(body: &Expr) -> bool {
    let mut found = false;
    body.walk(&mut |e| {
        if let ExprKind::Call(c) = &e.kind {
            found |= c.recur;
        }
    });
    found
}

struct Shape {
    id: usize,
    generics: Vec<String>,
    /// Each parameter, and whether it may take a new value: it is owned and
    /// holds no borrow and no function.
    params: Vec<(Local, bool)>,
    /// The shared borrows that point outside the frame
    /// (`reached_through_params`).
    outside: BTreeSet<u32>,
}

impl Shape {
    fn tail(&self, e: &mut Expr) {
        match &mut e.kind {
            ExprKind::Call(c) if self.loops_back(c) => {
                c.recur = true;
                self.keep_passed_on(c);
            }
            ExprKind::Block(b) => {
                for s in &mut b.stmts {
                    if let Stmt::Return { value: Some(v), .. } = s {
                        self.tail(v);
                    }
                }
                if let Some(t) = &mut b.tail {
                    self.tail(t);
                }
            }
            ExprKind::Match(m) => {
                for arm in &mut m.arms {
                    self.tail(&mut arm.body);
                }
            }
            ExprKind::If {
                then, otherwise, ..
            } => {
                self.tail(then);
                if let Some(o) = otherwise {
                    self.tail(o);
                }
            }
            _ => {}
        }
    }

    /// A parameter passed on unchanged keeps its value for the next run of
    /// the body, so another argument that reads it as its last use clones it
    /// instead of moving it out.
    fn keep_passed_on(&self, c: &mut CallNode) {
        let kept: BTreeSet<u32> = self
            .params
            .iter()
            .zip(&c.args)
            .filter(|((p, _), a)| passed_on(p, a))
            .map(|((p, _), _)| p.id)
            .collect();
        if kept.is_empty() {
            return;
        }
        for ((p, _), a) in self.params.iter().zip(&mut c.args) {
            if !passed_on(p, a) {
                clone_reads(a, &kept);
            }
        }
    }

    fn loops_back(&self, c: &CallNode) -> bool {
        if !matches!(c.callee, Callee::Inst(i) if i == self.id) || c.args.len() != self.params.len()
        {
            return false;
        }
        let same_targs = if self.generics.is_empty() {
            c.targs.is_empty()
        } else {
            c.targs.len() == self.generics.len()
                && c.targs
                    .iter()
                    .zip(&self.generics)
                    .all(|(t, g)| matches!(t, Ty::Param(p) if p == g))
        };
        same_targs
            && self
                .params
                .iter()
                .zip(&c.args)
                .all(|((p, owned), a)| *owned || passed_on(p, a) || self.reborrows_outside(p, a))
    }

    /// A shared borrow parameter that takes a borrow pointing outside the
    /// frame, which outlives every run of the body.
    fn reborrows_outside(&self, p: &Local, a: &Expr) -> bool {
        p.repr == Repr::Ref
            && match &a.kind {
                ExprKind::Read { local, .. } => {
                    local.repr == Repr::Ref && self.outside.contains(&local.id)
                }
                ExprKind::Ref(place) => {
                    place.local.repr == Repr::Ref
                        && place.path.is_empty()
                        && self.outside.contains(&place.local.id)
                }
                _ => false,
            }
    }
}

fn clone_reads(e: &mut Expr, kept: &BTreeSet<u32>) {
    match &mut e.kind {
        ExprKind::Read { local, how } => {
            if *how == Use::Move && kept.contains(&local.id) {
                *how = Use::Clone;
            }
        }
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            clone_reads(a, kept);
            clone_reads(b, kept);
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            clone_reads(cond, kept);
            clone_reads(then, kept);
            if let Some(o) = otherwise {
                clone_reads(o, kept);
            }
        }
        ExprKind::Match(m) => {
            clone_reads(&mut m.scrut, kept);
            for arm in &mut m.arms {
                if let Some(g) = &mut arm.guard {
                    clone_reads(g, kept);
                }
                clone_reads(&mut arm.body, kept);
            }
        }
        ExprKind::Block(b) => clone_block(b, kept),
        ExprKind::Budget(b) => {
            clone_reads(&mut b.steps, kept);
            clone_reads(&mut b.body, kept);
        }
        ExprKind::Closure(c) => clone_reads(&mut c.body, kept),
        ExprKind::Handle(h) => {
            clone_reads(&mut h.body, kept);
            if let Some(r) = &mut h.ret {
                clone_reads(&mut r.body, kept);
            }
            for a in h.direct.iter_mut().chain(&mut h.aborts).chain(&mut h.susp) {
                if let Some(g) = &mut a.guard {
                    clone_reads(g, kept);
                }
                clone_reads(&mut a.body, kept);
            }
        }
        _ => {
            for o in e.operands_mut() {
                clone_reads(o, kept);
            }
        }
    }
}

fn clone_block(b: &mut Block, kept: &BTreeSet<u32>) {
    for s in &mut b.stmts {
        match s {
            Stmt::Let { init, .. } | Stmt::Var { init, .. } => clone_reads(init, kept),
            Stmt::Assign { value, .. } => clone_reads(value, kept),
            Stmt::Expr(e) => clone_reads(e, kept),
            Stmt::While { cond, body, .. } => {
                clone_reads(cond, kept);
                clone_block(body, kept);
            }
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    clone_reads(v, kept);
                }
            }
        }
    }
    if let Some(t) = &mut b.tail {
        clone_reads(t, kept);
    }
}

/// The argument is the parameter itself, or a borrow parameter borrowed again:
/// a jump back leaves such a parameter as it is.
pub fn passed_on(p: &Local, a: &Expr) -> bool {
    match &a.kind {
        ExprKind::Read { local, .. } => local.id == p.id,
        ExprKind::Ref(place) | ExprKind::RefMut(place) => {
            place.local.id == p.id
                && place.path.is_empty()
                && matches!(p.repr, Repr::Ref | Repr::RefMut)
        }
        _ => false,
    }
}

/// The shared borrows of a function that point outside its frame: its
/// shared borrow parameters, and the names a borrowing `match` on one of
/// them binds, transitively. Such a name is never assigned, so it keeps
/// pointing where it was bound.
fn reached_through_params(f: &FnInst) -> BTreeSet<u32> {
    let mut out: BTreeSet<u32> = f
        .params
        .iter()
        .filter(|p| p.local.repr == Repr::Ref)
        .map(|p| p.local.id)
        .collect();
    loop {
        let before = out.len();
        f.body.walk(&mut |e| {
            let ExprKind::Match(m) = &e.kind else {
                return;
            };
            let from = match &m.scrut.kind {
                ExprKind::Read { local, .. } => local,
                ExprKind::Ref(place) => &place.local,
                _ => return,
            };
            if m.by_ref && from.repr == Repr::Ref && out.contains(&from.id) {
                for arm in &m.arms {
                    bound_borrows(&arm.pat, &mut out);
                }
            }
        });
        if out.len() == before {
            return out;
        }
    }
}

fn bound_borrows(p: &Pat, out: &mut BTreeSet<u32>) {
    match p {
        Pat::Bind(l, _) if l.repr == Repr::Ref => {
            out.insert(l.id);
        }
        Pat::Ctor { fields, .. } => fields.iter().for_each(|f| bound_borrows(f, out)),
        _ => {}
    }
}

fn loops_owned(pkg: &Package, p: &Param) -> bool {
    p.local.repr == Repr::Plain && !has_ref(pkg, &p.ty) && !has_fn(&p.ty)
}

/// Whether a type holds a borrow: a reference, or a `view` type.
fn has_ref(pkg: &Package, t: &Ty) -> bool {
    match t {
        Ty::Ref(a) | Ty::RefMut(a) => !matches!(**a, Ty::Fn(_)),
        Ty::Vec(a) | Ty::Slice(a) | Ty::Option(a) | Ty::Info(a) | Ty::BudgetAnswer(a) => {
            has_ref(pkg, a)
        }
        Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => has_ref(pkg, a) || has_ref(pkg, b),
        Ty::Product(ms) => ms.iter().any(|(_, m)| has_ref(pkg, m)),
        Ty::Data(n, args) => {
            pkg.datas.iter().any(|d| d.name == *n && d.view) || args.iter().any(|a| has_ref(pkg, a))
        }
        _ => false,
    }
}

fn has_fn(t: &Ty) -> bool {
    match t {
        Ty::Fn(_) => true,
        Ty::Ref(a)
        | Ty::RefMut(a)
        | Ty::Vec(a)
        | Ty::Array(a)
        | Ty::Slice(a)
        | Ty::Option(a)
        | Ty::Info(a)
        | Ty::BudgetAnswer(a) => has_fn(a),
        Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => has_fn(a) || has_fn(b),
        Ty::Product(ms) => ms.iter().any(|(_, m)| has_fn(m)),
        Ty::Data(_, args) => args.iter().any(has_fn),
        _ => false,
    }
}

fn holds_host_value(pkg: &Package, f: &FnInst) -> bool {
    let mut seen = BTreeSet::new();
    let mut found = f.params.iter().any(|p| holds_host(pkg, &p.ty, &mut seen));
    f.body.walk(&mut |e| {
        found = found || holds_host(pkg, &e.ty, &mut seen);
    });
    found
}

/// Whether a type holds a value of an `extern` type, or a `MutexGuard`. `seen` holds the data
/// types already found to hold none, or being looked into.
pub(crate) fn holds_host(pkg: &Package, t: &Ty, seen: &mut BTreeSet<String>) -> bool {
    match t {
        Ty::Vec(a)
        | Ty::Array(a)
        | Ty::Slice(a)
        | Ty::Option(a)
        | Ty::Ref(a)
        | Ty::RefMut(a)
        | Ty::SharedVar(_, a)
        | Ty::Info(a)
        | Ty::BudgetAnswer(a) => holds_host(pkg, a, seen),
        Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => {
            holds_host(pkg, a, seen) || holds_host(pkg, b, seen)
        }
        Ty::Product(ms) => ms.iter().any(|(_, m)| holds_host(pkg, m, seen)),
        // A mutex guard gives its lock back when it is dropped.
        Ty::Std(n, args) => n == "MutexGuard" || args.iter().any(|a| holds_host(pkg, a, seen)),
        Ty::Union(id) => pkg
            .unions
            .iter()
            .filter(|u| u.id == *id)
            .any(|u| u.members.iter().any(|m| holds_host(pkg, m, seen))),
        Ty::Data(n, args) => {
            if args.iter().any(|a| holds_host(pkg, a, seen)) {
                return true;
            }
            let Some(d) = pkg.datas.iter().find(|d| d.name == *n) else {
                return false;
            };
            if d.host {
                return true;
            }
            if !seen.insert(n.clone()) {
                return false;
            }
            d.ctors
                .iter()
                .flat_map(|c| &c.fields)
                .any(|field| holds_host(pkg, &field.ty, seen))
        }
        _ => false,
    }
}
