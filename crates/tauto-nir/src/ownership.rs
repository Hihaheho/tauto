//! Where each owned value is dropped, written in the tree.
//!
//! Rust drops a value at the end of its scope and JavaScript collects it, so
//! neither needs this; a native backend does. `insert` adds a call of the
//! builtin `drop` (`builtins::DROP`) for each owned local that is not moved:
//!
//! - a `let`, a `var` or a parameter that no code after it moves is dropped
//!   at the end of its block (or before a `return`), the latest first, as
//!   Rust drops it;
//! - a local moved in some branches of an `if` or a `match` but not in the
//!   others is dropped at the end of each branch that does not move it, so
//!   that on every path it is consumed once; a branch that gives a var a
//!   whole new value after dropping or moving the old one leaves it
//!   holding a value, as a branch that does not touch it does;
//! - a local a pattern binds is dropped at the end of its arm unless the arm
//!   moves it; a copy a `match` takes of a local is named and dropped as a
//!   local moved in as the scrutinee is;
//! - an assignment drops the value it replaces, after the new value is
//!   made, through a `&mut` or a shared var too, unless that value was
//!   moved (in the arm of a `match` that took it, in a loop that moves it
//!   and then gives it a new value);
//! - a product some members were moved out of is not dropped whole: the
//!   members left are dropped one by one;
//! - an owned temporary that `&(e)` lends, or a closure written where a
//!   borrowed function is expected, is named before the expression that
//!   lends it and dropped after it.
//! - a call or a `perform` that may abort carries the drops of what is
//!   still alive at it and made since the innermost `handle` around it
//!   (`CallNode::unwind`), run if it aborts: an abort leaves the frames it
//!   passes through having dropped what they own.
//! - a `linear` value an arm takes apart with its constructor's pattern
//!   is consumed there: what the arm releases of it is written as the
//!   builtin `release_shell` (`builtins::RELEASE_SHELL`), not `drop`, as a
//!   linear value never ends in a `drop`.
//!
//! A copy (`Use::Clone`) is already the place of a `dup`. A value of a type
//! with nothing to release (`Int`, `Bool`, a borrow) is never dropped. The
//! parts of a scrutinee the `match` owns that no pattern binds (a `_`) are
//! given a fresh name, and so are dropped at the end of the arm as what it
//! binds is; a `_` under a member of a union, whose type is not known here,
//! is left.
//!
//! `check` says whether every owned local is moved or dropped exactly once on
//! every path through a function.

use std::collections::HashSet;

use crate::builtins::{DROP, RELEASE_SHELL};

thread_local! {
    /// The ids of the locals that keep a value while the drops after it run,
    /// counted down from the top so that they meet no local of the program.
    /// `insert` starts the count again, so the ids it gives a package do not
    /// depend on what was compiled before.
    static RESULTS: std::cell::Cell<u32> = const { std::cell::Cell::new(u32::MAX) };
}

/// The id of a new local of the pass.
fn fresh_id() -> u32 {
    RESULTS.with(|next| {
        let id = next.get();
        next.set(id - 1);
        id
    })
}
use crate::*;

/// What the pass knows at a point of a function.
struct Cx {
    /// The owned locals of each scope open here, the innermost last.
    scopes: Vec<Vec<(Local, Ty)>>,
    /// The locals an enclosing expression has moved before this point: the
    /// local a `match` took as its scrutinee, in an arm that binds its parts.
    gone: Vec<u32>,
    /// The package's data types, for the fields of a constructor pattern.
    datas: std::rc::Rc<Vec<DataDef>>,
}

/// Inserts the drops of every function of the package.
pub fn insert(pkg: &mut Package) {
    RESULTS.with(|next| next.set(u32::MAX));
    let datas = std::rc::Rc::new(pkg.datas.clone());
    for f in &mut pkg.fns {
        let owned: Vec<(Local, Ty)> = f
            .params
            .iter()
            .filter(|p| needs_drop(&p.ty))
            .map(|p| (p.local.clone(), p.ty.clone()))
            .collect();
        let mut cx = Cx {
            scopes: vec![owned.clone()],
            gone: Vec::new(),
            datas: datas.clone(),
        };
        expr_at(&mut f.body, &mut cx);
        let body = std::mem::replace(&mut f.body, unit(f.span));
        // What is left of a parameter some members were moved out of is
        // dropped at the end of the body, as for a local of a block.
        let rest = rests(&[&body], &owned, &datas);
        f.body = end_scope_with(body, &owned, rest);
        let mut live = Live {
            owned: owned
                .iter()
                .map(|(l, t)| (l.clone(), t.clone(), Vec::new()))
                .collect(),
            base: 0,
            datas: datas.clone(),
        };
        unwind(&mut f.body, &mut live);
    }
}

/// The owned locals alive at a point of a function, after the drops are
/// written: each with the paths of the members moved out of it.
#[derive(Clone)]
struct Live {
    owned: Vec<(Local, Ty, Vec<Vec<String>>)>,
    /// The first of `owned` made inside the innermost `handle` here: an
    /// abort that handle takes leaves the ones before it alive.
    base: usize,
    datas: std::rc::Rc<Vec<DataDef>>,
}

impl Live {
    fn remove(&mut self, id: u32) {
        if let Some(i) = self.owned.iter().position(|(l, ..)| l.id == id) {
            self.owned.remove(i);
            if i < self.base {
                self.base -= 1;
            }
        }
    }

    fn add(&mut self, local: &Local, ty: &Ty) {
        if needs_drop(ty) && self.owned.iter().all(|(l, ..)| l.id != local.id) {
            self.owned.push((local.clone(), ty.clone(), Vec::new()));
        }
    }

    /// The drops an abort here runs: what is alive since `base`, the
    /// latest first, and of a local members were moved out of, the members
    /// left.
    fn drops(&self, span: Span) -> Vec<Stmt> {
        let mut out = Vec::new();
        for (l, t, moved) in self.owned[self.base..].iter().rev() {
            if moved.is_empty() {
                out.push(drop_of(l, t, span));
            } else {
                let at = Expr {
                    kind: ExprKind::Read {
                        local: l.clone(),
                        how: Use::Place,
                    },
                    ty: t.clone(),
                    span,
                };
                rest_drops(&at, t, &[], moved, &self.datas, &mut out);
            }
        }
        out
    }

    /// Keeps of `self` what is declared outside `inner`.
    fn forget(&mut self, inner: &HashSet<u32>) {
        let ids: Vec<u32> = self
            .owned
            .iter()
            .filter(|(l, ..)| inner.contains(&l.id))
            .map(|(l, ..)| l.id)
            .collect();
        for id in ids {
            self.remove(id);
        }
    }
}

/// Writes the drops each call and `perform` that may abort runs if it does
/// (`CallNode::unwind`), walking `e` in the order it runs.
///
/// After `insert`, every owned local is consumed once on every path, so the
/// branches of an `if` or a `match` leave the same locals of the code
/// around them alive; the state after a branch that does not come back
/// (`Never`) is not used.
fn unwind(e: &mut Expr, live: &mut Live) {
    match &mut e.kind {
        ExprKind::Read {
            local,
            how: Use::Move,
        } => live.remove(local.id),
        ExprKind::Field { how: Use::Move, .. } => {
            if let Some(root) = field_root(e)
                && let Some(path) = field_path(e, root)
                && let Some(entry) = live.owned.iter_mut().find(|(l, ..)| l.id == root)
            {
                entry.2.push(path);
            }
        }
        ExprKind::Call(c) => {
            if let Callee::Value(f) = &mut c.callee {
                unwind(f, live);
            }
            for a in &mut c.args {
                unwind(a, live);
            }
            if c.tier >= Tier::A {
                c.unwind = live.drops(c.span);
            }
        }
        ExprKind::Perform(p) => {
            for a in &mut p.args {
                unwind(a, live);
            }
            p.unwind = live.drops(p.span);
        }
        ExprKind::Block(b) => {
            let mut inner = HashSet::new();
            for s in &mut b.stmts {
                match s {
                    Stmt::Let {
                        local, ty, init, ..
                    }
                    | Stmt::Var {
                        local, ty, init, ..
                    } => {
                        unwind(init, live);
                        inner.insert(local.id);
                        live.add(local, ty);
                    }
                    Stmt::Assign { target, value, .. } => {
                        unwind(value, live);
                        // A local moved and given a new value owns it again.
                        if target.path.is_empty() {
                            live.add(&target.local, &target.ty);
                        }
                    }
                    Stmt::Expr(x) => unwind(x, live),
                    Stmt::While { cond, body, .. } => {
                        let mut l = live.clone();
                        unwind(cond, &mut l);
                        let mut b = Expr {
                            kind: ExprKind::Block(std::mem::replace(
                                body,
                                Block {
                                    stmts: Vec::new(),
                                    tail: None,
                                },
                            )),
                            ty: Ty::Unit,
                            span: cond.span,
                        };
                        unwind(&mut b, &mut l);
                        let ExprKind::Block(nb) = b.kind else {
                            unreachable!()
                        };
                        *body = nb;
                    }
                    Stmt::Return { value, .. } => {
                        if let Some(v) = value {
                            unwind(v, live);
                        }
                    }
                }
            }
            if let Some(t) = &mut b.tail {
                unwind(t, live);
            }
            live.forget(&inner);
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            unwind(cond, live);
            let mut a = live.clone();
            unwind(then, &mut a);
            let mut b = live.clone();
            if let Some(o) = otherwise {
                unwind(o, &mut b);
                if then.ty == Ty::Never {
                    a = b;
                }
            }
            *live = a;
        }
        ExprKind::Match(m) => {
            let whole = scrutinee_local(m);
            unwind(&mut m.scrut, live);
            // The drops are written: the local is now read as the place the
            // arms take it from (`scrutinee_local`).
            if whole.is_some()
                && let ExprKind::Read { how, .. } = &mut m.scrut.kind
            {
                *how = Use::Place;
            }
            let mut after: Option<Live> = None;
            for a in &mut m.arms {
                let mut l = live.clone();
                let mut binds = Vec::new();
                bound(&a.pat, &mut binds);
                if binds.is_empty()
                    && let Some((w, t)) = &whole
                {
                    l.add(w, t);
                }
                for (b, t) in &binds {
                    l.add(b, t);
                }
                if let Some(g) = &mut a.guard {
                    unwind(g, &mut l);
                }
                unwind(&mut a.body, &mut l);
                let mut ids: HashSet<u32> = binds.iter().map(|(b, _)| b.id).collect();
                if let Some((w, _)) = &whole {
                    ids.insert(w.id);
                }
                l.forget(&ids);
                if after.is_none() && a.body.ty != Ty::Never {
                    after = Some(l);
                }
            }
            if let Some(l) = after {
                *live = l;
            }
        }
        ExprKind::Closure(c) => {
            let mut inner = Live {
                owned: c
                    .params
                    .iter()
                    .filter(|(_, t)| needs_drop(t))
                    .map(|(l, t)| (l.clone(), t.clone(), Vec::new()))
                    .collect(),
                base: 0,
                datas: live.datas.clone(),
            };
            unwind(&mut c.body, &mut inner);
            // What the closure moves in is its own.
            let taken: Vec<u32> = live
                .owned
                .iter()
                .filter(|(l, ..)| moves(&c.body, l.id))
                .map(|(l, ..)| l.id)
                .collect();
            for id in taken {
                live.remove(id);
            }
        }
        ExprKind::Handle(h) => {
            let outer = live.clone();
            let mut l = live.clone();
            l.base = l.owned.len();
            unwind(&mut h.body, &mut l);
            l.base = outer.base;
            if let Some(r) = &mut h.ret {
                let mut binds = Vec::new();
                bound(&r.pat, &mut binds);
                for (b, t) in &binds {
                    l.add(b, t);
                }
                unwind(&mut r.body, &mut l);
                l.forget(&binds.iter().map(|(b, _)| b.id).collect());
            }
            for a in h.direct.iter_mut().chain(&mut h.aborts).chain(&mut h.susp) {
                let mut al = outer.clone();
                let mut binds = Vec::new();
                for p in &a.pats {
                    bound(p, &mut binds);
                }
                for (b, t) in &binds {
                    al.add(b, t);
                }
                if let Some(g) = &mut a.guard {
                    unwind(g, &mut al);
                }
                unwind(&mut a.body, &mut al);
            }
            *live = l;
        }
        ExprKind::Budget(b) => {
            unwind(&mut b.steps, live);
            unwind(&mut b.body, live);
        }
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            unwind(a, live);
            let mut l = live.clone();
            unwind(b, &mut l);
        }
        _ => {
            for op in e.operands_mut() {
                unwind(op, live);
            }
        }
    }
}

/// Whether a value of this type has something to release.
/// Whether a value of the type may hold a borrow: a borrow written in it,
/// or a view data type.
fn may_borrow(t: &Ty, datas: &[DataDef]) -> bool {
    match t {
        Ty::Ref(_) | Ty::RefMut(_) | Ty::Slice(_) => true,
        Ty::Vec(a) | Ty::Array(a) | Ty::Option(a) | Ty::Info(a) | Ty::BudgetAnswer(a) => {
            may_borrow(a, datas)
        }
        Ty::Result(a, b) | Ty::Pair(a, b) => {
            may_borrow(a, datas) || may_borrow(b, datas)
        }
        Ty::Std(_, args) => args.iter().any(|a| may_borrow(a, datas)),
        Ty::Data(n, args) => {
            args.iter().any(|a| may_borrow(a, datas))
                || datas.iter().any(|d| &d.name == n && d.view)
        }
        _ => false,
    }
}

pub fn needs_drop(t: &Ty) -> bool {
    !matches!(
        t,
        Ty::Int(_)
            | Ty::Bool
            | Ty::Unit
            | Ty::Never
            | Ty::Float
            | Ty::Float32
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Slice(_)
    ) || matches!(t, Ty::Int(Width::Nat))
}

fn unit(span: Span) -> Expr {
    Expr {
        kind: ExprKind::Unit,
        ty: Ty::Unit,
        span,
    }
}

fn drop_of(local: &Local, ty: &Ty, span: Span) -> Stmt {
    Stmt::Expr(Expr {
        kind: ExprKind::Call(Box::new(CallNode {
            callee: Callee::Builtin(DROP.into()),
            args: vec![Expr {
                kind: ExprKind::Read {
                    local: local.clone(),
                    how: Use::Move,
                },
                ty: ty.clone(),
                span,
            }],
            tier: Tier::S,
            targs: Vec::new(),
            tick: Tick::None,
            recur: false,
            unwind: Vec::new(),
            span,
        })),
        ty: Ty::Unit,
        span,
    })
}

/// Makes each `drop` of the local `id` in `e` a `release_shell`.
fn release_shells(e: &mut Expr, id: u32) {
    let stmts = |b: &mut Block| {
        for s in &mut b.stmts {
            match s {
                Stmt::Let { init: x, .. } | Stmt::Var { init: x, .. } => release_shells(x, id),
                Stmt::Assign { value, .. } => release_shells(value, id),
                Stmt::Expr(x) => release_shells(x, id),
                Stmt::While { cond, body, .. } => {
                    release_shells(cond, id);
                    for s in &mut body.stmts {
                        let mut b = Block {
                            stmts: vec![s.clone()],
                            tail: None,
                        };
                        release_block(&mut b, id);
                        *s = b.stmts.pop().expect("a statement");
                    }
                    if let Some(t) = &mut body.tail {
                        release_shells(t, id);
                    }
                }
                Stmt::Return { value, .. } => {
                    if let Some(x) = value {
                        release_shells(x, id);
                    }
                }
            }
        }
        if let Some(t) = &mut b.tail {
            release_shells(t, id);
        }
    };
    match &mut e.kind {
        ExprKind::Call(c) => {
            if matches!(&c.callee, Callee::Builtin(n) if n == DROP)
                && matches!(&c.args[0].kind, ExprKind::Read { local, .. } if local.id == id)
            {
                c.callee = Callee::Builtin(RELEASE_SHELL.into());
            }
            for s in &mut c.unwind {
                let mut b = Block {
                    stmts: vec![s.clone()],
                    tail: None,
                };
                release_block(&mut b, id);
                *s = b.stmts.pop().expect("a statement");
            }
        }
        ExprKind::Block(b) => stmts(b),
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            release_shells(cond, id);
            release_shells(then, id);
            if let Some(o) = otherwise {
                release_shells(o, id);
            }
        }
        ExprKind::Match(m) => {
            release_shells(&mut m.scrut, id);
            for a in &mut m.arms {
                if let Some(g) = &mut a.guard {
                    release_shells(g, id);
                }
                release_shells(&mut a.body, id);
            }
        }
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            release_shells(a, id);
            release_shells(b, id);
        }
        // Only the control flow of the function that owns the local holds
        // its drops; the other nodes are left as they are, listed so a new
        // node has to be placed here.
        ExprKind::Declaration(_)
        | ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Text(_)
        | ExprKind::Read { .. }
        | ExprKind::FnValue { .. }
        | ExprKind::Arith { .. }
        | ExprKind::Cmp { .. }
        | ExprKind::Eq { .. }
        | ExprKind::Not(_)
        | ExprKind::Ctor { .. }
        | ExprKind::Field { .. }
        | ExprKind::Closure(_)
        | ExprKind::Perform(_)
        | ExprKind::Handle(_)
        | ExprKind::Inject { .. }
        | ExprKind::Remap { .. }
        | ExprKind::Ref(_)
        | ExprKind::RefMut(_)
        | ExprKind::TempRef(_)
        | ExprKind::Deref { .. }
        | ExprKind::Shown(_)
        | ExprKind::Budget(_)
        | ExprKind::Unreachable(_)
        | ExprKind::FnCast(_) => {}
    }
    if !matches!(
        e.kind,
        ExprKind::Block(_) | ExprKind::If { .. } | ExprKind::Match(_)
    ) {
        for x in e.operands_mut() {
            release_shells(x, id);
        }
    }
}

fn release_block(b: &mut Block, id: u32) {
    let mut e = Expr {
        kind: ExprKind::Block(std::mem::replace(
            b,
            Block {
                stmts: Vec::new(),
                tail: None,
            },
        )),
        ty: Ty::Unit,
        span: Span::new(0, 0),
    };
    release_shells(&mut e, id);
    if let ExprKind::Block(x) = e.kind {
        *b = x;
    }
}

/// The drop of the value the borrow `local` points at: it is moved out of
/// the borrow into a new local, which is dropped.
fn drop_through(local: &Local, ty: &Ty, span: Span) -> [Stmt; 2] {
    let old = Local {
        id: fresh_id(),
        name: "replaced".into(),
        repr: Repr::Plain,
    };
    let init = Expr {
        kind: ExprKind::Deref {
            value: Box::new(Expr {
                kind: ExprKind::Read {
                    local: local.clone(),
                    how: Use::Place,
                },
                ty: Ty::RefMut(Box::new(ty.clone())),
                span,
            }),
            how: Use::Move,
        },
        ty: ty.clone(),
        span,
    };
    [
        Stmt::Let {
            stack: false,
            local: old.clone(),
            ty: ty.clone(),
            init,
            span,
        },
        drop_of(&old, ty, span),
    ]
}

/// Whether `e` moves the local `id` anywhere (in a closure too). The
/// scrutinee of a `match` by reference is a place, which nothing moves.
fn moves(e: &Expr, id: u32) -> bool {
    match &e.kind {
        ExprKind::Read {
            local,
            how: Use::Move,
        } => local.id == id,
        // Moving a field out moves that part of the local: the local is not
        // dropped whole after it. The members left are dropped one by one
        // (`rests`).
        ExprKind::Field {
            how: Use::Move,
            base,
            ..
        } if field_root(base) == Some(id) => true,
        ExprKind::Match(m) if scrutinee_local(m).is_some_and(|(l, _)| l.id == id) => true,
        ExprKind::Match(m) if m.by_ref => m
            .arms
            .iter()
            .any(|a| a.guard.as_ref().is_some_and(|g| moves(g, id)) || moves(&a.body, id)),
        // A closure holds a shared var of its own, and a copy of what it
        // clones when it is made: what it moves of either is not the hold
        // of the code around it.
        ExprKind::Closure(c) => !c.clones.iter().any(|l| l.id == id) && closure_moves(&c.body, id),
        _ => {
            let mut found = false;
            e.children(&mut |c| found = found || moves(c, id));
            found
        }
    }
}

/// Whether the body of a closure moves the captured local `id` (not a
/// shared var, and not through a closure inside that clones it).
fn closure_moves(e: &Expr, id: u32) -> bool {
    match &e.kind {
        ExprKind::Read {
            local,
            how: Use::Move,
        } => local.id == id && local.storage() != Storage::SharedVar,
        ExprKind::Closure(c) if c.clones.iter().any(|l| l.id == id) => false,
        _ => {
            let mut found = false;
            e.children(&mut |c| found = found || closure_moves(c, id));
            found
        }
    }
}

/// The paths of the members of the product `id` that `e` moves out, each
/// as the member indices from the local down.
fn moved_paths(e: &Expr, id: u32, out: &mut Vec<Vec<String>>) {
    e.walk(&mut |x| {
        if let ExprKind::Field { how: Use::Move, .. } = &x.kind
            && let Some(p) = field_path(x, id)
        {
            out.push(p);
        }
    });
}

/// The key of a member in a path: the index of a pair's, the name of a
/// struct field.
fn member_key(f: &FieldRef) -> Option<String> {
    f.index
        .map(|i| i.to_string())
        .or_else(|| Some(f.name.clone()))
}

fn field_path(e: &Expr, id: u32) -> Option<Vec<String>> {
    match &e.kind {
        ExprKind::Read { local, .. } if local.id == id => Some(Vec::new()),
        ExprKind::Field { base, field, .. } => {
            let mut p = field_path(base, id)?;
            p.push(member_key(field)?);
            Some(p)
        }
        _ => None,
    }
}

/// The drops of the members of a product that no path of `moved` takes,
/// where `at` reads the member at `path`. Nothing is dropped of a member
/// that is not a product and has a part moved out.
fn rest_drops(
    at: &Expr,
    ty: &Ty,
    path: &[String],
    moved: &[Vec<String>],
    datas: &[DataDef],
    out: &mut Vec<Stmt>,
) {
    if moved.iter().any(|p| p == path) {
        return;
    }
    let under = moved.iter().any(|p| p.starts_with(path));
    if !under {
        if needs_drop(ty) {
            let mut e = at.clone();
            if let ExprKind::Field { how, .. } = &mut e.kind {
                *how = Use::Move;
            }
            out.push(Stmt::Expr(Expr {
                kind: ExprKind::Call(Box::new(CallNode {
                    callee: Callee::Builtin(DROP.into()),
                    args: vec![e],
                    tier: Tier::S,
                    targs: Vec::new(),
                    tick: Tick::None,
                    recur: false,
                    unwind: Vec::new(),
                    span: at.span,
                })),
                ty: Ty::Unit,
                span: at.span,
            }));
        }
        return;
    }
    // The members of a product: a pair's, or a struct's fields.
    let members: Vec<(FieldRef, Ty)> = match ty {
        Ty::Pair(a, b) => [(&**a, "fst"), (&**b, "snd")]
            .into_iter()
            .enumerate()
            .map(|(i, (t, name))| {
                let f = FieldRef {
                    name: name.into(),
                    index: Some(i),
                    indirect: Indirect::None,
                };
                (f, t.clone())
            })
            .collect(),
        Ty::Data(name, args) => {
            let Some(d) = datas.iter().find(|d| &d.name == name) else {
                return;
            };
            if !d.is_struct || d.ctors.len() != 1 || d.generics.len() != args.len() {
                return;
            }
            let mut v = Vec::new();
            for f in &d.ctors[0].fields {
                let Some(n) = &f.name else {
                    return;
                };
                // A field behind a pointer is not split.
                if f.indirect != Indirect::None {
                    return;
                }
                let r = FieldRef {
                    name: n.clone(),
                    index: None,
                    indirect: Indirect::None,
                };
                v.push((r, subst(&f.ty, &d.generics, args)));
            }
            v
        }
        _ => return,
    };
    for (f, t) in members {
        let mut p = path.to_vec();
        let Some(key) = member_key(&f) else {
            return;
        };
        p.push(key);
        let field = Expr {
            kind: ExprKind::Field {
                base: Box::new(at.clone()),
                field: f,
                how: Use::Place,
                indirect: Indirect::None,
            },
            ty: t.clone(),
            span: at.span,
        };
        rest_drops(&field, &t, &p, moved, datas, out);
    }
}

/// The drops of what `e` leaves of the owned locals it moves members out
/// of and does not move whole.
fn rests(e: &[&Expr], owned: &[(Local, Ty)], datas: &[DataDef]) -> Vec<Stmt> {
    let mut out = Vec::new();
    for (l, t) in owned.iter().rev() {
        if e.iter().any(|x| moves_whole(x, l.id)) {
            continue;
        }
        let mut moved = Vec::new();
        for x in e {
            moved_paths(x, l.id, &mut moved);
        }
        if moved.is_empty() {
            continue;
        }
        let at = Expr {
            kind: ExprKind::Read {
                local: l.clone(),
                how: Use::Place,
            },
            ty: t.clone(),
            span: e.last().map_or(Span::new(0, 0), |x| x.span),
        };
        rest_drops(&at, t, &[], &moved, datas, &mut out);
    }
    out
}

/// Whether `e` moves the local `id` whole (not only members of it).
fn moves_whole(e: &Expr, id: u32) -> bool {
    match &e.kind {
        ExprKind::Read {
            local,
            how: Use::Move,
        } => local.id == id,
        ExprKind::Match(m) if scrutinee_local(m).is_some_and(|(l, _)| l.id == id) => true,
        ExprKind::Match(m) if m.by_ref => m.arms.iter().any(|a| {
            a.guard.as_ref().is_some_and(|g| moves_whole(g, id)) || moves_whole(&a.body, id)
        }),
        _ => {
            let mut found = false;
            e.children(&mut |c| found = found || moves_whole(c, id));
            found
        }
    }
}

/// The local a chain of field reads starts from.
fn field_root(e: &Expr) -> Option<u32> {
    match &e.kind {
        ExprKind::Read { local, .. } => Some(local.id),
        ExprKind::Field { base, .. } => field_root(base),
        _ => None,
    }
}

fn stmt_moves(s: &Stmt, id: u32) -> bool {
    let mut e = Vec::new();
    match s {
        Stmt::Let { init, .. } | Stmt::Var { init, .. } => e.push(init),
        Stmt::Assign { value, .. } => e.push(value),
        Stmt::Expr(x) => e.push(x),
        Stmt::While { cond, body, .. } => {
            e.push(cond);
            return moves(cond, id)
                || body.stmts.iter().any(|s| stmt_moves(s, id))
                || body.tail.as_deref().is_some_and(|t| moves(t, id));
        }
        Stmt::Return { value, .. } => e.extend(value),
    }
    e.into_iter().any(|x| moves(x, id))
}

/// `e`, then the drops of `owned` that `e` does not move, the latest first,
/// with `e`'s value kept.
fn end_scope(e: Expr, owned: &[(Local, Ty)]) -> Expr {
    end_scope_with(e, owned, Vec::new())
}

/// `end_scope`, with the drops `rest` after the others.
fn end_scope_with(e: Expr, owned: &[(Local, Ty)], rest: Vec<Stmt>) -> Expr {
    let mut drops: Vec<Stmt> = owned
        .iter()
        .rev()
        .filter(|(l, _)| !consumes(&e, l.id))
        .map(|(l, t)| drop_of(l, t, e.span))
        .collect();
    drops.extend(rest);
    if drops.is_empty() {
        return e;
    }
    // `e` does not come back (an abort, a loop that never ends): what it
    // does not use is dropped before it, as leaving the scope would.
    if e.ty == Ty::Never {
        let drops: Vec<Stmt> = owned
            .iter()
            .rev()
            .filter(|(l, _)| !moves(&e, l.id) && !mentions(&e, l.id))
            .map(|(l, t)| drop_of(l, t, e.span))
            .collect();
        if drops.is_empty() {
            return e;
        }
        let (ty, span) = (e.ty.clone(), e.span);
        return Expr {
            kind: ExprKind::Block(Block {
                stmts: drops,
                tail: Some(Box::new(e)),
            }),
            ty,
            span,
        };
    }
    let (ty, span) = (e.ty.clone(), e.span);
    let result = Local {
        id: fresh_id(),
        name: "dropped_after".into(),
        repr: Repr::Plain,
    };
    let mut stmts = vec![Stmt::Let {
        stack: false,
        local: result.clone(),
        ty: ty.clone(),
        init: e,
        span,
    }];
    stmts.extend(drops);
    Expr {
        kind: ExprKind::Block(Block {
            stmts,
            tail: Some(Box::new(Expr {
                kind: ExprKind::Read {
                    local: result,
                    how: Use::Move,
                },
                ty: ty.clone(),
                span,
            })),
        }),
        ty,
        span,
    }
}

/// Whether `e` reads, borrows, calls or captures the local `id` anywhere.
fn mentions(e: &Expr, id: u32) -> bool {
    let mut found = false;
    e.walk(&mut |x| match &x.kind {
        ExprKind::Read { local, .. } if local.id == id => found = true,
        ExprKind::Ref(p) | ExprKind::RefMut(p) if p.local.id == id => found = true,
        ExprKind::Closure(c) if c.clones.iter().any(|l| l.id == id) => found = true,
        // A call of the local itself, and a handler that captures it, use it.
        ExprKind::Call(c)
            if matches!(&c.callee, Callee::Local(l) | Callee::Cont(l) if l.id == id) =>
        {
            found = true
        }
        ExprKind::Handle(h)
            if h.captures.iter().chain(&h.clones).any(|l| l.id == id) =>
        {
            found = true
        }
        ExprKind::Read { .. }
        | ExprKind::Ref(_)
        | ExprKind::RefMut(_)
        | ExprKind::Closure(_)
        | ExprKind::Declaration(_)
        | ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Text(_)
        | ExprKind::FnValue { .. }
        | ExprKind::Call(_)
        | ExprKind::Arith { .. }
        | ExprKind::Cmp { .. }
        | ExprKind::Eq { .. }
        | ExprKind::Not(_)
        | ExprKind::And(..)
        | ExprKind::Or(..)
        | ExprKind::Ctor { .. }
        | ExprKind::Field { .. }
        | ExprKind::Match(_)
        | ExprKind::If { .. }
        | ExprKind::Block(_)
        | ExprKind::Perform(_)
        | ExprKind::Handle(_)
        | ExprKind::Inject { .. }
        | ExprKind::Remap { .. }
        | ExprKind::TempRef(_)
        | ExprKind::Deref { .. }
        | ExprKind::Shown(_)
        | ExprKind::Budget(_)
        | ExprKind::Unreachable(_)
        | ExprKind::FnCast(_) => {}
    });
    found
}

/// The owned local a `match` takes by value as its scrutinee.
///
/// While the drops are written the scrutinee reads `move x`; once they are,
/// it reads the place `x` (`match x { … }`), as `x` is not moved by the
/// `match`: an arm whose pattern takes parts of it moves them out of it, and
/// an arm whose pattern takes nothing holds `x` whole and moves or drops it
/// by its name. So the text shows the one move of `x` on each path.
pub fn scrutinee_local(m: &MatchNode) -> Option<(Local, Ty)> {
    match &m.scrut.kind {
        ExprKind::Read {
            local,
            how: Use::Move | Use::Place,
        } if !m.by_ref && needs_drop(&m.scrut.ty) => Some((local.clone(), m.scrut.ty.clone())),
        _ => None,
    }
}

/// The locals a pattern binds that own a value.
pub fn bound(p: &Pat, out: &mut Vec<(Local, Ty)>) {
    match p {
        // A pattern of a `match` by reference binds borrows.
        Pat::Bind(l, t) if needs_drop(t) && !matches!(l.repr, Repr::Ref | Repr::RefMut) => {
            out.push((l.clone(), t.clone()))
        }
        Pat::Ctor { fields, .. } => fields.iter().for_each(|f| bound(f, out)),
        Pat::Variant { pat, .. } => bound(pat, out),
        Pat::Bind(..) | Pat::Wild | Pat::Int(_) | Pat::Nat(_) | Pat::Bool(_) | Pat::Text(_) => {}
    }
}

/// `p` with each `_` that stands for a part owning a value replaced by a
/// fresh name of that part's type. A part whose type is not known here (a
/// member of a union) is left as it is.
fn name_unbound(p: &mut Pat, ty: &Ty, datas: &[DataDef]) {
    match p {
        Pat::Wild if needs_drop(ty) => {
            let local = Local {
                id: fresh_id(),
                name: "unbound".into(),
                repr: Repr::Plain,
            };
            *p = Pat::Bind(local, ty.clone());
        }
        Pat::Ctor { ctor, fields } => {
            let Some(tys) = field_tys(ty, ctor, datas) else {
                return;
            };
            if tys.len() != fields.len() {
                return;
            }
            for (f, t) in fields.iter_mut().zip(&tys) {
                name_unbound(f, t, datas);
            }
        }
        // The member's type is the union's, which this does not read; the lowering binds it.
        Pat::Variant { .. }
        | Pat::Wild
        | Pat::Bind(..)
        | Pat::Int(_)
        | Pat::Nat(_)
        | Pat::Bool(_)
        | Pat::Text(_) => {}
    }
}

/// The types of the fields of the constructor `ctor` of a value of type
/// `ty`, in the order its pattern lists them.
fn field_tys(ty: &Ty, ctor: &CtorRef, datas: &[DataDef]) -> Option<Vec<Ty>> {
    match (ty, &ctor.data) {
        (Ty::Option(a), DataRef::Option) => Some(match ctor.index {
            0 => Vec::new(),
            _ => vec![(**a).clone()],
        }),
        (Ty::Result(a, b), DataRef::Result) => Some(match ctor.index {
            0 => vec![(**a).clone()],
            _ => vec![(**b).clone()],
        }),
        (Ty::Pair(a, b), DataRef::Pair) => Some(vec![(**a).clone(), (**b).clone()]),
        (Ty::Data(name, args), DataRef::Gen(n)) if n == name => {
            let data = datas.iter().find(|d| &d.name == name)?;
            let c = data.ctors.get(ctor.index)?;
            if data.generics.len() != args.len() {
                return None;
            }
            Some(
                c.fields
                    .iter()
                    .map(|f| subst(&f.ty, &data.generics, args))
                    .collect(),
            )
        }
        _ => None,
    }
}

/// `t` with each generic of `names` replaced by the type at its place in
/// `args`.
pub fn subst(t: &Ty, names: &[String], args: &[Ty]) -> Ty {
    let b = |a: &Ty| Box::new(subst(a, names, args));
    match t {
        Ty::Param(p) => names
            .iter()
            .position(|n| n == p)
            .map_or_else(|| t.clone(), |i| args[i].clone()),
        Ty::Vec(a) => Ty::Vec(b(a)),
        Ty::Array(a) => Ty::Array(b(a)),
        Ty::Slice(a) => Ty::Slice(b(a)),
        Ty::Option(a) => Ty::Option(b(a)),
        Ty::Ref(a) => Ty::Ref(b(a)),
        Ty::RefMut(a) => Ty::RefMut(b(a)),
        Ty::Info(a) => Ty::Info(b(a)),
        Ty::BudgetAnswer(a) => Ty::BudgetAnswer(b(a)),
        Ty::SharedVar(c, a) => Ty::SharedVar(*c, b(a)),
        Ty::Result(x, y) => Ty::Result(b(x), b(y)),
        Ty::Pair(x, y) => Ty::Pair(b(x), b(y)),
        Ty::Data(n, xs) => Ty::Data(
            n.clone(),
            xs.iter().map(|x| subst(x, names, args)).collect(),
        ),
        Ty::Std(n, xs) => Ty::Std(*n, xs.iter().map(|x| subst(x, names, args)).collect()),
        Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
            params: f.params.iter().map(|x| subst(x, names, args)).collect(),
            ret: subst(&f.ret, names, args),
            kind: f.kind,
            tier: f.tier,
        })),
        _ => t.clone(),
    }
}

/// The locals declared anywhere inside `e`.
fn declared(e: &Expr, out: &mut HashSet<u32>) {
    // Every node kind is listed, with no catch-all: a new kind that binds
    // a local has to say so here, or `partly_moved` drops it outside its
    // scope.
    e.walk(&mut |x| match &x.kind {
        ExprKind::Block(b) => {
            for s in &b.stmts {
                match s {
                    Stmt::Let { local, .. } | Stmt::Var { local, .. } => {
                        out.insert(local.id);
                    }
                    Stmt::Assign { .. }
                    | Stmt::Expr(_)
                    | Stmt::While { .. }
                    | Stmt::Return { .. } => {}
                }
            }
        }
        ExprKind::Match(m) => {
            for a in &m.arms {
                let mut v = Vec::new();
                bound(&a.pat, &mut v);
                out.extend(v.iter().map(|(l, _)| l.id));
            }
        }
        ExprKind::Closure(c) => out.extend(c.params.iter().map(|(l, _)| l.id)),
        ExprKind::Handle(h) => {
            let mut v = Vec::new();
            if let Some(r) = &h.ret {
                bound(&r.pat, &mut v);
            }
            for a in h.direct.iter().chain(&h.aborts).chain(&h.susp) {
                for p in &a.pats {
                    bound(p, &mut v);
                }
                out.extend(a.k.iter().map(|k| k.id));
            }
            out.extend(v.iter().map(|(l, _)| l.id));
        }
        ExprKind::Declaration(_)
        | ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Text(_)
        | ExprKind::Read { .. }
        | ExprKind::FnValue { .. }
        | ExprKind::Call(_)
        | ExprKind::Arith { .. }
        | ExprKind::Cmp { .. }
        | ExprKind::Eq { .. }
        | ExprKind::Not(_)
        | ExprKind::And(..)
        | ExprKind::Or(..)
        | ExprKind::Ctor { .. }
        | ExprKind::Field { .. }
        | ExprKind::If { .. }
        | ExprKind::Perform(_)
        | ExprKind::Inject { .. }
        | ExprKind::Remap { .. }
        | ExprKind::Ref(_)
        | ExprKind::RefMut(_)
        | ExprKind::TempRef(_)
        | ExprKind::Deref { .. }
        | ExprKind::Shown(_)
        | ExprKind::Budget(_)
        | ExprKind::Unreachable(_)
        | ExprKind::FnCast(_) => {}
    });
}

/// The owned locals some branch moves and another does not, with their
/// types, leaving out what the branches declare.
fn partly_moved(branches: &[&Expr]) -> Vec<(Local, Ty)> {
    let mut inner = HashSet::new();
    for b in branches {
        declared(b, &mut inner);
    }
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for b in branches {
        b.walk(&mut |x| {
            if let ExprKind::Read {
                local,
                how: Use::Move,
            } = &x.kind
                && needs_drop(&x.ty)
                && !inner.contains(&local.id)
                && seen.insert(local.id)
            {
                out.push((local.clone(), x.ty.clone()));
            }
        });
    }
    out.retain(|(l, _)| {
        branches.iter().any(|b| consumes(b, l.id)) && !branches.iter().all(|b| consumes(b, l.id))
    });
    out
}

/// Whether `id` holds no value after `e`: `e` moves it and does not give
/// it a whole new value after that. A branch that drops a var's value and
/// assigns it a new one (`if c { r := Some(x) }`) leaves it holding one.
///
/// A nested `if` or `match` consumes `id` when some branch of it does: a
/// branch that assigns the var again (`else if c { r := Some(x) }`) leaves
/// it holding a value, as a block that ends with the assignment does.
fn consumes(e: &Expr, id: u32) -> bool {
    match &e.kind {
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            moves(cond, id)
                || consumes(then, id)
                || otherwise.as_deref().is_some_and(|o| consumes(o, id))
        }
        ExprKind::Match(m) => {
            moves(&m.scrut, id)
                || m.arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(|g| moves(g, id)) || consumes(&a.body, id)
                })
        }
        ExprKind::Block(b) => match b.tail.as_deref() {
            Some(t) if moves(t, id) => consumes(t, id),
            _ => moves(e, id) && last_change(&b.stmts, id) != Some(false),
        },
        _ => moves(e, id),
    }
}

/// Ends the branch `e` with the drops of `locals` it does not move.
fn finish_branch(e: &mut Expr, locals: &[(Local, Ty)]) {
    let body = std::mem::replace(e, unit(e.span));
    *e = end_scope(body, locals);
}

/// `expr`, then the owned temporaries `&(e)` lends in the straight-line
/// part of `e` are named before it and dropped after it.
fn expr_at(e: &mut Expr, cx: &mut Cx) {
    expr(e, cx);
    let mut temps = Vec::new();
    take_temps(e, &mut temps);
    if temps.is_empty() {
        return;
    }
    let owned: Vec<(Local, Ty)> = temps
        .iter()
        .map(|(l, init)| (l.clone(), init.ty.clone()))
        .collect();
    let body = std::mem::replace(e, unit(e.span));
    let body = end_scope(body, &owned);
    let (ty, span) = (body.ty.clone(), body.span);
    let stmts = temps
        .into_iter()
        .map(|(local, init)| Stmt::Let {
            stack: false,
            local,
            ty: init.ty.clone(),
            span: init.span,
            init,
        })
        .collect();
    *e = Expr {
        kind: ExprKind::Block(Block {
            stmts,
            tail: Some(Box::new(body)),
        }),
        ty,
        span,
    };
}

/// Replaces each `&(e)` of an owned value that runs whenever `e` does, in
/// the order they run, by a borrow of a new local that `out` gives `e`.
/// Blocks, branches and closures are left to their own `expr_at`.
fn take_temps(e: &mut Expr, out: &mut Vec<(Local, Expr)>) {
    match &mut e.kind {
        // A closure written where a borrowed function is expected is a
        // temporary that the borrow lends, as `&(e)` is.
        ExprKind::Closure(c) if c.borrowed && matches!(e.ty, Ty::Fn(_)) => {
            let local = Local {
                id: fresh_id(),
                name: "temporary".into(),
                repr: Repr::Plain,
            };
            let ty = e.ty.clone();
            let init = std::mem::replace(e, unit(e.span));
            *e = Expr {
                kind: ExprKind::Ref(Place {
                    local: local.clone(),
                    path: Vec::new(),
                    ty: ty.clone(),
                }),
                ty: Ty::Ref(Box::new(ty)),
                span: init.span,
            };
            out.push((local, init));
        }
        ExprKind::Block(_)
        | ExprKind::Closure(_)
        | ExprKind::And(..)
        | ExprKind::Or(..)
        | ExprKind::Handle(_)
        | ExprKind::Budget(_) => {}
        ExprKind::If { cond, .. } => take_temps(cond, out),
        ExprKind::Match(m) => take_temps(&mut m.scrut, out),
        ExprKind::TempRef(inner) => {
            // `&(() => ..)` is lowered as the closure alone.
            if !matches!(inner.kind, ExprKind::Closure(_)) {
                take_temps(inner, out);
            }
            if !needs_drop(&inner.ty) {
                return;
            }
            let local = Local {
                id: fresh_id(),
                name: "temporary".into(),
                repr: Repr::Plain,
            };
            let place = Place {
                local: local.clone(),
                path: Vec::new(),
                ty: inner.ty.clone(),
            };
            let init = std::mem::replace(&mut **inner, unit(e.span));
            e.kind = if matches!(e.ty, Ty::RefMut(_)) {
                ExprKind::RefMut(place)
            } else {
                ExprKind::Ref(place)
            };
            out.push((local, init));
        }
        _ => {
            for op in e.operands_mut() {
                take_temps(op, out);
            }
        }
    }
}

/// A field read of a local moved whole (`l.f` of a temporary) reads the
/// local in place: what the field read does not take of it is then dropped
/// as of any local (whole at the end of its scope, or the members left).
fn place_field_base(e: &mut Expr) {
    let ExprKind::Field { base, .. } = &mut e.kind else {
        return;
    };
    if let ExprKind::Read { how, .. } = &mut base.kind
        && *how == Use::Move
    {
        *how = Use::Place;
    }
}

/// A `match` that takes a copy of a local or of one of its fields
/// (`Use::Clone`) by value owns that copy: it is named, so that the arms drop it as they drop a local
/// moved in as the scrutinee.
fn name_cloned_scrutinee(e: &mut Expr) {
    let ExprKind::Match(m) = &mut e.kind else {
        return;
    };
    if m.by_ref
        || !needs_drop(&m.scrut.ty)
        || !matches!(
            m.scrut.kind,
            ExprKind::Read {
                how: Use::Clone,
                ..
            } | ExprKind::Field {
                how: Use::Clone,
                ..
            }
        )
    {
        return;
    }
    let local = Local {
        id: fresh_id(),
        name: "scrutinee".into(),
        repr: Repr::Plain,
    };
    let (sty, sspan) = (m.scrut.ty.clone(), m.scrut.span);
    let init = std::mem::replace(
        &mut m.scrut,
        Expr {
            kind: ExprKind::Read {
                local: local.clone(),
                how: Use::Move,
            },
            ty: sty.clone(),
            span: sspan,
        },
    );
    let (ty, span) = (e.ty.clone(), e.span);
    let matched = std::mem::replace(e, unit(span));
    *e = Expr {
        kind: ExprKind::Block(Block {
            stmts: vec![Stmt::Let {
                stack: false,
                local,
                ty: sty,
                init,
                span: sspan,
            }],
            tail: Some(Box::new(matched)),
        }),
        ty,
        span,
    };
}

fn expr(e: &mut Expr, cx: &mut Cx) {
    name_cloned_scrutinee(e);
    place_field_base(e);
    match &mut e.kind {
        ExprKind::Block(b) => {
            // A block whose value is not kept (the program's last value, a
            // block of type `Unit` ending in a value) reads its tail before
            // what the tail borrows is dropped.
            if e.ty == Ty::Unit
                && let Some(t) = &b.tail
                && t.ty != Ty::Unit
                && t.ty != Ty::Never
            {
                // Named, so that it is dropped first, as the latest local.
                let t = *b.tail.take().unwrap();
                b.stmts.push(Stmt::Let {
                    stack: false,
                    local: Local {
                        id: fresh_id(),
                        name: "discarded".into(),
                        repr: Repr::Plain,
                    },
                    ty: t.ty.clone(),
                    span: t.span,
                    init: t,
                });
            }
            block(b, cx)
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            expr(cond, cx);
            expr_at(then, cx);
            if otherwise.is_none() {
                *otherwise = Some(Box::new(unit(e.span)));
            }
            let o = otherwise.as_mut().unwrap();
            expr_at(o, cx);
            let partly = partly_moved(&[then, o]);
            finish_branch(then, &partly);
            finish_branch(o, &partly);
        }
        ExprKind::Match(m) => {
            expr(&mut m.scrut, cx);
            // What a pattern leaves unnamed of a value the `match` owns is
            // named, so that the arm drops it as it drops what it binds.
            if !m.by_ref && needs_drop(&m.scrut.ty) {
                // An arm that binds nothing of a local moved in owns the
                // local whole (it may read it again), and drops it whole.
                let whole_local = scrutinee_local(m).is_some();
                for a in &mut m.arms {
                    let mut binds = Vec::new();
                    bound(&a.pat, &mut binds);
                    if whole_local && binds.is_empty() {
                        continue;
                    }
                    name_unbound(&mut a.pat, &m.scrut.ty, &cx.datas);
                }
            }
            // A local moved in as the scrutinee is the matched value: an arm
            // that reads it again reads that value, and an arm whose pattern
            // takes no part of it owns it whole.
            let whole = scrutinee_local(m);
            for a in &mut m.arms {
                let mut binds = Vec::new();
                bound(&a.pat, &mut binds);
                // An arm whose pattern takes parts of the local has moved
                // the local: what the arm gives it is a new value.
                let taken = match &whole {
                    Some(w) if binds.is_empty() => {
                        binds.push(w.clone());
                        false
                    }
                    Some(w) => {
                        cx.gone.push(w.0.id);
                        true
                    }
                    None => false,
                };
                cx.scopes.push(binds.clone());
                if let Some(g) = &mut a.guard {
                    expr_at(g, cx);
                }
                expr_at(&mut a.body, cx);
                cx.scopes.pop();
                if taken {
                    cx.gone.pop();
                }
                finish_branch(&mut a.body, &binds);
                // A linear value taken apart by its constructor's pattern
                // is consumed there: what the arm releases of it is the
                // shell, which is no `drop`.
                if let (Some(w), Pat::Ctor { ctor, .. }) = (&whole, &a.pat)
                    && ctor.linear
                    && !taken
                {
                    release_shells(&mut a.body, w.0.id);
                }
            }
            let bodies: Vec<&Expr> = m.arms.iter().map(|a| &a.body).collect();
            let mut partly = partly_moved(&bodies);
            // What an arm's pattern binds exists in that arm only: another
            // arm has nothing of it to drop.
            let mut arm_binds = Vec::new();
            for a in &m.arms {
                bound(&a.pat, &mut arm_binds);
            }
            partly.retain(|(l, _)| {
                whole.as_ref().is_none_or(|(w, _)| w.id != l.id)
                    && arm_binds.iter().all(|(b, _)| b.id != l.id)
            });
            for a in &mut m.arms {
                finish_branch(&mut a.body, &partly);
            }
        }
        ExprKind::Closure(c) => {
            let params: Vec<(Local, Ty)> = c
                .params
                .iter()
                .filter(|(_, t)| needs_drop(t))
                .cloned()
                .collect();
            let mut inner = Cx {
                scopes: vec![params.clone()],
                gone: Vec::new(),
                datas: cx.datas.clone(),
            };
            expr_at(&mut c.body, &mut inner);
            finish_branch(&mut c.body, &params);
        }
        // Each part runs in its own place; what it binds is its own.
        ExprKind::Budget(b) => {
            expr_at(&mut b.steps, cx);
            expr_at(&mut b.body, cx);
        }
        // The right side runs only when the left does not decide: an owned
        // local it moves is released on the way where it does not run, so
        // `a && b` is `if a { b } else { false }` with those drops.
        ExprKind::And(..) | ExprKind::Or(..) => {
            let is_and = matches!(e.kind, ExprKind::And(..));
            let span = e.span;
            let placeholder = unit(span);
            let (mut a, mut b) = match std::mem::replace(&mut e.kind, placeholder.kind) {
                ExprKind::And(a, b) | ExprKind::Or(a, b) => (a, b),
                _ => unreachable!(),
            };
            expr_at(&mut a, cx);
            expr_at(&mut b, cx);
            let mut skipped = Expr {
                kind: ExprKind::Bool(!is_and),
                ty: Ty::Bool,
                span,
            };
            let partly = partly_moved(&[&b, &skipped]);
            if partly.is_empty() {
                e.kind = if is_and {
                    ExprKind::And(a, b)
                } else {
                    ExprKind::Or(a, b)
                };
            } else {
                finish_branch(&mut skipped, &partly);
                let (then, otherwise) = if is_and {
                    (b, Box::new(skipped))
                } else {
                    (Box::new(skipped), b)
                };
                e.kind = ExprKind::If {
                    cond: a,
                    then,
                    otherwise: Some(otherwise),
                };
            }
        }
        ExprKind::Handle(h) => {
            expr_at(&mut h.body, cx);
            if let Some(r) = &mut h.ret {
                let mut binds = Vec::new();
                bound(&r.pat, &mut binds);
                cx.scopes.push(binds.clone());
                expr_at(&mut r.body, cx);
                cx.scopes.pop();
                finish_branch(&mut r.body, &binds);
            }
            for a in h.direct.iter_mut().chain(&mut h.aborts).chain(&mut h.susp) {
                let mut binds = Vec::new();
                for p in &a.pats {
                    bound(p, &mut binds);
                }
                cx.scopes.push(binds.clone());
                if let Some(g) = &mut a.guard {
                    expr_at(g, cx);
                }
                expr_at(&mut a.body, cx);
                cx.scopes.pop();
                finish_branch(&mut a.body, &binds);
            }
        }
        _ => {
            for op in e.operands_mut() {
                expr(op, cx);
            }
        }
    }
}

fn block(b: &mut Block, cx: &mut Cx) {
    cx.scopes.push(Vec::new());
    let stmts = std::mem::take(&mut b.stmts);
    let mut out = Vec::with_capacity(stmts.len());
    for (i, mut s) in stmts.clone().into_iter().enumerate() {
        match &mut s {
            // A closure a local of its own kind holds is that local's value,
            // not a temporary a borrow lends: the local is dropped at the
            // end of its scope.
            Stmt::Let { local, init, .. }
                if local.repr == Repr::BorrowClosure
                    && matches!(init.kind, ExprKind::Closure(_)) =>
            {
                expr(init, cx)
            }
            // A value that may borrow a temporary `&(e)` lends keeps it: the
            // temporary lives to the end of this block, as the local does.
            Stmt::Let { init, .. } | Stmt::Var { init, .. } if may_borrow(&init.ty, &cx.datas) => {
                expr(init, cx);
                let mut temps = Vec::new();
                take_temps(init, &mut temps);
                for (local, t) in temps {
                    let ty = t.ty.clone();
                    if needs_drop(&ty) {
                        cx.scopes
                            .last_mut()
                            .unwrap()
                            .push((local.clone(), ty.clone()));
                    }
                    out.push(Stmt::Let {
                        stack: false,
                        local,
                        ty,
                        span: t.span,
                        init: t,
                    });
                }
            }
            Stmt::Let { init, .. } | Stmt::Var { init, .. } => expr_at(init, cx),
            Stmt::Assign {
                value,
                target,
                span,
            } => {
                expr_at(value, cx);
                // The value a whole assignment replaces is dropped first,
                // unless this block has moved it since it was last given one.
                let id = target.local.id;
                let held = match last_change(&stmts[..i], id) {
                    Some(moved) => !moved,
                    None => !cx.gone.contains(&id),
                };
                let whole = target.path.is_empty() && !moves(value, id);
                // An assignment into a member replaces that member: it is
                // dropped as a whole assignment drops the local, unless the
                // new value takes it.
                let member = !target.path.is_empty() && !moves_member(value, target);
                if (whole || member) && needs_drop(&target.ty) && held {
                    // A new value made from the old one is made first.
                    if mentions(value, id) {
                        let new = Local {
                            id: fresh_id(),
                            name: "assigned".into(),
                            repr: Repr::Plain,
                        };
                        let (vty, vspan) = (value.ty.clone(), value.span);
                        let init = std::mem::replace(
                            value,
                            Expr {
                                kind: ExprKind::Read {
                                    local: new.clone(),
                                    how: Use::Move,
                                },
                                ty: vty.clone(),
                                span: vspan,
                            },
                        );
                        out.push(Stmt::Let {
                            stack: false,
                            local: new,
                            ty: vty,
                            init,
                            span: vspan,
                        });
                    }
                    if member {
                        out.push(Stmt::Expr(Expr {
                            kind: ExprKind::Call(Box::new(CallNode {
                                callee: Callee::Builtin(DROP.into()),
                                args: vec![member_at(target, *span)],
                                tier: Tier::S,
                                targs: Vec::new(),
                                tick: Tick::None,
                                recur: false,
                                unwind: Vec::new(),
                                span: *span,
                            })),
                            ty: Ty::Unit,
                            span: *span,
                        }));
                    } else {
                        match target.local.repr {
                            // Through a `&mut` or a shared var, the value the
                            // borrow or the cell holds.
                            Repr::RefMut | Repr::SharedVar(_) => {
                                out.extend(drop_through(&target.local, &target.ty, *span))
                            }
                            _ => out.push(drop_of(&target.local, &target.ty, *span)),
                        }
                    }
                }
            }
            Stmt::Expr(x) => {
                expr_at(x, cx);
                // A value a statement discards is dropped right there: no
                // local holds it for the end of the block to drop.
                if needs_drop(&x.ty) && !matches!(x.kind, ExprKind::Read { .. }) {
                    let (ty, span) = (x.ty.clone(), x.span);
                    let init = std::mem::replace(x, unit(span));
                    let local = Local {
                        id: fresh_id(),
                        name: "discarded".into(),
                        repr: Repr::Plain,
                    };
                    out.push(Stmt::Let {
                        stack: false,
                        local: local.clone(),
                        ty: ty.clone(),
                        init,
                        span,
                    });
                    out.push(drop_of(&local, &ty, span));
                    continue;
                }
            }
            Stmt::While { cond, body, .. } => {
                expr_at(cond, cx);
                block(body, cx);
            }
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    expr_at(v, cx);
                }
                // Leaving the function drops what every scope still owns.
                let span = value.as_ref().map_or(Span::new(0, 0), |v| v.span);
                let mut dropped: Vec<(Local, Ty)> = Vec::new();
                for scope in cx.scopes.iter().rev() {
                    for (l, t) in scope.iter().rev() {
                        if !value.as_ref().is_some_and(|v| moves(v, l.id))
                            && !stmts[..i].iter().any(|s| stmt_moves(s, l.id))
                            && !cx.gone.contains(&l.id)
                        {
                            dropped.push((l.clone(), t.clone()));
                        }
                    }
                }
                // A value that still reads a local the return drops is
                // computed first, and the drops come after it.
                match value {
                    Some(v) if dropped.iter().any(|(l, _)| mentions(v, l.id)) => {
                        let (ty, vspan) = (v.ty.clone(), v.span);
                        let result = Local {
                            id: fresh_id(),
                            name: "returned".into(),
                            repr: Repr::Plain,
                        };
                        let init = std::mem::replace(
                            v,
                            Expr {
                                kind: ExprKind::Read {
                                    local: result.clone(),
                                    how: Use::Move,
                                },
                                ty: ty.clone(),
                                span: vspan,
                            },
                        );
                        out.push(Stmt::Let {
                            stack: false,
                            local: result,
                            ty,
                            init,
                            span: vspan,
                        });
                        for (l, t) in &dropped {
                            out.push(drop_of(l, t, span));
                        }
                    }
                    _ => {
                        for (l, t) in &dropped {
                            out.push(drop_of(l, t, span));
                        }
                    }
                }
            }
        }
        if let Stmt::Let { local, ty, .. } | Stmt::Var { local, ty, .. } = &s
            && needs_drop(ty)
        {
            cx.scopes
                .last_mut()
                .unwrap()
                .push((local.clone(), ty.clone()));
        }
        out.push(s);
    }
    b.stmts = out;
    if let Some(t) = &mut b.tail {
        expr_at(t, cx);
    }
    let owned = cx.scopes.pop().unwrap();
    // What the block's statements and tail do not move is dropped at its end.
    let (left, taken): (Vec<(Local, Ty)>, Vec<(Local, Ty)>) =
        owned.into_iter().partition(|(l, _)| {
            !value_moves_since(&b.stmts, l.id) && !b.tail.as_deref().is_some_and(|t| moves(t, l.id))
        });
    // What is left of a product some members were moved out of.
    let mut parts: Vec<&Expr> = Vec::new();
    for s in &b.stmts {
        match s {
            Stmt::Let { init, .. } | Stmt::Var { init, .. } => parts.push(init),
            Stmt::Assign { value, .. } => parts.push(value),
            Stmt::Expr(x) => parts.push(x),
            Stmt::While { .. } | Stmt::Return { .. } => {}
        }
    }
    parts.extend(b.tail.as_deref());
    let assigned = |id: u32| {
        b.stmts.iter().any(|s| {
            matches!(s, Stmt::Assign { target, .. } if target.local.id == id)
                || matches!(s, Stmt::While { .. } | Stmt::Return { .. })
        })
    };
    let taken: Vec<(Local, Ty)> = taken.into_iter().filter(|(l, _)| !assigned(l.id)).collect();
    let rest = rests(&parts, &taken, &cx.datas);
    if left.is_empty() && rest.is_empty() {
        return;
    }
    let tail = b.tail.take().map(|t| *t);
    match tail {
        Some(t) => {
            let t = end_scope_with(t, &left, rest);
            b.tail = Some(Box::new(t));
        }
        None => {
            let diverges = matches!(b.stmts.last(), Some(Stmt::Return { .. }));
            if !diverges {
                for (l, t) in left.iter().rev() {
                    b.stmts.push(drop_of(l, t, Span::new(0, 0)));
                }
                b.stmts.extend(rest);
            }
        }
    }
}

/// The member `target` names, moved out of its place: the local (through
/// its borrow or cell, as a place) and the fields down to it. Only the type
/// of the member itself is known here; the parts above it are places, which
/// nothing reads the type of.
fn member_at(target: &Place, span: Span) -> Expr {
    let mut e = Expr {
        kind: ExprKind::Read {
            local: target.local.clone(),
            how: Use::Place,
        },
        ty: target.ty.clone(),
        span,
    };
    let last = target.path.len() - 1;
    for (i, f) in target.path.iter().enumerate() {
        e = Expr {
            kind: ExprKind::Field {
                base: Box::new(e),
                field: f.clone(),
                how: if i == last { Use::Move } else { Use::Place },
                indirect: f.indirect.clone(),
            },
            ty: target.ty.clone(),
            span,
        };
    }
    e
}

/// Whether `e` moves the member `target` names (or a part of it) out.
fn moves_member(e: &Expr, target: &Place) -> bool {
    fn names(e: &Expr, out: &mut Vec<String>) -> Option<u32> {
        match &e.kind {
            ExprKind::Read { local, .. } => Some(local.id),
            ExprKind::Field { base, field, .. } => {
                let id = names(base, out)?;
                out.push(field.name.clone());
                Some(id)
            }
            _ => None,
        }
    }
    let mut found = false;
    e.walk(&mut |x| {
        if let ExprKind::Field { how: Use::Move, .. } = &x.kind {
            let mut path = Vec::new();
            if names(x, &mut path) == Some(target.local.id)
                && path.len() >= target.path.len()
                && path.iter().zip(&target.path).all(|(a, b)| *a == b.name)
            {
                found = true;
            }
        }
    });
    found || moves_whole(e, target.local.id)
}

/// Whether the statements move `id` after the last time they give it a
/// whole new value.
fn value_moves_since(stmts: &[Stmt], id: u32) -> bool {
    last_change(stmts, id) == Some(true)
}

/// What the statements last do to `id`: move it (`Some(true)`), give it a
/// whole new value (`Some(false)`), or neither (`None`). A loop whose body
/// moves the local and then gives it a new value leaves it holding one.
fn last_change(stmts: &[Stmt], id: u32) -> Option<bool> {
    for s in stmts.iter().rev() {
        match s {
            Stmt::Assign { target, .. } if target.path.is_empty() && target.local.id == id => {
                // `x := f(x)` moves the old value and holds the new one.
                return Some(false);
            }
            Stmt::While { cond, body, .. } if !moves(cond, id) => {
                // A tail that moves the local and gives it a new value on
                // every branch that moves it leaves it holding one.
                let tail = body.tail.as_deref().filter(|t| moves(t, id));
                match last_change(&body.stmts, id) {
                    _ if tail.is_some() => return Some(consumes(tail.unwrap(), id)),
                    Some(c) => return Some(c),
                    None => {}
                }
            }
            // A statement whose expression moves the local and gives it a
            // new value again on every branch that moves it, as a branch
            // ending in its drops does, leaves it holding one.
            Stmt::Expr(e)
            | Stmt::Let { init: e, .. }
            | Stmt::Var { init: e, .. }
            | Stmt::Assign { value: e, .. }
                if moves(e, id) =>
            {
                return Some(consumes(e, id));
            }
            _ if stmt_moves(s, id) => return Some(true),
            _ => {}
        }
    }
    None
}

/// Whether, on every path through `f`, each owned local of its parameters
/// and of every `let` and pattern is moved or dropped exactly once
/// (`blocks::ownership`).
pub fn check(f: &FnInst) -> Result<(), String> {
    match crate::blocks::ownership::check_fn(f).first() {
        Some(x) => Err(x.to_string()),
        None => Ok(()),
    }
}
