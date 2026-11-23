//! The static checks of what a package promises, read from the blocks of a
//! function (`crate::wf` says what each rule is).
//!
//! A local is bound where a path binds it: the scope of a path is what an
//! instruction binds, and where paths meet it is what every one of them
//! holds. The blocks carry what the tree rules read off the nesting: a
//! `{ .. }` opens and closes, what the parts of a region bind ends where they
//! meet, and a continuation's environment is what its `suspend` lists
//! (`Closed`).

use std::collections::HashMap;

use super::flow::*;
use super::*;
use crate::wf::{Finding, Rule, Scope, fits, fits_in, written};

#[derive(Clone, Default)]
struct State {
    scope: Scope,
    /// The `{ .. }` scopes open, each with the locals bound in it.
    open: Vec<(RegionId, Vec<u32>)>,
}

/// The findings of the block form of `f`: the rules that read the graph and
/// the rules that read what a node says.
pub fn check_fn(pkg: &Package, f: &FnInst) -> Vec<Finding> {
    let bf = lower_fn(f);
    check_blocks(pkg, f, &bf)
}

pub fn check_blocks(pkg: &Package, f: &FnInst, bf: &BlockFn) -> Vec<Finding> {
    let mut out = super::check(pkg, f, bf);
    let mut cx = Cx {
        pkg,
        out: Vec::new(),
        report: false,
        rets: vec![(f.ret.clone(), f.body.span, "the body of the function")],
        bound: HashMap::new(),
    };
    let mut st = State::default();
    for p in &f.params {
        st.scope.bind(&p.local, &p.ty);
    }
    solve(&mut cx, bf, 0, st, None, true);
    out.extend(cx.out);
    out
}

struct Cx<'a> {
    pkg: &'a Package,
    out: Vec<Finding>,
    report: bool,
    /// The type the body being run is to have, where its value is read: the
    /// function's, a closure's.
    rets: Vec<(Ty, Span, &'static str)>,
    bound: HashMap<usize, HashMap<RegionId, Vec<u32>>>,
}

impl Cx<'_> {
    fn find(&mut self, rule: Rule, span: Span, message: String) {
        if self.report {
            self.out.push(Finding {
                rule,
                span,
                message,
            });
        }
    }

    /// `have` where `want` is expected.
    fn ty(&mut self, want: &Ty, have: &Ty, span: Span, what: &str) {
        if !fits(want, have) && written(want) && written(have) {
            self.find(
                Rule::Type,
                span,
                format!("{what} is {have:?}, expected {want:?}"),
            );
        }
    }

    /// A pattern on a member of a union is on a value of that union, by a variant it has, and
    /// a name it binds there has the member's type (a borrow of it on a borrowed union).
    fn variant(&mut self, p: &Pat, scrut: &Ty, span: Span) {
        let Pat::Variant { union, variant, pat } = p else {
            return;
        };
        let at = match scrut {
            Ty::Ref(t) | Ty::RefMut(t) => &**t,
            t => t,
        };
        if *at != Ty::Union(*union) {
            self.find(
                Rule::Type,
                span,
                format!("a pattern on a member of the union {union} matches {scrut:?}"),
            );
            return;
        }
        let Some(member) = self.pkg.unions.get(*union).and_then(|u| u.members.get(*variant))
        else {
            self.find(
                Rule::Type,
                span,
                format!("the union {union} has no variant {variant}"),
            );
            return;
        };
        if let Pat::Bind(_, t) = &**pat {
            let t = match t {
                Ty::Ref(t) | Ty::RefMut(t) => &**t,
                t => t,
            };
            let member = member.clone();
            self.ty(&member, t, span, "a name bound on a member of a union");
        }
    }

    /// A use of `l`; its binder's type.
    fn use_local(&mut self, l: &Local, scope: &Scope, span: Span, what: &str) -> Option<Ty> {
        match scope.0.get(&l.id) {
            None => {
                self.find(
                    Rule::Scope,
                    span,
                    format!("{what} `{}#{}` is not bound here", l.name, l.id),
                );
                None
            }
            Some((b, t)) => {
                if b.name != l.name || b.repr != l.repr {
                    self.find(
                        Rule::Identity,
                        span,
                        format!(
                            "{what} `{}#{}` ({:?}) is bound as `{}#{}` ({:?})",
                            l.name, l.id, l.repr, b.name, b.id, b.repr
                        ),
                    );
                }
                Some(t.clone())
            }
        }
    }

    fn place(&mut self, p: &Place, scope: &Scope, span: Span, what: &str) {
        let bound = self.use_local(&p.local, scope, span, what);
        if p.path.is_empty()
            && let Some(b) = bound
        {
            // A borrow of a borrowed local borrows what it borrows, through
            // every borrow.
            let mut b = b;
            while let Ty::Ref(a) | Ty::RefMut(a) | Ty::SharedVar(_, a) = b {
                b = *a;
            }
            self.ty(&b, &p.ty, span, &format!("the place `{}`", p.local.name));
        }
    }

    fn value(&mut self, bf: &BlockFn, v: &Value, scope: &Scope) {
        if let Value::Leaf(e) = v {
            self.expr(bf, e, scope);
        }
    }

    // ---- instructions and terminators

    fn inst(&mut self, bf: &BlockFn, i: &Inst, st: &mut State) {
        match i {
            Inst::Let {
                local, ty, init, ..
            }
            | Inst::Var {
                local, ty, init, ..
            } => {
                self.value(bf, init, &st.scope);
                let have = match (ty, local.repr) {
                    (Ty::SharedVar(_, a), Repr::SharedVar(_)) => a,
                    _ => ty,
                };
                self.ty(
                    have,
                    &value_ty(bf, init),
                    value_span(bf, init),
                    &format!("the value of `{}`", local.name),
                );
                st.scope.bind(local, ty);
                if let Some((_, bound)) = st.open.last_mut() {
                    bound.push(local.id);
                }
            }
            Inst::Assign {
                target,
                value,
                span,
            } => {
                self.value(bf, value, &st.scope);
                self.place(target, &st.scope, *span, "the target");
            }
            Inst::Eval(v) => self.value(bf, v, &st.scope),
            Inst::Bind { local, ty, .. } => st.scope.bind(local, ty),
            Inst::Unpack { .. } | Inst::Release { .. } => {}
            Inst::End(l) => {
                st.scope.0.remove(&l.id);
            }
            Inst::Open(r) => st.open.push((*r, Vec::new())),
            Inst::Close(r, v) => {
                if let Some(v) = v {
                    self.value(bf, v, &st.scope);
                }
                while let Some((o, bound)) = st.open.pop() {
                    for id in bound {
                        st.scope.0.remove(&id);
                    }
                    if o == *r {
                        break;
                    }
                }
            }
        }
    }

    fn term(&mut self, bf: &BlockFn, b: BlockId, t: &Term, st: &State) -> Vec<(BlockId, State)> {
        let mut out = Vec::new();
        let mut go = |to: BlockId, s: &State| out.push((to, s.clone()));
        match t {
            Term::Jump(to, v) => {
                self.value(bf, v, &st.scope);
                go(*to, st);
            }
            Term::Goto(to) => go(*to, st),
            Term::Control {
                region,
                succs,
                join,
            } => {
                let ops = operands(bf, *region);
                for v in &ops {
                    self.value(bf, v, &st.scope);
                }
                let shell = bf.regions[*region].as_ref().map(|r| &r.shell);
                if let (Some(Shell::Node(Expr {
                    kind: ExprKind::If { .. },
                    ..
                })), Some(c)) = (shell, ops.first())
                {
                    self.ty(&Ty::Bool, &value_ty(bf, c), value_span(bf, c), "the condition");
                }
                if matches!(shell, Some(Shell::While { .. })) {
                    go(succs[0], st);
                } else {
                    for s in succs {
                        go(*s, st);
                    }
                }
                if skips(bf, *region) {
                    go(*join, st);
                }
            }
            Term::Enter { region, entry, .. } => {
                let ops = operands(bf, *region);
                for v in &ops {
                    self.value(bf, v, &st.scope);
                }
                if let Some(Region {
                    shell:
                        Shell::Node(Expr {
                            kind: ExprKind::Match(m),
                            span,
                            ..
                        }),
                    ..
                }) = &bf.regions[*region]
                    && let Some(s) = ops.first()
                {
                    let sty = value_ty(bf, s);
                    for a in &m.arms {
                        self.variant(&a.pat, &sty, *span);
                    }
                }
                go(*entry, st);
            }
            Term::Test { cases, default, .. } => {
                for (_, to) in cases {
                    go(*to, st);
                }
                if let Some(to) = default {
                    go(*to, st);
                }
            }
            Term::Branch { value, then, els } => {
                self.value(bf, value, &st.scope);
                let cond = bf.blocks[b].owner.is_some_and(|r| {
                    matches!(
                        bf.regions[r].as_ref().map(|r| &r.shell),
                        Some(Shell::While { .. })
                    )
                });
                if cond {
                    self.ty(
                        &Ty::Bool,
                        &value_ty(bf, value),
                        value_span(bf, value),
                        "the condition",
                    );
                }
                go(*then, st);
                if let Some(e) = els {
                    go(*e, st);
                }
            }
            Term::Handle { region, edges, .. } => {
                let Some(Region {
                    shell:
                        Shell::Node(
                            e @ Expr {
                                kind: ExprKind::Handle(h),
                                ..
                            },
                        ),
                    ..
                }) = &bf.regions[*region]
                else {
                    return out;
                };
                for l in h.captures.iter().chain(&h.clones) {
                    self.use_local(l, &st.scope, e.span, "the handler's capture");
                }
                let ks: Vec<Option<u32>> = h
                    .direct
                    .iter()
                    .chain(&h.aborts)
                    .chain(&h.susp)
                    .map(|a| a.k.as_ref().map(|k| k.id))
                    .collect();
                let mut arm = 0;
                for e in edges {
                    let mut s = st.clone();
                    let k = match e.kind {
                        EdgeKind::Body | EdgeKind::Ret => None,
                        _ => {
                            arm += 1;
                            ks.get(arm - 1).copied().flatten()
                        }
                    };
                    for (l, t) in &e.params {
                        // The continuation is bound with no type to read.
                        let t = if Some(l.id) == k { Ty::Never } else { t.clone() };
                        s.scope.bind(l, &t);
                    }
                    go(e.entry, &s);
                }
            }
            Term::Call { region, abort, join } | Term::Suspend { region, abort, join, .. } => {
                if let Some(Region {
                    shell: Shell::Call(e),
                    ..
                }) = &bf.regions[*region]
                {
                    self.expr(bf, e, &st.scope);
                }
                go(*abort, st);
                go(*join, st);
            }
            Term::Return { value, cont, .. } => {
                if let Some(v) = value {
                    self.value(bf, v, &st.scope);
                }
                go(*cont, st);
            }
            Term::Done(v) => {
                self.value(bf, v, &st.scope);
                if let Some((want, span, what)) = self.rets.last().cloned() {
                    self.ty(&want, &value_ty(bf, v), span, what);
                }
            }
            Term::Abort | Term::Unreachable | Term::Pending | Term::Decline => {}
        }
        out
    }

    // ---- expressions without control flow

    fn expr(&mut self, bf: &BlockFn, e: &Expr, scope: &Scope) {
        let span = e.span;
        match &e.kind {
            ExprKind::Declaration(_)
            | ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Text(_)
            | ExprKind::FnValue { .. } => {}
            ExprKind::Read { local, how } => {
                if let Some(b) = self.use_local(local, scope, span, "the read")
                    && *how != Use::Place
                {
                    let shows = match &b {
                        Ty::Ref(a) | Ty::RefMut(a) | Ty::SharedVar(_, a) => (**a).clone(),
                        b => b.clone(),
                    };
                    if e.ty != b && e.ty != shows {
                        self.ty(
                            &shows,
                            &e.ty,
                            span,
                            &format!("the read of `{}`", local.name),
                        );
                    }
                }
            }
            ExprKind::Call(c) => self.call(bf, e, c, scope),
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => args.iter().for_each(|a| self.expr(bf, a, scope)),
            ExprKind::Not(a)
            | ExprKind::TempRef(a)
            | ExprKind::Shown(a)
            | ExprKind::Unreachable(a)
            | ExprKind::FnCast(a) => self.expr(bf, a, scope),
            ExprKind::Ctor { fields, .. } => {
                fields.iter().for_each(|(_, x)| self.expr(bf, x, scope))
            }
            ExprKind::Field { base, .. } => self.expr(bf, base, scope),
            ExprKind::Closure(c) => {
                for l in c.clones.iter().chain(&c.owned_refs) {
                    self.use_local(l, scope, span, "the capture");
                }
                for r in &c.refs {
                    self.use_local(&r.outer, scope, span, "the captured reference");
                }
                let mut inner = scope.with(&c.params);
                for r in &c.refs {
                    let t = scope.0.get(&r.outer.id).map(|(_, t)| t.clone());
                    inner.bind(&r.inner, &t.unwrap_or(Ty::Never));
                }
                if let Some(k) = closure_body(c)
                    && let Some(body) = bf.closures.get(k)
                {
                    self.rets
                        .push((c.ret.clone(), c.body.span, "the body of the closure"));
                    let report = self.report;
                    let st = State {
                        scope: inner,
                        open: Vec::new(),
                    };
                    solve(self, body, 0, st, None, report);
                    self.rets.pop();
                }
            }
            ExprKind::Perform(p) => {
                p.args.iter().for_each(|a| self.expr(bf, a, scope));
                // An abort path's drops are a block of their own; one a leaf
                // keeps is read where the node is.
                let mut inner = scope.clone();
                for s in &p.unwind {
                    self.stmt_in_leaf(bf, s, &mut inner);
                }
            }
            ExprKind::Inject { value, .. }
            | ExprKind::Remap { value, .. }
            | ExprKind::Deref { value, .. } => self.expr(bf, value, scope),
            ExprKind::Ref(p) | ExprKind::RefMut(p) => self.place(p, scope, span, "the borrow of"),
            // Control flow is in the blocks, not in a leaf; a leaf that
            // holds it (a tree not in A-normal form) is read as its parts
            // under the scope around it.
            ExprKind::And(..)
            | ExprKind::Or(..)
            | ExprKind::Match(_)
            | ExprKind::If { .. }
            | ExprKind::Block(_)
            | ExprKind::Handle(_)
            | ExprKind::Budget(_) => {
                let mut parts = Vec::new();
                e.children(&mut |c| parts.push(c.clone()));
                for c in &parts {
                    self.expr(bf, c, scope);
                }
            }
        }
    }

    /// A statement of the drops a leaf keeps for its abort path.
    fn stmt_in_leaf(&mut self, bf: &BlockFn, s: &Stmt, scope: &mut Scope) {
        match s {
            Stmt::Let {
                local, ty, init, ..
            }
            | Stmt::Var {
                local, ty, init, ..
            } => {
                self.expr(bf, init, scope);
                let have = match (ty, local.repr) {
                    (Ty::SharedVar(_, a), Repr::SharedVar(_)) => a,
                    _ => ty,
                };
                self.ty(
                    have,
                    &init.ty,
                    init.span,
                    &format!("the value of `{}`", local.name),
                );
                scope.bind(local, ty);
            }
            Stmt::Assign {
                target,
                value,
                span,
            } => {
                self.expr(bf, value, scope);
                self.place(target, scope, *span, "the target");
            }
            Stmt::Expr(e) => self.expr(bf, e, scope),
            Stmt::While { cond, .. } => self.expr(bf, cond, scope),
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    self.expr(bf, v, scope);
                }
            }
        }
    }

    fn call(&mut self, bf: &BlockFn, e: &Expr, c: &CallNode, scope: &Scope) {
        let span = e.span;
        match &c.callee {
            Callee::Inst(id) => {
                if let Some(f) = self.pkg.fns.get(*id) {
                    if f.params.len() != c.args.len() {
                        self.find(
                            Rule::Arity,
                            span,
                            format!(
                                "{}@{} takes {} arguments, given {}",
                                f.source,
                                f.id,
                                f.params.len(),
                                c.args.len()
                            ),
                        );
                    }
                    if f.tier != c.tier {
                        self.find(
                            Rule::Tier,
                            span,
                            format!(
                                "a call of {}@{} states the tier {:?}, the function is {:?}",
                                f.source, f.id, c.tier, f.tier
                            ),
                        );
                    }
                    if f.generics.is_empty() && c.targs.is_empty() {
                        for (p, a) in f.params.iter().zip(&c.args) {
                            // A borrowed parameter takes the value it borrows.
                            let want = match (&p.ty, &a.ty) {
                                (Ty::Ref(t) | Ty::RefMut(t), have) if fits_in(t, have, true) => {
                                    have
                                }
                                _ => &p.ty,
                            };
                            self.ty(
                                want,
                                &a.ty,
                                a.span,
                                &format!("the argument `{}`", p.local.name),
                            );
                        }
                        self.ty(
                            &f.ret,
                            &e.ty,
                            span,
                            &format!("the result of {}@{}", f.source, f.id),
                        );
                    }
                } else {
                    self.find(Rule::Scope, span, format!("a call of no function @{id}"));
                }
            }
            Callee::Builtin(_) | Callee::Extern(_) => {}
            Callee::Local(l) => {
                self.use_local(l, scope, span, "the called function");
            }
            Callee::Cont(l) => {
                self.use_local(l, scope, span, "the resumed continuation");
            }
            Callee::Value(v) => self.expr(bf, v, scope),
        }
        c.args.iter().for_each(|a| self.expr(bf, a, scope));
        let mut inner = scope.clone();
        for s in &c.unwind {
            self.stmt_in_leaf(bf, s, &mut inner);
        }
    }
}

impl Analysis for Cx<'_> {
    type State = State;

    fn join(&mut self, _at: BlockId, into: &mut State, from: &State) -> bool {
        let before = into.scope.0.len();
        into.scope.0.retain(|id, _| from.scope.0.contains_key(id));
        into.scope.0.len() != before
    }

    fn step(
        &mut self,
        bf: &BlockFn,
        b: BlockId,
        mut st: State,
        report: bool,
    ) -> Vec<(BlockId, State)> {
        let saved = self.report;
        self.report = report;
        let blk = &bf.blocks[b];
        // Where the parts of a region meet, what they bound ends.
        if let Some(r) = blk.join_of {
            let key = bf as *const BlockFn as usize;
            let ids = self
                .bound
                .entry(key)
                .or_insert_with(|| bound_in(bf))
                .get(&r)
                .cloned()
                .unwrap_or_default();
            for id in ids {
                st.scope.0.remove(&id);
            }
        }
        for i in &blk.insts {
            self.inst(bf, i, &mut st);
        }
        let out = self.term(bf, b, &blk.term, &st);
        self.report = saved;
        out
    }
}
