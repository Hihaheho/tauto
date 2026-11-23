//! Where a function may stop and be resumed, with what its continuation
//! needs, in the typed tree.
//!
//! The tiers `O` and `M` are one thing here: a point where the rest of the
//! function becomes a continuation. What tells them apart is how many times
//! that continuation may run, `Resumes::Once` or `Resumes::Many`; a
//! continuation run once is a linear value, the same rule `lin` checks for
//! any other. A point of tier `A` (`resume 0`) has no continuation: it only
//! leaves. A native backend builds each continuation from `points`: its
//! parameter is the value of the point (`result`) and its environment the
//! locals `live` after it, each with its type; a backend that suspends by
//! other means (Rust's `async`, JavaScript's trampoline) can read the same
//! points to check its own.
//!
//! The function should be in A-normal form (`anf::normalize`), so that each
//! point is a `let` of its own and nothing of the statement it is in runs
//! after it.

use std::collections::HashSet;

use crate::*;

/// How a continuation may be run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Resumes {
    /// `resume 0`, or a call of tier `A`: there is no continuation.
    Never,
    /// `resume <=1`, `resume 1`, or a call of tier `O`.
    Once,
    /// `resume ω`, or a call of tier `M`.
    Many,
}

/// A point where the function may stop.
#[derive(Debug, Clone)]
pub struct Point {
    pub span: Span,
    /// The operation performed, or the function called.
    pub at: At,
    pub resumes: Resumes,
    /// The type of the value the continuation receives.
    pub result: Ty,
    /// The locals in scope that the code after the point reads, in the
    /// order they were bound.
    pub live: Vec<(Local, Ty)>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum At {
    Perform(OpIndex),
    Call(InstId),
    /// A call of a function value or a continuation of the tier.
    Indirect,
}

/// The points of a function body, in the order written.
pub fn points(f: &FnInst) -> Vec<Point> {
    let scope: Vec<(Local, Ty)> = f
        .params
        .iter()
        .map(|p| (p.local.clone(), p.ty.clone()))
        .collect();
    let mut out = Vec::new();
    visit(&f.body, &scope, &HashSet::new(), &mut out);
    out
}

pub(crate) fn resumes_of(e: &Expr) -> Option<(At, Resumes)> {
    match &e.kind {
        ExprKind::Perform(p) => {
            let r = match p.quant {
                Quant::Zero => Resumes::Never,
                Quant::AtMostOne | Quant::One => Resumes::Once,
                Quant::Many => Resumes::Many,
                Quant::Direct => return None,
            };
            Some((At::Perform(p.op), r))
        }
        ExprKind::Call(c) => {
            let r = match c.tier {
                Tier::S => return None,
                Tier::A => Resumes::Never,
                Tier::O => Resumes::Once,
                Tier::M => Resumes::Many,
            };
            let at = match &c.callee {
                Callee::Inst(i) => At::Call(*i),
                _ => At::Indirect,
            };
            Some((at, r))
        }
        _ => None,
    }
}

/// The operands of a node that evaluates them first, in order.
fn operands(e: &Expr) -> Vec<&Expr> {
    match &e.kind {
        ExprKind::Call(c) => {
            let mut v = Vec::new();
            if let Callee::Value(f) = &c.callee {
                v.push(&**f);
            }
            v.extend(c.args.iter());
            v
        }
        ExprKind::Arith { args, .. } | ExprKind::Cmp { args, .. } | ExprKind::Eq { args, .. } => {
            args.iter().collect()
        }
        ExprKind::Not(a)
        | ExprKind::TempRef(a)
        | ExprKind::Shown(a)
        | ExprKind::Unreachable(a)
        | ExprKind::FnCast(a)
        | ExprKind::Field { base: a, .. }
        | ExprKind::Inject { value: a, .. }
        | ExprKind::Remap { value: a, .. }
        | ExprKind::Deref { value: a, .. } => vec![&**a],
        ExprKind::Ctor { fields, .. } => fields.iter().map(|(_, e)| e).collect(),
        ExprKind::Perform(p) => p.args.iter().collect(),
        _ => Vec::new(),
    }
}

/// The locals `e` reads, calls, borrows or captures.
pub(crate) fn mentions(e: &Expr, out: &mut HashSet<u32>) {
    e.walk(&mut |x| match &x.kind {
        ExprKind::Read { local, .. } => {
            out.insert(local.id);
        }
        ExprKind::Ref(p) | ExprKind::RefMut(p) => {
            out.insert(p.local.id);
        }
        ExprKind::Call(c) => {
            if let Callee::Local(l) | Callee::Cont(l) = &c.callee {
                out.insert(l.id);
            }
        }
        ExprKind::Closure(c) => out.extend(c.clones.iter().map(|l| l.id)),
        ExprKind::Block(b) => {
            for s in &b.stmts {
                stmt_targets(s, out);
            }
        }
        _ => {}
    });
}

/// The places a statement writes, which keep their local live.
fn stmt_targets(s: &Stmt, out: &mut HashSet<u32>) {
    if let Stmt::Assign { target, .. } = s {
        out.insert(target.local.id);
    }
}

pub(crate) fn stmt_mentions(s: &Stmt, out: &mut HashSet<u32>) {
    stmt_targets(s, out);
    match s {
        Stmt::Let { init, .. } | Stmt::Var { init, .. } => mentions(init, out),
        Stmt::Assign { value, .. } => mentions(value, out),
        Stmt::Expr(e) => mentions(e, out),
        Stmt::While { cond, body, .. } => {
            mentions(cond, out);
            body.stmts.iter().for_each(|s| stmt_mentions(s, out));
            if let Some(t) = &body.tail {
                mentions(t, out);
            }
        }
        Stmt::Return { value, .. } => {
            if let Some(v) = value {
                mentions(v, out)
            }
        }
    }
}

pub(crate) fn binds(p: &Pat, out: &mut Vec<(Local, Ty)>) {
    match p {
        Pat::Bind(l, t) => out.push((l.clone(), t.clone())),
        Pat::Ctor { fields, .. } => fields.iter().for_each(|f| binds(f, out)),
        Pat::Variant { pat, .. } => binds(pat, out),
        _ => {}
    }
}

/// Records the points in `e`, where `later` holds the locals the code after
/// `e` reads.
fn visit(e: &Expr, scope: &[(Local, Ty)], later: &HashSet<u32>, out: &mut Vec<Point>) {
    // The operands run before the node, from left to right.
    let evaluates_operands = matches!(
        e.kind,
        ExprKind::Call(_)
            | ExprKind::Arith { .. }
            | ExprKind::Cmp { .. }
            | ExprKind::Eq { .. }
            | ExprKind::Not(_)
            | ExprKind::TempRef(_)
            | ExprKind::Shown(_)
            | ExprKind::Unreachable(_)
            | ExprKind::FnCast(_)
            | ExprKind::Ctor { .. }
            | ExprKind::Field { .. }
            | ExprKind::Perform(_)
            | ExprKind::Inject { .. }
            | ExprKind::Remap { .. }
            | ExprKind::Deref { .. }
    );
    if evaluates_operands {
        let ops = operands(e);
        for (i, op) in ops.iter().enumerate() {
            let mut after = later.clone();
            for o in &ops[i + 1..] {
                mentions(o, &mut after);
            }
            visit(op, scope, &after, out);
        }
    }
    if let Some((at, resumes)) = resumes_of(e) {
        out.push(Point {
            span: e.span,
            at,
            resumes,
            result: e.ty.clone(),
            live: scope
                .iter()
                .filter(|(l, _)| later.contains(&l.id))
                .cloned()
                .collect(),
        });
    }
    if evaluates_operands {
        return;
    }
    match &e.kind {
        ExprKind::Block(b) => {
            let mut scope = scope.to_vec();
            for (i, s) in b.stmts.iter().enumerate() {
                let mut after = later.clone();
                for t in &b.stmts[i + 1..] {
                    stmt_mentions(t, &mut after);
                }
                if let Some(t) = &b.tail {
                    mentions(t, &mut after);
                }
                match s {
                    Stmt::Let { init, .. } | Stmt::Var { init, .. } => {
                        visit(init, &scope, &after, out)
                    }
                    Stmt::Assign { value, target, .. } => {
                        after.insert(target.local.id);
                        visit(value, &scope, &after, out)
                    }
                    Stmt::Expr(x) => visit(x, &scope, &after, out),
                    Stmt::Return { value, .. } => {
                        if let Some(v) = value {
                            // Nothing after a `return` runs.
                            visit(v, &scope, &HashSet::new(), out)
                        }
                    }
                    Stmt::While { cond, body, .. } => {
                        // The loop runs again: what it reads is live in it.
                        stmt_mentions(s, &mut after);
                        visit(cond, &scope, &after, out);
                        let inner = Expr {
                            kind: ExprKind::Block(body.clone()),
                            ty: Ty::Unit,
                            span: cond.span,
                        };
                        visit(&inner, &scope, &after, out);
                    }
                }
                if let Stmt::Let { local, ty, .. } | Stmt::Var { local, ty, .. } = s {
                    scope.push((local.clone(), ty.clone()));
                }
            }
            if let Some(t) = &b.tail {
                visit(t, &scope, later, out);
            }
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            let mut after = later.clone();
            mentions(then, &mut after);
            if let Some(o) = otherwise {
                mentions(o, &mut after);
            }
            visit(cond, scope, &after, out);
            visit(then, scope, later, out);
            if let Some(o) = otherwise {
                visit(o, scope, later, out);
            }
        }
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            let mut after = later.clone();
            mentions(b, &mut after);
            visit(a, scope, &after, out);
            visit(b, scope, later, out);
        }
        ExprKind::Match(m) => {
            let mut after = later.clone();
            for a in &m.arms {
                if let Some(g) = &a.guard {
                    mentions(g, &mut after);
                }
                mentions(&a.body, &mut after);
            }
            visit(&m.scrut, scope, &after, out);
            for a in &m.arms {
                let mut inner = scope.to_vec();
                binds(&a.pat, &mut inner);
                if let Some(g) = &a.guard {
                    let mut after = later.clone();
                    mentions(&a.body, &mut after);
                    visit(g, &inner, &after, out);
                }
                visit(&a.body, &inner, later, out);
            }
        }
        // A closure's body is its own function: what it captures is in its
        // scope, and nothing after it in the enclosing body is its concern.
        ExprKind::Closure(c) => {
            let mut inner = scope.to_vec();
            inner.extend(c.params.iter().cloned());
            visit(&c.body, &inner, &HashSet::new(), out);
        }
        ExprKind::Handle(h) => {
            visit(&h.body, scope, later, out);
            let arms = h.direct.iter().chain(&h.aborts).chain(&h.susp);
            for a in arms {
                let mut inner = scope.to_vec();
                for p in &a.pats {
                    binds(p, &mut inner);
                }
                visit(&a.body, &inner, later, out);
            }
            if let Some(r) = &h.ret {
                let mut inner = scope.to_vec();
                binds(&r.pat, &mut inner);
                visit(&r.body, &inner, later, out);
            }
        }
        ExprKind::Budget(b) => {
            let mut after = later.clone();
            mentions(&b.body, &mut after);
            visit(&b.steps, scope, &after, out);
            visit(&b.body, scope, later, out);
        }
        _ => {}
    }
}
