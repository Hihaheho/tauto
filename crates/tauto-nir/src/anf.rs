//! A-normal form: every operand that computes a value is given a name
//! first.
//!
//! After `normalize`, the operands of a call, an operation, a constructor,
//! an arithmetic or comparison node, a field read, an injection and the
//! scrutinee of a `match` that takes its value are atoms (a literal, a read
//! of a local, a function value) or places (a borrow, a read of a place).
//! Each value is bound by a `let` in the order the operands are evaluated,
//! in a block around the node that uses it, so the order of evaluation and
//! the life of each temporary are written in the tree: a backend without a
//! host language to order them (a native one) reads them from here.
//!
//! The pass keeps the meaning: a value moves into its temporary and from
//! there into the node, once. It names nothing inside a branch that is not
//! always taken (`&&`, `||`, `if`, the arms), and nothing whose type is still
//! to be inferred.

use crate::*;

/// Puts every function of the package in A-normal form.
pub fn normalize(pkg: &mut Package) {
    let mut next = first_free_local(pkg);
    for f in &mut pkg.fns {
        expr(&mut f.body, &mut next);
    }
}

/// Puts the body of one function in A-normal form: for a reader that takes
/// a few functions of a large package, which `normalize` would walk whole.
/// The names it gives are free in this function.
pub fn normalize_fn(f: &mut FnInst) {
    let mut next = first_free_in(&format!("{f:?}"));
    expr(&mut f.body, &mut next);
}

/// Whether `e` is in A-normal form, with the path of the first operand that
/// is not, for a test to show.
pub fn check(e: &Expr) -> Result<(), String> {
    let mut found = None;
    e.walk(&mut |x| {
        if found.is_some() {
            return;
        }
        let mut x = x.clone();
        let what = kind(&x.kind);
        for (i, op) in operands(&mut x).into_iter().enumerate() {
            if names(op) {
                found = Some(format!("operand {i} of a {what} at {:?}", op.span));
                break;
            }
        }
    });
    match found {
        Some(f) => Err(f),
        None => Ok(()),
    }
}

fn kind(k: &ExprKind) -> &'static str {
    match k {
        ExprKind::Call(_) => "call",
        ExprKind::Ctor { .. } => "constructor",
        ExprKind::Match(_) => "match",
        ExprKind::If { .. } => "if",
        ExprKind::Block(_) => "block",
        ExprKind::Perform(_) => "perform",
        ExprKind::Handle(_) => "handle",
        _ => "expression",
    }
}

/// The local ids are unique in a package; the first one no local has.
pub(crate) fn first_free_local(pkg: &Package) -> u32 {
    first_free_in(&format!("{pkg:?}"))
}

fn first_free_in(text: &str) -> u32 {
    let mut max = 0;
    for part in text.split("Local { id: ").skip(1) {
        let n: String = part.chars().take_while(|c| c.is_ascii_digit()).collect();
        if let Ok(n) = n.parse::<u32>() {
            max = max.max(n);
        }
    }
    max + 1
}

/// The operands this pass names: those `Expr::operands_mut` gives, and the
/// scrutinee of a `match` on a value.
fn operands(e: &mut Expr) -> Vec<&mut Expr> {
    if matches!(&e.kind, ExprKind::Match(m) if !m.by_ref) {
        let ExprKind::Match(m) = &mut e.kind else {
            unreachable!()
        };
        return vec![&mut m.scrut];
    }
    e.operands_mut()
}

/// Whether an operand computes a value that the pass binds to a name.
fn names(e: &Expr) -> bool {
    if e.ty.has_arm_generic() {
        return false;
    }
    match &e.kind {
        // Atoms.
        ExprKind::Declaration(_)
        | ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Text(_)
        | ExprKind::Read { .. }
        | ExprKind::FnValue { .. } => false,
        // Places and borrows: naming them would move or copy what they
        // point at.
        ExprKind::Ref(_) | ExprKind::RefMut(_) | ExprKind::TempRef(_) => false,
        ExprKind::Field {
            how: Use::Place, ..
        }
        | ExprKind::Deref {
            how: Use::Place, ..
        } => false,
        // A field read of a place is a path, not a computation.
        ExprKind::Field { base, .. } => !is_path(base),
        ExprKind::Closure(c) => !c.borrowed,
        _ => true,
    }
}

/// Whether an operand reads the current value of a local: a read or a field
/// read by value, which a later operand may change.
fn reads(e: &Expr) -> bool {
    !e.ty.has_arm_generic()
        && match &e.kind {
            ExprKind::Read { how, .. } => *how != Use::Place,
            ExprKind::Field { how, base, .. } | ExprKind::Deref { how, value: base } => {
                *how != Use::Place && is_path(base)
            }
            _ => false,
        }
}

fn is_path(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Read { .. } | ExprKind::Ref(_) | ExprKind::RefMut(_) => true,
        ExprKind::Field { base, .. } | ExprKind::Deref { value: base, .. } => is_path(base),
        _ => false,
    }
}

/// Normalizes `e` in place: the expression itself stays where it is, and
/// what is evaluated first returns as statements to run before it.
fn expr(e: &mut Expr, next: &mut u32) {
    let prefix = lift(e, next);
    wrap(e, prefix);
}

/// `prefix` then `e`, as one expression.
fn wrap(e: &mut Expr, prefix: Vec<Stmt>) {
    if prefix.is_empty() {
        return;
    }
    let (ty, span) = (e.ty.clone(), e.span);
    let inner = std::mem::replace(
        e,
        Expr {
            kind: ExprKind::Unit,
            ty: Ty::Unit,
            span,
        },
    );
    *e = Expr {
        kind: ExprKind::Block(Block {
            stmts: prefix,
            tail: Some(Box::new(inner)),
        }),
        ty,
        span,
    };
}

/// Normalizes the parts of `e`, and returns the statements that bind its
/// operands, to be run before it in the order written. Nested operands go
/// to the same list, so a deep term (a long list) gives one flat block.
fn lift(e: &mut Expr, next: &mut u32) -> Vec<Stmt> {
    branches(e, next);
    let mut ops = operands(e);
    let prefixes: Vec<Vec<Stmt>> = ops.iter_mut().map(|op| lift(op, next)).collect();
    // An operand runs code before the node when it is named or has a
    // prefix. A read before such an operand is named too, so that it still
    // sees the local as it was before that code (which may assign it).
    let runs: Vec<bool> = ops
        .iter()
        .zip(&prefixes)
        .map(|(op, p)| names(op) || !p.is_empty())
        .collect();
    let mut out = Vec::new();
    for (i, (op, prefix)) in ops.iter_mut().zip(prefixes).enumerate() {
        out.extend(prefix);
        let later = runs[i + 1..].iter().any(|r| *r);
        if names(op) || (later && reads(op)) {
            out.push(bind(op, next));
        }
    }
    out
}

/// `let t = op`, leaving a read of `t` where `op` was.
fn bind(op: &mut Expr, next: &mut u32) -> Stmt {
    let local = Local {
        id: *next,
        name: "anf".into(),
        repr: Repr::Plain,
    };
    *next += 1;
    let read = Expr {
        kind: ExprKind::Read {
            local: local.clone(),
            how: Use::Move,
        },
        ty: op.ty.clone(),
        span: op.span,
    };
    let init = std::mem::replace(op, read);
    Stmt::Let {
        stack: false,
        local,
        ty: init.ty.clone(),
        span: init.span,
        init,
    }
}

/// Normalizes the parts of `e` that are not its operands: each runs only
/// when it is reached, so what it binds stays inside it.
fn branches(e: &mut Expr, next: &mut u32) {
    match &mut e.kind {
        ExprKind::Block(b) => block(b, next),
        ExprKind::Match(m) => {
            if m.by_ref {
                expr(&mut m.scrut, next);
            }
            for a in &mut m.arms {
                if let Some(g) = &mut a.guard {
                    expr(g, next);
                }
                expr(&mut a.body, next);
            }
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            expr(cond, next);
            expr(then, next);
            if let Some(o) = otherwise {
                expr(o, next);
            }
        }
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            expr(a, next);
            expr(b, next);
        }
        ExprKind::Budget(b) => {
            expr(&mut b.steps, next);
            expr(&mut b.body, next);
        }
        ExprKind::Closure(c) => expr(&mut c.body, next),
        ExprKind::Handle(h) => {
            expr(&mut h.body, next);
            if let Some(r) = &mut h.ret {
                expr(&mut r.body, next);
            }
            for a in h.direct.iter_mut().chain(&mut h.aborts).chain(&mut h.susp) {
                if let Some(g) = &mut a.guard {
                    expr(g, next);
                }
                expr(&mut a.body, next);
            }
        }
        _ => {}
    }
}

/// Each statement's bindings stay inside that statement, in a block around
/// its expression, so a temporary is dropped at the end of its statement
/// as the ownership rules ask.
fn block(b: &mut Block, next: &mut u32) {
    for s in &mut b.stmts {
        match s {
            Stmt::Let { init, .. } | Stmt::Var { init, .. } => expr(init, next),
            Stmt::Assign { value, .. } => expr(value, next),
            Stmt::Expr(e) => expr(e, next),
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    expr(v, next);
                }
            }
            Stmt::While { cond, body, .. } => {
                expr(cond, next);
                block(body, next);
            }
        }
    }
    if let Some(t) = &mut b.tail {
        expr(t, next);
    }
}
