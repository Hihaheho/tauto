//! The last use of a name moves it (`docs/design/rust-backend.md`「使用」): a read
//! that clones a local nothing reads afterwards is a move. Without this, a
//! shared value is cloned at every use, and a list walked by a loop or by
//! recursion is copied at each step.
//!
//! The analysis is a backward liveness over the expressions of a function, in
//! the order Rust evaluates them. What it cannot follow (a closure, a
//! `handle`, a `budget`) is opaque: everything it mentions stays live, and
//! nothing inside it changes.

use std::collections::HashSet;

use crate::*;

type Live = HashSet<u32>;

pub fn elide(pkg: &mut Package) {
    for f in &mut pkg.fns {
        let mut live = Live::new();
        live_in(&mut f.body, &mut live, true);
    }
}

/// The locals the node mentions anywhere, for what is opaque.
fn mentions(e: &Expr, out: &mut Live) {
    e.walk(&mut |x| match &x.kind {
        ExprKind::Read { local, .. } => {
            out.insert(local.id);
        }
        ExprKind::Ref(p) | ExprKind::RefMut(p) => {
            out.insert(p.local.id);
        }
        ExprKind::Call(c) => match &c.callee {
            Callee::Local(l) | Callee::Cont(l) => {
                out.insert(l.id);
            }
            _ => {}
        },
        ExprKind::Closure(c) => {
            out.extend(c.clones.iter().map(|l| l.id));
        }
        ExprKind::Handle(h) => {
            out.extend(h.captures.iter().map(|l| l.id));
            out.extend(h.clones.iter().map(|l| l.id));
        }
        _ => {}
    });
    // `walk` does not enter statements' targets.
    assigned(e, out);
}

fn assigned(e: &Expr, out: &mut Live) {
    e.walk(&mut |x| {
        if let ExprKind::Block(b) = &x.kind {
            block_targets(b, out);
        }
    });
}

fn block_targets(b: &Block, out: &mut Live) {
    for s in &b.stmts {
        match s {
            Stmt::Assign { target, .. } => {
                out.insert(target.local.id);
            }
            Stmt::While { body, .. } => block_targets(body, out),
            _ => {}
        }
    }
}

/// Makes `e` the expression it is after the elision, and `live` the set of
/// locals live before it, given the ones live after it.
fn live_in(e: &mut Expr, live: &mut Live, mutate: bool) {
    match &mut e.kind {
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Text(_) => {}
        ExprKind::FnValue { .. } => {}
        ExprKind::Read { local, how } => {
            if mutate
                && *how == Use::Clone
                && local.repr == Repr::Plain
                && !live.contains(&local.id)
            {
                *how = Use::Move;
            }
            live.insert(local.id);
        }
        ExprKind::Ref(p) | ExprKind::RefMut(p) => {
            live.insert(p.local.id);
        }
        ExprKind::Call(c) => {
            match &c.callee {
                Callee::Local(l) | Callee::Cont(l) => {
                    live.insert(l.id);
                }
                _ => {}
            }
            for a in c.args.iter_mut().rev() {
                live_in(a, live, mutate);
            }
            if let Callee::Value(f) = &mut c.callee {
                live_in(f, live, mutate);
            }
        }
        ExprKind::Arith { args, .. } | ExprKind::Cmp { args, .. } | ExprKind::Eq { args, .. } => {
            for a in args.iter_mut().rev() {
                live_in(a, live, mutate);
            }
        }
        ExprKind::Not(a)
        | ExprKind::TempRef(a)
        | ExprKind::Shown(a)
        | ExprKind::Unreachable(a)
        | ExprKind::FnCast(a) => live_in(a, live, mutate),
        ExprKind::Inject { value, .. }
        | ExprKind::Remap { value, .. }
        | ExprKind::Member { value, .. }
        | ExprKind::Deref { value, .. } => live_in(value, live, mutate),
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            // `b` may not run.
            let after = live.clone();
            live_in(b, live, mutate);
            live.extend(after);
            live_in(a, live, mutate);
        }
        ExprKind::Ctor { fields, .. } => {
            for (_, f) in fields.iter_mut().rev() {
                live_in(f, live, mutate);
            }
        }
        ExprKind::Product { members, .. } => {
            for m in members.iter_mut().rev() {
                live_in(m, live, mutate);
            }
        }
        ExprKind::Field { base, .. } => live_in(base, live, mutate),
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            let after = live.clone();
            live_in(then, live, mutate);
            let mut other = after;
            if let Some(o) = otherwise {
                live_in(o, &mut other, mutate);
            }
            live.extend(other);
            live_in(cond, live, mutate);
        }
        ExprKind::Block(b) => live_block(b, live, mutate),
        ExprKind::Match(m) => {
            let after = live.clone();
            let mut union = Live::new();
            // The arms that have a guard may fall to a later one.
            let mut arm_lives = Vec::new();
            for arm in m.arms.iter_mut() {
                let mut l = after.clone();
                live_in(&mut arm.body, &mut l, mutate);
                arm_lives.push(l);
            }
            for l in &arm_lives {
                union.extend(l.iter().copied());
            }
            for (arm, l) in m.arms.iter_mut().zip(arm_lives.iter_mut()) {
                if let Some(g) = &mut arm.guard {
                    let mut gl = union.clone();
                    gl.extend(after.iter().copied());
                    live_in(g, &mut gl, mutate);
                    l.extend(gl);
                }
                // A name the pattern binds is new in each run of the arm.
                let mut bound = Vec::new();
                binds(&arm.pat, &mut bound);
                for (b, _) in &bound {
                    l.remove(b);
                }
            }
            // `match xs` of a name nobody reads again where an arm takes the
            // value apart: Rust moves the parts out, and an arm that takes
            // nothing leaves `xs` as it is.
            if mutate
                && let ExprKind::Read { local, how } = &mut m.scrut.kind
                && *how == Use::Clone
                && local.repr == Repr::Plain
                && m.arms.iter().zip(&arm_lives).all(|(arm, l)| {
                    let mut bound = Vec::new();
                    binds(&arm.pat, &mut bound);
                    !bound.iter().any(|(_, ty)| !is_copy(ty)) || !l.contains(&local.id)
                })
            {
                *how = Use::Move;
            }
            *live = after;
            for l in arm_lives {
                live.extend(l);
            }
            live_in(&mut m.scrut, live, mutate);
        }
        ExprKind::Closure(_) | ExprKind::Perform(_) | ExprKind::Handle(_) | ExprKind::Budget(_) => {
            if let ExprKind::Perform(p) = &mut e.kind {
                for a in p.args.iter_mut().rev() {
                    live_in(a, live, mutate);
                }
            } else {
                mentions(e, live);
            }
        }
    }
}

fn binds(p: &Pat, out: &mut Vec<(u32, Ty)>) {
    match p {
        Pat::Bind(l, t) => out.push((l.id, t.clone())),
        Pat::Ctor { fields, .. } => {
            for f in fields {
                binds(f, out);
            }
        }
        _ => {}
    }
}

fn is_copy(t: &Ty) -> bool {
    matches!(
        t,
        Ty::Int(_) | Ty::Bool | Ty::Unit | Ty::Never | Ty::Float | Ty::Float32 | Ty::Ref(_)
    ) && !matches!(t, Ty::Int(Width::Nat))
}

fn live_block(b: &mut Block, live: &mut Live, mutate: bool) {
    if let Some(t) = &mut b.tail {
        live_in(t, live, mutate);
    }
    for s in b.stmts.iter_mut().rev() {
        match s {
            Stmt::Let { local, init, .. } | Stmt::Var { local, init, .. } => {
                live.remove(&local.id);
                live_in(init, live, mutate);
            }
            Stmt::Assign { target, value, .. } => {
                if target.path.is_empty() {
                    live.remove(&target.local.id);
                } else {
                    live.insert(target.local.id);
                }
                live_in(value, live, mutate);
            }
            Stmt::Expr(e) => live_in(e, live, mutate),
            Stmt::Return { value, .. } => {
                live.clear();
                if let Some(v) = value {
                    live_in(v, live, mutate);
                }
            }
            Stmt::While { cond, body, .. } => {
                // The set live at the head of the loop, until it settles.
                let exit = live.clone();
                let mut head = exit.clone();
                loop {
                    let mut l = head.clone();
                    live_block(&mut body.clone(), &mut l, false);
                    l.extend(exit.iter().copied());
                    live_in(&mut cond.clone(), &mut l, false);
                    l.extend(head.iter().copied());
                    if l.len() == head.len() {
                        break;
                    }
                    head = l;
                }
                if mutate {
                    let mut l = head.clone();
                    live_block(body, &mut l, true);
                    l.extend(exit.iter().copied());
                    live_in(cond, &mut l, true);
                }
                *live = head;
            }
        }
    }
}
