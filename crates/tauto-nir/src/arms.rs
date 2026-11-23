//! The arms of an operation for every instance (`∀ T. give<T>(a)`), written
//! once for each type the program performs the operation with.
//!
//! Lowering gives such an arm's operation generic a type parameter of its
//! own (`skolem`). `instantiate` finds, for each arm, the payload types the
//! program performs its operation with that its payload type takes, and
//! puts in its place one copy of the arm for each, with the generic
//! replaced, in the order the types are first performed. After it every arm
//! the program can reach is written at the types it runs at. An arm whose
//! generic no `perform` fixes is left out: no `perform` of the program
//! reaches it.

use std::collections::HashMap;

use crate::*;

const PREFIX: &str = "?arm";

/// The name of the type parameter that stands for an arm's operation
/// generic with the checker's serial `serial`.
pub fn skolem(serial: usize) -> String {
    format!("{PREFIX}{serial}")
}

/// Whether `name` is the type parameter of an arm's operation generic.
pub fn is_skolem(name: &str) -> bool {
    name.starts_with(PREFIX)
}

fn has_skolem(t: &Ty) -> bool {
    let mut found = false;
    t.clone().each_mut(&mut |t| {
        if matches!(t, Ty::Param(p) if is_skolem(p)) {
            found = true;
        }
    });
    found
}

/// Writes each arm for every instance once for each payload type it takes.
pub fn instantiate(pkg: &mut Package) {
    let mut payloads: HashMap<OpIndex, Vec<Vec<Ty>>> = HashMap::new();
    for f in &pkg.fns {
        f.body.walk_with_handlers(&mut |x| {
            if let ExprKind::Perform(p) = &x.kind {
                let tys: Vec<Ty> = p.args.iter().map(|a| a.ty.clone()).collect();
                if tys.iter().any(has_skolem) {
                    return;
                }
                let seen = payloads.entry(p.op).or_default();
                if !seen.contains(&tys) {
                    seen.push(tys);
                }
            }
        });
    }
    for f in &mut pkg.fns {
        handles(&mut f.body, &payloads);
    }
}

fn handles(e: &mut Expr, payloads: &HashMap<OpIndex, Vec<Vec<Ty>>>) {
    if let ExprKind::Handle(h) = &mut e.kind {
        for arms in [&mut h.direct, &mut h.aborts, &mut h.susp] {
            let old = std::mem::take(arms);
            for a in old {
                arms.extend(copies(a, payloads));
            }
        }
    }
    match &mut e.kind {
        ExprKind::Handle(h) => {
            handles(&mut h.body, payloads);
            if let Some(r) = &mut h.ret {
                handles(&mut r.body, payloads);
            }
            for a in h.direct.iter_mut().chain(&mut h.aborts).chain(&mut h.susp) {
                if let Some(g) = &mut a.guard {
                    handles(g, payloads);
                }
                handles(&mut a.body, payloads);
            }
        }
        _ => each_child_mut(e, &mut |c| handles(c, payloads)),
    }
}

/// The arm once for each payload type of its operation that its own payload
/// type takes: the arm as it is when it has no generic, and none when no
/// payload type fits.
fn copies(arm: OpArm, payloads: &HashMap<OpIndex, Vec<Vec<Ty>>>) -> Vec<OpArm> {
    if !arm.params.iter().any(has_skolem) {
        return vec![arm];
    }
    let mut out: Vec<OpArm> = Vec::new();
    for p in payloads.get(&arm.op).into_iter().flatten() {
        let mut env = HashMap::new();
        if p.len() != arm.params.len()
            || !arm.params.iter().zip(p).all(|(a, b)| unify(a, b, &mut env))
        {
            continue;
        }
        // The checked signature the arm carries names the generic by a
        // parameter of its own: the same payload fixes it.
        if let Some(i) = &arm.instance
            && i.params.len() == p.len()
        {
            for (a, b) in i.params.iter().zip(p) {
                unify(a, b, &mut env);
            }
        }
        let mut copy = arm.clone();
        copy.instantiated = true;
        copy.tys_mut(&mut |t| {
            if let Ty::Param(n) = t
                && let Some(x) = env.get(n)
            {
                *t = x.clone();
            }
        });
        if !out.iter().any(|o| o.params == copy.params) {
            out.push(copy);
        }
    }
    // No `perform` of the program reaches an arm none of whose payload
    // types fits: it is left out, as there is no type to write it at.
    out
}

/// Whether `actual` is `pat` with each arm generic in it replaced, adding
/// what each stands for to `env`.
fn unify(pat: &Ty, actual: &Ty, env: &mut HashMap<String, Ty>) -> bool {
    use Ty::*;
    match (pat, actual) {
        (Param(n), _) if is_skolem(n) => match env.get(n) {
            Some(t) => t == actual,
            None => {
                env.insert(n.clone(), actual.clone());
                true
            }
        },
        (Vec(a), Vec(b))
        | (Array(a), Array(b))
        | (Slice(a), Slice(b))
        | (Option(a), Option(b))
        | (Ref(a), Ref(b))
        | (RefMut(a), RefMut(b))
        | (Info(a), Info(b))
        | (BudgetAnswer(a), BudgetAnswer(b)) => unify(a, b, env),
        (SharedVar(x, a), SharedVar(y, b)) => x == y && unify(a, b, env),
        (Result(a, c), Result(b, d))
        | (Pair(a, c), Pair(b, d)) => unify(a, b, env) && unify(c, d, env),
        (Data(n, xs), Data(m, ys)) => n == m && unify_all(xs, ys, env),
        (Std(n, xs), Std(m, ys)) => n == m && unify_all(xs, ys, env),
        (Fn(f), Fn(g)) => {
            f.kind == g.kind
                && f.tier == g.tier
                && unify_all(&f.params, &g.params, env)
                && unify(&f.ret, &g.ret, env)
        }
        _ => pat == actual,
    }
}

fn unify_all(xs: &[Ty], ys: &[Ty], env: &mut HashMap<String, Ty>) -> bool {
    xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| unify(x, y, env))
}

/// Calls `f` on each expression directly inside `e` (statements included).
fn each_child_mut(e: &mut Expr, f: &mut dyn FnMut(&mut Expr)) {
    match &mut e.kind {
        ExprKind::Block(b) => {
            for s in &mut b.stmts {
                match s {
                    Stmt::Let { init, .. } | Stmt::Var { init, .. } => f(init),
                    Stmt::Assign { value, .. } => f(value),
                    Stmt::Expr(x) => f(x),
                    Stmt::While { cond, body, .. } => {
                        f(cond);
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
                        f(&mut b);
                        if let ExprKind::Block(nb) = b.kind {
                            *body = nb;
                        }
                    }
                    Stmt::Return { value, .. } => {
                        if let Some(v) = value {
                            f(v);
                        }
                    }
                }
            }
            if let Some(t) = &mut b.tail {
                f(t);
            }
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            f(cond);
            f(then);
            if let Some(o) = otherwise {
                f(o);
            }
        }
        ExprKind::Match(m) => {
            f(&mut m.scrut);
            for a in &mut m.arms {
                if let Some(g) = &mut a.guard {
                    f(g);
                }
                f(&mut a.body);
            }
        }
        ExprKind::Closure(c) => f(&mut c.body),
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            f(a);
            f(b);
        }
        ExprKind::Budget(b) => {
            f(&mut b.steps);
            f(&mut b.body);
        }
        _ => {
            for op in e.operands_mut() {
                f(op);
            }
        }
    }
}
