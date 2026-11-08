//! A function returning a `Nat` whose calls to itself add a constant to the
//! result, as `List::length`'s `Succ(length(t))` does, given an accumulator.
//!
//! ```text
//! fn length(l) { match l { Nil => 0, Cons(_, t) => length(t) + 1 } }
//! ```
//!
//! becomes a function that keeps the sum so far in a new last parameter, and
//! the function itself calls it with `0`:
//!
//! ```text
//! fn length(l) { length__acc(l, 0) }
//! fn length__acc(l, acc) { match l { Nil => acc + 0, Cons(_, t) => length__acc(t, acc + 1) } }
//! ```
//!
//! The call in `length__acc` is then in tail position, and `tail.rs` makes
//! it a jump: the recursion does not grow the stack with the input. Nothing
//! changes in what is checked; this is how the program is compiled, as
//! `tail.rs` is.
//!
//! The sum is the same because `Nat` addition is associative and
//! commutative and never fails. A function is rewritten only when
//! - it returns a `Nat` and is not of the M tier;
//! - every call to itself (at its own type arguments) is an operand of a `+`
//!   in tail position (as in `tail.rs`), and the other operand is a literal
//!   or a name: evaluating it before the call instead of after it changes
//!   nothing;
//! - nothing else names it: no other call to itself, no value of it, and no
//!   handler in its body;
//! - every `return` in its body is in tail position, so every value it
//!   returns passes through the accumulator.

use crate::{
    Arith, Block, CallNode, Callee, Expr, ExprKind, FnInst, Local, Package, Param, Repr, Stmt,
    Tick, Tier, Ty, Use, Width,
};

/// Rewrites every function of the shape above; `fresh` gives a new local.
pub fn introduce(pkg: &mut Package, fresh: &mut dyn FnMut(&str, Repr) -> Local) {
    let candidates: Vec<usize> = (0..pkg.fns.len())
        .filter(|&i| accumulates(&pkg.fns[i]))
        .collect();
    for i in candidates {
        let new_id = pkg.fns.len();
        let acc = fresh("acc", Repr::Plain);
        let f = &mut pkg.fns[i];
        let mut body = std::mem::replace(
            &mut f.body,
            Expr {
                kind: ExprKind::Unit,
                ty: Ty::Unit,
                span: f.span,
            },
        );
        let shape = Shape {
            id: f.id,
            generics: f.generics.iter().map(|(g, _)| g.clone()).collect(),
        };
        shape.rewrite(&mut body, &acc, new_id);
        let targs: Vec<Ty> = shape
            .generics
            .iter()
            .map(|g| Ty::Param(g.clone()))
            .collect();
        let mut args: Vec<Expr> = f
            .params
            .iter()
            .map(|p| Expr {
                kind: ExprKind::Read {
                    local: p.local.clone(),
                    how: Use::Move,
                },
                ty: p.ty.clone(),
                span: f.span,
            })
            .collect();
        args.push(nat(ExprKind::Int(0), f.span));
        f.body = Expr {
            kind: ExprKind::Call(Box::new(CallNode {
                callee: Callee::Inst(new_id),
                args,
                tier: f.tier,
                targs,
                tick: Tick::None,
                recur: false,
                span: f.span,
            })),
            ty: f.ret.clone(),
            span: f.span,
        };
        let mut params = f.params.clone();
        params.push(Param {
            local: acc,
            ty: Ty::Int(Width::Nat),
        });
        let inner = FnInst {
            id: new_id,
            source: f.source.clone(),
            rust_name: format!("{}__acc", f.rust_name),
            tier: f.tier,
            generics: f.generics.clone(),
            params,
            ret: f.ret.clone(),
            body,
            span: f.span,
        };
        pkg.fns.push(inner);
    }
}

fn nat(kind: ExprKind, span: crate::Span) -> Expr {
    Expr {
        kind,
        ty: Ty::Int(Width::Nat),
        span,
    }
}

fn accumulates(f: &FnInst) -> bool {
    if f.tier == Tier::M || f.ret != Ty::Int(Width::Nat) {
        return false;
    }
    let shape = Shape {
        id: f.id,
        generics: f.generics.iter().map(|(g, _)| g.clone()).collect(),
    };
    let (mut named, mut returns, mut handles) = (0usize, 0usize, false);
    f.body.walk(&mut |e| match &e.kind {
        ExprKind::Call(c) if matches!(c.callee, Callee::Inst(i) if i == f.id) => named += 1,
        ExprKind::FnValue { inst, .. } if *inst == f.id => named += 1,
        ExprKind::Handle(_) => handles = true,
        ExprKind::Block(b) => {
            returns += b
                .stmts
                .iter()
                .filter(|s| matches!(s, Stmt::Return { .. }))
                .count()
        }
        _ => {}
    });
    if handles || named == 0 {
        return false;
    }
    let mut seen = Seen::default();
    shape.count(&f.body, &mut seen);
    seen.calls == named && seen.returns == returns
}

#[derive(Default)]
struct Seen {
    calls: usize,
    returns: usize,
}

struct Shape {
    id: usize,
    generics: Vec<String>,
}

impl Shape {
    fn is_self(&self, e: &Expr) -> bool {
        let ExprKind::Call(c) = &e.kind else {
            return false;
        };
        matches!(c.callee, Callee::Inst(i) if i == self.id)
            && c.targs.len() == self.generics.len()
            && c.targs
                .iter()
                .zip(&self.generics)
                .all(|(t, g)| matches!(t, Ty::Param(p) if p == g))
    }

    /// The index of the call to itself among the operands of a `Nat` `+`
    /// whose other operand is a literal or a name.
    fn added(&self, e: &Expr) -> Option<usize> {
        let ExprKind::Arith {
            op: Arith::Add,
            args,
            width: Width::Nat,
        } = &e.kind
        else {
            return None;
        };
        let [a, b] = args.as_slice() else {
            return None;
        };
        let simple = |e: &Expr| matches!(e.kind, ExprKind::Int(_) | ExprKind::Read { .. });
        if self.is_self(a) && simple(b) && self.args_free(a) {
            Some(0)
        } else if self.is_self(b) && simple(a) && self.args_free(b) {
            Some(1)
        } else {
            None
        }
    }

    /// The arguments of a call to itself do not name it again.
    fn args_free(&self, call: &Expr) -> bool {
        let ExprKind::Call(c) = &call.kind else {
            return false;
        };
        let mut free = true;
        for a in &c.args {
            a.walk(&mut |e| match &e.kind {
                ExprKind::Call(c) if matches!(c.callee, Callee::Inst(i) if i == self.id) => {
                    free = false
                }
                ExprKind::FnValue { inst, .. } if *inst == self.id => free = false,
                _ => {}
            });
        }
        free
    }

    fn count(&self, e: &Expr, seen: &mut Seen) {
        if self.added(e).is_some() {
            seen.calls += 1;
            return;
        }
        match &e.kind {
            ExprKind::Block(b) => {
                for s in &b.stmts {
                    if let Stmt::Return { value: Some(v), .. } = s {
                        seen.returns += 1;
                        self.count(v, seen);
                    }
                }
                if let Some(t) = &b.tail {
                    self.count(t, seen);
                }
            }
            ExprKind::Match(m) => m.arms.iter().for_each(|a| self.count(&a.body, seen)),
            ExprKind::If {
                then, otherwise, ..
            } => {
                self.count(then, seen);
                if let Some(o) = otherwise {
                    self.count(o, seen);
                }
            }
            _ => {}
        }
    }

    fn rewrite(&self, e: &mut Expr, acc: &Local, new_id: usize) {
        if let Some(i) = self.added(e) {
            let ExprKind::Arith { args, .. } = &mut e.kind else {
                unreachable!()
            };
            let mut call = args.remove(i);
            let k = args.remove(0);
            let ExprKind::Call(c) = &mut call.kind else {
                unreachable!()
            };
            c.callee = Callee::Inst(new_id);
            c.args.push(nat(
                ExprKind::Arith {
                    op: Arith::Add,
                    args: vec![read(acc, e.span), k],
                    width: Width::Nat,
                },
                e.span,
            ));
            *e = call;
            return;
        }
        match &mut e.kind {
            ExprKind::Block(b) => {
                self.rewrite_block(b, acc, new_id);
                return;
            }
            ExprKind::Match(m) => {
                for a in &mut m.arms {
                    self.rewrite(&mut a.body, acc, new_id);
                }
                return;
            }
            ExprKind::If {
                then, otherwise, ..
            } => {
                self.rewrite(then, acc, new_id);
                if let Some(o) = otherwise {
                    self.rewrite(o, acc, new_id);
                }
                return;
            }
            _ => {}
        }
        // A value the function returns: it is added to the sum so far. One
        // that never comes back (`Never`) is left as it is.
        if e.ty == Ty::Never {
            return;
        }
        let span = e.span;
        if matches!(e.kind, ExprKind::Int(0)) {
            *e = read(acc, span);
            return;
        }
        let v = std::mem::replace(e, nat(ExprKind::Unit, span));
        *e = nat(
            ExprKind::Arith {
                op: Arith::Add,
                args: vec![read(acc, span), v],
                width: Width::Nat,
            },
            span,
        );
    }

    fn rewrite_block(&self, b: &mut Block, acc: &Local, new_id: usize) {
        for s in &mut b.stmts {
            if let Stmt::Return { value: Some(v), .. } = s {
                self.rewrite(v, acc, new_id);
            }
        }
        if let Some(t) = &mut b.tail {
            self.rewrite(t, acc, new_id);
        }
    }
}

fn read(acc: &Local, span: crate::Span) -> Expr {
    nat(
        ExprKind::Read {
            local: acc.clone(),
            how: Use::Move,
        },
        span,
    )
}
