//! Operations that resume once but answer like `direct` ones.
//!
//! An operation of `resume 1` or `resume <=1` runs on tier `O`: each function
//! that performs it becomes a future, and each `perform` hands its arguments
//! to the handler and waits for the answer. When every arm of the operation
//! in the program is of the tail form of a `direct` arm (`k(e)` ends each
//! path, and `k` is nowhere else) and performs only `direct` operations, the
//! arm means the same as the `direct` arm `T[e/k(e)]`: it computes the
//! answer and resumes once, in the same order. Such an operation is lowered
//! as `direct`, on tier `S`.
//!
//! The checker is not changed: what it accepted for `resume 1` (the borrow an
//! answer carries among it) holds of the program as written, and the program
//! lowered runs the same steps.

use std::collections::HashSet;

use crate::rows::RowReport;
use crate::types::Quant;
use tauto_surface::surface::walk::{self, Node};
use tauto_surface::surface::{Handler, Name, Program, Stmt, SurfaceTerm, TermKind};

/// Marks as `Quant::Direct` in `rows.quants` each operation of `resume 1` or
/// `resume <=1` whose every arm is a tail form that performs only `direct`
/// operations.
pub(crate) fn promote(program: &Program, rows: &mut RowReport) {
    let mut arms: Vec<(&Name, Option<&Name>, &SurfaceTerm, Option<&SurfaceTerm>)> = Vec::new();
    for s in &program.stmts {
        stmt(s, &mut |n| {
            let Node::Term(t) = n else { return };
            match &*t.kind {
                TermKind::Handle { handlers, .. } => {
                    for h in handlers {
                        if let Handler::Operation {
                            effect,
                            cont,
                            guard,
                            body,
                            ..
                        } = h
                        {
                            arms.push((effect, cont.as_ref(), body, guard.as_ref()));
                        }
                    }
                }
                _ => {}
            }
        });
    }
    let once = |q: Option<&Quant>| matches!(q, Some(Quant::One | Quant::AtMostOne));
    // An operation with no arm is left as it is: nothing is known of it.
    let mut candidates: HashSet<Name> = arms
        .iter()
        .map(|(e, ..)| (*e).clone())
        .filter(|e| once(rows.quants.get(e)) && !e.row_variable().is_some())
        .collect();
    // An arm may perform an operation promoted here too, so drop the
    // candidates whose arms fail until none does.
    loop {
        let direct = |e: &Name, c: &HashSet<Name>| {
            rows.quants.get(e) == Some(&Quant::Direct) || c.contains(e)
        };
        let failed: Vec<Name> = arms
            .iter()
            .filter(|(e, ..)| candidates.contains(*e))
            .filter(|(_, k, body, guard)| {
                let Some(k) = k else { return true };
                if !tauto_surface::direct::is_tail_form(body, k) {
                    return true;
                }
                let mut ok = true;
                let mut check = |t: &SurfaceTerm| {
                    walk::values(t, &mut |n| match n {
                        Node::Stmt(Stmt::While { .. } | Stmt::For { .. } | Stmt::Loop { .. }) => {
                            ok = false
                        }
                        // The tail `k(e)` itself is the resumption, not a call.
                        Node::Term(t)
                            if matches!(&*t.kind, TermKind::App { function, .. }
                                if matches!(&*function.kind, TermKind::Var(v) if v == *k)) => {}
                        Node::Term(t)
                            if matches!(
                                &*t.kind,
                                TermKind::App { .. } | TermKind::Perform { .. }
                            ) =>
                        {
                            match rows.calls.get(&t.id()) {
                                Some(row) => {
                                    if !row.iter().all(|e| direct(e, &candidates)) {
                                        ok = false;
                                    }
                                }
                                None => {}
                            }
                        }
                        Node::Term(t) if matches!(&*t.kind, TermKind::Handle { .. }) => ok = false,
                        _ => {}
                    })
                };
                check(body);
                if let Some(g) = guard {
                    check(g);
                }
                !ok
            })
            .map(|(e, ..)| (*e).clone())
            .collect();
        if failed.is_empty() {
            break;
        }
        for e in failed {
            candidates.remove(&e);
        }
    }
    for e in candidates {
        rows.quants.insert(e, Quant::Direct);
    }
}

fn stmt<'a>(s: &'a Stmt, f: &mut impl FnMut(Node<'a>)) {
    match s {
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            items.iter().for_each(|i| stmt(i, f))
        }
        Stmt::Attributed { stmt: inner, .. } => stmt(inner, f),
        _ => walk::values_stmt(s, f),
    }
}
