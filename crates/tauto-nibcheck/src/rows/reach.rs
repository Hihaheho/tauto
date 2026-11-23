//! Reachability of row errors from a function: the expander and expansion
//! lowering refuse the same reachable failures.

use std::collections::{HashMap, HashSet};

use tauto_message::Message;
use tauto_surface::surface::{FnDecl, Handler, Program, Stmt, SurfaceTerm, TermKind, walk};

use super::RowReport;
use crate::lin::pattern_names;
use crate::surface::Name;

/// A function of the library that `function` reaches whose declared row does
/// not hold what it performs, with the call path and the row checker's reason.
/// The macro stage runs the function, so it holds the same rows a run does.
pub fn row_error_reached(
    program: &Program,
    rows: &RowReport,
    function: &Name,
) -> Option<(Vec<String>, String)> {
    if rows.errors.is_empty() {
        return None;
    }
    let fns: HashMap<&Name, &FnDecl> = program
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Fn(f) => Some((&f.name, f)),
            _ => None,
        })
        .collect();
    let mut seen = HashSet::new();
    let mut stack = vec![vec![function.clone()]];
    while let Some(path) = stack.pop() {
        let here = path.last().expect("a path has a name").clone();
        if !seen.insert(here.clone()) {
            continue;
        }
        let Some(f) = fns.get(&here) else {
            continue;
        };
        let (lo, hi) = (f.span.start, f.body.span.end.max(f.span.end));
        if let Some(e) = rows
            .errors
            .iter()
            .find(|e| lo <= e.span.start && e.span.start < hi && !operator_effect_only(&e.message))
        {
            return Some((
                path.iter().map(ToString::to_string).collect(),
                e.message.to_string(),
            ));
        }
        for n in free_names_of(f) {
            if fns.contains_key(&n) {
                let mut next = path.clone();
                next.push(n);
                stack.push(next);
            }
        }
    }
    None
}

/// Whether a row error is only that a function may perform an operator's
/// effect (`overflow`, `divzero`) its row leaves out: a macro function may
/// perform them as it may `div`, and one performed while it runs is that
/// macro's error.
fn operator_effect_only(message: &Message) -> bool {
    message.args.iter().any(|(key, value)| {
        key == "effect"
            && matches!(value, tauto_message::Value::Text(t) if t == "overflow" || t == "divzero")
    })
}

/// The names the body of `f` uses that nothing inside it binds: a parameter, a
/// `let`, a pattern variable, a λ parameter or a handler's variable hides a
/// function of the same spelling, as it does where the function runs.
pub fn free_names_of(f: &FnDecl) -> Vec<Name> {
    let mut body = f.body.clone();
    let mut bound: Vec<Name> = f.params.clone();
    let mut out = Vec::new();
    free_names_in(&mut body, &mut bound, &mut out);
    out
}

fn free_names_in(t: &mut SurfaceTerm, bound: &mut Vec<Name>, out: &mut Vec<Name>) {
    if !matches!(
        &*t.kind,
        TermKind::Var(_)
            | TermKind::Lam { .. }
            | TermKind::Exists { .. }
            | TermKind::Block(_)
            | TermKind::Match { .. }
            | TermKind::Handle { .. }
    ) {
        walk::children(t, &mut |c| free_names_in(c, bound, out));
        return;
    }
    match std::sync::Arc::make_mut(&mut t.kind) {
        TermKind::Var(n) => {
            if !bound.contains(n) {
                out.push(n.clone());
            }
        }
        TermKind::Lam {
            params,
            body,
            types,
            ..
        } => {
            for ty in types.iter_mut().flatten() {
                free_names_in(ty, bound, out);
            }
            let mark = bound.len();
            bound.extend(params.iter().cloned());
            free_names_in(body, bound, out);
            bound.truncate(mark);
        }
        TermKind::Exists {
            binder,
            domain,
            body,
            ..
        } => {
            free_names_in(domain, bound, out);
            let mark = bound.len();
            bound.push(binder.clone());
            free_names_in(body, bound, out);
            bound.truncate(mark);
        }
        TermKind::Block(stmts) => {
            let mark = bound.len();
            for s in stmts.iter_mut() {
                match s {
                    Stmt::Let {
                        name, ty, value, ..
                    }
                    | Stmt::Var {
                        name, ty, value, ..
                    } => {
                        if let Some(ty) = ty {
                            free_names_in(ty, bound, out);
                        }
                        free_names_in(value, bound, out);
                        bound.push(name.clone());
                    }
                    Stmt::Assign { name, value, .. } => {
                        if !bound.contains(name) {
                            out.push(name.clone());
                        }
                        free_names_in(value, bound, out);
                    }
                    Stmt::Fn(_) => {
                        let (name, params) = match &*s {
                            Stmt::Fn(d) => (d.name.clone(), d.params.clone()),
                            _ => unreachable!(),
                        };
                        bound.push(name);
                        let inner = bound.len();
                        bound.extend(params);
                        walk::roots(s, &mut |u| free_names_in(u, bound, out));
                        bound.truncate(inner);
                    }
                    _ => walk::roots(s, &mut |u| free_names_in(u, bound, out)),
                }
            }
            bound.truncate(mark);
        }
        TermKind::Match {
            scrutinee,
            result,
            binder,
            arms,
            ..
        } => {
            free_names_in(scrutinee, bound, out);
            if let Some(r) = result {
                free_names_in(r, bound, out);
            }
            for a in arms {
                let mark = bound.len();
                pattern_names(&a.pattern, bound);
                bound.extend(binder.iter().cloned());
                if let Some(g) = &mut a.guard {
                    free_names_in(g, bound, out);
                }
                if let Some(g) = &mut a.goal {
                    free_names_in(g, bound, out);
                }
                free_names_in(&mut a.body, bound, out);
                bound.truncate(mark);
            }
        }
        TermKind::Handle { body, handlers } => {
            free_names_in(body, bound, out);
            for h in handlers {
                let mark = bound.len();
                match h {
                    Handler::Return { pattern, body } => {
                        pattern_names(pattern, bound);
                        free_names_in(body, bound, out);
                    }
                    Handler::Operation {
                        patterns,
                        cont,
                        guard,
                        body,
                        ..
                    } => {
                        patterns.iter().for_each(|p| pattern_names(p, bound));
                        bound.extend(cont.iter().cloned());
                        if let Some(g) = guard {
                            free_names_in(g, bound, out);
                        }
                        free_names_in(body, bound, out);
                    }
                }
                bound.truncate(mark);
            }
        }
        _ => unreachable!("the other kinds are walked by their children"),
    }
}
