//! How many times each `handle` arm calls its continuation, held to the
//! `resume` its effect declares.
//!
//! The kernel reads a handler as a fold of a tree of operations, where calling
//! `k` twice is as good as calling it once; the programs that run move `k` like
//! any other value. So an arm for `effect choose(): Bool` (`resume <=1`) that
//! calls `k(true)` and `k(false)` is rejected here, as the run rejects it, rather
//! than proven about and then not run.

use crate::surface::{Handler, Pattern, Stmt, SurfaceTerm, TermKind, walk};
use std::collections::HashMap;
use tauto_message::{Message, msg};
use tauto_parol::Span;

/// The most calls a `resume` allows, `None` for `ω`.
fn bound(resume: Option<&str>) -> Option<u32> {
    match resume {
        Some("0") => Some(0),
        Some("ω") => None,
        _ => Some(1),
    }
}

/// The most calls of `k` on one path through a term, `None` for any number.
#[derive(Clone, Copy)]
struct Uses {
    max: Option<u32>,
}

impl Uses {
    const NONE: Uses = Uses { max: Some(0) };
    const ONE: Uses = Uses { max: Some(1) };
    const MANY: Uses = Uses { max: None };

    fn then(self, other: Uses) -> Uses {
        Uses {
            max: self.max.zip(other.max).map(|(a, b)| a + b),
        }
    }

    fn or(self, other: Uses) -> Uses {
        Uses {
            max: self.max.zip(other.max).map(|(a, b)| a.max(b)),
        }
    }

    fn any(self) -> bool {
        self.max != Some(0)
    }
}

fn binds(p: &Pattern, k: &str) -> bool {
    let mut names = Vec::new();
    super::pattern_binders(p, &mut names);
    names.iter().any(|n| n == k)
}

/// The calls of `k` on the path through `t` that calls it most.
fn uses(t: &SurfaceTerm, k: &str) -> Uses {
    match &*t.kind {
        TermKind::Var(v) if v == k => Uses::ONE,
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            let other = otherwise.as_ref().map_or(Uses::NONE, |o| uses(o, k));
            uses(condition, k).then(uses(then, k).or(other))
        }
        TermKind::Match {
            scrutinee, arms, ..
        } => {
            let mut most = Uses::NONE;
            for a in arms {
                if binds(&a.pattern, k) {
                    continue;
                }
                let g = a.guard.as_ref().map_or(Uses::NONE, |g| uses(g, k));
                most = most.or(g.then(uses(&a.body, k)));
            }
            uses(scrutinee, k).then(most)
        }
        // A closure that holds `k` holds it once, as a move into it.
        TermKind::Lam { params, body, .. } => {
            match !params.iter().any(|p| p == k) && uses(body, k).any() {
                true => Uses::ONE,
                false => Uses::NONE,
            }
        }
        TermKind::Block(stmts) => block(stmts, k),
        TermKind::Handle { body, handlers } => {
            let mut total = uses(body, k);
            for h in handlers {
                let (inner, shadowed) = match h {
                    Handler::Return { pattern, body } => (uses(body, k), binds(pattern, k)),
                    Handler::Operation {
                        patterns,
                        cont,
                        guard,
                        body,
                        ..
                    } => {
                        let g = guard.as_ref().map_or(Uses::NONE, |g| uses(g, k));
                        let shadowed =
                            cont.as_deref() == Some(k) || patterns.iter().any(|p| binds(p, k));
                        // An operation arm runs once for each operation performed.
                        let inner = match g.then(uses(body, k)).any() {
                            true => Uses::MANY,
                            false => Uses::NONE,
                        };
                        (inner, shadowed)
                    }
                };
                if !shadowed {
                    total = total.then(inner);
                }
            }
            total
        }
        _ => {
            let mut total = Uses::NONE;
            let mut t = t.clone();
            walk::children(&mut t, &mut |c| total = total.then(uses(c, k)));
            total
        }
    }
}

fn block(stmts: &[Stmt], k: &str) -> Uses {
    let mut total = Uses::NONE;
    for s in stmts {
        match s {
            Stmt::Let { name, value, .. } | Stmt::Var { name, value, .. } => {
                total = total.then(uses(value, k));
                if name == k {
                    return total;
                }
            }
            Stmt::While { condition, body } => {
                if uses(condition, k).then(uses(body, k)).any() {
                    total = Uses::MANY;
                }
            }
            _ => {
                let mut s = s.clone();
                walk::roots(&mut s, &mut |t| total = total.then(uses(t, k)));
            }
        }
    }
    total
}

/// The first arm in `s` that calls its continuation more often than its
/// effect's `resume` allows, with the message to give.
pub(super) fn overused(
    s: &Stmt,
    resumes: &HashMap<String, Option<String>>,
) -> Option<(Message, Span)> {
    let mut found = None;
    let mut s = s.clone();
    walk::stmt(&mut s, &mut |t| {
        if found.is_some() {
            return;
        }
        let TermKind::Handle { handlers, .. } = &*t.kind else {
            return;
        };
        for h in handlers {
            let Handler::Operation {
                effect,
                cont: Some(k),
                guard,
                body,
                ..
            } = h
            else {
                continue;
            };
            let Some(resume) = resumes.get(effect) else {
                continue;
            };
            let Some(most) = bound(resume.as_deref()) else {
                continue;
            };
            let g = guard.as_ref().map_or(Uses::NONE, |g| uses(g, k));
            let called = g.then(uses(body, k)).max;
            if called.is_none_or(|n| n > most) {
                let written = resume.as_deref().unwrap_or("<=1");
                let times = match called {
                    Some(1) => msg!("kernel-resume-once"),
                    Some(n) => msg!("kernel-resume-times", count = n),
                    None => msg!("kernel-resume-any"),
                };
                let hint = match most {
                    0 => msg!("kernel-resume-hint-once"),
                    _ => msg!("kernel-resume-hint-many"),
                };
                found = Some((
                    msg!(
                        "kernel-resume-overused",
                        effect = effect,
                        cont = k,
                        times = times,
                        written = written,
                        hint = hint
                    ),
                    body.span,
                ));
                return;
            }
        }
    });
    found
}
