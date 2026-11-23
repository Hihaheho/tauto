//! `loop`, `while` with `break`/`continue`, and `for … in`, expanded where the
//! program is read so the checkers, the evaluator and the backends see only
//! forms they already have.
//!
//! ```text
//! loop { B }   ⇒   { var go = true; while go { var run = true; B' } }
//! while c { B } ⇒  { var go = true; while go { if c { var run = true; B' } else { go := false } } }
//! for p in e { B } ⇒
//!   { let pack = iterator_ready(e);
//!     for_ready(pack, Star, (_acc, item) => {
//!       match item { p => { B' as IterationControl(Unit) } }
//!     }) }
//! ```
//!
//! `for` is lowered before `while`/`loop`, so its `break`/`continue` become the
//! fold's `IterationControl` and are not mistaken for outer loop jumps. A
//! `break`/`continue` still inside a nested `while`/`loop` is left for
//! [`lower_loops`]. A `for` without `break` or `continue` is still expanded:
//! the finite fold is what removes `div`.

use std::sync::Arc;

use crate::span::Span;
use tauto_message::{Message, msg};

use super::program::{MatchArm, Pattern, Stmt};
use super::walk::{self, Node};
use super::{SurfaceTerm, TermKind};

/// Names a `for` expansion reads from the standard library. Import lists treat
/// them as used when they appear only after lowering ([`super::qualify::SourceUse::keeps_only`]).
pub const FOR_EXPANSION_NAMES: &[&str] = &[
    "for_ready",
    "iterator_ready",
    "IteratorReady",
    "fold_finite",
    "IterationControl",
];

/// The modules a file with a `for` reads as if it had imported them
/// (`iterator_ready`, `for_ready` and `IterationControl`), so an author writes no import for it.
pub const FOR_EXPANSION_MODULES: &[&str] = &["std::iterator", "std::finite_iteration"];

/// Whether `stmts` write a `for` anywhere.
pub fn has_for(stmts: &[Stmt]) -> bool {
    fn one(s: &Stmt, found: &mut bool) {
        match s {
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                items.iter().for_each(|i| one(i, found));
            }
            Stmt::Attributed { stmt, .. } => one(stmt, found),
            _ => walk::values_stmt(s, &mut |n| {
                *found |= matches!(n, Node::Stmt(Stmt::For { .. }));
            }),
        }
    }
    let mut found = false;
    stmts.iter().for_each(|s| one(s, &mut found));
    found
}

/// Expands each `for` of `files` into `iterator_ready` and `for_ready`. Its names are in scope
/// because a file with a `for` reads `std::iterator` and
/// `std::finite_iteration` ([`FOR_EXPANSION_MODULES`]). Returns errors and, for each lowered `for`,
/// the file index and span (so import lists can keep the expansion's names).
pub fn lower_fors(files: &mut [Vec<Stmt>]) -> (Vec<(Message, Span)>, Vec<(usize, Span)>) {
    let mut lower = ForLower {
        next: 0,
        errors: Vec::new(),
        sites: Vec::new(),
        file: 0,
    };
    for (file, stmts) in files.iter_mut().enumerate() {
        lower.file = file;
        for s in stmts.iter_mut() {
            walk::roots(s, &mut |t| lower.term(t));
        }
    }
    (lower.errors, lower.sites)
}

/// Expands the loops of `files`. Returns a `break` or `continue` outside a loop,
/// and a `break` with a value.
pub fn lower_loops(files: &mut [Vec<Stmt>]) -> Vec<(Message, Span)> {
    let mut lower = Lower {
        next: 0,
        errors: Vec::new(),
    };
    for stmts in files.iter_mut() {
        for s in stmts.iter_mut() {
            walk::roots(s, &mut |t| lower.term(t));
        }
    }
    // What is left is outside every loop.
    for stmts in files.iter_mut() {
        for s in stmts.iter_mut() {
            walk::roots(s, &mut |t| lower.strip(t));
        }
    }
    lower.errors
}

struct Lower {
    next: u32,
    errors: Vec<(Message, Span)>,
}

struct ForLower {
    next: u32,
    errors: Vec<(Message, Span)>,
    sites: Vec<(usize, Span)>,
    file: usize,
}

fn block(stmts: Vec<Stmt>, span: Span) -> SurfaceTerm {
    SurfaceTerm::new(TermKind::Block(stmts), span)
}

fn flag(name: &str, value: bool, span: Span) -> Stmt {
    Stmt::Var {
        stack: None,
        name: name.into(),
        ty: Some(SurfaceTerm::var("Bool", span)),
        value: SurfaceTerm::new(TermKind::Bool(value), span),
        borrow: false,
        unused: None,
    }
}

fn clear(name: &str, span: Span) -> Stmt {
    Stmt::Assign {
        name: name.into(),
        place: None,
        value: SurfaceTerm::new(TermKind::Bool(false), span),
        deref: None,
    }
}

fn app(function: &str, arguments: Vec<SurfaceTerm>, span: Span) -> SurfaceTerm {
    SurfaceTerm::new(
        TermKind::App {
            function: Box::new(SurfaceTerm::var(function, span)),
            arguments,
        },
        span,
    )
}

fn jumps(s: &Stmt) -> bool {
    let mut found = false;
    walk::values_stmt(s, &mut |n| {
        if matches!(n, Node::Stmt(Stmt::Break(_) | Stmt::Continue)) {
            found = true;
        }
    });
    found
}

fn term_jumps(t: &SurfaceTerm) -> bool {
    let mut found = false;
    walk::values(t, &mut |n| {
        if matches!(n, Node::Stmt(Stmt::Break(_) | Stmt::Continue)) {
            found = true;
        }
    });
    found
}

/// Whether `s` holds a `break`/`continue` that belongs to an enclosing `for`,
/// not to a nested `while`/`loop`/`for`.
fn for_jumps(s: &Stmt) -> bool {
    match s {
        Stmt::Break(_) | Stmt::Continue => true,
        Stmt::While { .. } | Stmt::Loop { .. } | Stmt::For { .. } => false,
        Stmt::Expr(t)
        | Stmt::Return(Some(t))
        | Stmt::Assign { value: t, .. }
        | Stmt::Let { value: t, .. }
        | Stmt::Var { value: t, .. } => term_for_jumps(t),
        _ => false,
    }
}

fn term_for_jumps(t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::Block(stmts) => stmts.iter().any(for_jumps),
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            term_for_jumps(condition)
                || term_for_jumps(then)
                || otherwise.as_deref().is_some_and(term_for_jumps)
        }
        TermKind::Match {
            scrutinee, arms, ..
        } => {
            term_for_jumps(scrutinee)
                || arms.iter().any(|arm| {
                    term_for_jumps(&arm.body)
                        || arm.guard.as_ref().is_some_and(term_for_jumps)
                })
        }
        // A `break`/`continue` inside a nested λ is not this `for`'s jump.
        TermKind::Lam { .. } | TermKind::BorrowLam { .. } => false,
        _ => false,
    }
}

impl ForLower {
    fn term(&mut self, t: &mut SurfaceTerm) {
        walk::children(t, &mut |c| self.term(c));
        if let TermKind::Block(_) = &*t.kind {
            let TermKind::Block(stmts) = Arc::make_mut(&mut t.kind) else {
                return;
            };
            for s in stmts.iter_mut() {
                if let Stmt::For {
                    pattern,
                    source,
                    body,
                } = s
                {
                    self.sites.push((self.file, body.span));
                    // What the expansion makes borrows the span of the loop it
                    // replaces and has no text of its own; only the terms the
                    // loop writes keep theirs.
                    let mut written = std::collections::HashSet::new();
                    for t in [&*source, &*body] {
                        walk::term(&mut t.clone(), &mut |u| {
                            written.insert(u.identity);
                        });
                    }
                    let mut lowered = self.lower(pattern.clone(), source.clone(), body.clone());
                    walk::stmt(&mut lowered, &mut |u| {
                        if !written.contains(&u.identity) {
                            u.lowered = true;
                        }
                    });
                    *s = lowered;
                }
            }
        }
    }

    /// `return` that leaves the `for` body (not a nested λ or nested loop).
    fn reject_escaping_returns(&mut self, t: &SurfaceTerm) {
        match &*t.kind {
            TermKind::Block(stmts) => {
                for s in stmts {
                    match s {
                        Stmt::Return(v) => self.errors.push((
                            msg!("surface-return-in-for"),
                            v.as_ref().map_or(t.span, |v| v.span),
                        )),
                        Stmt::While { .. } | Stmt::Loop { .. } | Stmt::For { .. } => {}
                        Stmt::Expr(u)
                        | Stmt::Assign { value: u, .. }
                        | Stmt::Let { value: u, .. }
                        | Stmt::Var { value: u, .. } => self.reject_escaping_returns(u),
                        _ => {}
                    }
                }
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.reject_escaping_returns(condition);
                self.reject_escaping_returns(then);
                if let Some(other) = otherwise {
                    self.reject_escaping_returns(other);
                }
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                self.reject_escaping_returns(scrutinee);
                for arm in arms {
                    self.reject_escaping_returns(&arm.body);
                    if let Some(guard) = &arm.guard {
                        self.reject_escaping_returns(guard);
                    }
                }
            }
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } => {}
            _ => {}
        }
    }

    fn lower(&mut self, pattern: Pattern, source: SurfaceTerm, body: SurfaceTerm) -> Stmt {
        let n = self.next;
        self.next += 1;
        let span = body.span;
        self.reject_escaping_returns(&body);
        let acc = format!("_acc@{n}");
        let item = format!("item@{n}");

        let inner = match &*body.kind {
            TermKind::Block(stmts) => stmts.clone(),
            _ => vec![Stmt::Expr(body.clone())],
        };
        let control_ty = app(
            "std::finite_iteration::IterationControl",
            vec![SurfaceTerm::var("Unit", span)],
            span,
        );
        // `break`/`continue` become the step's `IterationControl` value. No
        // `var` flags: a `var` in this λ would keep an effectful caller from
        // using `iterator_ready` / `fold_finite`.
        let arm_body = self.to_control(inner, span);
        let step_body = vec![Stmt::Expr(SurfaceTerm::new(
            TermKind::Match {
                scrutinee: Box::new(SurfaceTerm::var(item.as_str(), span)),
                result: Some(Box::new(control_ty)),
                binder: None,
                binder_unused: None,
                arms: vec![MatchArm {
                    pattern,
                    guard: None,
                    goal: None,
                    body: arm_body,
                }],
            },
            span,
        ))];

        let step = SurfaceTerm::new(
            TermKind::Lam {
                params: vec![acc.as_str().into(), item.as_str().into()],
                body: Box::new(block(step_body, span)),
                types: vec![Some(SurfaceTerm::var("Unit", span)), None],
                unused_params: Vec::new(),
            },
            span,
        );

        let pack = format!("pack@{n}");
        let ready = app("std::iterator::iterator_ready", vec![source], span);
        Stmt::Expr(block(
            vec![
                Stmt::Let {
                    name: pack.as_str().into(),
                    ty: None,
                    value: ready,
                    borrow: false,
                    borrow_mut: false,
                    stack: None,
                    unused: None,
                },
                Stmt::Expr(app(
                    "std::iterator::for_ready",
                    vec![
                        SurfaceTerm::var(pack.as_str(), span),
                        SurfaceTerm::unit(span),
                        step,
                    ],
                    span,
                )),
            ],
            span,
        ))
    }

    /// The body's statements as one term of type `IterationControl(Unit)`.
    fn to_control(&mut self, stmts: Vec<Stmt>, span: Span) -> SurfaceTerm {
        self.finish(stmts, span, Fallthrough::Continue)
    }

    /// An expression that may `break`/`continue` (`if`, `match`, block),
    /// sequenced with the statements after it.
    fn expr_to_control(
        &mut self,
        t: SurfaceTerm,
        after: Vec<Stmt>,
        span: Span,
        end: Fallthrough,
    ) -> SurfaceTerm {
        match &*t.kind {
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                let then = self.branch_to_control((**then).clone(), after.clone(), span, end);
                let otherwise = match otherwise {
                    Some(other) => self.branch_to_control((**other).clone(), after, span, end),
                    None => self.finish(after, span, end),
                };
                SurfaceTerm::new(
                    TermKind::If {
                        condition: condition.clone(),
                        then: Box::new(then),
                        otherwise: Some(Box::new(otherwise)),
                    },
                    span,
                )
            }
            TermKind::Match {
                scrutinee,
                binder,
                arms,
                ..
            } => {
                // Pattern binders stay in scope for the whole arm: do not move
                // `after` into arms. Close the match as Option first, then run
                // `after` outside (same boundary as `block_then_after`).
                let rewrite_arms = |this: &mut Self, arm_end: Fallthrough| {
                    arms.iter()
                        .map(|arm| MatchArm {
                            pattern: arm.pattern.clone(),
                            guard: arm.guard.clone(),
                            goal: arm.goal.clone(),
                            body: this.branch_to_control(
                                arm.body.clone(),
                                Vec::new(),
                                span,
                                arm_end,
                            ),
                        })
                        .collect::<Vec<_>>()
                };
                if after.is_empty() {
                    SurfaceTerm::new(
                        TermKind::Match {
                            scrutinee: scrutinee.clone(),
                            result: Some(Box::new(end.result_ty(span))),
                            binder: binder.clone(),
                            binder_unused: None,
                            arms: rewrite_arms(self, end),
                        },
                        span,
                    )
                } else {
                    let inner = SurfaceTerm::new(
                        TermKind::Match {
                            scrutinee: scrutinee.clone(),
                            result: Some(Box::new(Fallthrough::Ready.result_ty(span))),
                            binder: binder.clone(),
                            binder_unused: None,
                            arms: rewrite_arms(self, Fallthrough::Ready),
                        },
                        span,
                    );
                    self.after_optional(inner, after, span, end)
                }
            }
            TermKind::Block(stmts) => self.block_then_after(stmts.clone(), after, span, end),
            _ => {
                if term_for_jumps(&t) {
                    // Jump in a form we do not rewrite (nested λ, …): keep it
                    // for later diagnostics. Do not call `finish` on the same
                    // term — that would loop.
                    let mut stmts = vec![Stmt::Expr(t)];
                    stmts.extend(after);
                    stmts.push(Stmt::Expr(end.fallthrough(span)));
                    block(stmts, span)
                } else {
                    let mut stmts = vec![Stmt::Expr(t)];
                    stmts.extend(after);
                    self.finish(stmts, span, end)
                }
            }
        }
    }

    fn branch_to_control(
        &mut self,
        branch: SurfaceTerm,
        after: Vec<Stmt>,
        span: Span,
        end: Fallthrough,
    ) -> SurfaceTerm {
        match &*branch.kind {
            TermKind::Block(stmts) => self.block_then_after(stmts.clone(), after, span, end),
            _ if term_for_jumps(&branch) => self.expr_to_control(branch, after, span, end),
            _ => {
                let mut stmts = vec![Stmt::Expr(branch)];
                stmts.extend(after);
                self.finish(stmts, span, end)
            }
        }
    }

    /// Rewrite `stmts`, then run `after` from outside this block. The two are
    /// not concatenated: `stmts` become `Option(IterationControl)` (`None` =
    /// fallthrough, `Some` = break/continue), and `after` runs only on `None`
    /// in a scope that does not see `stmts`' binders.
    fn block_then_after(
        &mut self,
        stmts: Vec<Stmt>,
        after: Vec<Stmt>,
        span: Span,
        end: Fallthrough,
    ) -> SurfaceTerm {
        if after.is_empty() {
            return self.finish(stmts, span, end);
        }
        let inner = self.finish(stmts, span, Fallthrough::Ready);
        self.after_optional(inner, after, span, end)
    }

    /// Bind `inner` (often a block) then
    /// `match opt { None => <after>, Some(ctl) => <jump ctl> }` with `end`'s
    /// encoding (`IterationControl` or `Option` of it).
    fn after_optional(
        &mut self,
        inner: SurfaceTerm,
        after: Vec<Stmt>,
        span: Span,
        end: Fallthrough,
    ) -> SurfaceTerm {
        let n = self.next;
        self.next += 1;
        let opt = format!("opt@{n}");
        let ctl = format!("ctl@{n}");
        let matched = SurfaceTerm::new(
            TermKind::Match {
                scrutinee: Box::new(SurfaceTerm::var(opt.as_str(), span)),
                result: Some(Box::new(end.result_ty(span))),
                binder: None,
                binder_unused: None,
                arms: vec![
                    MatchArm {
                        pattern: Pattern::Ctor {
                            name: "None".into(),
                            args: vec![],
                        },
                        guard: None,
                        goal: None,
                        body: self.finish(after, span, end),
                    },
                    MatchArm {
                        pattern: Pattern::Ctor {
                            name: "Some".into(),
                            args: vec![Pattern::bind(ctl.as_str())],
                        },
                        guard: None,
                        goal: None,
                        body: end.jump(SurfaceTerm::var(ctl.as_str(), span), span),
                    },
                ],
            },
            span,
        );
        block(
            vec![
                Stmt::Let {
                    name: opt.as_str().into(),
                    ty: Some(Fallthrough::Ready.result_ty(span)),
                    value: inner,
                    borrow: false,
                    borrow_mut: false,
                    stack: None,
                    unused: None,
                },
                Stmt::Expr(matched),
            ],
            span,
        )
    }

    fn finish(&mut self, stmts: Vec<Stmt>, span: Span, end: Fallthrough) -> SurfaceTerm {
        let mut out = Vec::new();
        let mut rest = stmts.into_iter();
        while let Some(s) = rest.next() {
            match s {
                Stmt::Return(v) => {
                    self.errors.push((
                        msg!("surface-return-in-for"),
                        v.as_ref().map_or(span, |v| v.span),
                    ));
                    out.push(Stmt::Return(v));
                    return block(out, span);
                }
                Stmt::Break(value) => {
                    if let Some(v) = value {
                        self.errors.push((msg!("surface-break-value"), v.span));
                    }
                    out.push(Stmt::Expr(end.jump(Fallthrough::control_break(span), span)));
                    return block(out, span);
                }
                Stmt::Continue => {
                    out.push(Stmt::Expr(end.jump(Fallthrough::control_continue(span), span)));
                    return block(out, span);
                }
                Stmt::While { .. } | Stmt::Loop { .. } | Stmt::For { .. } => {
                    out.push(s);
                }
                Stmt::Expr(t) if for_jumps(&Stmt::Expr(t.clone())) => {
                    // Same-block remainder only — never mix in statements from
                    // outside this block (those go through `block_then_after`).
                    let after: Vec<Stmt> = rest.by_ref().collect();
                    out.push(Stmt::Expr(self.expr_to_control(t, after, span, end)));
                    return block(out, span);
                }
                other => out.push(other),
            }
        }
        // A trailing expression was the block's value; the fallthrough replaces
        // that role. Keep the expression as a match scrutinee so its type is
        // checked and its effects run.
        let ending = if let Some(Stmt::Expr(_)) = out.last() {
            let Some(Stmt::Expr(e)) = out.pop() else {
                unreachable!("last statement checked as Expr");
            };
            SurfaceTerm::new(
                TermKind::Match {
                    scrutinee: Box::new(e),
                    result: Some(Box::new(end.result_ty(span))),
                    binder: None,
                    binder_unused: None,
                    arms: vec![MatchArm {
                        pattern: Pattern::Wild,
                        guard: None,
                        goal: None,
                        body: end.fallthrough(span),
                    }],
                },
                span,
            )
        } else {
            end.fallthrough(span)
        };
        out.push(Stmt::Expr(ending));
        block(out, span)
    }
}

/// How a rewritten block ends when it does not `break` or `continue`.
#[derive(Clone, Copy)]
enum Fallthrough {
    /// `IterationControl::Continue(Unit)` — the fold step's normal end.
    Continue,
    /// `None` of `Option(IterationControl(Unit))`, so a caller can run
    /// outside-block statements without seeing this block's binders; jumps
    /// are `Some(Break/Continue)`.
    Ready,
}

impl Fallthrough {
    fn control_break(span: Span) -> SurfaceTerm {
        app(
            "std::finite_iteration::IterationControl::Break",
            vec![SurfaceTerm::unit(span)],
            span,
        )
    }

    fn control_continue(span: Span) -> SurfaceTerm {
        app(
            "std::finite_iteration::IterationControl::Continue",
            vec![SurfaceTerm::unit(span)],
            span,
        )
    }

    fn fallthrough(self, span: Span) -> SurfaceTerm {
        match self {
            Self::Continue => Self::control_continue(span),
            Self::Ready => SurfaceTerm::var("None", span),
        }
    }

    fn jump(self, ctl: SurfaceTerm, span: Span) -> SurfaceTerm {
        match self {
            Self::Continue => ctl,
            Self::Ready => app("Some", vec![ctl], span),
        }
    }

    fn result_ty(self, span: Span) -> SurfaceTerm {
        let control = app(
            "std::finite_iteration::IterationControl",
            vec![SurfaceTerm::var("Unit", span)],
            span,
        );
        match self {
            Self::Continue => control,
            Self::Ready => app("Option", vec![control], span),
        }
    }
}

impl Lower {
    /// Inner loops first, so what is left of a loop's body is its own.
    fn term(&mut self, t: &mut SurfaceTerm) {
        walk::children(t, &mut |c| self.term(c));
        match &*t.kind {
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } => self.strip(t),
            TermKind::Block(_) => {
                let TermKind::Block(stmts) = Arc::make_mut(&mut t.kind) else {
                    return;
                };
                for s in stmts.iter_mut() {
                    let lowered = match s {
                        Stmt::Loop { body } => Some((None, body.clone())),
                        Stmt::While { condition, body } if term_jumps(body) => {
                            Some((Some(condition.clone()), body.clone()))
                        }
                        _ => None,
                    };
                    if let Some((condition, body)) = lowered {
                        // As for `for`: what the expansion makes (the flags,
                        // their `Bool`, the `if`s and blocks around the body)
                        // borrows the span of the loop and has no text of its
                        // own; only the terms the loop writes keep theirs.
                        let mut written = std::collections::HashSet::new();
                        for t in condition.iter().chain([&body]) {
                            walk::term(&mut t.clone(), &mut |u| {
                                written.insert(u.identity);
                            });
                        }
                        let mut made = self.lower(condition, body);
                        walk::stmt(&mut made, &mut |u| {
                            if !written.contains(&u.identity) {
                                u.lowered = true;
                            }
                        });
                        *s = made;
                    }
                }
            }
            _ => {}
        }
    }

    fn lower(&mut self, condition: Option<SurfaceTerm>, body: SurfaceTerm) -> Stmt {
        let n = self.next;
        self.next += 1;
        let (go, run) = (format!("go@{n}"), format!("run@{n}"));
        let span = body.span;
        let inner = match &*body.kind {
            TermKind::Block(stmts) => stmts.clone(),
            _ => vec![Stmt::Expr(body.clone())],
        };
        let mut iteration = vec![flag(&run, true, span)];
        iteration.extend(self.rewrite(inner, &go, &run, span));
        let iteration = block(iteration, span);
        let body = match condition {
            None => iteration,
            Some(c) => block(
                vec![Stmt::Expr(SurfaceTerm::new(
                    TermKind::If {
                        condition: Box::new(c),
                        then: Box::new(iteration),
                        otherwise: Some(Box::new(block(vec![clear(&go, span)], span))),
                    },
                    span,
                ))],
                span,
            ),
        };
        Stmt::Expr(block(
            vec![
                flag(&go, true, span),
                Stmt::While {
                    condition: SurfaceTerm::var(go.as_str(), span),
                    body,
                },
            ],
            span,
        ))
    }

    /// `stmts` of a loop's body with its `break`s and `continue`s written as the
    /// flags, and what follows a statement that may jump under `if run`.
    fn rewrite(&mut self, stmts: Vec<Stmt>, go: &str, run: &str, span: Span) -> Vec<Stmt> {
        let mut out = Vec::new();
        let mut rest = stmts.into_iter();
        while let Some(mut s) = rest.next() {
            match s {
                Stmt::Break(value) => {
                    if let Some(v) = value {
                        self.errors.push((msg!("surface-break-value"), v.span));
                    }
                    out.push(clear(go, span));
                    out.push(clear(run, span));
                    break;
                }
                Stmt::Continue => {
                    out.push(clear(run, span));
                    break;
                }
                _ => {}
            }
            let may_jump = jumps(&s);
            if may_jump {
                walk::roots(&mut s, &mut |t| {
                    walk::term(t, &mut |x| {
                        if let TermKind::Block(inner) = Arc::make_mut(&mut x.kind) {
                            let taken = std::mem::take(inner);
                            *inner = self.rewrite(taken, go, run, span);
                        }
                    })
                });
            }
            out.push(s);
            if may_jump {
                let after: Vec<Stmt> = rest.by_ref().collect();
                if !after.is_empty() {
                    let after = self.rewrite(after, go, run, span);
                    out.push(Stmt::Expr(SurfaceTerm::new(
                        TermKind::If {
                            condition: Box::new(SurfaceTerm::var(run, span)),
                            then: Box::new(block(after, span)),
                            otherwise: None,
                        },
                        span,
                    )));
                }
                break;
            }
        }
        out
    }

    /// Takes the `break`s and `continue`s out of `t`: they have no loop.
    fn strip(&mut self, t: &mut SurfaceTerm) {
        walk::term(t, &mut |x| {
            if let TermKind::Block(stmts) = Arc::make_mut(&mut x.kind) {
                stmts.retain(|s| {
                    let (message, span) = match s {
                        Stmt::Break(v) => (
                            msg!("surface-break-outside-loop"),
                            v.as_ref().map_or(x.span, |v| v.span),
                        ),
                        Stmt::Continue => (msg!("surface-continue-outside-loop"), x.span),
                        _ => return true,
                    };
                    self.errors.push((message, span));
                    false
                });
            }
        });
    }
}
