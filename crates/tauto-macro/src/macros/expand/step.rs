//! Steps of a proof (`docs/design/macro-steps.md`):
//! `by t!(arg): G0 { Δ ⊢ G from p … }`. The tactic `t` is a macro whose
//! function takes a `ProofStep`; it makes a term of `G0` with a hole `?armK` for the
//! goal of the K-th arm. The goals written are compared with the ones the
//! tactic left, each arm's proof goes in its hole as `the(G, p)`, and the step
//! becomes `the(G0, term)`: the kernel checks every goal written, and nothing
//! the tactic made is trusted.

use std::cell::RefCell;
use std::sync::Arc;

use super::typed::kernel_decl;
use super::*;
use crate::macros::checker::{HoleGoal, PrefixedChecker, Verdict};
use crate::macros::syn::SpanTable;
use crate::surface::{Step, StepArm};
use tauto_message::{Message, msg};

/// The hole a step stands in while the declaration is checked without it.
const GOAL: &str = "step'goal";
/// The variable of the declarations that compare two types.
const VALUE: &str = "step'v";

fn arm_hole(k: usize) -> String {
    format!("step'arm{k}")
}

impl Expander<'_> {
    /// Expands the steps of the declarations of this file, one declaration at
    /// a time and, in one, the outermost first.
    pub(super) fn step_pass(&mut self, stmts: Vec<Stmt>) -> Vec<Stmt> {
        self.step_items(stmts, &[], &[])
    }

    /// [`Self::step_pass`] of the statements of the module `path` (none at the
    /// top level); `outer` is what comes before the module, with the modules
    /// around it written up to it.
    fn step_items(
        &mut self,
        stmts: Vec<Stmt>,
        path: &[(String, Span)],
        outer: &[Stmt],
    ) -> Vec<Stmt> {
        let mut out: Vec<Stmt> = Vec::new();
        for s in stmts {
            match first_step(&s) {
                None => out.push(s),
                Some(_) if matches!(s, Stmt::Module { .. }) => {
                    let Stmt::Module { name, items, span } = s else {
                        unreachable!()
                    };
                    let mut inner = path.to_vec();
                    inner.push((name.clone(), span));
                    let mut around = outer.to_vec();
                    around.extend(wrap(path, out.clone()));
                    let items = self.step_items(items, &inner, &around);
                    out.push(Stmt::Module { name, items, span });
                }
                Some((_, at)) if matches!(s, Stmt::Mutual { .. }) => {
                    self.error("step.fragment", msg!("macro-step-mutual"), at);
                    out.push(s);
                }
                Some(_) => {
                    // The declaration is checked with its names written out
                    // (`add` in `module Nat` and `Nat.add` are the function
                    // `Nat.add`), and keeps its own name, which the module
                    // still gives it.
                    let mut before = outer.to_vec();
                    before.extend(wrap(path, out.clone()));
                    let mut all: Vec<Stmt> = self.done.clone();
                    all.extend(before.iter().cloned());
                    all.extend(wrap(path, vec![s.clone()]));
                    let flat = crate::surface::modules::resolve_in_prelude(all)
                        .0
                        .pop()
                        .expect("the declaration");
                    let mut done = self.step_decl(flat, &before);
                    set_name(&mut done, &s);
                    out.push(done);
                }
            }
        }
        out
    }

    fn step_decl(&mut self, mut d: Stmt, before: &[Stmt]) -> Stmt {
        let Some((_, at)) = first_step(&d) else {
            return d;
        };
        if kernel_decl(&d).is_none() {
            self.error("step.fragment", msg!("macro-step-fragment"), at);
            return without_steps(d);
        }
        if let Some(problem) = self.lib.as_ref().and_then(|l| l.problem.clone()) {
            self.error(
                "macro.library",
                msg!("macro-step-library", problem = problem),
                at,
            );
            return without_steps(d);
        }
        if let Err((m, at)) = fill_before(&mut d) {
            self.error("step.before", m, at);
            return without_steps(d);
        }
        let mut all: Vec<Stmt> = self.done.clone();
        all.extend(before.iter().cloned());
        let (prefix, _) = crate::surface::modules::resolve_in_prelude(all);
        self.elab_prefix = prefix.clone();
        let kernel = match self.checker.prefixed(&prefix) {
            Ok(k) => k,
            Err(m) => {
                self.error("step.kernel", m, at);
                return without_steps(d);
            }
        };
        while let Some((step, _)) = first_step(&d) {
            match self.one_step(kernel.as_ref(), &d, before, &step) {
                Some(term) => {
                    put_first_step(&mut d, term);
                    d = self.resolved(d, before);
                    self.file_expanded = true;
                }
                None => return without_steps(d),
            }
        }
        d
    }

    /// The term the first step of `d` stands for, or `None` after an error.
    fn one_step(
        &mut self,
        kernel: &dyn PrefixedChecker,
        d: &Stmt,
        before: &[Stmt],
        step: &Step,
    ) -> Option<SurfaceTerm> {
        let at = step.call;
        let g0 = step.before.clone().expect("filled by fill_before");
        // 1. The variables in scope where the step is: the declaration with a
        // hole in its place.
        let probe = with_first_step(d, SurfaceTerm::new(TermKind::Hole(GOAL.into()), at));
        let here = match kernel.verdict(&probe) {
            Some(Verdict::Incomplete { holes, .. }) => holes.into_iter().find(|h| h.name == GOAL),
            Some(Verdict::Skipped(_)) => {
                self.error("step.fragment", msg!("macro-step-fragment"), at);
                return None;
            }
            Some(Verdict::Failed(e)) => {
                self.error(
                    "step.context",
                    msg!("macro-step-context", message = e.message.clone()),
                    at,
                );
                return None;
            }
            _ => None,
        };
        let Some(here) = here else {
            self.error("step.context", msg!("macro-step-no-goal"), at);
            return None;
        };
        // 2. The goal written is the goal there.
        if let Err(m) = self.same_type(kernel, before, &here.context, &here.goal, &g0, at) {
            self.error(
                "step.before_mismatch",
                msg!(
                    "macro-step-before-mismatch",
                    here = crate::surface::print::print_term(&here.goal),
                    written = crate::surface::print::print_term(&g0),
                    why = m
                ),
                at,
            );
            return None;
        }
        // 3. The tactic.
        let id = self.expansions.len() as u32 + 1;
        let (term, exp) = self.run_tactic(step, id, &here)?;
        let mut found: Vec<String> = Vec::new();
        let mut probe_term = term.clone();
        walk::term(&mut probe_term, &mut |t| {
            if let TermKind::Hole(h) = Arc::make_mut(&mut t.kind) {
                found.push(h.clone());
                if let Some(k) = h.strip_prefix("arm").and_then(|k| k.parse::<usize>().ok()) {
                    *h = arm_hole(k);
                }
            }
        });
        // A step written with no arm, whose tactic leaves goals: what the arms
        // are is said, for `tauto expand --by` to write.
        let proposing = step.arms.is_empty() && !found.is_empty();
        let count = if proposing {
            found.len()
        } else {
            step.arms.len()
        };
        let wanted: Vec<String> = (1..=count).map(|k| format!("arm{k}")).collect();
        let mut sorted = found.clone();
        sorted.sort();
        let mut wanted_sorted = wanted.clone();
        wanted_sorted.sort();
        if sorted != wanted_sorted {
            self.error(
                "step.holes",
                msg!(
                    "macro-step-holes",
                    arms = step.arms.len(),
                    holes = found
                        .iter()
                        .map(|h| format!("?{h}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                at,
            );
            return None;
        }
        // 4. The goals the tactic left, against the arms.
        let made = SurfaceTerm::app("the", vec![g0.clone(), probe_term.clone()], step.call);
        let probe = self.resolved(with_first_step(d, made), before);
        let holes: Vec<HoleGoal> = match kernel.verdict(&probe) {
            Some(Verdict::Incomplete { holes, .. }) => holes,
            Some(Verdict::Failed(e)) => {
                self.error(
                    "step.output_ill_typed",
                    msg!("macro-step-output-rejected", message = e.message.clone()),
                    at,
                );
                return None;
            }
            _ => Vec::new(),
        };
        let outer: Vec<&str> = here.context.iter().map(|(n, _)| n.as_str()).collect();
        if proposing {
            let mut arms = Vec::new();
            for k in 1..=count {
                let Some(hole) = holes.iter().find(|h| h.name == arm_hole(k)) else {
                    self.error("step.holes", msg!("macro-step-hole-no-goal", k = k), at);
                    return None;
                };
                let added: Vec<String> = hole
                    .context
                    .iter()
                    .filter(|(n, _)| !outer.contains(&n.as_str()))
                    .map(|(n, t)| format!("{n}: {}", crate::surface::print::print_term(t)))
                    .collect();
                let binders = if added.is_empty() {
                    String::new()
                } else {
                    format!("{} ", added.join(", "))
                };
                arms.push(format!(
                    "{binders}⊢ {} from ?arm{k}",
                    crate::surface::print::print_term(&hole.goal)
                ));
            }
            self.error(
                "step.arms",
                msg!("macro-step-arms", count = count, arms = arms.join("\n")),
                at,
            );
            return None;
        }
        for (k, arm) in step.arms.iter().enumerate() {
            let k = k + 1;
            let Some(hole) = holes.iter().find(|h| h.name == arm_hole(k)) else {
                self.error(
                    "step.holes",
                    msg!("macro-step-hole-no-goal", k = k),
                    arm.span,
                );
                return None;
            };
            let added: Vec<&(String, SurfaceTerm)> = hole
                .context
                .iter()
                .filter(|(n, _)| !outer.contains(&n.as_str()))
                .collect();
            let names: Vec<&str> = added.iter().map(|(n, _)| n.as_str()).collect();
            let written: Vec<&str> = arm.binders.iter().map(|(n, _)| n.as_str()).collect();
            if names != written {
                self.error(
                    "step.context_mismatch",
                    msg!(
                        "macro-step-binders-mismatch",
                        k = k,
                        added = names.join(", "),
                        written = written.join(", ")
                    ),
                    arm.span,
                );
                self.rewrite_arm(arm, &added, &hole.goal);
                return None;
            }
            for ((name, ty), (_, wrote)) in added.iter().zip(&arm.binders) {
                if let Err(m) = self.same_type(kernel, before, &hole.context, ty, wrote, arm.span) {
                    self.error(
                        "step.context_mismatch",
                        msg!(
                            "macro-step-binder-type",
                            k = k,
                            name = name,
                            ty = crate::surface::print::print_term(ty),
                            written = crate::surface::print::print_term(wrote),
                            why = m
                        ),
                        arm.span,
                    );
                    self.rewrite_arm(arm, &added, &hole.goal);
                    return None;
                }
            }
            if let Err(m) = self.same_type(
                kernel,
                before,
                &hole.context,
                &hole.goal,
                &arm.goal,
                arm.span,
            ) {
                self.error(
                    "step.goal_mismatch",
                    msg!(
                        "macro-step-goal-mismatch",
                        k = k,
                        left = crate::surface::print::print_term(&hole.goal),
                        written = crate::surface::print::print_term(&arm.goal),
                        why = m
                    ),
                    arm.span,
                );
                self.rewrite_arm(arm, &added, &hole.goal);
                return None;
            }
        }
        // 5. The arms' proofs in their holes.
        let mut out = probe_term;
        walk::term(&mut out, &mut |t| {
            if let TermKind::Hole(h) = &*t.kind
                && let Some(k) = h
                    .strip_prefix("step'arm")
                    .and_then(|k| k.parse::<usize>().ok())
            {
                let arm = &step.arms[k - 1];
                // A step that proves the arm says its goal itself.
                *t = match &*arm.body.kind {
                    TermKind::Step(_) => arm.body.clone(),
                    _ => {
                        SurfaceTerm::app("the", vec![arm.goal.clone(), arm.body.clone()], arm.span)
                    }
                };
            }
        });
        self.expansions.push(exp);
        Some(SurfaceTerm::app("the", vec![g0, out], step.call))
    }

    fn resolved(&self, d: Stmt, before: &[Stmt]) -> Stmt {
        let ctors = ctor_names(
            self.done
                .iter()
                .chain(before.iter())
                .chain(std::iter::once(&d)),
        );
        let d = scope::resolve(vec![d], &ctors)
            .pop()
            .expect("one statement");
        // What a tactic makes names functions by their full names
        // (`Nat.norm_eq`), as the declaration's own names are.
        let mut known = crate::surface::modules::declared(&self.done);
        known.extend(crate::surface::modules::declared(before));
        crate::surface::modules::resolve_in_prelude_against(
            vec![d],
            known.iter().map(|n| n.as_str()),
        )
        .0
        .pop()
        .expect("one statement")
    }

    /// The edit that makes the arm's header (`Δ ⊢ G`, up to `=>`) say what the tactic
    /// left. The arm keeps the names it wrote when there are as many as the tactic added.
    fn rewrite_arm(&mut self, arm: &StepArm, added: &[&(String, SurfaceTerm)], goal: &SurfaceTerm) {
        use crate::surface::print::print_term;
        let kept = added.len() == arm.binders.len();
        let binders: Vec<String> = added
            .iter()
            .enumerate()
            .map(|(i, (n, t))| {
                let name = if kept { &arm.binders[i].0 } else { n };
                format!("{name}: {}", print_term(t))
            })
            .collect();
        let head = if binders.is_empty() {
            "⊢ ".to_string()
        } else {
            format!("{} ⊢ ", binders.join(", "))
        };
        let (start, end) = (arm.span.start, arm.goal.span.end);
        if start >= end {
            return;
        }
        self.fixes.push((
            arm.span,
            crate::surface::Fix {
                title: "Write the goal the tactic leaves".into(),
                span: Span::new(start, end),
                text: format!("{head}{}", print_term(goal)),
            },
        ));
    }

    /// Whether `found` and `written` are the same type in `context`, up to
    /// conversion: the kernel takes `step'v: found` for a `written`.
    fn same_type(
        &self,
        kernel: &dyn PrefixedChecker,
        before: &[Stmt],
        context: &[(String, SurfaceTerm)],
        found: &SurfaceTerm,
        written: &SurfaceTerm,
        at: Span,
    ) -> Result<(), Message> {
        let mut params = context.to_vec();
        params.push((VALUE.into(), found.clone()));
        let check = Stmt::Theorem(crate::surface::TheoremDecl {
            budget: None,
            vis: Default::default(),
            decreasing_by: None,
            name: "step'check".into(),
            implicit: 0,
            params,
            ty: written.clone(),
            body: Some(SurfaceTerm::var(VALUE, at)),
            span: at,
        });
        match kernel.verdict(&self.resolved(check, before)) {
            Some(Verdict::Checked { .. }) => Ok(()),
            Some(Verdict::Failed(e)) => Err(e.message),
            _ => Err(msg!("macro-step-not-checked")),
        }
    }

    /// Runs the tactic of `step` where the variables are `here.context`.
    fn run_tactic(
        &mut self,
        step: &Step,
        id: u32,
        here: &HoleGoal,
    ) -> Option<(SurfaceTerm, Expansion)> {
        let name = step.tactic.as_str();
        let (name, _) = split(name);
        let name = name.to_string();
        let Some(reg) = self.macros.get(&name) else {
            self.error(
                "macro.unknown",
                msg!("macro-unknown", name = &name),
                step.call,
            );
            return None;
        };
        if reg.file >= self.file {
            self.error(
                "macro.same_file",
                msg!("macro-same-file", name = &name),
                step.call,
            );
            return None;
        }
        let info = self.registration(&name, step.call)?;
        if !matches!(info.input, Input::Step) || !matches!(info.shape, Shape::Expr) {
            self.error(
                "step.tactic",
                msg!("macro-step-not-tactic", name = &name),
                step.call,
            );
            return None;
        }
        // The variables in scope, then each arm's, are atoms from 1.
        let mut atoms: HashMap<String, u64> = HashMap::new();
        let mut ctx: Vec<(u64, String, SurfaceTerm)> = Vec::new();
        for (name, ty) in &here.context {
            let atom = ctx.len() as u64 + 1;
            atoms.insert(name.clone(), atom);
            ctx.push((atom, name.clone(), ty.clone()));
        }
        let mut next = ctx.len() as u64 + 1;
        let mut arms: Vec<(Vec<(u64, String, SurfaceTerm)>, SurfaceTerm)> = Vec::new();
        for arm in &step.arms {
            let mut added = Vec::new();
            for (n, ty) in &arm.binders {
                atoms.insert(n.clone(), next);
                added.push((next, n.clone(), ty.clone()));
                next += 1;
            }
            arms.push((added, arm.goal.clone()));
        }
        let table = RefCell::new(SpanTable::default());
        let lift = crate::macros::syn::Lift {
            scopes: &[u64::from(id)],
            quote: false,
            atoms: Some(&atoms),
            spans: Some(&table),
            reflip: None,
        };
        let span_node = |at: Span| {
            Node::Ctor(
                "SynSpan".into(),
                vec![(Some("id".into()), Node::Int(i64::from(at.start)))],
            )
        };
        let binders = |items: &[(u64, String, SurfaceTerm)]| -> Result<Vec<Node>, String> {
            items
                .iter()
                .map(|(atom, name, ty)| {
                    Ok(Node::Ctor(
                        "Judgement::Binder".into(),
                        vec![
                            (Some("atom".into()), Node::Int(*atom as i64)),
                            (Some("name".into()), Node::text(name)),
                            (Some("ty".into()), lift.expr(ty)?),
                        ],
                    ))
                })
                .collect()
        };
        // A goal as a `Judgement` of `Type`, in a context.
        let code = |goal: &SurfaceTerm, ctx: Vec<Node>| -> Result<Node, String> {
            Ok(Node::Ctor(
                "Judgement".into(),
                vec![
                    (Some("term".into()), lift.expr(goal)?),
                    (
                        Some("ty".into()),
                        lift.expr(&SurfaceTerm::var("Type", goal.span))?,
                    ),
                    (Some("row".into()), Node::List(Vec::new())),
                    (Some("ctx".into()), Node::List(ctx)),
                    (Some("fragment".into()), Node::text("Kernel")),
                    (Some("tys".into()), Node::List(Vec::new())),
                    (Some("usage".into()), Node::List(Vec::new())),
                    (Some("span".into()), span_node(goal.span)),
                ],
            ))
        };
        let built = (|| -> Result<Node, String> {
            let outer = binders(&ctx)?;
            let before = code(step.before.as_ref().expect("filled"), outer.clone())?;
            let mut after = Vec::new();
            for (added, goal) in &arms {
                let mut inner = outer.clone();
                let mine = binders(added)?;
                inner.extend(mine.iter().cloned());
                after.push(Node::Ctor(
                    "StepGoal".into(),
                    vec![
                        (Some("binders".into()), Node::List(mine)),
                        (Some("ty".into()), code(goal, inner)?),
                    ],
                ));
            }
            Ok(Node::Ctor(
                "ProofStep".into(),
                vec![
                    (Some("before".into()), before),
                    (Some("arg".into()), lift.expr(&step.arg)?),
                    (Some("after".into()), Node::List(after)),
                    (Some("span".into()), span_node(step.call)),
                ],
            ))
        })();
        let input = match built {
            Ok(n) => n,
            Err(m) => {
                self.error("macro.code", m, step.call);
                return None;
            }
        };
        let lib = self.lib.as_ref().expect("the library is built");
        let function = self.macros[&name].function.clone();
        let mut host = Host::new(self.opts.call_steps, self.opts.allocations);
        host.elab = Some(self.elab_for(id));
        let ran = call_function(&lib.program, &lib.report, &function, &[input], &mut host);
        let (out, stats) = match ran {
            Ok(r) => r,
            Err(e) => {
                self.run_error(&name, e, step.call);
                return None;
            }
        };
        let names: HashMap<u64, String> = atoms.iter().map(|(n, a)| (*a, n.clone())).collect();
        let mut captures = Vec::new();
        let lowered = {
            let spans = &mut self.spans;
            let mut fresh = |written: u32| spans.fresh(written, id);
            let mut lower = Lower {
                scope: u64::from(id),
                fresh: &mut fresh,
                captures: Vec::new(),
                atoms: &names,
                opened: Vec::new(),
            };
            let r = lower.expr(&out);
            captures.append(&mut lower.captures);
            r
        };
        let mut term = match lowered {
            Ok(t) => t,
            Err(m) => {
                let (code, message) = m
                    .split_once(": ")
                    .filter(|(c, _)| c.starts_with("macro."))
                    .unwrap_or(("macro.shape", &m));
                self.error(code, message.to_string(), step.call);
                return None;
            }
        };
        self.term(&mut term);
        let print = crate::surface::print::print_term;
        let exp = Expansion {
            id,
            macro_name: name.clone(),
            function,
            kind: "step",
            parent: None,
            call: step.call,
            root: 0,
            syntax: String::new(),
            text: print(&step.arg),
            steps: stats.steps,
            allocations: stats.allocations,
            captures,
            input: format!(
                "{} |- {}{}",
                here.context
                    .iter()
                    .map(|(n, t)| format!("{n}: {}", print(t)))
                    .collect::<Vec<_>>()
                    .join(", "),
                print(step.before.as_ref().expect("filled")),
                step.arms
                    .iter()
                    .map(|a| format!(
                        " ; {} |- {}",
                        a.binders
                            .iter()
                            .map(|(n, t)| format!("{n}: {}", print(t)))
                            .collect::<Vec<_>>()
                            .join(", "),
                        print(&a.goal)
                    ))
                    .collect::<String>()
            ),
            output: print(&term),
        };
        Some((term, exp))
    }
}

/// The first step of `s` in the order the text reads, and where its call is.
fn first_step(s: &Stmt) -> Option<(Step, Span)> {
    let mut s = s.clone();
    let mut found = None;
    walk::stmt(&mut s, &mut |t| {
        if found.is_none()
            && let TermKind::Step(step) = &*t.kind
        {
            found = Some(((**step).clone(), step.call));
        }
    });
    found
}

/// `d` with its first step replaced by `by`, and every other step by a hole.
fn with_first_step(d: &Stmt, by: SurfaceTerm) -> Stmt {
    let mut d = d.clone();
    let mut by = Some(by);
    let mut other = 0usize;
    walk::stmt(&mut d, &mut |t| {
        if let TermKind::Step(_) = &*t.kind {
            match by.take() {
                Some(b) => *t = b,
                None => {
                    other += 1;
                    *t = SurfaceTerm::new(TermKind::Hole(format!("step'other{other}")), t.span);
                }
            }
        }
    });
    d
}

/// `d` with its first step replaced by `by`, the others left as they are.
fn put_first_step(d: &mut Stmt, by: SurfaceTerm) {
    let mut by = Some(by);
    walk::stmt(d, &mut |t| {
        if by.is_some() && matches!(&*t.kind, TermKind::Step(_)) {
            *t = by.take().expect("checked");
        }
    });
}

/// After an error: each step is a hole, so that nothing else is said of it.
/// `items` in the modules `path`, innermost last.
fn wrap(path: &[(String, Span)], items: Vec<Stmt>) -> Vec<Stmt> {
    let mut items = items;
    for (name, span) in path.iter().rev() {
        items = vec![Stmt::Module {
            name: name.clone(),
            items,
            span: *span,
        }];
    }
    items
}

/// Gives `d` back the name `original` was written with.
fn set_name(d: &mut Stmt, original: &Stmt) {
    match (d, original) {
        (Stmt::Theorem(t) | Stmt::Def(t), Stmt::Theorem(o) | Stmt::Def(o)) => {
            t.name = o.name.clone()
        }
        (Stmt::Fn(f), Stmt::Fn(o)) => f.name = o.name.clone(),
        _ => {}
    }
}

fn without_steps(mut d: Stmt) -> Stmt {
    walk::stmt(&mut d, &mut |t| {
        if matches!(&*t.kind, TermKind::Step(_)) {
            *t = SurfaceTerm::new(TermKind::Hole("step".into()), t.span);
        }
    });
    d
}

/// The goal a step starts from: written after `->`, or, for the whole proof
/// of an arm, the arm's goal (and then `->` is not written).
fn fill_before(d: &mut Stmt) -> Result<(), (Message, Span)> {
    let mut error = None;
    walk::stmt(d, &mut |t| {
        let TermKind::Step(step) = Arc::make_mut(&mut t.kind) else {
            return;
        };
        if step.before.is_none() && error.is_none() {
            error = Some((msg!("macro-step-write-before"), step.call));
        }
        for arm in &mut step.arms {
            if let TermKind::Step(inner) = Arc::make_mut(&mut arm.body.kind) {
                if inner.before.is_some() {
                    if error.is_none() {
                        error = Some((msg!("macro-step-arm-before"), inner.call));
                    }
                } else {
                    inner.before = Some(arm.goal.clone());
                }
            }
        }
    });
    match error {
        Some(e) => Err(e),
        None => Ok(()),
    }
}
