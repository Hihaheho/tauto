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

/// A statement as `Debug` writes it, without the places it holds: what a statement before a
/// declaration gives its steps does not depend on where it is written.
fn placeless(s: &Stmt) -> String {
    let text = format!("{s:?}");
    let mut out = String::with_capacity(text.len());
    let mut rest = text.as_str();
    while let Some(i) = rest.find("Span { start: ") {
        out.push_str(&rest[..i]);
        match rest[i..].find('}') {
            Some(j) => rest = &rest[i + j + 1..],
            None => {
                rest = &rest[i..];
                break;
            }
        }
    }
    out.push_str(rest);
    out
}

#[derive(Clone)]
struct KeptStep {
    /// The declaration as it was given, and where it started.
    given: Stmt,
    start: u32,
    out: Stmt,
    spans: SpanMap,
    expansions: Vec<Expansion>,
    errors: Vec<(Message, Span)>,
    fixes: Vec<(Span, crate::surface::Fix)>,
    warnings: Vec<(Message, Span)>,
    written: Vec<(usize, crate::surface::Name, String, Span)>,
    file_steps: u64,
    file_expanded: bool,
}

const KEPT_STEPS_MAX: usize = 4096;

thread_local! {
    static KEEP_STEPS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static KEPT_STEPS: RefCell<HashMap<(u64, u64), KeptStep>> = RefCell::new(HashMap::new());
}

thread_local! {
    /// A digest of each file of the program being expanded: its path and its text.
    static SOURCES: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

/// The files of the program the next expansion reads, each as a digest of its path and its
/// text: what the steps of a declaration made is kept on disk (`tauto-cache`) by these and
/// the declaration, for a server that reads the same files after it starts again.
pub fn set_sources(digests: Vec<String>) {
    SOURCES.with(|s| *s.borrow_mut() = digests);
}

/// Whether this thread keeps what the steps of each declaration made, for an expansion that
/// reaches the same declaration after the same statements again (an editor's server, which
/// reads a file again at every edit); off by default.
pub fn keep_steps(keep: bool) {
    KEEP_STEPS.with(|k| k.set(keep));
    if !keep {
        KEPT_STEPS.with(|m| m.borrow_mut().clear());
    }
}

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
                // A step in the argument of a typed macro runs where the
                // argument is checked, in the typed pass (`typed.rs`).
                Some(_) if self.step_in_typed(&s) => out.push(s),
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
                    let mut before = outer.to_vec();
                    before.extend(wrap(path, out.clone()));
                    self.elab_module = path.iter().map(|(n, _)| n.clone()).collect();
                    let done = self.step_decl_kept(s, &before, path);
                    self.elab_module.clear();
                    out.push(done);
                }
            }
        }
        out
    }

    /// [`Self::step_decl`], or what it made the last time it was given the same declaration
    /// after the same statements, at the same point of the expansion ([`keep_steps`]), when
    /// the declaration has only moved since: what it made moves with it. What it adds to the
    /// expansion (errors, expansions and their spans, …) is added again.
    fn step_decl_kept(&mut self, d: Stmt, before: &[Stmt], path: &[(String, Span)]) -> Stmt {
        // The declaration is checked with its names written out (`add` in `module Nat` and
        // `Nat.add` are the function `Nat.add`), and keeps its own name, which the module
        // still gives it.
        let flat = |e: &Self, d: Stmt| {
            let mut all: Vec<Stmt> = e.done.clone();
            all.extend(before.iter().cloned());
            all.extend(wrap(path, vec![d]));
            crate::surface::modules::resolve_in_prelude(all)
                .0
                .pop()
                .expect("the declaration")
        };
        if !KEEP_STEPS.with(std::cell::Cell::get) {
            let d = flat(self, d);
            return self.step_decl(d, before);
        }
        let start = super::stmt_range(&d).map_or(0, |(lo, _)| lo);
        let done_key = self.done_key();
        let key = {
            use std::hash::{Hash, Hasher};
            // Each statement with its places counted from where it starts: one that only
            // moved reads the same.
            let relative = |s: &Stmt| {
                let mut s = s.clone();
                let lo = super::stmt_range(&s).map_or(0, |(lo, _)| lo);
                crate::surface::shift::moved(&mut s, -(lo as i64));
                format!("{s:?}")
            };
            let mut text = relative(&d);
            for b in before {
                text.push('|');
                text.push_str(&placeless(b));
            }
            // The binders' numbers count every binder the thread has made.
            let mut text = tauto_identity::refs_in_order(&text);
            text.push_str(&format!(
                "|{:?}|{}|{}|{}|{}|{}|{}",
                self.elab_module,
                done_key,
                self.file,
                self.spans.len(),
                self.expansions.len(),
                self.errors.len(),
                self.file_steps
            ));
            let mut a = std::collections::hash_map::DefaultHasher::new();
            text.hash(&mut a);
            let mut b = std::collections::hash_map::DefaultHasher::new();
            0xa5u8.hash(&mut b);
            text.hash(&mut b);
            (a.finish(), b.finish())
        };
        if let Some(k) = KEPT_STEPS.with(|m| m.borrow().get(&key).cloned()) {
            let by = start as i64 - k.start as i64;
            if crate::surface::shift::moved_to(&k.given, &d, by) {
                use crate::surface::shift::place;
                let from = self.spans.len();
                self.spans = k.spans;
                self.spans.moved_from(from, by);
                self.expansions
                    .extend(k.expansions.into_iter().map(|mut e| {
                        e.call = place(e.call, by);
                        e
                    }));
                self.errors
                    .extend(k.errors.into_iter().map(|(m, at)| (m, place(at, by))));
                self.fixes.extend(k.fixes.into_iter().map(|(at, mut f)| {
                    f.span = place(f.span, by);
                    (place(at, by), f)
                }));
                self.warnings
                    .extend(k.warnings.into_iter().map(|(m, at)| (m, place(at, by))));
                self.written.extend(
                    k.written
                        .into_iter()
                        .map(|(i, n, t, at)| (i, n, t, place(at, by))),
                );
                self.file_steps = k.file_steps;
                self.file_expanded |= k.file_expanded;
                let mut out = k.out;
                crate::surface::shift::moved(&mut out, by);
                crate::surface::walk::stmt(&mut out, &mut SurfaceTerm::freshen);
                return out;
            }
        }
        let lens = (
            self.expansions.len(),
            self.errors.len(),
            self.fixes.len(),
            self.warnings.len(),
            self.written.len(),
        );
        let expanded = self.file_expanded;
        self.file_expanded = false;
        let given = d.clone();
        let d = flat(self, d);
        let out = self.step_decl_stored(&given, d, before);
        let kept = KeptStep {
            given,
            start,
            out: out.clone(),
            spans: self.spans.clone(),
            expansions: self.expansions[lens.0..].to_vec(),
            errors: self.errors[lens.1..].to_vec(),
            fixes: self.fixes[lens.2..].to_vec(),
            warnings: self.warnings[lens.3..].to_vec(),
            written: self.written[lens.4..].to_vec(),
            file_steps: self.file_steps,
            file_expanded: self.file_expanded,
        };
        self.file_expanded |= expanded;
        KEPT_STEPS.with(|m| {
            let mut m = m.borrow_mut();
            if m.len() >= KEPT_STEPS_MAX {
                m.clear();
            }
            m.insert(key, kept);
        });
        out
    }

    /// [`Self::step_decl`] of `d` (`given` as written), from what its tactics made the last
    /// time the same files were read, when that is on disk: the tactics are not run again,
    /// and neither are the checks of their goals, as the kernel checks the declaration they
    /// make anyway. What a run makes without an error is put on disk for the next time.
    fn step_decl_stored(&mut self, given: &Stmt, d: Stmt, before: &[Stmt]) -> Stmt {
        let action = self.stored_action(given);
        let cache = tauto_cache::BuildCache::from_env().ok();
        if let (Some(action), Some(cache)) = (&action, &cache)
            && let Some(outputs) = cache.get(action)
            && let Some(blob) = outputs.0.get("steps")
            && let Some(bytes) = cache.get_blob(blob)
            && let Ok(text) = String::from_utf8(bytes)
        {
            let texts: Vec<&str> = text.split('\u{0}').collect();
            if let Some(out) = self.steps_from(d.clone(), before, &texts) {
                return out;
            }
        }
        let errors = self.errors.len();
        let outer = self.step_texts.replace(Vec::new());
        let out = self.step_decl(d, before);
        let texts = std::mem::replace(&mut self.step_texts, outer).unwrap_or_default();
        if self.errors.len() == errors
            && !texts.is_empty()
            && texts
                .iter()
                .all(|t| !t.contains('\u{0}') && crate::surface::parse_expr_at(t, 0).is_ok())
            && let (Some(action), Some(cache)) = (&action, &cache)
            && let Ok(blob) = cache.put_blob(texts.join("\u{0}").as_bytes())
        {
            let mut outputs = tauto_cache::Outputs::default();
            outputs.0.insert("steps".into(), blob);
            let _ = cache.put(action, &outputs);
        }
        out
    }

    /// The action on disk of the steps of `given` in this file, read after the files it is
    /// read after; none when the files are not known.
    fn stored_action(&self, given: &Stmt) -> Option<tauto_cache::Action> {
        let sources = SOURCES.with(|s| s.borrow().get(..=self.file).map(|d| d.join("\n")));
        let sources = sources?;
        let mut d = given.clone();
        let lo = super::stmt_range(&d).map_or(0, |(lo, _)| lo);
        crate::surface::shift::moved(&mut d, -(lo as i64));
        let decl = tauto_identity::refs_in_order(&format!("{d:?}"));
        Some(
            tauto_cache::Action::new("steps", "")
                .input("expander", include_str!("step.rs").as_bytes())
                .input("version", env!("CARGO_PKG_VERSION").as_bytes())
                .input("sources", sources.as_bytes())
                .input("module", format!("{:?}", self.elab_module).as_bytes())
                .input("declaration", decl.as_bytes()),
        )
    }

    /// The steps of `d` made from what their tactics made before (`texts`, one for each step
    /// in the order they are expanded): each step becomes `the(G0, term)` with the arms in
    /// its holes. None when the texts do not fit the steps; they are then expanded again.
    fn steps_from(&mut self, mut d: Stmt, before: &[Stmt], texts: &[&str]) -> Option<Stmt> {
        first_step(&d)?;
        kernel_decl(&d)?;
        if self.lib.as_ref().is_some_and(|l| l.problem.is_some()) {
            return None;
        }
        fill_before(&mut d).ok()?;
        self.bindings.statements(std::slice::from_mut(&mut d));
        let mut expanded = false;
        for text in texts {
            let (step, _) = first_step(&d)?;
            let mut term = crate::surface::parse_expr_at(text, 0).ok()?;
            walk::term(&mut term, &mut |t| t.span = step.call);
            let mut found = Vec::new();
            walk::term(&mut term, &mut |t| {
                if let TermKind::Hole(h) = Arc::make_mut(&mut t.kind) {
                    found.push(h.clone());
                    if let Some(k) = h.strip_prefix("arm").and_then(|k| k.parse::<usize>().ok()) {
                        *h = arm_hole(k);
                    }
                }
            });
            let mut wanted: Vec<String> =
                (1..=step.arms.len()).map(|k| format!("arm{k}")).collect();
            found.sort();
            wanted.sort();
            if found != wanted {
                return None;
            }
            walk::term(&mut term, &mut |t| {
                if let TermKind::Hole(h) = &*t.kind
                    && let Some(k) = h
                        .strip_prefix("step'arm")
                        .and_then(|k| k.parse::<usize>().ok())
                {
                    let arm = &step.arms[k - 1];
                    *t = match &*arm.body.kind {
                        TermKind::Step(_) => arm.body.clone(),
                        _ => SurfaceTerm::app(
                            "the",
                            vec![arm.goal.clone(), arm.body.clone()],
                            arm.span,
                        ),
                    };
                }
            });
            let g0 = step.before.clone()?;
            put_first_step(&mut d, SurfaceTerm::app("the", vec![g0, term], step.call));
            d = self.resolved(d, before);
            expanded = true;
        }
        if first_step(&d).is_some() {
            return None;
        }
        self.file_expanded |= expanded;
        Some(d)
    }

    /// A hash of the statements of the files before this one, made once for each file.
    fn done_key(&mut self) -> u64 {
        if let Some(h) = self.done_key {
            return h;
        }
        // Written into the hash as it is made: the text of every statement of the files
        // before can be larger than an allocation may be.
        struct Hashing(std::collections::hash_map::DefaultHasher);
        impl std::fmt::Write for Hashing {
            fn write_str(&mut self, s: &str) -> std::fmt::Result {
                std::hash::Hasher::write(&mut self.0, s.as_bytes());
                Ok(())
            }
        }
        let mut a = Hashing(std::collections::hash_map::DefaultHasher::new());
        for s in &self.done {
            let _ = std::fmt::Write::write_fmt(&mut a, format_args!("{s:?}\n"));
        }
        let h = std::hash::Hasher::finish(&a.0);
        self.done_key = Some(h);
        h
    }

    /// Whether a step of `s` is in the argument of a typed macro's call.
    fn step_in_typed(&mut self, s: &Stmt) -> bool {
        let mut calls = Vec::new();
        let mut probe = s.clone();
        walk::stmt(&mut probe, &mut |t| {
            if matches!(&*t.kind, TermKind::MacroCall { .. }) {
                calls.push(t.clone());
            }
        });
        calls.into_iter().any(|call| {
            let mut call = call;
            let mut any = false;
            walk::term(&mut call, &mut |t| {
                any |= matches!(&*t.kind, TermKind::Step(_))
            });
            any && self.is_typed(&call)
        })
    }

    pub(super) fn step_decl(&mut self, mut d: Stmt, before: &[Stmt]) -> Stmt {
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
        let (mut prefix, _) = crate::surface::modules::resolve_in_prelude(all);
        self.bindings.statements(&mut prefix);
        self.bindings.statements(std::slice::from_mut(&mut d));
        self.elab_prefix = prefix.clone();
        let kernel = match self.checker.prefixed(&prefix) {
            Ok(k) => k,
            Err(m) => {
                self.error("step.kernel", m, at);
                return without_steps(d);
            }
        };
        // The context of the next step, taken from the check of the output of
        // the one before it.
        let mut carried: Option<HoleGoal> = None;
        while let Some((step, _)) = first_step(&d) {
            match self.one_step(kernel.as_ref(), &d, before, &step, carried.take()) {
                Some((term, next)) => {
                    carried = next;
                    put_first_step(&mut d, term);
                    d = self.resolved(d, before);
                    self.file_expanded = true;
                }
                None => return without_steps(d),
            }
        }
        d
    }

    /// The term the first step of `d` stands for, or `None` after an error,
    /// with the hole of the step after it as the check of the output left it.
    /// `known` is the hole of this step from the check of the step before it;
    /// without it the declaration is checked with a hole in this step's place.
    fn one_step(
        &mut self,
        kernel: &dyn PrefixedChecker,
        d: &Stmt,
        before: &[Stmt],
        step: &Step,
        known: Option<HoleGoal>,
    ) -> Option<(SurfaceTerm, Option<HoleGoal>)> {
        let at = step.call;
        let g0 = step.before.clone().expect("filled by fill_before");
        // 1. The variables in scope where the step is: the declaration with a
        // hole in its place.
        let here = if known.is_some() {
            known
        } else {
            let probe = with_first_step(d, SurfaceTerm::new(TermKind::Hole(GOAL.into()), at));
            match kernel.verdict(&probe) {
                Some(Verdict::Incomplete { holes, .. }) => {
                    holes.into_iter().find(|h| h.name == GOAL)
                }
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
            }
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
        let id = self.expansions.len() as u32 + 1;
        let (term, exp) = self.run_tactic(step, id, &here)?;
        if let Some(texts) = &mut self.step_texts {
            texts.push(crate::surface::print::print_term(&term));
        }
        // A tactic makes a term with holes for the arms. A step in what it makes
        // would run another tactic on a goal nobody wrote.
        let mut made = term.clone();
        let mut nested = false;
        walk::term(&mut made, &mut |t| {
            nested |= matches!(&*t.kind, TermKind::Step(_))
        });
        if nested {
            self.error("step.nested", msg!("macro-step-nested"), at);
            return None;
        }
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
        let is_outer = |name: &crate::surface::Name| {
            let mut reference = name.clone();
            loop {
                if here.context.iter().any(|(outer, _)| outer == &reference) {
                    return true;
                }
                match reference.as_local().and_then(|local| local.origin()) {
                    Some(origin) => reference = origin.clone().into(),
                    None => return false,
                }
            }
        };
        if proposing {
            let visible = self.seeing.get(self.file).cloned().unwrap_or_default();
            let names = tauto_surface::source_names::SourceNames::new(&self.bindings, &visible);
            let mut arms = Vec::new();
            for k in 1..=count {
                let Some(hole) = holes.iter().find(|h| h.name == arm_hole(k)) else {
                    self.error("step.holes", msg!("macro-step-hole-no-goal", k = k), at);
                    return None;
                };
                let locals: Vec<_> = hole.context.iter().map(|(name, _)| name.clone()).collect();
                let added = hole
                    .context
                    .iter()
                    .filter(|(n, _)| !is_outer(n))
                    .map(|(n, ty)| {
                        names
                            .term(ty, &locals)
                            .map(|ty| format!("{}: {ty}", crate::surface::print::raw(n)))
                    })
                    .collect::<Result<Vec<_>, _>>();
                let (added, goal) = match (added, names.term(&hole.goal, &locals)) {
                    (Ok(added), Ok(goal)) => (added, goal),
                    (Err(error), _) | (_, Err(error)) => {
                        self.error("step.source", error, at);
                        return None;
                    }
                };
                let binders = if added.is_empty() {
                    String::new()
                } else {
                    format!("{} ", added.join(", "))
                };
                arms.push(format!("{binders}⊢ {} from ?arm{k}", goal));
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
            let added: Vec<&(crate::surface::Name, SurfaceTerm)> =
                hole.context.iter().filter(|(n, _)| !is_outer(n)).collect();
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
                            name = name.to_string(),
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
        // The next step is the first `step'other` of this probe, unless a step
        // in the body of an arm comes before it: then the declaration is
        // checked again for its context.
        let nested = step.arms.iter().any(|a| {
            let mut body = a.body.clone();
            let mut any = false;
            walk::term(&mut body, &mut |t| {
                any |= matches!(&*t.kind, TermKind::Step(_))
            });
            any
        });
        let next = if nested {
            None
        } else {
            holes.into_iter().find(|h| h.name == "step'other1")
        };
        Some((SurfaceTerm::app("the", vec![g0, out], step.call), next))
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
    fn rewrite_arm(
        &mut self,
        arm: &StepArm,
        added: &[&(crate::surface::Name, SurfaceTerm)],
        goal: &SurfaceTerm,
    ) {
        use crate::surface::print::print_term;
        let kept = added.len() == arm.binders.len();
        let binders: Vec<String> = added
            .iter()
            .enumerate()
            .map(|(i, (n, t))| {
                let name = if kept {
                    arm.binders[i].0.as_str()
                } else {
                    n.as_str()
                };
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
        context: &[(crate::surface::Name, SurfaceTerm)],
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
        // A step a macro made calls its tactic as one written in the file: the
        // file's import of the tactic is used.
        if self.spans.origin(step.call.start).is_some() {
            self.written.push((
                self.file,
                crate::surface::Name::from(name.as_str()),
                format!("{}{name}", crate::surface::qualify::CALLED),
                step.call,
            ));
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
        let mut atoms: HashMap<crate::surface::Name, u64> = HashMap::new();
        let mut ctx: Vec<(u64, String, SurfaceTerm)> = Vec::new();
        for (name, ty) in &here.context {
            let atom = ctx.len() as u64 + 1;
            atoms.insert(name.clone(), atom);
            ctx.push((atom, name.to_string(), ty.clone()));
        }
        let context: Vec<_> = here.context.iter().map(|(name, _)| name.clone()).collect();
        let mut resolver = self.bindings.clone();
        let mut before = step.before.clone().expect("filled");
        resolver.term_in_context(&mut before, &context);
        let mut argument = step.arg.clone();
        resolver.term_in_context(&mut argument, &context);
        let mut next = ctx.len() as u64 + 1;
        let mut arms: Vec<(Vec<(u64, String, SurfaceTerm)>, SurfaceTerm)> = Vec::new();
        for arm in &step.arms {
            let mut context = context.clone();
            let mut added = Vec::new();
            for (n, ty) in &arm.binders {
                let mut ty = ty.clone();
                resolver.term_in_context(&mut ty, &context);
                let reference = match n {
                    crate::surface::Name::Local(_) => n.clone(),
                    _ => crate::surface::Name::Local(tauto_surface::identity::LocalRef::fresh(
                        n.as_str(),
                    )),
                };
                atoms.insert(reference.clone(), next);
                context.push(reference);
                added.push((next, n.to_string(), ty));
                next += 1;
            }
            let mut goal = arm.goal.clone();
            resolver.term_in_context(&mut goal, &context);
            arms.push((added, goal));
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
            let before = code(&before, outer.clone())?;
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
                    (Some("arg".into()), lift.expr(&argument)?),
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
        host.resolve_global = Some(self.global_resolver(&name));
        host.elab = Some(self.elab_for(id, &atoms));
        let ran = call_bound_function(
            &lib.program,
            &lib.report,
            &info.function,
            &[input],
            &mut host,
        );
        let (out, stats) = match ran {
            Ok(r) => r,
            Err(e) => {
                self.run_error(&name, e, step.call);
                return None;
            }
        };
        let names: HashMap<u64, crate::surface::Name> =
            atoms.iter().map(|(n, a)| (*a, n.clone())).collect();
        let mut captures = Vec::new();
        let lowered = {
            let spans = &mut self.spans;
            let mut fresh = |written: u32| spans.fresh(written, id, step.call.start);
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
            function: function.to_string(),
            kind: "step",
            parent: None,
            call: step.call,
            root: 0,
            syntax: String::new(),
            text: print(&step.arg),
            steps: stats.steps,
            allocations: stats.allocations,
            captures,
            input_tree: None,
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
pub(super) fn wrap(path: &[(String, Span)], items: Vec<Stmt>) -> Vec<Stmt> {
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

fn without_steps(mut d: Stmt) -> Stmt {
    // Each hole has its own name: one declaration may hold several steps, and
    // a hole written twice is an error of its own.
    let mut n = 0usize;
    walk::stmt(&mut d, &mut |t| {
        if matches!(&*t.kind, TermKind::Step(_)) {
            n += 1;
            *t = SurfaceTerm::new(
                TermKind::Hole(if n == 1 {
                    "step".into()
                } else {
                    format!("step'{n}")
                }),
                t.span,
            );
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

/// Whether `s` has a step anywhere, the arguments of macros' calls too.
pub(super) fn has_step(s: &Stmt) -> bool {
    first_step(s).is_some()
}
