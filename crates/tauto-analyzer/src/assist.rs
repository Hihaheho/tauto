//! What an editor (or an AI) asks about a hole beyond its goal: the constants
//! and hypotheses whose type fits it (`suggest`), and the skeleton of a proof
//! that a type decides (`expand`). Neither decides anything: a candidate is a
//! guess from the shape of the types, and the kernel's verdict on it comes from
//! `try` (`report::try_fill`) like any other text.

use std::collections::{HashMap, HashSet};

use tauto::check::{LibEntry, Verdict, describe, free_vars};
use tauto::report::{Attempt, Hole, Json, Report, check_report, find_hole, term_json, try_fill};
use tauto::surface::{SurfaceTerm as T, TermKind};

/// First-order matching of a type that names unknowns (the parameters of a
/// constant) against another, up to the names of bound variables.
struct Matcher<'a> {
    metas: &'a HashSet<String>,
    bound: HashMap<String, T>,
    /// The binders passed under, as (in the pattern, in the target).
    env: Vec<(String, String)>,
}

impl<'a> Matcher<'a> {
    fn new(metas: &'a HashSet<String>) -> Self {
        Self {
            metas,
            bound: HashMap::new(),
            env: Vec::new(),
        }
    }

    fn unify(&mut self, p: &T, t: &T) -> bool {
        match (&*p.kind, &*t.kind) {
            (TermKind::Var(m), _)
                if self.metas.contains(m) && !self.env.iter().any(|(a, _)| a == m) =>
            {
                if let Some(b) = self.bound.get(m).cloned() {
                    return Matcher::new(&HashSet::new()).unify(&b, t);
                }
                // The target must not mention what it binds on the way.
                if free_vars(t)
                    .iter()
                    .any(|v| self.env.iter().any(|(_, tv)| tv == v))
                {
                    return false;
                }
                self.bound.insert(m.clone(), t.clone());
                true
            }
            (TermKind::Var(a), TermKind::Var(b)) => {
                match self.env.iter().rev().find(|(pa, _)| pa == a) {
                    Some((_, tb)) => tb == b,
                    None => a == b && !self.env.iter().any(|(_, tb)| tb == b),
                }
            }
            (TermKind::Nat(a), TermKind::Nat(b)) | (TermKind::Text(a), TermKind::Text(b)) => a == b,
            (TermKind::Bool(a), TermKind::Bool(b)) => a == b,
            (
                TermKind::App {
                    function: f,
                    arguments: xs,
                },
                TermKind::App {
                    function: g,
                    arguments: ys,
                },
            ) => {
                xs.len() == ys.len()
                    && self.unify(f, g)
                    && xs.iter().zip(ys).all(|(x, y)| self.unify(x, y))
            }
            (
                TermKind::Pi {
                    params: ps,
                    result: r,
                    ..
                },
                TermKind::Pi {
                    params: qs,
                    result: s,
                    ..
                },
            ) if ps.len() == qs.len() => {
                let depth = self.env.len();
                let mut ok = true;
                for ((pn, pd), (qn, qd)) in ps.iter().zip(qs) {
                    if !self.unify(pd, qd) {
                        ok = false;
                        break;
                    }
                    self.env.push((
                        pn.clone().unwrap_or_else(|| "_".into()),
                        qn.clone().unwrap_or_else(|| "_".into()),
                    ));
                }
                let ok = ok && self.unify(r, s);
                self.env.truncate(depth);
                ok
            }
            (
                TermKind::Lam {
                    params: ps,
                    body: a,
                    ..
                },
                TermKind::Lam {
                    params: qs,
                    body: b,
                    ..
                },
            ) if ps.len() == qs.len() => {
                let depth = self.env.len();
                self.env.extend(ps.iter().cloned().zip(qs.iter().cloned()));
                let ok = self.unify(a, b);
                self.env.truncate(depth);
                ok
            }
            _ => false,
        }
    }

    /// `t` with the unknowns that were matched replaced by what they matched,
    /// and those that were not by `?name`.
    fn apply(&self, t: &T) -> T {
        self.apply_under(t, &mut Vec::new())
    }

    fn apply_under(&self, t: &T, shadow: &mut Vec<String>) -> T {
        let sp = t.span;
        match &*t.kind {
            TermKind::Var(n) if self.metas.contains(n) && !shadow.contains(n) => {
                match self.bound.get(n) {
                    Some(b) => b.clone(),
                    None => T::var(&format!("?{n}"), sp),
                }
            }
            TermKind::App {
                function,
                arguments,
            } => T::new(
                TermKind::App {
                    function: Box::new(self.apply_under(function, shadow)),
                    arguments: arguments
                        .iter()
                        .map(|a| self.apply_under(a, shadow))
                        .collect(),
                },
                sp,
            ),
            TermKind::Pi {
                params,
                result,
                effects,
            } => {
                let depth = shadow.len();
                let mut out = Vec::new();
                for (n, d) in params {
                    out.push((n.clone(), self.apply_under(d, shadow)));
                    shadow.extend(n.clone());
                }
                let result = self.apply_under(result, shadow);
                shadow.truncate(depth);
                T::new(
                    TermKind::Pi {
                        params: out,
                        result: Box::new(result),
                        effects: effects.clone(),
                    },
                    sp,
                )
            }
            TermKind::Lam {
                params,
                body,
                types,
            } => {
                let depth = shadow.len();
                shadow.extend(params.iter().cloned());
                let body = self.apply_under(body, shadow);
                shadow.truncate(depth);
                T::new(
                    TermKind::Lam {
                        params: params.clone(),
                        body: Box::new(body),
                        types: types.clone(),
                    },
                    sp,
                )
            }
            _ => t.clone(),
        }
    }
}

/// The parameters of a type written as a chain of Π, and what is left.
fn chain(ty: &T) -> (Vec<(Option<String>, T)>, &T) {
    let mut params = Vec::new();
    let mut at = ty;
    while let TermKind::Pi {
        params: ps, result, ..
    } = &*at.kind
    {
        params.extend(ps.iter().cloned());
        at = result;
    }
    (params, at)
}

/// An argument a suggestion leaves as a hole of its own.
#[derive(Debug, Clone)]
pub struct SuggestedArg {
    pub name: Option<String>,
    /// The hole written for it in [`Suggestion::term`].
    pub hole: String,
    /// Its type once the goal fixed what it could; an unknown nothing fixed
    /// is written `?name`.
    pub ty: T,
    pub unresolved_metas: Vec<String>,
}

/// A term whose type fits a hole: a hypothesis, or a constant applied to
/// holes for the premises it needs.
#[derive(Debug, Clone)]
pub struct Suggestion {
    pub name: String,
    /// `hypothesis`, or the kind of a library constant (`theorem`, …).
    pub kind: &'static str,
    /// `context` or `library`.
    pub source: &'static str,
    /// The text to give `try`, premises as holes: `and_left(?h_p)`.
    pub term: String,
    pub ty: T,
    pub args: Vec<SuggestedArg>,
    /// The result is a bare unknown (`False_elim`, `and_left`): it fits any
    /// goal, so it says little, and ranks last.
    pub generic: bool,
}

impl Suggestion {
    /// Nothing is left to prove: the candidate closes the hole by itself.
    pub fn exact(&self) -> bool {
        self.args.is_empty()
    }

    pub fn json(&self) -> Json {
        Json::Obj(vec![
            ("name", Json::Str(self.name.clone())),
            ("kind", Json::Str(self.kind.into())),
            ("source", Json::Str(self.source.into())),
            ("term", Json::Str(self.term.clone())),
            ("exact", Json::Bool(self.exact())),
            ("generic", Json::Bool(self.generic)),
            ("type", Json::Str(describe(&self.ty))),
            ("type_term", term_json(&self.ty)),
            (
                "arguments",
                Json::Arr(
                    self.args
                        .iter()
                        .map(|a| {
                            let mut f = Vec::new();
                            if let Some(n) = &a.name {
                                f.push(("name", Json::Str(n.clone())));
                            }
                            f.push(("hole", Json::Str(a.hole.clone())));
                            f.push(("type", Json::Str(describe(&a.ty))));
                            f.push(("type_term", term_json(&a.ty)));
                            f.push((
                                "unresolved_metas",
                                Json::Arr(
                                    a.unresolved_metas
                                        .iter()
                                        .map(|m| Json::Str(m.clone()))
                                        .collect(),
                                ),
                            ));
                            Json::Obj(f)
                        })
                        .collect(),
                ),
            ),
        ])
    }
}

/// Tries `ty` (of something called `name`, with `implicit` leading generics
/// that a call leaves out) against the goal: as it is, and applied to holes
/// for every explicit parameter.
fn candidate(
    hole: &Hole,
    name: &str,
    kind: &'static str,
    source: &'static str,
    ty: &T,
    implicit: usize,
) -> Option<Suggestion> {
    let goal = &hole.goal.goal;
    let (params, result) = chain(ty);
    let implicit = implicit.min(params.len());
    let metas: HashSet<String> = params.iter().filter_map(|(n, _)| n.clone()).collect();
    let explicit = &params[implicit..];

    // As it stands: a hypothesis whose type is the goal.
    if implicit == 0 {
        let none = HashSet::new();
        if Matcher::new(&none).unify(ty, goal) {
            return Some(Suggestion {
                name: name.into(),
                kind,
                source,
                term: name.into(),
                ty: ty.clone(),
                args: Vec::new(),
                generic: false,
            });
        }
    }
    // Applied: the generics are what matching fixes; the explicit parameters
    // are premises, each a hole.
    let mut m = Matcher::new(&metas);
    if !m.unify(result, goal) {
        return None;
    }
    let args: Vec<SuggestedArg> = explicit
        .iter()
        .enumerate()
        .map(|(i, (n, d))| {
            let ty = m.apply(d);
            SuggestedArg {
                name: n.clone().filter(|n| n != "_"),
                hole: format!(
                    "{}_{}",
                    hole.goal.name,
                    n.as_deref()
                        .filter(|n| *n != "_")
                        .map_or_else(|| (i + 1).to_string(), str::to_string)
                ),
                unresolved_metas: free_vars(&ty)
                    .into_iter()
                    .filter(|v| v.starts_with('?'))
                    .collect(),
                ty,
            }
        })
        .collect();
    let term = if args.is_empty() && implicit == 0 {
        name.to_string()
    } else {
        format!(
            "{name}({})",
            args.iter()
                .map(|a| format!("?{}", a.hole))
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    Some(Suggestion {
        name: name.into(),
        kind,
        source,
        term,
        ty: ty.clone(),
        args,
        generic: matches!(&*result.kind, TermKind::Var(v) if metas.contains(v)),
    })
}

/// The hypotheses and constants whose type fits `hole`, best first: those
/// that close it outright, then the fewest premises left, a hypothesis before
/// a constant, then by name. `limit` caps the list.
pub fn suggest(report: &Report, hole: &Hole, limit: usize) -> Vec<Suggestion> {
    let mut out = Vec::new();
    let in_scope: HashSet<&str> = hole.goal.context.iter().map(|(n, _)| n.as_str()).collect();
    for (n, ty) in hole.goal.context.iter().rev() {
        // A generated name cannot be written: the proof reaches it by a call.
        if n.contains('\'') {
            continue;
        }
        out.extend(candidate(hole, n, "hypothesis", "context", ty, 0));
    }
    for l in &report.library {
        let usable = l.state == "ok"
            && !matches!(&*l.kind, "inductive" | "eliminator")
            && !in_scope.contains(l.name.as_str())
            && !l.name.contains('\'');
        if usable {
            // The goal is held as a program writes it (`a = b`), so the type is too.
            let ty = tauto::check::Kernel::eqs_written(&l.ty);
            out.extend(candidate(hole, &l.name, l.kind, "library", &ty, l.implicit));
        }
    }
    out.sort_by_key(|s| {
        (
            s.generic,
            s.args.len(),
            s.source == "library",
            s.name.clone(),
        )
    });
    out.truncate(limit);
    out
}

/// How to break a hole into smaller ones.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum By {
    /// The goal is a function type: bind its argument.
    Intro,
    /// A `match` on a variable, an arm for each constructor of its type.
    Match(String),
    /// A step, `by name!(arg): G { … }`, with the arms its tactic leaves
    /// (`docs/design/macro-steps.md`): see [`expand_step`].
    Tactic { name: String, arg: String },
}

impl By {
    /// `intro`, `match(x)`; `induction(x)` is `match(x)`, the language having
    /// no other induction (a call of the theorem on a recursive field is the
    /// hypothesis).
    pub fn parse(text: &str) -> Result<By, String> {
        let text = text.trim();
        if text == "intro" {
            return Ok(By::Intro);
        }
        if let Some((name, rest)) = text.split_once("!(")
            && let Some(arg) = rest.strip_suffix(')')
            && !name.is_empty()
            && name.chars().all(|c| c.is_alphanumeric() || c == '_')
        {
            return Ok(By::Tactic {
                name: name.to_string(),
                arg: arg.to_string(),
            });
        }
        for head in ["match", "induction"] {
            if let Some(rest) = text.strip_prefix(head)
                && let Some(var) = rest
                    .trim()
                    .strip_prefix('(')
                    .and_then(|r| r.strip_suffix(')'))
                && !var.trim().is_empty()
            {
                return Ok(By::Match(var.trim().to_string()));
            }
        }
        Err(tauto_message::msg!("analyzer-not-an-expansion", text = text).to_string())
    }
}

/// One arm (or the one function body) an expansion wrote.
#[derive(Debug, Clone)]
pub struct Piece {
    pub hole: String,
    /// The constructor of the arm, if it is one.
    pub constructor: Option<String>,
    /// The variables the arm binds, with their types.
    pub binds: Vec<(String, T)>,
    /// Which of them are of the matched type: a call of the theorem on one is
    /// the induction hypothesis.
    pub recursive: Vec<String>,
}

/// The text that stands for a hole, and the holes it makes.
#[derive(Debug, Clone)]
pub struct Expansion {
    pub text: String,
    pub pieces: Vec<Piece>,
}

impl Expansion {
    pub fn json(&self) -> Json {
        Json::Obj(vec![
            ("text", Json::Str(self.text.clone())),
            (
                "holes",
                Json::Arr(
                    self.pieces
                        .iter()
                        .map(|p| {
                            let mut f = vec![("name", Json::Str(p.hole.clone()))];
                            if let Some(c) = &p.constructor {
                                f.push(("constructor", Json::Str(c.clone())));
                            }
                            f.push((
                                "binds",
                                Json::Arr(
                                    p.binds
                                        .iter()
                                        .map(|(n, t)| {
                                            Json::Obj(vec![
                                                ("name", Json::Str(n.clone())),
                                                ("type", Json::Str(describe(t))),
                                                ("type_term", term_json(t)),
                                            ])
                                        })
                                        .collect(),
                                ),
                            ));
                            f.push((
                                "recursive",
                                Json::Arr(
                                    p.recursive.iter().map(|n| Json::Str(n.clone())).collect(),
                                ),
                            ));
                            Json::Obj(f)
                        })
                        .collect(),
                ),
            ),
        ])
    }
}

/// A name for a binder that nothing in scope (or already chosen) uses.
fn fresh(wanted: &str, taken: &HashSet<String>) -> String {
    let wanted = if wanted.is_empty() || wanted == "_" || wanted.contains('\'') {
        "x"
    } else {
        wanted
    };
    if !taken.contains(wanted) {
        return wanted.to_string();
    }
    (1..)
        .map(|i| format!("{wanted}{i}"))
        .find(|n| !taken.contains(n))
        .expect("an unused name")
}

/// A hole name that no hole of the file has.
fn fresh_hole(wanted: &str, taken: &HashSet<String>) -> String {
    if !taken.contains(wanted) {
        return wanted.to_string();
    }
    (2..)
        .map(|i| format!("{wanted}{i}"))
        .find(|n| !taken.contains(n))
        .expect("an unused name")
}

/// The family a type is a value of: `Nat`, `List(A)`.
fn family_of(ty: &T) -> Option<&str> {
    match &*ty.kind {
        TermKind::Var(n) => Some(n),
        TermKind::App { function, .. } => match &*function.kind {
            TermKind::Var(n) => Some(n),
            _ => None,
        },
        _ => None,
    }
}

/// The skeleton `by` gives `hole`, its new holes named `<hole>_<part>` (the
/// constructor's name lowercased, or `body`), so that they stay the same
/// when the others are filled.
pub fn expand(report: &Report, hole: &Hole, by: &By) -> Result<Expansion, String> {
    let taken_holes: HashSet<String> = report.holes().into_iter().map(|h| h.goal.name).collect();
    let mut taken_names: HashSet<String> =
        hole.goal.context.iter().map(|(n, _)| n.clone()).collect();
    let base = &hole.goal.name;
    match by {
        By::Intro => {
            let TermKind::Pi { params, .. } = &*hole.goal.goal.kind else {
                return Err(tauto_message::msg!(
                    "analyzer-intro-not-function",
                    goal = describe(&hole.goal.goal)
                )
                .to_string());
            };
            let (wanted, domain) = &params[0];
            let name = fresh(wanted.as_deref().unwrap_or("h"), &taken_names);
            let new = fresh_hole(&format!("{base}_body"), &taken_holes);
            Ok(Expansion {
                text: format!("{name} => ?{new}"),
                pieces: vec![Piece {
                    hole: new,
                    constructor: None,
                    binds: vec![(name, domain.clone())],
                    recursive: Vec::new(),
                }],
            })
        }
        By::Match(var) => {
            let Some((_, ty)) = hole.goal.context.iter().find(|(n, _)| n == var) else {
                return Err(tauto_message::msg!(
                    "analyzer-match-not-in-scope",
                    var = var,
                    hole = base
                )
                .to_string());
            };
            let Some(family) = family_of(ty) else {
                return Err(tauto_message::msg!(
                    "analyzer-match-not-inductive-var",
                    var = var,
                    ty = describe(ty)
                )
                .to_string());
            };
            let Some(info) = report
                .library
                .iter()
                .find(|l| l.name == family)
                .and_then(|l: &LibEntry| l.inductive.as_ref())
            else {
                return Err(
                    tauto_message::msg!("analyzer-match-not-inductive", family = family)
                        .to_string(),
                );
            };
            let mut pieces = Vec::new();
            let mut arms = Vec::new();
            for c in &info.ctors {
                let mut used = taken_names.clone();
                let mut binds: Vec<(String, T)> = Vec::new();
                for (n, t) in &c.fields {
                    let name = fresh(n, &used);
                    used.insert(name.clone());
                    binds.push((name, t.clone()));
                }
                let recursive = c
                    .recursive
                    .iter()
                    .filter_map(|&i| binds.get(i).map(|(n, _)| n.clone()))
                    .collect();
                let new = fresh_hole(
                    &format!("{base}_{}", c.name.to_lowercase()),
                    &taken_holes
                        .iter()
                        .cloned()
                        .chain(pieces.iter().map(|p: &Piece| p.hole.clone()))
                        .collect(),
                );
                let pattern = if binds.is_empty() {
                    c.name.clone()
                } else {
                    format!(
                        "{}({})",
                        c.name,
                        binds
                            .iter()
                            .map(|(n, _)| n.as_str())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                arms.push(format!("{pattern} => ?{new}"));
                pieces.push(Piece {
                    hole: new,
                    constructor: Some(c.name.clone()),
                    binds,
                    recursive,
                });
            }
            taken_names.clear();
            let body = arms
                .iter()
                .map(|a| format!("  {a}"))
                .collect::<Vec<_>>()
                .join("\n");
            Ok(Expansion {
                text: format!("match {var} {{\n{body}\n}}"),
                pieces,
            })
        }
        By::Tactic { name, .. } => {
            Err(tauto_message::msg!("analyzer-tactic-needs-step", name = name).to_string())
        }
    }
}

/// `text` with every line after the first indented as the line of the hole is.
pub fn indented(report: &Report, hole: &Hole, text: &str) -> String {
    let source = report.source(&hole.file);
    let start = (hole.goal.span.start as usize).min(source.len());
    let line = source[..start].rsplit('\n').next().unwrap_or("");
    let indent: String = line.chars().take_while(|c| c.is_whitespace()).collect();
    text.replace('\n', &format!("\n{indent}"))
}

/// The step `by name!(arg): G { … }` in place of the hole `?hole` of
/// `path`, with an arm for each goal the tactic leaves and a new hole for
/// each arm's proof. The step is first written with no arm: its tactic runs,
/// and the expander says what the arms are (`step.arms`). For the whole
/// proof of a step's arm, `-> G` is left out.
pub fn expand_step(
    path: &std::path::Path,
    hole: &str,
    name: &str,
    arg: &str,
) -> Result<(Expansion, Attempt), String> {
    let before = check_report(path, None)?;
    let h = find_hole(&before, path, hole)?;
    let goal = tauto::surface::print::print_term(&h.goal.goal);
    let failure = |a: &Attempt| -> Option<String> {
        a.report
            .entries
            .iter()
            .find_map(|e| match &e.entry.verdict {
                Verdict::Failed(d)
                    if e.file == a.hole.file
                        && (e.entry.name == a.hole.declaration || e.entry.name == "macro") =>
                {
                    Some(d.message.to_string())
                }
                _ => None,
            })
    };
    let mut head = format!("by {name}!({arg}): {goal}");
    let mut a = try_fill(path, hole, &format!("{head} {{}}"))?;
    // The macro's errors reach here as text, written by the same writer as
    // this message, so the comparison holds in every language.
    let arm_before = tauto_message::msg!("macro-step-arm-before").to_string();
    if failure(&a).is_some_and(|m| m.starts_with("step.before:") && m.ends_with(&arm_before)) {
        head = format!("by {name}!({arg})");
        a = try_fill(path, hole, &format!("{head} {{}}"))?;
    }
    // The code `step.arms:` is written in every language, and the arms
    // follow the first line.
    let Some(arms) = failure(&a).and_then(|m| {
        m.strip_prefix("step.arms: ")
            .and_then(|m| m.split_once('\n'))
            .map(|(_, arms)| arms.to_string())
    }) else {
        // No goal left, or an error the step says itself.
        return Ok((
            Expansion {
                text: format!("{head} {{}}"),
                pieces: Vec::new(),
            },
            a,
        ));
    };
    let mut taken: HashSet<String> = before.holes().into_iter().map(|h| h.goal.name).collect();
    let mut lines = Vec::new();
    let mut names = Vec::new();
    for (k, line) in arms.lines().enumerate() {
        let k = k + 1;
        let new = fresh_hole(&format!("{hole}_{k}"), &taken);
        taken.insert(new.clone());
        let line = line.strip_suffix(&format!("?arm{k}")).ok_or_else(|| {
            tauto_message::msg!("analyzer-step-arm-reads", k = k, line = line).to_string()
        })?;
        lines.push(format!("  {line}?{new}"));
        names.push(new);
    }
    let text = format!("{head} {{\n{}\n}}", lines.join("\n"));
    let a = try_fill(path, hole, &indented(&before, &h, &text))?;
    let outer: Vec<&str> = h.goal.context.iter().map(|(n, _)| n.as_str()).collect();
    let made = a.report.holes();
    let pieces = names
        .into_iter()
        .map(|new| {
            let binds = made
                .iter()
                .find(|m| m.goal.name == new)
                .map(|m| {
                    m.goal
                        .context
                        .iter()
                        .filter(|(n, _)| !outer.contains(&n.as_str()))
                        .cloned()
                        .collect()
                })
                .unwrap_or_default();
            Piece {
                hole: new,
                constructor: None,
                binds,
                recursive: Vec::new(),
            }
        })
        .collect();
    Ok((Expansion { text, pieces }, a))
}
