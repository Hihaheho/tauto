//! What `tauto check`, `goals`, `try` and `fill` tell a reader (or an AI that
//! writes a proof one step at a time): the verdicts of a file's declarations,
//! the goals of its holes, and a candidate for a hole checked without writing
//! it. Nothing here decides anything; the kernel's verdicts are only laid out,
//! as text or as JSON (`--json`).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use tauto_message::msg;

use crate::check::{self, Diagnostic, FileEntry, HoleGoal, LibEntry, Verdict, describe, free_vars};
use crate::surface::{Stmt, SurfaceTerm, TermKind, parse_program_at};

/// A JSON value; the output is small, so it is built by hand.
pub enum Json {
    Bool(bool),
    Num(usize),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(&'static str, Json)>),
}

impl Json {
    pub fn render(&self) -> String {
        let mut out = String::new();
        self.write(&mut out);
        out
    }

    fn write(&self, out: &mut String) {
        match self {
            Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Json::Num(n) => out.push_str(&n.to_string()),
            Json::Str(s) => {
                out.push('"');
                for c in s.chars() {
                    match c {
                        '"' => out.push_str("\\\""),
                        '\\' => out.push_str("\\\\"),
                        '\n' => out.push_str("\\n"),
                        '\r' => out.push_str("\\r"),
                        '\t' => out.push_str("\\t"),
                        c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
                        c => out.push(c),
                    }
                }
                out.push('"');
            }
            Json::Arr(items) => {
                out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    item.write(out);
                }
                out.push(']');
            }
            Json::Obj(fields) => {
                out.push('{');
                for (i, (key, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    Json::Str((*key).to_string()).write(out);
                    out.push(':');
                    value.write(out);
                }
                out.push('}');
            }
        }
    }
}

fn s(text: impl Into<String>) -> Json {
    Json::Str(text.into())
}

/// A term as a tree: each node has a `kind` (`var`, `nat`, `text`, `bool`,
/// `app`, `pi`, `exists`, `lam`, `hole`), and what it holds under the names
/// of [`TermKind`]'s fields. A name that starts with `?` is an unknown that
/// nothing fixed. Syntax the kernel does not read is `other`, with its text.
/// The operators are applications of a variable (`a + b` is `app` of `+`),
/// as in the surface AST.
pub fn term_json(t: &SurfaceTerm) -> Json {
    let node = |kind: &'static str, mut rest: Vec<(&'static str, Json)>| {
        let mut fields = vec![("kind", s(kind))];
        fields.append(&mut rest);
        Json::Obj(fields)
    };
    match &*t.kind {
        TermKind::Var(n) => node("var", vec![("name", s(n))]),
        TermKind::Nat(n) => node("nat", vec![("value", s(n))]),
        TermKind::Text(n) => node("text", vec![("value", s(n))]),
        TermKind::Bool(b) => node("bool", vec![("value", Json::Bool(*b))]),
        TermKind::Hole(n) => node("hole", vec![("name", s(n))]),
        TermKind::App {
            function,
            arguments,
        } => node(
            "app",
            vec![
                ("function", term_json(function)),
                (
                    "arguments",
                    Json::Arr(arguments.iter().map(term_json).collect()),
                ),
            ],
        ),
        TermKind::Pi {
            params,
            result,
            effects,
        } => {
            let params = params
                .iter()
                .map(|(n, d)| {
                    let mut f = Vec::new();
                    // An anonymous parameter is named `_'N` inside the kernel.
                    if let Some(n) = n.as_ref().filter(|n| *n != "_" && !n.starts_with("_'")) {
                        f.push(("name", s(n)));
                    }
                    f.push(("type", term_json(d)));
                    Json::Obj(f)
                })
                .collect();
            let mut f = vec![("params", Json::Arr(params)), ("result", term_json(result))];
            if let Some(e) = effects {
                f.push(("effects", Json::Arr(e.iter().map(s).collect())));
            }
            node("pi", f)
        }
        TermKind::Exists {
            binder,
            domain,
            body,
        } => node(
            "exists",
            vec![
                ("binder", s(binder)),
                ("domain", term_json(domain)),
                ("body", term_json(body)),
            ],
        ),
        TermKind::Lam { params, body, .. } => node(
            "lam",
            vec![
                ("params", Json::Arr(params.iter().map(s).collect())),
                ("body", term_json(body)),
            ],
        ),
        _ => node("other", vec![("text", s(describe(t)))]),
    }
}

/// `name` and its type, as text and as a tree.
fn typed(
    fields: &mut Vec<(&'static str, Json)>,
    text: &'static str,
    tree: &'static str,
    t: &SurfaceTerm,
) {
    fields.push((text, s(describe(t))));
    fields.push((tree, term_json(t)));
}

/// The overall answer: `Failed` if anything is wrong, else `Incomplete` if a
/// hole is left, else `Ok`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Ok,
    Incomplete,
    Failed,
}

impl Status {
    pub fn name(self) -> &'static str {
        match self {
            Status::Ok => "ok",
            Status::Incomplete => "incomplete",
            Status::Failed => "failed",
        }
    }
}

/// A hole with the declaration and file it is in.
#[derive(Clone)]
pub struct Hole {
    pub file: PathBuf,
    pub declaration: String,
    pub goal: HoleGoal,
}

/// A file's declarations checked, with the text of every file they came from.
pub struct Report {
    pub entries: Vec<FileEntry>,
    pub expansions: Vec<check::ExpansionInfo>,
    /// The constants a proof may use, by name.
    pub library: Vec<LibEntry>,
    /// The time each declaration took, in order (`text_timings`).
    pub timings: Vec<check::Timing>,
    /// What is never used or never runs in the files checked as one's own
    /// (`crate::deadcode`, and the `match` arms no value reaches). A warning
    /// does not change the status.
    pub warnings: Vec<FileWarning>,
    sources: BTreeMap<PathBuf, String>,
}

/// A warning with the file it is in.
#[derive(Debug, Clone, PartialEq)]
pub struct FileWarning {
    pub file: PathBuf,
    pub warning: crate::deadcode::Warning,
}

/// The warnings `crate::deadcode` finds in the file `path` of text `source`;
/// a file that does not read has none (the checker says why).
fn dead_code(path: &Path, source: &str, runs_alone: bool) -> Vec<FileWarning> {
    let file = crate::program::canonical_path(path);
    crate::deadcode::analyze(path, source, runs_alone)
        .unwrap_or_default()
        .into_iter()
        .map(|warning| FileWarning {
            file: file.clone(),
            warning,
        })
        .collect()
}

/// Checks `path` and what it imports; `text` stands for the content of `path`
/// itself when it is given.
pub fn check_report(path: &Path, text: Option<&str>) -> Result<Report, String> {
    let (entries, expansions, library, timings) = check::check_file_timed(path, text)?;
    let mut sources = BTreeMap::new();
    // The file itself, even when it declares nothing the kernel checks.
    let own = match text {
        Some(t) => Some(t.to_string()),
        None => std::fs::read_to_string(path).ok(),
    };
    if let Some(own) = own {
        sources.insert(
            path.canonicalize().unwrap_or_else(|_| path.to_path_buf()),
            own,
        );
    }
    for e in &entries {
        if !sources.contains_key(&e.file) {
            let source = match text {
                Some(t) if e.file == path.canonicalize().unwrap_or_default() => t.to_string(),
                _ => crate::stdlib::read(&e.file).unwrap_or_default(),
            };
            sources.insert(e.file.clone(), source);
        }
    }
    let mut entries = entries;
    let alone = text.is_none() && runs_alone(path);
    let own_path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let mut warnings = match sources.get(&own_path) {
        Some(own) => dead_code(path, own, alone),
        None => Vec::new(),
    };
    // What `run` rejects before it runs is rejected here too. The kernel
    // checks the proof language; the program `run` makes of it is checked as
    // Nib only once it is extracted (a `Nat` result put in a `u64` field).
    // A file `run FILE` takes as a program is checked as that program; any
    // other file of a tote with a program is checked as part of the tote's
    // program, for the errors written in it.
    if text.is_none()
        && entries
            .iter()
            .all(|e| !e.entry.failed() && !e.entry.incomplete())
    {
        let own_file = |f: &Path| f == own_path;
        let (errors, arms) = if is_program(path) {
            program_errors(path, crate::program::load_extracted(path), &own_file)
        } else if let Some((dir, main)) = tote_program(&own_path) {
            let (errors, arms) = program_errors(&main, crate::program::load_tote(&dir), &own_file);
            let errors = errors.into_iter().filter(|e| e.file == own_path).collect();
            (errors, arms)
        } else {
            (Vec::new(), Vec::new())
        };
        entries.extend(errors);
        warnings.extend(arms);
    }
    warnings.sort_by_key(|w| (w.file.clone(), w.warning.span.start));
    Ok(Report {
        entries,
        expansions,
        library,
        timings,
        warnings,
        sources,
    })
}

/// Whether `tauto run FILE` is how `path` runs: a Tauto file with statements
/// of its own to run (a top-level `let`, `perform`, …), not in a tote. A
/// library is checked as a program where a program imports it; a tote's file
/// runs with the tote, and `check --tote` checks it so.
fn runs_alone(path: &Path) -> bool {
    if !crate::program::is_source_file(path) {
        return false;
    }
    let canonical = crate::program::canonical_path(path);
    if canonical
        .ancestors()
        .skip(1)
        .any(|dir| dir.join("Tauto.eure").is_file())
    {
        return false;
    }
    let Ok(source) = std::fs::read_to_string(path) else {
        return false;
    };
    crate::read::parse_program_unexpanded(&source).is_ok_and(|p| {
        p.stmts.iter().any(|s| {
            matches!(
                s,
                Stmt::Let { .. }
                    | Stmt::Var { .. }
                    | Stmt::Assign { .. }
                    | Stmt::While { .. }
                    | Stmt::Expr(_)
            )
        })
    })
}

/// Whether `tauto run FILE` takes `path` as a program: a Tauto file with
/// statements of its own to run or a `main` function, in a tote or not.
fn is_program(path: &Path) -> bool {
    if !crate::program::is_source_file(path) {
        return false;
    }
    let Ok(source) = std::fs::read_to_string(path) else {
        return false;
    };
    crate::read::parse_program_unexpanded(&source).is_ok_and(|p| {
        p.stmts.iter().any(|s| match s {
            Stmt::Fn(f) => f.name == "main",
            Stmt::Let { .. }
            | Stmt::Var { .. }
            | Stmt::Assign { .. }
            | Stmt::While { .. }
            | Stmt::Expr(_) => true,
            _ => false,
        })
    })
}

/// The tote `path` belongs to and the file its program starts from, when it
/// has one.
fn tote_program(path: &Path) -> Option<(PathBuf, PathBuf)> {
    if !crate::program::is_source_file(path) {
        return None;
    }
    let dir = path
        .ancestors()
        .skip(1)
        .find(|dir| dir.join("Tauto.eure").is_file())?;
    let main = ["src/main.taut", "src/main.tauto"]
        .iter()
        .map(|name| dir.join(name))
        .find(|p| p.is_file())?;
    Some((dir.to_path_buf(), main))
}

/// The Nib type, effect and use errors of `loaded`, the program `tauto run`
/// makes of `path`, at the place each is written, and the `match` arms of
/// the files `own` takes that no value reaches. A program that does not
/// extract (one that uses axioms, say) gives none: what `run` says about it
/// is not an error of its program.
fn program_errors(
    path: &Path,
    loaded: Result<crate::program::Loaded, String>,
    own_file: &dyn Fn(&Path) -> bool,
) -> (Vec<FileEntry>, Vec<FileWarning>) {
    let Ok(loaded) = loaded else {
        return (Vec::new(), Vec::new());
    };
    let own = crate::program::canonical_path(path);
    let types = crate::types::check_program(&loaded.program);
    let rows = loaded.check_rows_with_types(false, &types);
    let errors: Vec<(String, u32)> = if rows.errors.is_empty() {
        crate::eval::errors_before_run(&loaded.program, &rows)
    } else {
        rows.errors
            .into_iter()
            .map(|e| (e.message, e.span.start))
            .collect()
    };
    // The file and the place in it where `at` of the program is written.
    let place = |mut at: u32| {
        while let Some((written, _)) = loaded.spans.origin(at) {
            at = written;
        }
        loaded
            .files
            .iter()
            .rev()
            .find(|f| f.base <= at)
            .filter(|f| f.path.is_file())
            .map(|f| (crate::program::canonical_path(&f.path), at - f.base))
    };
    let mut arms: Vec<FileWarning> = types
        .redundant_arms
        .values()
        .filter_map(|span| {
            let (file, start) = place(span.start)?;
            own_file(&file).then(|| FileWarning {
                file,
                warning: crate::deadcode::Warning {
                    code: "unreachable_arm",
                    message: msg!("tauto-unreachable-arm").to_string(),
                    span: tauto_parol::Span::new(start, start + (span.end - span.start)),
                },
            })
        })
        .collect();
    arms.sort_by_key(|w| (w.file.clone(), w.warning.span.start));
    arms.dedup();
    let errors = errors
        .into_iter()
        .map(|(message, at)| {
            let (file, span) = match place(at) {
                Some((file, at)) => (file, Some(tauto_parol::Span::new(at, at))),
                None => (own.clone(), None),
            };
            FileEntry {
                file,
                entry: check::Entry {
                    name: "program".into(),
                    verdict: Verdict::Failed(Diagnostic::new(message, span)),
                },
            }
        })
        .collect();
    (errors, arms)
}

/// What `tauto check --tote DIR` reports: the tote's own declarations, and of
/// the files it reads from its dependencies and the standard library, only
/// what did not check.
pub struct ToteReport {
    pub report: Report,
    /// The tote's own files, its `sources` and the rest, by canonical path.
    pub own: std::collections::BTreeSet<PathBuf>,
}

/// Checks the tote in `dir` with its dependencies and what its files import:
/// its `sources` and every other Tauto file in it, such as proofs and examples.
/// A proof checked before with the same statement and dependencies is taken
/// from the proof cache, so a dependency is checked again only when it changes.
pub fn check_tote_report(dir: &Path) -> Result<ToteReport, String> {
    let others = crate::program::package_other_files(dir)?;
    let mut roots: Vec<PathBuf> = crate::program::tote_inputs(dir)?
        .into_iter()
        .filter(|p| crate::program::is_source_file(p))
        .collect();
    roots.extend(others.iter().cloned());
    let loaded = crate::program::load_roots(&roots)?;
    let mut checked = crate::check::check_tote_files(&roots, true)?;
    // The functions that only run were taken out before the kernel saw
    // them; they still get a line, so that what was not proved is not
    // mistaken for what was.
    let seen: BTreeSet<String> = checked
        .entries
        .iter()
        .map(|e| e.entry.name.clone())
        .collect();
    for (file, stmts) in loaded.files.iter().zip(&loaded.per_file) {
        let mut fns = Vec::new();
        run_only_fns(stmts, &mut fns);
        for name in fns {
            if checked.runtime.contains(&name) && !seen.contains(&name) {
                checked.entries.push(FileEntry {
                    file: crate::program::canonical_path(&file.path),
                    entry: check::Entry {
                        name,
                        verdict: Verdict::Skipped(msg!("tauto-skipped-runs").to_string()),
                    },
                });
            }
        }
    }
    let sources = loaded
        .files
        .iter()
        .map(|f| (crate::program::canonical_path(&f.path), f.text.clone()))
        .collect();
    // A tote with a program runs as `run --tote` reads it, and is rejected
    // here for what that rejects.
    let main = ["src/main.taut", "src/main.tauto"]
        .iter()
        .map(|name| dir.join(name))
        .find(|p| p.is_file());
    let own: BTreeSet<PathBuf> = crate::program::package_source_files(dir)?
        .iter()
        .chain(&others)
        .map(|p| crate::program::canonical_path(p))
        .collect();
    // A tote's files do not import, and what they declare is for one another.
    let mut warnings: Vec<FileWarning> = loaded
        .files
        .iter()
        .filter(|f| own.contains(&crate::program::canonical_path(&f.path)))
        .flat_map(|f| dead_code(&f.path, &f.text, false))
        .collect();
    warnings.extend(unchecked_builtins(&loaded, &checked.runtime, &own));
    if let Some(main) = main
        && checked
            .entries
            .iter()
            .all(|e| !e.entry.failed() && !e.entry.incomplete())
    {
        let (errors, arms) =
            program_errors(&main, crate::program::load_tote(dir), &|f| own.contains(f));
        checked.entries.extend(errors);
        warnings.extend(arms);
    }
    // Each command the tote gives runs as `tauto NAME` reads it in this tote,
    // and is rejected here for what that rejects.
    let manifest = crate::manifest::read(dir)?;
    for (name, command) in &manifest.commands {
        let main = crate::program::command_main(dir, &manifest, name, &command.main)?;
        if checked
            .entries
            .iter()
            .all(|e| !e.entry.failed() && !e.entry.incomplete())
        {
            let (errors, arms) =
                program_errors(&main, crate::program::load_command(dir, dir, name), &|f| {
                    own.contains(f)
                });
            checked.entries.extend(errors);
            warnings.extend(arms);
        }
    }
    warnings.sort_by_key(|w| (w.file.clone(), w.warning.span.start));
    let mut report = Report::from_parts(
        checked.entries,
        crate::check::expansion_infos(&loaded),
        sources,
    );
    report.warnings = warnings;
    Ok(ToteReport { report, own })
}

/// A function of the tote's own files that runs as written, and so leaves
/// the kernel's checking, only because it calls a built-in of the prelude
/// whose model the standard library declares, while the program reads that
/// model: a file imports `std::Text`, but not this one. What a tote imports
/// from the standard library does not reach the totes that import it, so a
/// call such a function took for the model's `text_len` would otherwise
/// become the prelude's without a word. Said at the first such function of
/// each chain; those that use it say so in their own verdicts.
fn unchecked_builtins(
    loaded: &crate::program::Loaded,
    runtime: &std::collections::HashSet<String>,
    own: &BTreeSet<PathBuf>,
) -> Vec<FileWarning> {
    let read: BTreeSet<&str> = loaded
        .files
        .iter()
        .filter(|f| crate::stdlib::text(&f.path).is_some())
        .filter_map(|f| f.path.file_stem()?.to_str())
        .collect();
    fn fns<'a>(stmts: &'a [Stmt], out: &mut Vec<&'a Stmt>) {
        for s in stmts {
            match s {
                Stmt::Fn(_) => out.push(s),
                Stmt::Mutual { items, .. } => fns(items, out),
                _ => {}
            }
        }
    }
    let mut out = Vec::new();
    for (i, (file, stmts)) in loaded.files.iter().zip(&loaded.per_file).enumerate() {
        let path = crate::program::canonical_path(&file.path);
        if !own.contains(&path) {
            continue;
        }
        let mut these = Vec::new();
        fns(stmts, &mut these);
        for s in these {
            let Stmt::Fn(f) = s else { continue };
            if !runtime.contains(&f.name) {
                continue;
            }
            let mut refs: Vec<String> = crate::lin::free_vars(&f.body).into_iter().collect();
            refs.sort();
            let found = refs.iter().find_map(|n| {
                if !runtime.contains(n)
                    || f.params.contains(n)
                    || crate::surface::qualify::short(n) != n.as_str()
                {
                    return None;
                }
                let module = crate::stdlib::module_of(n)?;
                read.contains(module).then_some((n, module))
            });
            let Some((n, module)) = found else { continue };
            let Some(span) = check::stmt_span(loaded, i, s) else {
                continue;
            };
            out.push(FileWarning {
                file: path.clone(),
                warning: crate::deadcode::Warning {
                    code: "unchecked_builtin",
                    message: msg!(
                        "tauto-unchecked-builtin",
                        name = &f.name,
                        builtin = n.as_str(),
                        module = module
                    )
                    .to_string(),
                    span,
                },
            });
        }
    }
    out
}

fn run_only_fns(stmts: &[Stmt], out: &mut Vec<String>) {
    for s in stmts {
        match s {
            Stmt::Fn(f) => out.push(f.name.clone()),
            Stmt::Mutual { items, .. } => run_only_fns(items, out),
            _ => {}
        }
    }
}

impl ToteReport {
    /// One line per declaration of the tote's own files, and per declaration
    /// elsewhere that failed or is incomplete (every one with `verbose`), then a
    /// line that counts them.
    pub fn text(&self, verbose: bool) -> String {
        let mut out = String::new();
        let (mut ok, mut failed, mut incomplete, mut skipped, mut hidden) = (0, 0, 0, 0, 0);
        for e in &self.report.entries {
            let own = self.own.contains(&e.file);
            match &e.entry.verdict {
                Verdict::Checked { .. } if own => ok += 1,
                // Not proof-checked, so never counted as ok.
                Verdict::Skipped(_) if own => skipped += 1,
                Verdict::Failed(_) => failed += 1,
                Verdict::Incomplete { .. } => incomplete += 1,
                _ => {}
            }
            let shown = verbose || own || e.entry.failed() || e.entry.incomplete();
            if !shown {
                hidden += 1;
                continue;
            }
            out.push_str(&self.report.entry_line(e));
        }
        out.push_str(&self.report.warning_lines());
        out.push_str(&format!(
            "{ok} ok, {failed} failed, {incomplete} incomplete"
        ));
        if skipped > 0 {
            out.push_str(&format!(", {skipped} skipped (not checked by the kernel)"));
        }
        if hidden > 0 {
            out.push_str(&format!(
                "; {hidden} declarations of dependencies and imports not shown (--verbose shows them)"
            ));
        }
        out.push('\n');
        out
    }
}

/// What kind of diagnostic this is, for a client to branch on.
fn code_of(d: &Diagnostic) -> &'static str {
    use crate::said::says;
    let m = &d.message;
    if d.detail.is_some() {
        "type_mismatch"
    } else if says(m, &["kernel-too-many-arguments"]) {
        "too_many_arguments"
    } else if says(m, CANNOT_INFER) {
        "cannot_infer"
    } else if says(m, crate::said::USES_FAILED) {
        "uses_failed_declaration"
    } else if says(m, crate::read::ALREADY_DEFINED) {
        "duplicate_declaration"
    } else if says(m, &["kernel-hole-twice", "totebag-state-index-twice"]) {
        "duplicate_hole"
    } else if says(m, &["kernel-let-unused"]) {
        "unused_binding"
    } else if says(m, &["kernel-core-rejects"]) {
        "core_rejects"
    } else {
        "error"
    }
}

/// The messages that say something cannot be inferred, or needs an expected
/// type.
const CANNOT_INFER: &[&str] = &[
    "kernel-core-cannot-infer-function",
    "kernel-cannot-infer-function",
    "kernel-hole-type-unknown",
    "kernel-implicit-no-match",
    "kernel-implicit-cannot-infer",
    "kernel-implicit-generic",
    "kernel-implicit-class-type",
    "kernel-implicit-instance-types",
];

impl Report {
    /// A report of verdicts checked elsewhere (an incremental checker's), with
    /// the text of every file they came from, by canonical path.
    pub fn from_parts(
        entries: Vec<FileEntry>,
        expansions: Vec<check::ExpansionInfo>,
        sources: BTreeMap<PathBuf, String>,
    ) -> Report {
        Report {
            entries,
            expansions,
            library: Vec::new(),
            timings: Vec::new(),
            warnings: Vec::new(),
            sources,
        }
    }

    /// The constants a proof may use, when the checker that made the verdicts
    /// knows them (`suggest`, `expand` and `library_json` read them).
    pub fn with_library(mut self, library: Vec<LibEntry>) -> Report {
        self.library = library;
        self
    }
}

fn is_hypothesis(name: &str) -> bool {
    name.starts_with("ih'")
}

/// `line:col` (1-based, in characters) of a byte offset.
pub fn line_col(source: &str, offset: usize) -> (usize, usize) {
    let before = &source[..offset.min(source.len())];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    (line, col)
}

impl Report {
    /// The files the report is of, with their text.
    pub fn files(&self) -> impl Iterator<Item = (&Path, &str)> {
        self.sources.iter().map(|(p, t)| (p.as_path(), t.as_str()))
    }

    pub fn source(&self, file: &Path) -> &str {
        self.sources.get(file).map_or("", String::as_str)
    }

    /// The `extern` functions the files declare: signatures trusted as an
    /// axiom's statement is, listed with the axioms.
    pub fn externs(&self) -> Vec<String> {
        let mut out = Vec::new();
        for (path, source) in &self.sources {
            let Ok(program) = crate::read::parse_program_unexpanded(source) else {
                continue;
            };
            for stmt in &program.stmts {
                if let crate::surface::Stmt::Extern { fns, types, .. } = stmt {
                    let line = |at: u32| {
                        source[..(at as usize).min(source.len())]
                            .matches('\n')
                            .count()
                            + 1
                    };
                    out.extend(types.iter().map(|t| {
                        format!(
                            "extern type {} ({}:{})",
                            t.name,
                            path.display(),
                            line(t.span.start)
                        )
                    }));
                    out.extend(fns.iter().map(|f| {
                        format!(
                            "extern {} ({}:{})",
                            f.name,
                            path.display(),
                            line(f.span.start)
                        )
                    }));
                }
            }
        }
        out
    }

    pub fn status(&self) -> Status {
        if self.entries.iter().any(|e| e.entry.failed()) {
            Status::Failed
        } else if self.entries.iter().any(|e| e.entry.incomplete()) {
            Status::Incomplete
        } else {
            Status::Ok
        }
    }

    pub fn holes(&self) -> Vec<Hole> {
        let mut out = Vec::new();
        for e in &self.entries {
            if let Verdict::Incomplete { holes, .. } = &e.entry.verdict {
                for h in holes {
                    out.push(Hole {
                        file: e.file.clone(),
                        declaration: e.entry.name.clone(),
                        goal: h.clone(),
                    });
                }
            }
        }
        out
    }

    /// `line:col` of a byte offset in `file`.
    pub fn place(&self, file: &Path, offset: usize) -> (usize, usize) {
        line_col(self.source(file), offset)
    }

    fn position(&self, file: &Path, span: Option<tauto_parol::Span>) -> Vec<(&'static str, Json)> {
        match span {
            Some(sp) => {
                let (line, col) = self.place(file, sp.start as usize);
                vec![("line", Json::Num(line)), ("col", Json::Num(col))]
            }
            None => Vec::new(),
        }
    }

    fn end_position(
        &self,
        file: &Path,
        span: Option<tauto_parol::Span>,
    ) -> Vec<(&'static str, Json)> {
        match span {
            Some(sp) => {
                let (line, col) = self.place(file, sp.end as usize);
                vec![("end_line", Json::Num(line)), ("end_col", Json::Num(col))]
            }
            None => Vec::new(),
        }
    }

    pub fn hole_json(&self, h: &Hole) -> Json {
        let mut fields = vec![
            ("name", s(&h.goal.name)),
            ("declaration", s(&h.declaration)),
            ("file", s(h.file.display().to_string())),
        ];
        fields.extend(self.position(&h.file, Some(h.goal.span)));
        fields.extend(self.end_position(&h.file, Some(h.goal.span)));
        typed(&mut fields, "goal", "goal_term", &h.goal.goal);
        if let Some(statement) = &h.goal.statement {
            typed(
                &mut fields,
                "declaration_type",
                "declaration_type_term",
                statement,
            );
        }
        fields.push((
            "context",
            Json::Arr(
                h.goal
                    .context
                    .iter()
                    .map(|(n, t)| {
                        // A hypothesis of an induction has a generated name
                        // (`ih'7`) that cannot be written: the proof reaches it
                        // by calling the theorem on the matched field.
                        let (kind, origin) = if is_hypothesis(n) {
                            ("induction_hypothesis", "induction_hypothesis")
                        } else if h.goal.params.contains(n) {
                            ("variable", "parameter")
                        } else {
                            ("variable", "local")
                        };
                        let mut f = vec![("name", s(n))];
                        typed(&mut f, "type", "type_term", t);
                        f.push(("kind", s(kind)));
                        f.push(("origin", s(origin)));
                        Json::Obj(f)
                    })
                    .collect(),
            ),
        ));
        // Unknowns of an implicit argument that nothing fixed: the goal is
        // not final until they are, and is never guessed.
        let mut metas: Vec<String> = Vec::new();
        for t in std::iter::once(&h.goal.goal).chain(h.goal.context.iter().map(|(_, t)| t)) {
            for v in free_vars(t) {
                if v.starts_with('?') && !metas.contains(&v) {
                    metas.push(v);
                }
            }
        }
        fields.push(("unresolved_metas", Json::Arr(metas.iter().map(s).collect())));
        Json::Obj(fields)
    }

    /// The constants a proof may use, each with its type as text and as a
    /// tree. `file` is where a constant of the checked files was declared;
    /// the prelude's have none.
    pub fn library_json(&self) -> Json {
        let declared: BTreeMap<&str, &Path> = self
            .entries
            .iter()
            .map(|e| (e.entry.name.as_str(), e.file.as_path()))
            .collect();
        Json::Arr(
            self.library
                .iter()
                .map(|l| {
                    let mut f = vec![("name", s(&l.name)), ("kind", s(l.kind))];
                    typed(&mut f, "type", "type_term", &l.ty);
                    f.push(("implicit", Json::Num(l.implicit)));
                    f.push(("state", s(l.state)));
                    if let Some(file) = declared.get(l.name.as_str()) {
                        f.push(("file", s(file.display().to_string())));
                    }
                    Json::Obj(f)
                })
                .collect(),
        )
    }

    /// The whole answer as JSON: the status, each declaration's verdict, the
    /// goals of the holes and the errors.
    pub fn json(&self) -> Json {
        let mut declarations = Vec::new();
        let mut errors = Vec::new();
        for e in &self.entries {
            let file = e.file.display().to_string();
            let mut fields = vec![("name", s(&e.entry.name)), ("file", s(&file))];
            match &e.entry.verdict {
                Verdict::Checked { axioms } => {
                    fields.push(("status", s("ok")));
                    fields.push(("axioms", Json::Arr(axioms.iter().map(s).collect())));
                }
                Verdict::Skipped(why) => {
                    fields.push(("status", s("skipped")));
                    fields.push(("reason", s(why)));
                }
                Verdict::Failed(d) => {
                    fields.push(("status", s("failed")));
                    errors.push(self.error_json(&e.entry.name, &e.file, d));
                }
                Verdict::Incomplete { holes, uses } => {
                    fields.push(("status", s("incomplete")));
                    fields.push((
                        "holes",
                        Json::Arr(holes.iter().map(|h| s(&h.name)).collect()),
                    ));
                    fields.push(("uses_incomplete", Json::Arr(uses.iter().map(s).collect())));
                }
            }
            declarations.push(Json::Obj(fields));
        }
        Json::Obj(vec![
            ("status", s(self.status().name())),
            ("declarations", Json::Arr(declarations)),
            ("externs", Json::Arr(self.externs().iter().map(s).collect())),
            (
                "holes",
                Json::Arr(self.holes().iter().map(|h| self.hole_json(h)).collect()),
            ),
            ("errors", Json::Arr(errors)),
            ("warnings", Json::Arr(self.warnings_json())),
            ("expansions", Json::Arr(self.expansions_json())),
        ])
    }

    fn expansions_json(&self) -> Vec<Json> {
        self.expansions
            .iter()
            .map(|e| {
                let mut f = vec![
                    ("id", Json::Num(e.id as usize)),
                    ("macro", s(&e.macro_name)),
                    ("kind", s(e.kind)),
                ];
                if let Some(p) = e.parent {
                    f.push(("parent", Json::Num(p as usize)));
                }
                if let Some((file, line, col)) = &e.at {
                    f.push(("file", s(file.display().to_string())));
                    f.push(("line", Json::Num(*line)));
                    f.push(("col", Json::Num(*col)));
                }
                f.push(("steps", Json::Num(e.steps as usize)));
                f.push(("captures", Json::Arr(e.captures.iter().map(s).collect())));
                Json::Obj(f)
            })
            .collect()
    }

    fn error_json(&self, declaration: &str, file: &Path, d: &Diagnostic) -> Json {
        let mut fields = vec![
            ("declaration", s(declaration)),
            ("file", s(file.display().to_string())),
        ];
        fields.extend(self.position(file, d.span));
        fields.extend(self.end_position(file, d.span));
        fields.push(("code", s(code_of(d))));
        fields.push(("message", s(d.message.to_string())));
        if let Some(m) = &d.detail {
            typed(&mut fields, "expected", "expected_term", &m.expected);
            typed(&mut fields, "found", "found_term", &m.found);
            if let Some((e, f)) = &m.differing {
                let mut part = vec![
                    ("expected", s(describe(e))),
                    ("expected_term", term_json(e)),
                    ("found", s(describe(f))),
                    ("found_term", term_json(f)),
                ];
                if let Some(sp) = m.differing_span {
                    part.extend(self.position(file, Some(sp)));
                    part.extend(self.end_position(file, Some(sp)));
                }
                fields.push(("differing", Json::Obj(part)));
            }
            if let Some((callee, index)) = &m.argument {
                fields.push((
                    "argument",
                    Json::Obj(vec![("callee", s(callee)), ("index", Json::Num(*index))]),
                ));
            }
        }
        if let Some(fix) = &d.fix {
            let mut edit = vec![("title", s(&fix.title))];
            edit.extend(self.position(file, Some(fix.span)));
            edit.extend(self.end_position(file, Some(fix.span)));
            edit.push(("text", s(&fix.text)));
            fields.push(("fix", Json::Obj(edit)));
        }
        Json::Obj(fields)
    }

    /// The declarations that took longest, slowest first, with the time
    /// of all of them (`tauto check --timings`).
    pub fn text_timings(&self, shown: usize) -> String {
        let mut slow: Vec<&check::Timing> = self.timings.iter().collect();
        slow.sort_by(|a, b| b.elapsed.cmp(&a.elapsed));
        let total: std::time::Duration = self.timings.iter().map(|t| t.elapsed).sum();
        let cached = self.timings.iter().filter(|t| t.cached).count();
        let mut out = format!(
            "timings: {} declarations, {:.3}s in all",
            self.timings.len(),
            total.as_secs_f64()
        );
        if cached > 0 {
            // A proof from the cache was not checked again: its time is not
            // what checking it takes (`--fresh` checks every proof).
            out.push_str(&format!(
                "; {cached} proofs from the cache, not checked again (--fresh checks them)"
            ));
        }
        out.push_str("; the slowest:\n");
        for t in slow.into_iter().take(shown) {
            out.push_str(&format!(
                "{:>9.3}s {:>12} steps  {}",
                t.elapsed.as_secs_f64(),
                t.steps,
                t.name
            ));
            if t.cached {
                out.push_str("  (cached)");
            }
            if !t.top.is_empty() {
                let top: Vec<String> = t.top.iter().map(|(n, k)| format!("{n} ×{k}")).collect();
                out.push_str(&format!("  (unfolded most: {})", top.join(", ")));
            }
            out.push('\n');
        }
        out
    }

    /// `--timings=json`: every declaration, in order.
    pub fn timings_json(&self) -> Json {
        Json::Arr(
            self.timings
                .iter()
                .map(|t| {
                    Json::Obj(vec![
                        ("name", s(t.name.clone())),
                        ("micros", Json::Num(t.elapsed.as_micros() as usize)),
                        ("steps", Json::Num(t.steps as usize)),
                        ("cached", Json::Bool(t.cached)),
                        (
                            "unfolded_most",
                            Json::Arr(
                                t.top
                                    .iter()
                                    .map(|(n, k)| {
                                        Json::Obj(vec![
                                            ("name", s(n.clone())),
                                            ("times", Json::Num(*k as usize)),
                                        ])
                                    })
                                    .collect(),
                            ),
                        ),
                    ])
                })
                .collect(),
        )
    }

    /// The same answer for a person: one line per declaration with its
    /// verdict, then one `trusted` line per `extern`. The declarations an
    /// imported file has that the kernel does not check (a macro's helpers)
    /// are one line per file, with how many; `--json` lists each.
    pub fn text(&self) -> String {
        let mut out = String::new();
        let entry = self.entries.last().map(|e| e.file.clone());
        let mut skipped: Vec<(&Path, usize)> = Vec::new();
        for e in &self.entries {
            if matches!(e.entry.verdict, Verdict::Skipped(_)) && Some(&e.file) != entry.as_ref() {
                match skipped.iter_mut().find(|(f, _)| *f == e.file.as_path()) {
                    Some((_, n)) => *n += 1,
                    None => skipped.push((&e.file, 1)),
                }
            }
        }
        for (f, n) in &skipped {
            out.push_str(&format!(
                "skipped {n} of {} (not checked by the kernel; --json lists them)\n",
                f.display()
            ));
        }
        for e in &self.entries {
            if matches!(e.entry.verdict, Verdict::Skipped(_)) && Some(&e.file) != entry.as_ref() {
                continue;
            }
            out.push_str(&self.entry_line(e));
        }
        for e in self.externs() {
            out.push_str(&format!("trusted {e}\n"));
        }
        out.push_str(&self.warning_lines());
        out
    }

    /// The answer for a person checking `own`: only what went wrong in that
    /// file, then one summary line with the counts and the axioms used.
    /// Declarations of imported files are counted, not listed; so are the
    /// skipped ones. A failure that only uses another declaration that
    /// failed is counted under that one.
    pub fn summary_text(&self, own: &Path) -> String {
        let own = own.canonicalize().unwrap_or_else(|_| own.to_path_buf());
        let mut out = String::new();
        let (mut ok, mut failed, mut incomplete, mut skipped, mut imported) = (0, 0, 0, 0, 0);
        let mut cascaded = 0;
        let mut axioms = BTreeSet::new();
        for e in &self.entries {
            if e.file != own {
                imported += 1;
                if e.entry.failed() || e.entry.incomplete() {
                    // A problem outside the file still has to be seen.
                    out.push_str(&self.entry_line(e));
                }
                continue;
            }
            match &e.entry.verdict {
                Verdict::Checked { axioms: a } => {
                    ok += 1;
                    axioms.extend(a.iter().cloned());
                }
                Verdict::Skipped(_) => skipped += 1,
                Verdict::Failed(d)
                    if crate::said::ends_with(&d.message, &["kernel-uses-failed"]).is_some() =>
                {
                    failed += 1;
                    cascaded += 1;
                }
                Verdict::Failed(_) => {
                    failed += 1;
                    out.push_str(&self.entry_line(e));
                }
                Verdict::Incomplete { .. } => {
                    incomplete += 1;
                    out.push_str(&self.entry_line(e));
                }
            }
        }
        for e in self.externs() {
            out.push_str(&format!("trusted {e}\n"));
        }
        out.push_str(&self.warning_lines());
        let mut line = format!("{ok} ok, {failed} failed, {incomplete} incomplete");
        if cascaded > 0 {
            line.push_str(&format!(
                " ({cascaded} only because a declaration they use failed)"
            ));
        }
        line.push_str(&format!("; {skipped} skipped, {imported} from imports"));
        if !self.warnings.is_empty() {
            line.push_str(&format!("; {} warnings", self.warnings.len()));
        }
        if axioms.is_empty() {
            line.push_str("; axioms: none");
        } else {
            let axioms: Vec<_> = axioms.into_iter().collect();
            line.push_str(&format!("; axioms: {}", axioms.join(", ")));
        }
        out.push_str(&line);
        out.push('\n');
        out
    }

    /// One line per warning: `warning CODE: FILE:LINE:COL: message`.
    pub fn warning_lines(&self) -> String {
        let mut out = String::new();
        for w in &self.warnings {
            let (l, c) = self.place(&w.file, w.warning.span.start as usize);
            out.push_str(&format!(
                "warning {}: {}:{l}:{c}: {}\n",
                w.warning.code,
                w.file.display(),
                w.warning.message
            ));
        }
        out
    }

    fn warnings_json(&self) -> Vec<Json> {
        self.warnings
            .iter()
            .map(|w| {
                let mut fields = vec![("file", s(w.file.display().to_string()))];
                fields.extend(self.position(&w.file, Some(w.warning.span)));
                fields.extend(self.end_position(&w.file, Some(w.warning.span)));
                fields.push(("code", s(w.warning.code)));
                fields.push(("message", s(&w.warning.message)));
                Json::Obj(fields)
            })
            .collect()
    }

    /// The line `text` writes for one declaration.
    fn entry_line(&self, e: &FileEntry) -> String {
        let mut out = String::new();
        let file = e.file.display().to_string();
        let name = crate::surface::qualify::written(&e.entry.name);
        match &e.entry.verdict {
            Verdict::Checked { axioms } if axioms.is_empty() => {
                out.push_str(&format!("ok      {name}\n"));
            }
            Verdict::Checked { axioms } => out.push_str(&format!(
                "ok      {} (axioms: {})\n",
                name,
                axioms.join(", ")
            )),
            Verdict::Skipped(why) => {
                out.push_str(&format!("skipped {name} ({why})\n"));
            }
            Verdict::Failed(d) => {
                let place = match d.span {
                    Some(sp) => {
                        let (l, c) = self.place(&e.file, sp.start as usize);
                        format!("{file}:{l}:{c}: ")
                    }
                    None => format!("{file}: "),
                };
                out.push_str(&format!("FAILED  {}: {place}{}\n", name, d.message));
            }
            Verdict::Incomplete { holes, uses } => {
                let mut why: Vec<String> = holes.iter().map(|h| format!("?{}", h.name)).collect();
                why.extend(uses.iter().map(|u| format!("uses `{u}`")));
                out.push_str(&format!("INCOMPLETE {} ({})\n", name, why.join(", ")));
            }
        }
        out
    }

    /// One goal, as a proof state: the variables in scope, then `⊢ goal`.
    pub fn goal_text(&self, h: &Hole) -> String {
        let (line, col) = self.place(&h.file, h.goal.span.start as usize);
        let mut out = format!(
            "?{} in {} ({}:{line}:{col})\n",
            h.goal.name,
            h.declaration,
            h.file.display()
        );
        for (n, t) in &h.goal.context {
            if is_hypothesis(n) {
                out.push_str(&format!(
                    "  (induction hypothesis, by a call on the matched field) : {}\n",
                    describe(t)
                ));
            } else {
                out.push_str(&format!("  {n} : {}\n", describe(t)));
            }
        }
        out.push_str(&format!("⊢ {}\n", describe(&h.goal.goal)));
        out
    }
}

/// The hole named `name` in `path` itself (not in a file it imports).
pub fn find_hole(report: &Report, path: &Path, name: &str) -> Result<Hole, String> {
    // As the loader names files, so that a file only an editor holds (not on
    // disk) is found too.
    let root = crate::program::canonical_path(path);
    let mut found = report
        .holes()
        .into_iter()
        .filter(|h| h.goal.name == name && h.file == root);
    let Some(hole) = found.next() else {
        return Err(msg!(
            "tauto-no-hole",
            name = name,
            path = path.display().to_string()
        )
        .to_string());
    };
    if found.next().is_some() {
        return Err(msg!(
            "tauto-hole-many",
            name = name,
            path = path.display().to_string()
        )
        .to_string());
    }
    Ok(hole)
}

/// A candidate for a hole, checked but not written.
pub struct Attempt {
    pub hole: Hole,
    /// The file's text with the hole replaced by the candidate.
    pub candidate: String,
    pub report: Report,
    /// The holes of the file before the candidate went in.
    pub before: Vec<Hole>,
    /// The declaration with the hole is not rejected by the candidate.
    pub accepted: bool,
}

/// The text of the file `hole` is in with `expr` in place of the hole, spliced
/// as written.
pub fn splice(report: &Report, hole: &Hole, expr: &str) -> Result<String, String> {
    let name = &hole.goal.name;
    if name.starts_with("law:") {
        return splice_law(report, hole, expr);
    }
    let source = report.source(&hole.file);
    let (start, end) = (hole.goal.span.start as usize, hole.goal.span.end as usize);
    if source.get(start..end) != Some(&format!("?{name}")) {
        return Err(msg!("tauto-hole-text-differs", name = name.as_str()).to_string());
    }
    Ok(format!("{}{}{}", &source[..start], expr, &source[end..]))
}

/// The declarations of `source`, the items of a `mutual` block among them.
fn declarations(source: &str) -> Vec<Stmt> {
    let Ok(program) = parse_program_at(source, 0) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for s in program.stmts {
        match s {
            Stmt::Mutual { items, .. } => out.extend(items),
            s => out.push(s),
        }
    }
    out
}

/// `text` with the identifier `from` written as `to`.
fn rename_ident(text: &str, from: &str, to: &str) -> String {
    let word = |c: char| c.is_alphanumeric() || c == '_';
    let mut out = String::new();
    let mut rest = text;
    while let Some(i) = rest.find(from) {
        let before = rest[..i].chars().next_back();
        let after = rest[i + from.len()..].chars().next();
        out.push_str(&rest[..i]);
        if before.is_some_and(word) || after.is_some_and(word) {
            out.push_str(from);
        } else {
            out.push_str(to);
        }
        rest = &rest[i + from.len()..];
    }
    out.push_str(rest);
    out
}

/// `?law:C(H)::l`: the law `l` of the instance `C(H)` that is not proved.
/// `expr` is its proof: the law is written into the instance, with the
/// statement of the class and `H` for its parameter (or, for a law written
/// without a body, the body is added).
fn splice_law(report: &Report, hole: &Hole, expr: &str) -> Result<String, String> {
    let name = &hole.goal.name;
    let source = report.source(&hole.file);
    let (start, end) = (hole.goal.span.start as usize, hole.goal.span.end as usize);
    let at = source
        .get(start..end)
        .ok_or_else(|| msg!("tauto-hole-text-missing", name = name.as_str()).to_string())?;
    let law = name.rsplit("::").next().unwrap_or_default();
    let class = name
        .trim_start_matches("law:")
        .split('(')
        .next()
        .unwrap_or_default();
    if at.starts_with("law") {
        return Ok(format!("{} {{ {expr} }}{}", &source[..end], &source[end..]));
    }
    let instance = declarations(source)
        .into_iter()
        .find_map(|s| match s {
            Stmt::Instance(i) if i.span.start as usize == start && i.class == class => Some(i),
            _ => None,
        })
        .ok_or_else(|| {
            msg!(
                "tauto-hole-no-instance",
                class = class,
                name = name.as_str()
            )
            .to_string()
        })?;
    let (decl, decl_source) = report
        .files()
        .find_map(|(_, text)| {
            declarations(text).into_iter().find_map(|s| match s {
                Stmt::Class(c) if c.name == class => Some((c, text.to_string())),
                _ => None,
            })
        })
        .ok_or_else(|| msg!("tauto-hole-no-class", class = class).to_string())?;
    let law_decl = decl
        .laws
        .iter()
        .find(|l| l.name == law)
        .ok_or_else(|| msg!("tauto-hole-no-law", class = class, law = law).to_string())?;
    let header = decl_source
        .get(law_decl.span.start as usize..law_decl.span.end as usize)
        .ok_or_else(|| msg!("tauto-hole-law-text", law = law, class = class).to_string())?;
    let item = rename_ident(header.trim(), &decl.param, &describe(&instance.head));
    let close = source[..instance.span.end as usize]
        .rfind('}')
        .ok_or_else(|| msg!("tauto-hole-no-brace", name = name.as_str()).to_string())?;
    let body = source[..close].trim_end().len();
    Ok(format!(
        "{}\n  {item} {{ {expr} }}\n{}",
        &source[..body],
        &source[close..]
    ))
}

/// Puts `expr` in place of `?name` in `path` and checks the result, leaving
/// the file as it is. The text of `expr` is spliced as written, so it is a
/// term that reads as one wherever the hole stands (a call, a name, a
/// `{ … }` block).
pub fn try_fill(path: &Path, name: &str, expr: &str) -> Result<Attempt, String> {
    let before = check_report(path, None)?;
    let hole = find_hole(&before, path, name)?;
    let candidate = splice(&before, &hole, expr)?;
    let report = check_report(path, Some(&candidate))
        .map_err(|e| msg!("tauto-fill-breaks", expr = expr, name = name, error = e).to_string())?;
    // Macro failures, including proof steps, are reported separately from
    // declarations in the file containing the call.
    let macro_failures = |r: &Report| {
        r.entries
            .iter()
            .filter(|e| e.entry.name == "macro" && e.file == hole.file && e.entry.failed())
            .count()
    };
    let accepted = !report
        .entries
        .iter()
        .any(|e| e.entry.name == hole.declaration && e.entry.failed())
        && macro_failures(&report) <= macro_failures(&before);
    let before_holes: Vec<Hole> = before
        .holes()
        .into_iter()
        .filter(|h| h.file == hole.file)
        .collect();
    Ok(Attempt {
        hole,
        candidate,
        report,
        before: before_holes,
        accepted,
    })
}

impl Attempt {
    pub fn json(&self) -> Json {
        let Json::Obj(mut fields) = self.report.json() else {
            unreachable!("a report is an object")
        };
        // Holes keep their names, so an editor can follow them: the ones this
        // candidate closed, and the ones it made.
        let before: Vec<String> = self.before.iter().map(|h| h.goal.name.clone()).collect();
        let after: Vec<String> = self
            .report
            .holes()
            .iter()
            .filter(|h| h.file == self.hole.file)
            .map(|h| h.goal.name.clone())
            .collect();
        let names = |v: Vec<&String>| Json::Arr(v.into_iter().map(s).collect());
        let mut out = vec![
            ("hole", s(&self.hole.goal.name)),
            ("accepted", Json::Bool(self.accepted)),
            (
                "closed_holes",
                names(before.iter().filter(|n| !after.contains(n)).collect()),
            ),
            (
                "new_holes",
                names(after.iter().filter(|n| !before.contains(n)).collect()),
            ),
        ];
        out.append(&mut fields);
        Json::Obj(out)
    }
}
