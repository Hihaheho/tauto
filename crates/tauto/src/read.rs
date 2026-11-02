mod runtime;

use crate::program::Loaded;
use crate::surface::{Program, Stmt, SurfaceTerm, parse_program_unresolved_at};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use tauto_kernel::check::{self, *};
use tauto_message::msg;
use tauto_parol::Span;

pub fn parse_program(source: &str) -> Result<Program, String> {
    let program = parse_program_at(source, 0)?;
    Ok(crate::types::expand_classes(program, 1 << 30))
}

/// Parses a whole program whose spans start at `base`.
pub fn parse_program_at(source: &str, base: u32) -> Result<Program, String> {
    expand_program(parse_program_unresolved_at(source, base)?, true)
}

/// [`parse_program`] of the prelude itself, whose names are its own.
pub fn parse_prelude(source: &str) -> Result<Program, String> {
    let program = parse_prelude_at(source, 0).map_err(|e| {
        if source == crate::nibstd::PRELUDE {
            crate::nibstd::locate_error(e, 0, crate::nibstd::PRELUDE_FILES)
        } else {
            e
        }
    })?;
    Ok(crate::types::expand_classes(program, 1 << 30))
}

/// [`parse_program_at`] of the prelude itself, whose names are its own.
pub(crate) fn parse_prelude_at(source: &str, base: u32) -> Result<Program, String> {
    let mut program = parse_program_unresolved_at(source, base)?;
    // The prelude's own names are short: `#(a, b)` matches its `Pair`.
    crate::surface::qualify::lower_prelude_names(&mut program.stmts);
    expand_program(program, false)
}

/// [`parse_program_at`] of the text of the file at `path`: its
/// `include_text!` calls read relative to it (`program/include.rs`).
pub fn parse_file_at(source: &str, base: u32, path: &std::path::Path) -> Result<Program, String> {
    let mut program = parse_program_unresolved_at(source, base)?;
    let mut included = crate::program::include::Included::default();
    crate::program::include::read_includes(&mut program.stmts, path, &|_| None, &mut included);
    program.errors.splice(0..0, included.errors);
    expand_program(program, true)
}

/// The statements of `source` as written, with names qualified and modules
/// resolved as [`parse_program`] has them, but no macro expanded. A macro
/// makes only declarations, so what is read here of the top level (a `let`
/// to run, an `extern`) is what `parse_program` would show, without running
/// the macros (a tactic checks the declarations before it).
pub(crate) fn parse_program_unexpanded(source: &str) -> Result<Program, String> {
    let mut program = parse_program_unresolved_at(source, 0)?;
    let mut files = vec![std::mem::take(&mut program.stmts)];
    crate::surface::qualify::files(&mut files, &["main".to_string()], None);
    program.stmts = crate::surface::modules::resolve(files.concat()).0;
    Ok(program)
}

fn expand_program(mut program: Program, qualify: bool) -> Result<Program, String> {
    let modules = ["main".to_string()];
    let mut files = vec![std::mem::take(&mut program.stmts)];
    let mut qualified = if qualify {
        crate::surface::qualify::files_before_macros(&mut files, &modules, None, None).0
    } else {
        crate::surface::qualify::record_bases(&mut files)
    };
    let mut out = crate::macros::expand_files(files, &crate::macros::Options::default());
    if qualify {
        qualified.extend(crate::surface::qualify::files(
            &mut out.files,
            &modules,
            None,
        ));
        qualified.extend(crate::surface::qualify::sealed_visibility(
            &out.files, &modules,
        ));
        qualified.extend(crate::surface::qualify::std_models(&out.files, &modules));
    }
    out.stmts = out.files.concat();
    out.errors.extend(qualified);
    let (stmts, mut errors) = crate::surface::modules::resolve_with(
        out.stmts,
        &crate::surface::effect_sets::Sets::new(),
        crate::program::prelude_module_names(),
    );
    errors.extend(std::mem::take(&mut program.errors));
    errors.extend(out.errors);
    program.stmts = stmts;
    program.errors = errors;
    Ok(program)
}

/// Checks `source`: the prelude's constants, then each declaration in order.
pub fn check(source: &str) -> Result<Vec<Entry>, String> {
    let program = parse_program(source)?;
    if program
        .stmts
        .iter()
        .any(|s| matches!(s, Stmt::Import { .. }))
    {
        return Err(msg!("tauto-imports-need-path").to_string());
    }
    let mut kernel = Kernel::new();
    check::declare_prelude(&mut kernel)?;
    Ok(kernel.declare_program(&program))
}

pub fn check_types(source: &str) -> Result<crate::types::TypeReport, String> {
    let program = parse_program(source)?;
    Ok(crate::types::check_program(&program))
}

pub fn check_rows(source: &str) -> Result<crate::rows::RowReport, String> {
    let program = parse_program(source)?;
    Ok(crate::rows::check_program_rows(&program))
}

pub fn check_lin(source: &str) -> Result<Vec<crate::lin::LinError>, String> {
    crate::lin::check_lin_program(&parse_program(source)?)
}

use crate::eval::{DEFAULT_BUDGET, Outcome, RunError, RunOptions, run_program_with};

/// Runs a loaded program with the effect evidence retained by its loader.
pub fn run_loaded_with(
    loaded: &Loaded,
    budget: u64,
    options: RunOptions,
) -> Result<Outcome, RunError> {
    let rows = loaded.check_rows(false);
    if let Some(error) = rows.errors.first() {
        return Err(RunError::Type(error.to_string()));
    }
    // `syn_parse` reads the tables the program was read with, not those of
    // the thread's current search directories.
    crate::syntax::with_search_dirs(loaded.syntax_dirs.clone(), || {
        crate::eval::run_program_with_rows(&loaded.program, budget, options, &rows)
    })
}

pub fn run(source: &str) -> Result<Outcome, RunError> {
    run_with_budget(source, DEFAULT_BUDGET)
}

/// Runs with the dynamic ownership check: a test
/// of the static check, not a mode for programs.
pub fn run_checking_ownership(source: &str) -> Result<Outcome, RunError> {
    run_source(source, DEFAULT_BUDGET, true)
}

pub fn run_with_budget(source: &str, budget: u64) -> Result<Outcome, RunError> {
    run_source(source, budget, false)
}

fn run_source(source: &str, budget: u64, check: bool) -> Result<Outcome, RunError> {
    let program = parse_program(source).map_err(RunError::Syntax)?;
    run_program_with(
        &program,
        budget,
        RunOptions {
            check_ownership: check,
            ..RunOptions::default()
        },
    )
}

/// Checks a file and, first, every file it imports (once each, relative to
/// the importing file). Declarations are told apart by their full names
/// (`surface::qualify`).
pub fn check_file(path: &std::path::Path) -> Result<Vec<FileEntry>, String> {
    check_file_with(path, None)
}

/// [`check_file`] with the text of `path` itself given instead of read: a
/// candidate edit is checked without touching the file. Its imports are
/// still read relative to `path`.
pub fn check_file_with(
    path: &std::path::Path,
    text: Option<&str>,
) -> Result<Vec<FileEntry>, String> {
    check_file_full(path, text).map(|(entries, _)| entries)
}

fn expansion_infos_of(loaded: &crate::program::Loaded) -> Vec<ExpansionInfo> {
    loaded
        .expansions
        .iter()
        .map(|e| ExpansionInfo {
            id: e.id,
            macro_name: e.macro_name.clone(),
            kind: e.kind,
            parent: e.parent,
            at: loaded
                .locate(e.call.start)
                .map(|(f, l, c)| (crate::program::canonical_path(f), l, c)),
            steps: e.steps,
            captures: e.captures.clone(),
        })
        .collect()
}

/// [`check_file_with`] and the macro runs that made the declarations.
pub fn check_file_full(
    path: &std::path::Path,
    text: Option<&str>,
) -> Result<(Vec<FileEntry>, Vec<ExpansionInfo>), String> {
    check_file_lib(path, text).map(|(entries, expansions, _)| (entries, expansions))
}

/// [`check_file_full`] and the constants known at the end, by name.
pub fn check_file_lib(
    path: &std::path::Path,
    text: Option<&str>,
) -> Result<(Vec<FileEntry>, Vec<ExpansionInfo>, Vec<LibEntry>), String> {
    check_file_timed(path, text)
        .map(|(entries, expansions, library, _)| (entries, expansions, library))
}

/// [`check_file_lib`] and the time each declaration took. A declaration
/// may take at most `TAUTO_TIMEOUT` seconds when that is set
/// (`Kernel::set_timeout`).
pub fn check_file_timed(
    path: &std::path::Path,
    text: Option<&str>,
) -> Result<
    (
        Vec<FileEntry>,
        Vec<ExpansionInfo>,
        Vec<LibEntry>,
        Vec<Timing>,
    ),
    String,
> {
    let given = text.and_then(|t| Some((path.canonicalize().ok()?, t.to_string())));
    check_file_sourced(path, &|p: &std::path::Path| match &given {
        Some((own, text)) if own == p => Some(Ok(text.clone())),
        _ => None,
    })
}

/// [`check_file_timed`] with the text of some files given by `source`
/// ([`crate::program::load_with_source`]).
pub fn check_file_sourced(
    path: &std::path::Path,
    source: &crate::program::Source<'_>,
) -> Result<
    (
        Vec<FileEntry>,
        Vec<ExpansionInfo>,
        Vec<LibEntry>,
        Vec<Timing>,
    ),
    String,
> {
    let mut kernel = Kernel::new();
    check::declare_prelude(&mut kernel)?;
    kernel.use_cache();
    let timeout = std::env::var("TAUTO_TIMEOUT")
        .ok()
        .and_then(|s| s.parse::<f64>().ok())
        .filter(|s| s.is_finite() && *s > 0.0)
        .map(std::time::Duration::from_secs_f64);
    kernel.set_timeout(timeout);
    let mut loaded = crate::program::load_with_source(path, source)?;
    let expansions = expansion_infos_of(&loaded);
    // A program's functions that only run, such as one calling the
    // prelude's `concat`, are taken out as `run` takes them out, so that
    // `check` and `run` agree on what the kernel is given.
    let mut fns_of = Vec::new();
    for stmts in &loaded.per_file {
        let mut fns = Vec::new();
        fn_names(stmts, &mut fns);
        fns_of.push(fns);
    }
    let (runtime, why) = if loaded
        .files
        .iter()
        .all(|f| crate::program::is_source_file(&f.path))
    {
        let (runtime, _, why) = runtime::separate(&mut loaded)?;
        (runtime, why)
    } else {
        // A Nib file runs as a whole, but its `inductive struct` and
        // `inductive enum` are families to the kernel as in a source file.
        runtime::families_only(&mut loaded);
        (HashSet::new(), HashMap::new())
    };
    let mut out = declare_loaded(&mut kernel, &loaded)?;
    runtime::explain_undefined(&mut out, &why);
    let seen: HashSet<String> = out.iter().map(|e| e.entry.name.clone()).collect();
    for (file, fns) in loaded.files.iter().zip(fns_of) {
        for name in fns {
            if runtime.contains(&name) && !seen.contains(&name) {
                out.push(FileEntry {
                    file: crate::program::canonical_path(&file.path),
                    entry: check::Entry {
                        name,
                        verdict: Verdict::Skipped(msg!("tauto-skipped-runs").to_string()),
                    },
                });
            }
        }
    }
    let library = kernel.library();
    let timings = kernel.timings().to_vec();
    Ok((out, expansions, library, timings))
}

fn fn_names(stmts: &[Stmt], out: &mut Vec<String>) {
    for s in stmts {
        match s {
            Stmt::Fn(f) => out.push(f.name.clone()),
            Stmt::Mutual { items, .. } => fn_names(items, out),
            _ => {}
        }
    }
}

/// Checks `path` without the proof cache, and gives the term each body
/// elaborated to: implicit arguments, instances and motives filled in, macros
/// expanded. What the kernel checks, not what was written.
pub fn elaborate_file(
    path: &std::path::Path,
) -> Result<(Vec<FileEntry>, Vec<(String, SurfaceTerm)>), String> {
    let mut kernel = Kernel::new();
    check::declare_prelude(&mut kernel)?;
    kernel.record_elaborated();
    let loaded = crate::program::load_with_text(path, None)?;
    let out = declare_loaded(&mut kernel, &loaded)?;
    Ok((out, kernel.elaborated().to_vec()))
}

/// Declares the files of `loaded` in order, with what went wrong reading
/// their macros and syntaxes.
/// How long checking each file of `loaded` may take, as the `check` section
/// of the `Tauto.eure` above it says.
pub fn time_limits(loaded: &crate::program::Loaded) -> Result<Vec<std::time::Duration>, String> {
    loaded
        .files
        .iter()
        .map(|f| crate::manifest::time_limit(&f.path))
        .collect()
}

fn declare_loaded(
    kernel: &mut Kernel,
    loaded: &crate::program::Loaded,
) -> Result<Vec<FileEntry>, String> {
    let limits = time_limits(loaded)?;
    let mut out = Vec::new();
    kernel.show_syntax(shown_syntax(loaded));
    // The file that first declared each name, so that a name declared again
    // in another file is reported with where it was first.
    let mut declared_in: HashMap<String, usize> = HashMap::new();
    for (index, (file, stmts)) in loaded.files.iter().zip(&loaded.kernel_files).enumerate() {
        let shown = file.path.display().to_string();
        kernel.set_file_limit(Some((&shown, limits[index])));
        let program = Program {
            stmts: stmts.clone(),
            errors: Vec::new(),
        };
        for entry in kernel.declare_program(&program) {
            // A call whose macro failed is reported where the macro was.
            if !keeps_entry(loaded, &entry) {
                continue;
            }
            let mut entry = entry;
            if !already_defined_elsewhere(loaded, index, stmts, &declared_in, &mut entry) {
                declared_in.entry(entry.name.clone()).or_insert(index);
            }
            localize(&loaded, file, &mut entry.verdict);
            out.push(FileEntry {
                file: crate::program::canonical_path(&file.path),
                entry,
            });
        }
    }
    kernel.set_file_limit(None);
    out.extend(macro_failures(loaded));
    Ok(out)
}

pub(crate) const ALREADY_DEFINED: &[&str] = &[
    "kernel-core-already-defined",
    "kernel-core-ctor-already-defined",
    "kernel-already-defined",
    "kernel-class-defined",
    "kernel-instance-defined",
];

/// When `entry` of `loaded.files[index]` says its name is already defined
/// and another file declared it first: says which file, places it at the
/// declaration when it has no place, and, when one of the two files is a
/// standard library file read by its path, says to import it by name. Both
/// copies of the same file are then read, which is why the name is twice.
fn already_defined_elsewhere(
    loaded: &crate::program::Loaded,
    index: usize,
    stmts: &[Stmt],
    declared_in: &HashMap<String, usize>,
    entry: &mut check::Entry,
) -> bool {
    let Verdict::Failed(d) = &mut entry.verdict else {
        return false;
    };
    if !crate::said::says(&d.message, ALREADY_DEFINED) {
        return false;
    }
    let Some(&first) = declared_in.get(&entry.name) else {
        return true;
    };
    if first == index {
        return true;
    }
    if d.span.is_none() {
        d.span = declaration_span(stmts, &entry.name);
    }
    let shown = |f: &crate::program::SourceFile| match crate::stdlib::module_of_path(&f.path) {
        Some(m) if crate::stdlib::text(&f.path).is_some() => format!("std.{m}"),
        _ => f.path.display().to_string(),
    };
    let earlier = &loaded.files[first];
    let here = &loaded.files[index];
    let by_path = [here, earlier].into_iter().find_map(|f| {
        if crate::stdlib::text(&f.path).is_some() {
            return None;
        }
        crate::stdlib::std_copy(&f.path, &f.text).map(|m| (f, m))
    });
    let message = msg!(
        "tauto-already-defined-in",
        message = d.message.clone(),
        earlier = shown(earlier)
    );
    d.message = match by_path {
        Some((f, module)) => msg!(
            "tauto-std-by-path",
            message = message,
            path = f.path.display().to_string(),
            module = module
        ),
        None => message,
    };
    true
}

/// Where `name` is declared among `stmts`, for a message the kernel gave no place.
fn declaration_span(stmts: &[Stmt], name: &str) -> Option<Span> {
    stmts.iter().find_map(|s| match s {
        Stmt::Theorem(t) | Stmt::Def(t) if t.name == name => Some(t.span),
        Stmt::Fn(f) if f.name == name => Some(f.span),
        Stmt::Inductive(i) if i.name == name => Some(i.span),
        Stmt::Class(c) if c.name == name => Some(c.span),
        Stmt::Mutual { items, .. } => declaration_span(items, name),
        _ => None,
    })
}

/// What a syntax macro's output was written as, by the span of its root node.
fn shown_syntax(loaded: &crate::program::Loaded) -> HashMap<u32, String> {
    loaded
        .expansions
        .iter()
        .filter(|e| e.root != 0 && e.kind == "syntax")
        .map(|e| {
            let text = e.text.split_whitespace().collect::<Vec<_>>().join(" ");
            (e.root, format!("{}!(`{text}`)", e.macro_name))
        })
        .collect()
}

/// Whether an entry is reported: a call whose macro failed is reported where
/// the macro was, not as a term the kernel cannot read.
fn keeps_entry(loaded: &crate::program::Loaded, entry: &Entry) -> bool {
    loaded.program.errors.is_empty()
        || !matches!(&entry.verdict, Verdict::Failed(d)
            if d.message.id == "kernel-not-kernel-term-kind"
                && crate::said::text_arg(&d.message, "kind") == Some("this syntax"))
}

/// What went wrong reading the macros and syntaxes, at where it was written.
fn macro_failures(loaded: &crate::program::Loaded) -> Vec<FileEntry> {
    let mut out = Vec::new();
    for (message, at) in &loaded.program.errors {
        let origin = |mut offset: u32| {
            while let Some((w, _)) = loaded.spans.origin(offset) {
                offset = w;
            }
            offset
        };
        let written = origin(at.start);
        let Some(file) = loaded.files.iter().rev().find(|f| f.base <= written) else {
            continue;
        };
        // The whole of what is written, when its end is in the same file after
        // its start; else where it starts.
        let end = Some(origin(at.end))
            .filter(|&e| written <= e && e <= file.base + file.text.len() as u32)
            .unwrap_or(written);
        let mut diagnostic = Diagnostic::new(
            message.clone(),
            Some(Span::new(written - file.base, end - file.base)),
        );
        // The edit is where the source says; spans made by a macro are walked back as
        // the error's is.
        diagnostic.fix = loaded
            .fixes
            .iter()
            .find(|(span, _)| span == at)
            .and_then(|(_, fix)| {
                let written = |mut offset: u32| {
                    while let Some((w, _)) = loaded.spans.origin(offset) {
                        offset = w;
                    }
                    offset
                };
                let (start, end) = (written(fix.span.start), written(fix.span.end));
                (file.base <= start && start <= end).then(|| Fix {
                    title: fix.title.clone(),
                    span: Span::new(start - file.base, end - file.base),
                    text: fix.text.clone(),
                })
            });
        out.push(FileEntry {
            file: crate::program::canonical_path(&file.path),
            entry: Entry {
                name: "macro".into(),
                verdict: Verdict::Failed(diagnostic),
            },
        });
    }
    out
}

/// A span of the program as a span of `file`: one made by a macro is where the
/// macro was written (or, if that is in another file, where it was called), and
/// the base of the file is taken off.
fn local_span(
    loaded: &crate::program::Loaded,
    file: &crate::program::SourceFile,
    sp: Span,
) -> Span {
    let file_of = |at: u32| loaded.files.iter().rev().find(|f| f.base <= at);
    let mut at = sp.start;
    let mut moved = false;
    let mut call = None;
    while let Some((written, expansion)) = loaded.spans.origin(at) {
        call = loaded
            .expansions
            .iter()
            .find(|e| e.id == expansion)
            .map(|e| e.call.start)
            .or(call);
        at = written;
        moved = true;
    }
    if file_of(at).is_none_or(|f| f.base != file.base) {
        let mut c = call.unwrap_or(at);
        while let Some((written, _)) = loaded.spans.origin(c) {
            c = written;
        }
        at = c;
        moved = true;
    }
    let start = at.saturating_sub(file.base);
    let end = if moved {
        start
    } else {
        start + (sp.end - sp.start)
    };
    Span::new(start, end)
}

/// Rewrites the spans of a verdict as offsets into `file`: a span made by a
/// macro becomes where the macro was written (or, if that is in another file,
/// where it was called), and the base of the file is taken off.
fn localize(
    loaded: &crate::program::Loaded,
    file: &crate::program::SourceFile,
    verdict: &mut Verdict,
) {
    let local = |sp: Span| local_span(loaded, file, sp);
    match verdict {
        Verdict::Failed(d) => {
            if let Some(hint) = crate::said::ends_with(
                &d.message,
                &["kernel-not-defined", "kernel-not-defined-hint"],
            )
            .and_then(|m| crate::said::text_arg(m, "name"))
            .and_then(crate::stdlib::not_imported_name)
            {
                d.message = msg!(
                    "tauto-not-imported",
                    message = d.message.clone(),
                    hint = hint
                );
            }
            if let Some(sp) = d.span {
                let mut at = sp.start;
                while let Some((written, expansion)) = loaded.spans.origin(at) {
                    if let Some(e) = loaded.expansions.iter().find(|e| e.id == expansion) {
                        let mut call = e.call.start;
                        while let Some((w, _)) = loaded.spans.origin(call) {
                            call = w;
                        }
                        let message = d.message.clone();
                        d.message = match loaded.files.iter().rev().find(|f| f.base <= call) {
                            Some(f) if f.base == file.base => msg!(
                                "tauto-in-expansion-at",
                                message = message,
                                name = &e.macro_name,
                                byte = call - f.base
                            ),
                            _ => msg!(
                                "tauto-in-expansion",
                                message = message,
                                name = &e.macro_name
                            ),
                        };
                    }
                    at = written;
                }
                // A node the macro wrote itself (a `quote` of its own file):
                // the place in the macro, which the call's place does not say.
                if at != sp.start
                    && let Some(f) = loaded.files.iter().rev().find(|f| f.base <= at)
                    && f.base != file.base
                    && let Some(before) = f.text.get(..(at - f.base) as usize)
                {
                    let line = before.matches('\n').count() + 1;
                    let column = before.len() - before.rfind('\n').map_or(0, |i| i + 1) + 1;
                    let file = f
                        .path
                        .file_name()
                        .map_or(f.path.display(), |n| std::path::Path::new(n).display())
                        .to_string();
                    d.message = msg!(
                        "tauto-written-in-macro-at",
                        message = d.message.clone(),
                        file = file,
                        line = line as u64,
                        column = column as u64
                    );
                }
            }
            d.span = d.span.map(local);
            if let Some(fix) = &mut d.fix {
                fix.span = local(fix.span);
            }
        }
        Verdict::Incomplete { holes, .. } => {
            for h in holes {
                h.span = local(h.span);
            }
        }
        _ => {}
    }
}

/// Checks the files (each with what it imports, every file once) and reads
/// the signatures of the declarations that checked.
pub fn check_files(roots: &[PathBuf]) -> Result<Checked, String> {
    check_files_cached(roots, true)
}

/// [`check_files`], where a proof that was checked before is taken as
/// checked (`crates/tauto-kernel/src/check/cache.rs`) when `cached`; otherwise every proof is
/// checked again.
pub fn check_files_cached(roots: &[PathBuf], cached: bool) -> Result<Checked, String> {
    check_files_mode(roots, cached, false)
}

pub fn check_tote_files(roots: &[PathBuf], cached: bool) -> Result<Checked, String> {
    check_files_mode(roots, cached, true)
}

fn check_files_mode(roots: &[PathBuf], cached: bool, mixed: bool) -> Result<Checked, String> {
    check_files_for_extraction(roots, cached, mixed).map(|input| input.checked)
}

/// The exact expanded source that was presented to the kernel, including
/// executable declarations before they are separated from the proof environment.
pub(crate) struct ExtractionInput {
    pub checked: Checked,
    pub sources: Vec<(crate::program::SourceFile, Vec<Stmt>)>,
    pub imports: std::collections::HashMap<PathBuf, Vec<PathBuf>>,
}

pub(crate) fn check_files_for_extraction(
    roots: &[PathBuf],
    cached: bool,
    mixed: bool,
) -> Result<ExtractionInput, String> {
    let mut kernel = Kernel::new();
    let prelude_names = check::declare_prelude(&mut kernel)?;
    kernel.record_ctor_sites();
    if cached {
        kernel.use_cache();
    }
    let mut loaded = crate::program::load_roots(roots)?;
    // The statements the kernel checks, classes as written: the extracted
    // functions follow the kernel's signatures, whose `where` records a
    // program expanded for Nib has already turned into parameters.
    let sources = loaded
        .files
        .iter()
        .cloned()
        .zip(loaded.kernel_files.clone())
        .collect();
    let imports = loaded
        .files
        .iter()
        .map(|f| f.path.clone())
        .zip(loaded.imports.clone())
        .collect();
    let (mut runtime, effectful, why) = if mixed {
        for file in &loaded.files {
            if !crate::program::is_source_file(&file.path) {
                return Err(format!(
                    "{}: tote sources must use .taut or .tauto",
                    file.path.display()
                ));
            }
        }
        runtime::separate(&mut loaded)?
    } else {
        (HashSet::new(), HashSet::new(), HashMap::new())
    };
    let mut out = declare_loaded(&mut kernel, &loaded)?;
    runtime::explain_undefined(&mut out, &why);
    let files = loaded
        .files
        .iter()
        .map(|f| f.path.canonicalize().unwrap_or_else(|_| f.path.clone()))
        .collect();
    let mut checked = check::checked_entries(kernel, files, out, prelude_names);
    for e in &checked.entries {
        if effectful.contains(&e.entry.name) && matches!(e.entry.verdict, Verdict::Skipped(_)) {
            runtime.insert(e.entry.name.clone());
        }
    }
    checked.runtime = runtime;
    let sources = with_derived(sources, &checked.derived);
    Ok(ExtractionInput {
        checked,
        sources,
        imports,
    })
}

/// `sources` with the declarations a decidable equality generated written right after the
/// family that lists them, so that extraction reaches them as it reaches what is written.
fn with_derived(
    sources: Vec<(crate::program::SourceFile, Vec<Stmt>)>,
    derived: &[(String, Vec<Stmt>)],
) -> Vec<(crate::program::SourceFile, Vec<Stmt>)> {
    if derived.is_empty() {
        return sources;
    }
    sources
        .into_iter()
        .map(|(file, stmts)| {
            let mut out = Vec::with_capacity(stmts.len());
            for s in stmts {
                let made = match &s {
                    Stmt::Inductive(i) => derived.iter().find(|(f, _)| *f == i.name),
                    _ => None,
                };
                out.push(s);
                if let Some((_, made)) = made {
                    out.extend(made.iter().cloned());
                }
            }
            (file, out)
        })
        .collect()
}

/// The verdicts of a statement as offsets into the file it is in, which is
/// `loaded.files[file]`.
/// Returns whether a failed verdict's span originates in a macro expansion,
/// before localization moves its span to the written call site.
pub fn localize_entries(loaded: &Loaded, file: usize, entries: &mut Vec<Entry>) -> bool {
    entries.retain(|e| keeps_entry(loaded, e));
    let positional = entries.iter().any(|entry| match &entry.verdict {
        Verdict::Failed(d) => d
            .span
            .is_some_and(|span| loaded.spans.origin(span.start).is_some()),
        _ => false,
    });
    for e in entries {
        localize(loaded, &loaded.files[file], &mut e.verdict);
    }
    positional
}

/// Where a statement of `loaded.files[file]` starts in that file, as the
/// spans of its verdicts are placed; none when it has no place of its own.
/// Moving a statement moves its verdicts by the change of this.
pub fn anchor_of(loaded: &Loaded, file: usize, stmt: &Stmt) -> Option<u32> {
    stmt_span(loaded, file, stmt).map(|s| s.start)
}

/// The text a statement of `loaded.files[file]` was written as, when it has
/// a place of its own. Its verdicts are placed by this text and the anchor
/// alone: two statements that read the same and start at the same place have
/// their holes and errors at the same places. The statement itself does not
/// tell this, as parentheses and spaces leave no trace in it.
pub fn text_of<'a>(loaded: &'a Loaded, file: usize, stmt: &Stmt) -> Option<&'a str> {
    let span = stmt_span(loaded, file, stmt)?;
    loaded.files[file]
        .text
        .get(span.start as usize..span.end as usize)
}

pub(crate) fn stmt_span(loaded: &Loaded, file: usize, stmt: &Stmt) -> Option<Span> {
    let span = match stmt {
        Stmt::Theorem(t) | Stmt::Def(t) => t.span,
        Stmt::Inductive(i) => i.span,
        Stmt::Fn(f) => f.span,
        Stmt::Class(c) => c.span,
        Stmt::Instance(i) => i.span,
        Stmt::Mutual { span, .. } => *span,
        Stmt::Let { value, .. } => value.span,
        _ => return None,
    };
    Some(local_span(loaded, &loaded.files[file], span))
}

/// The macro and syntax failures of a program, as `check_file` ends its list with.
pub fn macro_failures_of(loaded: &Loaded) -> Vec<FileEntry> {
    macro_failures(loaded)
}

/// What `check --json` says of each macro run.
pub fn expansion_infos(loaded: &Loaded) -> Vec<ExpansionInfo> {
    expansion_infos_of(loaded)
}

#[derive(Clone)]
pub struct Checker {
    inner: check::Checker,
}

impl Checker {
    /// The prelude's constants and nothing else. With `proof_cache`, reuse
    /// proofs from `TAUTO_CACHE`; otherwise check each proof again.
    pub fn new(proof_cache: bool) -> Result<Self, String> {
        Ok(Self {
            inner: check::Checker::new(proof_cache)?,
        })
    }

    /// Show syntax macro output as it was written in the loaded source.
    pub fn show_syntax(&mut self, loaded: &Loaded) {
        self.inner.show_syntax(shown_syntax(loaded));
    }

    /// The constants in scope, sorted by name.
    pub fn library(&self) -> Vec<LibEntry> {
        self.inner.library()
    }

    /// Declare one statement with the same checks as a whole program.
    pub fn declare(&mut self, stmt: &Stmt) -> Declared {
        self.inner.declare(stmt)
    }
}

/// `expr` in normal form after the declarations of `path` and what it
/// imports, and its type, as `tauto eval` shows them.
/// A value of `Text` is also shown as the characters its bytes spell.
pub fn eval_file(
    path: &std::path::Path,
    expr: &str,
) -> Result<(String, String, Option<String>), String> {
    let mut kernel = Kernel::new();
    check::declare_prelude(&mut kernel)?;
    kernel.use_cache();
    let loaded = crate::program::load_with_text(path, None)?;
    declare_loaded(&mut kernel, &loaded)?;
    let term = crate::surface::parse_expr_at(expr, 0)
        .map_err(|e| msg!("tauto-not-a-term", expr = expr, error = e).to_string())?;
    let (value, ty) = check::eval_term(&mut kernel, &term)?;
    let spelled = text_bytes(&value).and_then(|b| String::from_utf8(b).ok());
    Ok((check::describe(&value), check::describe(&ty), spelled))
}

/// The bytes of `Text::Mk(Cons(b0, Cons(b1, … Nil)))`.
fn text_bytes(t: &crate::surface::SurfaceTerm) -> Option<Vec<u8>> {
    use crate::surface::TermKind;
    let call = |t: &crate::surface::SurfaceTerm| match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } => match &*function.kind {
            TermKind::Var(f) => Some((f.clone(), arguments.clone())),
            _ => None,
        },
        TermKind::Var(f) => Some((f.clone(), Vec::new())),
        _ => None,
    };
    let (f, args) = call(t)?;
    let [mut list] = <[_; 1]>::try_from(args).ok()?;
    if f != "Text::Mk" && f != "Mk" {
        return None;
    }
    let mut out = Vec::new();
    loop {
        match call(&list)? {
            (n, a) if n == "Nil" && a.is_empty() => return Some(out),
            (c, a) if c == "Cons" && a.len() == 2 => {
                let TermKind::Nat(b) = &*a[0].kind else {
                    return None;
                };
                out.push(b.parse().ok()?);
                list = a[1].clone();
            }
            _ => return None,
        }
    }
}
