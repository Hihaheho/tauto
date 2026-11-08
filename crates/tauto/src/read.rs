//! Reading, expanding and checking source files.

use crate::surface::Name;
mod runtime;
pub(crate) use runtime::prefix_families;
mod term_generics;

use crate::program::Loaded;
use crate::surface::{Program, Stmt, SurfaceTerm, parse_program_unresolved_at};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use tauto_kernel::check::{self, *};
use tauto_message::{Message, msg};
use tauto_parol::Span;

pub fn parse_program(source: &str) -> Result<Program, Message> {
    let program = parse_program_at(source, 0)?;
    let mut program = crate::types::expand_classes(program, 1 << 30);
    tauto_surface::resolve::Resolver::default().statements(&mut program.stmts);
    Ok(program)
}

/// Parses a whole program whose spans start at `base`.
pub fn parse_program_at(source: &str, base: u32) -> Result<Program, Message> {
    expand_program(parse_program_unresolved_at(source, base)?, true)
}

/// [`parse_program`] of the prelude itself, whose names are its own.
pub fn parse_prelude(source: &str) -> Result<Program, Message> {
    let program = parse_prelude_at(source, 0).map_err(|e| {
        if source == crate::nibstd::PRELUDE {
            Message::text(crate::nibstd::locate_error(
                e.to_string(),
                0,
                crate::nibstd::PRELUDE_FILES,
            ))
        } else {
            e
        }
    })?;
    Ok(crate::types::expand_classes(program, 1 << 30))
}

/// [`parse_program_at`] of the prelude itself, whose names are its own.
pub(crate) fn parse_prelude_at(source: &str, base: u32) -> Result<Program, Message> {
    let mut program = parse_program_unresolved_at(source, base)?;
    // The prelude's own names are short: `#(a, b)` matches its `Pair`.
    crate::surface::qualify::lower_prelude_names(&mut program.stmts);
    expand_program(program, false)
}

/// [`parse_program_at`] of the text of the file at `path`: its
/// `include_text!` calls read relative to it (`program/include.rs`).
pub fn parse_file_at(source: &str, base: u32, path: &std::path::Path) -> Result<Program, Message> {
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
pub(crate) fn parse_program_unexpanded(source: &str) -> Result<Program, Message> {
    let mut program = parse_program_unresolved_at(source, 0)?;
    let mut files = vec![std::mem::take(&mut program.stmts)];
    crate::surface::qualify::files(&mut files, &["main".to_string()], None);
    tauto_surface::records::declare(&mut files);
    program.stmts = crate::surface::modules::resolve(files.concat()).0;
    Ok(program)
}

fn expand_program(mut program: Program, qualify: bool) -> Result<Program, Message> {
    let modules = ["main".to_string()];
    let mut files = vec![std::mem::take(&mut program.stmts)];
    let mut qualified = if qualify {
        crate::surface::qualify::files_before_macros(&mut files, &modules, None, None, None).0
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
        // A record without a name is one struct for the whole program.
        tauto_surface::records::declare(&mut out.files);
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
    let mut bindings = if qualify {
        out.bindings
    } else {
        tauto_surface::resolve::Resolver::new(tauto_surface::bindings::library_definition_bindings())
    };
    bindings.statements(&mut program.stmts);
    bindings.source_modules(&modules);
    program.errors = errors;
    Ok(program)
}

/// Checks `source`: the prelude's constants, then each declaration in order.
pub fn check(source: &str) -> Result<Vec<Entry>, Message> {
    let program = parse_program(source)?;
    if program
        .stmts
        .iter()
        .any(|s| matches!(s, Stmt::Import { .. }))
    {
        return Err(msg!("tauto-imports-need-path"));
    }
    let mut kernel = Kernel::new();
    check::declare_prelude(&mut kernel)?;
    Ok(kernel.declare_program(&program))
}

pub fn check_types(source: &str) -> Result<crate::types::TypeReport, Message> {
    let program = parse_program(source)?;
    Ok(crate::types::check_program(&program))
}

pub fn check_rows(source: &str) -> Result<crate::rows::RowReport, Message> {
    let program = parse_program(source)?;
    Ok(crate::rows::check_program_rows(&program))
}

pub fn check_lin(source: &str) -> Result<Vec<crate::lin::LinError>, Message> {
    Ok(crate::lin::check_lin_program(&parse_program(source)?)?)
}

use crate::eval::{DEFAULT_BUDGET, Outcome, RunError, RunOptions, run_program_with};

/// Runs a loaded program with the effect evidence retained by its loader.
pub fn run_loaded_with(
    loaded: &Loaded,
    budget: u64,
    options: RunOptions,
) -> Result<Outcome, RunError> {
    let mut loaded = loaded.clone();
    loaded.resolve_runtime();
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
    let mut program = parse_program(source).map_err(|e| RunError::Syntax(e.to_string()))?;
    tauto_surface::resolve::Resolver::default().statements(&mut program.stmts);
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
pub fn check_file(path: &std::path::Path) -> Result<Vec<FileEntry>, Message> {
    check_file_with(path, None)
}

/// [`check_file`] with the text of `path` itself given instead of read: a
/// candidate edit is checked without touching the file. Its imports are
/// still read relative to `path`.
pub fn check_file_with(
    path: &std::path::Path,
    text: Option<&str>,
) -> Result<Vec<FileEntry>, Message> {
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
) -> Result<(Vec<FileEntry>, Vec<ExpansionInfo>), Message> {
    check_file_lib(path, text).map(|(entries, expansions, _)| (entries, expansions))
}

/// [`check_file_full`] and the constants known at the end, by name.
pub fn check_file_lib(
    path: &std::path::Path,
    text: Option<&str>,
) -> Result<(Vec<FileEntry>, Vec<ExpansionInfo>, Vec<LibEntry>), Message> {
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
    Message,
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
    Message,
> {
    let (entries, expansions, library, timings, _) = check_file_sourced_with_names(path, source)?;
    Ok((entries, expansions, library, timings))
}

pub(crate) type SourceNames =
    std::collections::BTreeMap<std::path::PathBuf, tauto_surface::source_names::SourceNames>;

pub(crate) fn check_file_timed_with_names(
    path: &std::path::Path,
    text: Option<&str>,
) -> Result<
    (
        Vec<FileEntry>,
        Vec<ExpansionInfo>,
        Vec<LibEntry>,
        Vec<Timing>,
        SourceNames,
    ),
    Message,
> {
    let given = text.and_then(|text| Some((path.canonicalize().ok()?, text.to_string())));
    check_file_sourced_with_names(path, &|path| match &given {
        Some((own, text)) if own == path => Some(Ok(text.clone())),
        _ => None,
    })
}

fn check_file_sourced_with_names(
    path: &std::path::Path,
    source: &crate::program::Source<'_>,
) -> Result<
    (
        Vec<FileEntry>,
        Vec<ExpansionInfo>,
        Vec<LibEntry>,
        Vec<Timing>,
        SourceNames,
    ),
    Message,
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
    let mut loaded = crate::program::load_with_source_in(path, source)?;
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
    let (runtime, why) = for_kernel(&mut loaded)?;
    let mut out = declare_loaded(&mut kernel, &loaded)?;
    runtime::explain_undefined(&mut out, &why);
    let seen: HashSet<Name> = out.iter().map(|e| e.entry.name.clone()).collect();
    for (file, fns) in loaded.files.iter().zip(fns_of) {
        for name in fns {
            if runtime.contains(&name) && !seen.contains(&name) {
                out.push(FileEntry {
                    file: crate::program::canonical_path(&file.path),
                    entry: check::Entry {
                        name,
                        verdict: Verdict::Skipped(msg!("tauto-skipped-runs")),
                    },
                });
            }
        }
    }
    let library = kernel.library();
    let timings = kernel.timings().to_vec();
    Ok((out, expansions, library, timings, loaded.source_names()))
}

/// Sets apart what runs as written from what the kernel reads, in
/// `loaded.kernel_files`: the names that run as written, and why each does.
fn for_kernel(
    loaded: &mut crate::program::Loaded,
) -> Result<(HashSet<Name>, runtime::Why), Message> {
    if loaded
        .files
        .iter()
        .all(|f| crate::program::is_source_file(&f.path))
    {
        let (runtime, _, why) = runtime::separate(loaded)?;
        Ok((runtime, why))
    } else {
        // A Nib file runs as a whole, but its `inductive struct` and
        // `inductive enum` are families to the kernel as in a source file.
        runtime::families_only(loaded);
        Ok((HashSet::new(), HashMap::new()))
    }
}

/// Sugar refers to the standard declarations even when a tote's module
/// prefix changes their displayed source paths: the short name of each one a
/// standard file declares, and the declaration.
fn standard_aliases(
    file: &crate::program::SourceFile,
    stmts: &[Stmt],
) -> Vec<(String, tauto_surface::identity::DeclRef)> {
    let standard = file.path.starts_with(crate::stdlib::ROOT)
        || crate::stdlib::FILES
            .iter()
            .any(|(_, text)| *text == file.text);
    if !standard {
        return Vec::new();
    }
    crate::bindings::declared_names(stmts)
        .into_iter()
        .filter_map(|name| {
            let reference = name.as_global()?;
            Some((
                crate::surface::qualify::short(name).to_string(),
                reference.clone(),
            ))
        })
        .collect()
}

/// The statements of each file of a loaded program as `check_file` gives
/// them to the kernel, for a checker that declares them one at a time
/// ([`Checker`]): what runs as written set apart, the `inductive enum`s and
/// `inductive struct`s as families, the classes as written, and each file's
/// statements in the order the kernel checks them in. The program itself is
/// left as it is.
pub struct KernelStatements {
    pub files: Vec<Vec<Stmt>>,
    /// [`standard_aliases`] of each file.
    aliases: Vec<Vec<(String, tauto_surface::identity::DeclRef)>>,
    why: runtime::Why,
}

impl KernelStatements {
    pub fn of(loaded: &crate::program::Loaded) -> Result<KernelStatements, String> {
        let mut loaded = loaded.clone();
        let (_, why) = for_kernel(&mut loaded).map_err(|e| e.to_string())?;
        let aliases = loaded
            .files
            .iter()
            .zip(&loaded.kernel_files)
            .map(|(file, stmts)| standard_aliases(file, stmts))
            .collect();
        // In the order `check_file` checks each file's statements in.
        let files = loaded
            .kernel_files
            .into_iter()
            .map(|stmts| {
                check::checking_order(&stmts)
                    .into_iter()
                    .map(|i| stmts[i].clone())
                    .collect()
            })
            .collect();
        Ok(KernelStatements {
            files,
            aliases,
            why,
        })
    }

    /// A proof that failed on a name that runs as written says why, as
    /// `check_file` says it.
    pub fn explain(&self, entries: &mut [FileEntry]) {
        runtime::explain_undefined(entries, &self.why);
    }
}

fn fn_names(stmts: &[Stmt], out: &mut Vec<Name>) {
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
) -> Result<(Vec<FileEntry>, Vec<(Name, SurfaceTerm)>), Message> {
    let mut kernel = Kernel::new();
    check::declare_prelude(&mut kernel)?;
    kernel.record_elaborated();
    let loaded = crate::program::load_with_text_in(path, None)?;
    let out = declare_loaded(&mut kernel, &loaded)?;
    Ok((out, kernel.elaborated().to_vec()))
}

/// Declares the files of `loaded` in order, with what went wrong reading
/// their macros and syntaxes.
/// How long checking each file of `loaded` may take, as the `check` section
/// of the `Tauto.eure` above it says.
pub fn time_limits(loaded: &crate::program::Loaded) -> Result<Vec<std::time::Duration>, Message> {
    loaded
        .files
        .iter()
        .map(|f| crate::manifest::time_limit(&f.path))
        .collect()
}

pub(crate) fn declare_loaded(
    kernel: &mut Kernel,
    loaded: &crate::program::Loaded,
) -> Result<Vec<FileEntry>, Message> {
    let limits = time_limits(loaded)?;
    let mut out = Vec::new();
    kernel.show_syntax(shown_syntax(loaded));
    // The file that first declared each name, so that a name declared again
    // in another file is reported with where it was first.
    let mut declared_in: HashMap<Name, usize> = HashMap::new();
    for (index, (file, stmts)) in loaded.files.iter().zip(&loaded.kernel_files).enumerate() {
        for (spelling, reference) in standard_aliases(file, stmts) {
            kernel.source_alias(&spelling, &reference);
        }
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
    refuse_unlisted_axioms(&mut out)?;
    Ok(out)
}

/// A declaration that depends on an axiom its file's `check.axioms` does not
/// list fails. An axiom's own declaration lists itself: what is refused is
/// the use of it.
fn refuse_unlisted_axioms(entries: &mut [FileEntry]) -> Result<(), Message> {
    let mut allowed = HashMap::new();
    for FileEntry { file, entry } in entries {
        let Verdict::Checked { axioms } = &entry.verdict else {
            continue;
        };
        if axioms.is_empty() || axioms.as_slice() == [entry.name.clone()] {
            continue;
        }
        if !allowed.contains_key(file) {
            allowed.insert(file.clone(), crate::manifest::allowed_axioms(file)?);
        }
        let Some(listed) = &allowed[file] else {
            continue;
        };
        let unlisted: Vec<String> = axioms
            .iter()
            .map(|axiom| (axiom, axiom.to_string()))
            .filter(|(axiom, written)| {
                !listed
                    .iter()
                    .any(|name| name == written || crate::bindings::is_library(axiom, name))
            })
            .map(|(_, written)| written)
            .collect();
        if !unlisted.is_empty() {
            let name = entry.name.to_string();
            entry.verdict = Verdict::Failed(crate::check::Diagnostic::new(
                msg!(
                    "tauto-unlisted-axioms",
                    name = name,
                    axioms = unlisted.join(", ")
                ),
                None,
            ));
        }
    }
    Ok(())
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
    declared_in: &HashMap<Name, usize>,
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
        Stmt::Theorem(t) | Stmt::Def(t) if t.name.as_str() == name => Some(t.span),
        Stmt::Fn(f) if f.name.as_str() == name => Some(f.span),
        Stmt::Inductive(i) if i.name.as_str() == name => Some(i.span),
        Stmt::Class(c) if c.name.as_str() == name => Some(c.span),
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
            // The other uses of names that are not defined, each as a failure
            // of its own; one written outside this file is left out.
            let also = std::mem::take(&mut d.also);
            for a in also {
                let in_file = a.span.is_some_and(|sp| {
                    loaded
                        .files
                        .iter()
                        .rev()
                        .find(|f| f.base <= sp.start)
                        .is_some_and(|f| f.base == file.base)
                });
                if !in_file {
                    continue;
                }
                let mut v = Verdict::Failed(a);
                localize(loaded, file, &mut v);
                if let Verdict::Failed(a) = v {
                    d.also.push(a);
                }
            }
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
pub fn check_files(roots: &[PathBuf]) -> Result<Checked, Message> {
    check_files_cached(roots, true)
}

/// [`check_files`], where a proof that was checked before is taken as
/// checked (`crates/tauto-kernel/src/check/cache.rs`) when `cached`; otherwise every proof is
/// checked again.
pub fn check_files_cached(roots: &[PathBuf], cached: bool) -> Result<Checked, Message> {
    check_files_mode(roots, cached, false)
}

pub fn check_tote_files(roots: &[PathBuf], cached: bool) -> Result<Checked, Message> {
    check_files_mode(roots, cached, true)
}

fn check_files_mode(roots: &[PathBuf], cached: bool, mixed: bool) -> Result<Checked, Message> {
    check_files_for_extraction(roots, cached, mixed).map(|input| input.checked)
}

/// The exact expanded source that was presented to the kernel, including
/// executable declarations before they are separated from the proof environment.
pub(crate) struct ExtractionInput {
    pub bindings: tauto_surface::resolve::Resolver,
    pub checked: Checked,
    pub runtime_reasons: HashMap<Name, tauto_message::Message>,
    pub sources: Vec<(crate::program::SourceFile, Vec<Stmt>)>,
    pub loaded: Loaded,
}

pub(crate) fn check_files_for_extraction(
    roots: &[PathBuf],
    cached: bool,
    mixed: bool,
) -> Result<ExtractionInput, Message> {
    let mut kernel = Kernel::new();
    let prelude_names = check::declare_prelude(&mut kernel)?;
    kernel.record_ctor_sites();
    if cached {
        kernel.use_cache();
    }
    let mut loaded = crate::program::load_roots_in(roots)?;
    // The statements the kernel checks, classes as written: the extracted
    // functions follow the kernel's signatures, whose `where` records a
    // program expanded for Nib has already turned into parameters.
    let mut sources: Vec<_> = loaded
        .files
        .iter()
        .cloned()
        .zip(loaded.kernel_files.clone())
        .collect();
    let (mut runtime, effectful, why) = if mixed {
        for file in &loaded.files {
            if !crate::program::is_source_file(&file.path) {
                return Err(msg!(
                    "tauto-tote-source-extension",
                    file = file.path.display().to_string()
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
    for (_, statements) in &mut sources {
        kernel.resolve_statements(statements);
    }
    kernel.resolve_statements(&mut loaded.program.stmts);
    for statements in &mut loaded.per_file {
        kernel.resolve_statements(statements);
    }
    for statements in &mut loaded.kernel_files {
        kernel.resolve_statements(statements);
    }
    runtime = runtime
        .into_iter()
        .map(|name| kernel.resolve_declaration(&name))
        .collect();
    let effectful: HashSet<_> = effectful
        .into_iter()
        .map(|name| kernel.resolve_declaration(&name))
        .collect();
    let mut runtime_reasons: HashMap<_, _> = why
        .into_iter()
        .map(|(name, reason)| (kernel.resolve_declaration(&name), reason))
        .collect();
    term_generics::specialize(&mut kernel, &mut sources, &mut loaded, &runtime, &mut out)?;
    let bindings = kernel.binding_session();
    let mut checked = check::checked_entries(kernel, files, out, prelude_names);
    for e in &checked.entries {
        if effectful.contains(&e.entry.name) && matches!(e.entry.verdict, Verdict::Skipped(_)) {
            runtime.insert(e.entry.name.clone());
            if let Verdict::Skipped(reason) = &e.entry.verdict {
                runtime_reasons
                    .entry(e.entry.name.clone())
                    .or_insert_with(|| reason.clone());
            }
        }
    }
    checked.runtime = runtime;
    let sources = with_class_dictionaries(sources, &mut checked)?;
    let mut sources = with_derived(sources, &checked.derived);
    for (_, statements) in &mut sources {
        crate::extract::selected_references(&checked, statements)?;
    }
    Ok(ExtractionInput {
        runtime_reasons,
        bindings,
        checked,
        sources,
        loaded,
    })
}

/// Retains the kernel's dictionary expansion for classes with a typed telescope.
/// The expanded declarations are lowered through the ordinary checked value
/// representation; Nib does not resolve value-indexed instances a second time.
fn with_class_dictionaries(
    sources: Vec<(crate::program::SourceFile, Vec<Stmt>)>,
    checked: &mut Checked,
) -> Result<Vec<(crate::program::SourceFile, Vec<Stmt>)>, Message> {
    fn type_parameter(ty: &SurfaceTerm) -> bool {
        match &*ty.kind {
            crate::surface::TermKind::Var(name) => name.as_str() == "Type",
            crate::surface::TermKind::Pi {
                params,
                result,
                effects,
            } => {
                effects.as_ref().is_none_or(|row| row.is_empty())
                    && params.iter().all(|(_, ty)| type_parameter(ty))
                    && type_parameter(result)
            }
            _ => false,
        }
    }
    fn legacy_head(head: &SurfaceTerm, generics: &[Name]) -> bool {
        match &*head.kind {
            crate::surface::TermKind::Var(name) => !generics.contains(name),
            crate::surface::TermKind::App { function, arguments } => {
                matches!(&*function.kind, crate::surface::TermKind::Var(_))
                    && arguments.iter().enumerate().all(|(index, argument)| {
                        matches!(&*argument.kind, crate::surface::TermKind::Var(name)
                            if generics.contains(name) && !arguments[..index].iter().any(|earlier| earlier.kind == argument.kind))
                    })
            }
            crate::surface::TermKind::Product(arguments) => match arguments.as_slice() {
                [left, right] => matches!((&*left.kind, &*right.kind),
                    (crate::surface::TermKind::Var(a), crate::surface::TermKind::Var(b))
                    if a != b && generics.contains(a) && generics.contains(b)),
                _ => false,
            },
            _ => false,
        }
    }
    fn extended(stmts: &[Stmt]) -> bool {
        stmts.iter().any(|stmt| match stmt {
            Stmt::Class(class) => {
                class.parameters.len() > 1
                    || class
                        .parameters
                        .first()
                        .is_some_and(|(_, ty)| !type_parameter(ty))
                    || class.methods.iter().any(|method| {
                        method
                            .generic_parameters()
                            .iter()
                            .any(|(_, ty)| !type_parameter(ty))
                    })
            }
            Stmt::Instance(instance) => {
                !instance.arguments.is_empty()
                    || instance.generic_types.iter().any(|ty| !type_parameter(ty))
                    || !legacy_head(&instance.head, &instance.generics)
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => extended(items),
            _ => false,
        })
    }
    fn flatten<'a>(statements: &'a [Stmt], out: &mut Vec<&'a Stmt>) {
        for statement in statements {
            match statement {
                Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => flatten(items, out),
                _ => out.push(statement),
            }
        }
    }
    let mut statements = Vec::new();
    for (_, source) in &sources {
        flatten(source, &mut statements);
    }
    let mut selected: HashSet<Name> = checked
        .class_members
        .iter()
        .filter_map(|(name, class)| {
            checked
                .signatures
                .get(name)
                .is_some_and(|signature| signature.result == check::Role::Type)
                .then(|| class.clone())
        })
        .collect();
    let mut nodes = HashSet::new();
    let mut class_names = HashSet::new();
    for statement in &statements {
        match statement {
            Stmt::Class(class) => {
                nodes.insert(class.name.clone());
                class_names.insert(class.name.clone());
                // The legacy class printer erases method-local binders.
                // Keep polymorphic fields in the kernel-checked dictionary
                // representation, but do not select native-only classes.
                let checked_polymorphic = checked.classes.contains(&class.name)
                    && class
                        .methods
                        .iter()
                        .any(|method| !method.generics.is_empty());
                if extended(std::slice::from_ref(*statement)) || checked_polymorphic {
                    selected.insert(class.name.clone());
                }
            }
            Stmt::Instance(instance) => {
                if extended(std::slice::from_ref(*statement)) {
                    selected.insert(instance.class.clone());
                }
            }
            Stmt::Fn(function) => {
                nodes.insert(function.name.clone());
            }
            _ => {}
        }
    }
    if selected.is_empty() {
        return Ok(sources);
    }
    // A compilation unit may also contain classes supported only by the
    // legacy Nib path. Switch the connected checked call/dictionary component,
    // not every class merely because one unrelated declaration is extended.
    // Dependencies of affected callers are needed too, but another caller of
    // a shared utility does not itself become affected.
    let mut edges: HashMap<Name, HashSet<Name>> = HashMap::new();
    for statement in statements {
        let owner = match statement {
            Stmt::Class(class) => &class.name,
            Stmt::Instance(instance) => &instance.class,
            Stmt::Fn(function) => &function.name,
            _ => continue,
        };
        let mut copy = (*statement).clone();
        crate::surface::references::statement(&mut copy, &mut |reference| {
            let target = checked.class_members.get(reference).unwrap_or(reference);
            if target != owner && nodes.contains(target) {
                edges
                    .entry(owner.clone())
                    .or_default()
                    .insert(target.clone());
            }
        });
    }
    let mut callers: HashMap<Name, HashSet<Name>> = HashMap::new();
    for (owner, targets) in &edges {
        for target in targets {
            callers
                .entry(target.clone())
                .or_default()
                .insert(owner.clone());
        }
    }
    fn reachable(start: &HashSet<Name>, edges: &HashMap<Name, HashSet<Name>>) -> HashSet<Name> {
        let mut found = start.clone();
        let mut pending: Vec<_> = found.iter().cloned().collect();
        while let Some(name) = pending.pop() {
            for next in edges.get(&name).into_iter().flatten() {
                if found.insert(next.clone()) {
                    pending.push(next.clone());
                }
            }
        }
        found
    }
    loop {
        let before = selected.len();
        let affected = reachable(&selected, &callers);
        let needed = reachable(&affected, &edges);
        selected.extend(needed.intersection(&class_names).cloned());
        if selected.len() == before {
            break;
        }
    }
    fn selected_expansion(source: &Stmt, selected: &HashSet<Name>) -> bool {
        match source {
            Stmt::Class(class) => selected.contains(&class.name),
            Stmt::Instance(instance) => selected.contains(&instance.class),
            Stmt::Fn(function) => function
                .where_
                .iter()
                .any(|constraint| selected.contains(&constraint.class)),
            _ => false,
        }
    }
    // Preserve the ownership check performed by the ordinary Nib class
    // expander before replacing the declarations with executable evidence.
    fn declarations(statements: &[Stmt], classes: &mut HashSet<Name>, types: &mut HashSet<Name>) {
        for statement in statements {
            match statement {
                Stmt::Class(class) => {
                    classes.insert(class.name.clone());
                }
                Stmt::Inductive(data) => {
                    types.insert(data.name.clone());
                }
                Stmt::Struct(data) | Stmt::Enum(data) => {
                    types.insert(data.name.clone());
                }
                Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                    declarations(items, classes, types)
                }
                _ => {}
            }
        }
    }
    fn local_head(term: &SurfaceTerm, types: &HashSet<Name>) -> bool {
        match &*term.kind {
            crate::surface::TermKind::Var(name) => types.contains(name),
            crate::surface::TermKind::App { function, .. } => local_head(function, types),
            _ => false,
        }
    }
    fn ownership(
        statements: &[Stmt],
        classes: &HashSet<Name>,
        types: &HashSet<Name>,
    ) -> Result<(), Message> {
        for statement in statements {
            match statement {
                Stmt::Instance(instance)
                    if !classes.contains(&instance.class)
                        && !std::iter::once(&instance.head)
                            .chain(&instance.arguments)
                            .any(|head| local_head(head, types)) =>
                {
                    return Err(msg!(
                        "tauto-instance-outside-tote",
                        class = instance.class.to_string()
                    ));
                }
                Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                    ownership(items, classes, types)?
                }
                _ => {}
            }
        }
        Ok(())
    }
    let mut own_classes = HashSet::new();
    let mut own_types = HashSet::new();
    for (_, statements) in &sources {
        declarations(statements, &mut own_classes, &mut own_types);
    }
    for (file, statements) in &sources {
        if !file.is_standard() {
            ownership(statements, &own_classes, &own_types)?;
        }
    }
    // The legacy Nib class expander passes methods independently and marks
    // its source dictionary binders as erased. Here the checked method record
    // itself is executable evidence; law records remain proof-erased.
    for (source, expansion) in &checked.class_expansions {
        if !selected_expansion(source, &selected) {
            continue;
        }
        for statement in expansion {
            let Stmt::Fn(function) = statement else {
                continue;
            };
            let Some(signature) = checked.signatures.get_mut(&function.name) else {
                continue;
            };
            for (index, ty) in function.param_types.iter().enumerate() {
                let Some(ty) = ty else { continue };
                let head = match &*ty.kind {
                    crate::surface::TermKind::Var(name) => Some(name),
                    crate::surface::TermKind::App { function, .. } => match &*function.kind {
                        crate::surface::TermKind::Var(name) => Some(name),
                        _ => None,
                    },
                    _ => None,
                };
                if head.is_some_and(|name| checked.classes.contains(name)) {
                    if let Some(role) = signature.params.get_mut(function.generics.len() + index) {
                        *role = check::Role::Value;
                    }
                }
            }
        }
    }
    fn corresponds(source: &Stmt, expanded: &Stmt) -> bool {
        match (source, expanded) {
            (Stmt::Class(a), Stmt::Class(b)) => a.name == b.name,
            (Stmt::Instance(a), Stmt::Instance(b)) => a.span == b.span && a.class == b.class,
            (Stmt::Fn(a), Stmt::Fn(b)) => a.name == b.name,
            _ => false,
        }
    }
    fn lower(statements: Vec<Stmt>, checked: &Checked, selected: &HashSet<Name>) -> Vec<Stmt> {
        let mut out = Vec::new();
        for statement in statements {
            match statement {
                Stmt::Mutual { items, span } => out.push(Stmt::Mutual {
                    items: lower(items, checked, selected),
                    span,
                }),
                Stmt::Module { .. } => out.push(statement),
                Stmt::Fn(ref f) if checked.runtime.contains(&f.name) => out.push(statement),
                _ => {
                    // An empty capture records a skipped/unsupported class
                    // pass, not a replacement by no declarations. Preserve
                    // that source for the legacy path and its diagnostics.
                    if let Some((_, expansion)) =
                        checked.class_expansions.iter().find(|(source, expansion)| {
                            !expansion.is_empty()
                                && selected_expansion(source, selected)
                                && corresponds(&statement, source)
                        })
                    {
                        out.extend(expansion.iter().cloned());
                    } else {
                        out.push(statement);
                    }
                }
            }
        }
        out
    }
    Ok(sources
        .into_iter()
        .map(|(file, stmts)| (file, lower(stmts, checked, &selected)))
        .collect())
}

/// `sources` with the declarations a decidable equality generated written right after the
/// family that lists them, so that extraction reaches them as it reaches what is written.
fn with_derived(
    sources: Vec<(crate::program::SourceFile, Vec<Stmt>)>,
    derived: &[(Name, Vec<Stmt>)],
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

/// The verdicts of a statement that [`localize_entries`] keeps, as the kernel gave them.
pub fn kept_entries(loaded: &Loaded, entries: &mut Vec<Entry>) {
    entries.retain(|e| keeps_entry(loaded, e));
}

/// [`localize_entries`] of verdicts already kept ([`kept_entries`]), with the expansions
/// `loaded` has now: for the verdicts of a statement that moved while each expansion its
/// messages tell a place of was made again.
pub fn localize_kept(loaded: &Loaded, file: usize, entries: &mut [Entry]) {
    for e in entries {
        localize(loaded, &loaded.files[file], &mut e.verdict);
    }
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
    pub fn new(proof_cache: bool) -> Result<Self, Message> {
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

    /// Declare statement `index` of file `file` of `kernel`, with the names
    /// its sugar refers to as `check_file` gives them.
    pub fn declare_from(
        &mut self,
        kernel: &KernelStatements,
        file: usize,
        index: usize,
    ) -> Declared {
        for (spelling, reference) in &kernel.aliases[file] {
            self.inner.source_alias(spelling, reference);
        }
        self.inner.declare(&kernel.files[file][index])
    }
}

/// `expr` in normal form after the declarations of `path` and what it
/// imports, and its type, as `tauto eval` shows them.
/// A value of `Text` is also shown as the characters its bytes spell.
pub fn eval_file(
    path: &std::path::Path,
    expr: &str,
) -> Result<(String, String, Option<String>), Message> {
    let mut kernel = Kernel::new();
    check::declare_prelude(&mut kernel)?;
    kernel.use_cache();
    let loaded = crate::program::load_with_text_in(path, None)?;
    declare_loaded(&mut kernel, &loaded)?;
    let term = crate::surface::parse_expr_at(expr, 0)
        .map_err(|e| msg!("tauto-not-a-term", expr = expr, error = e))?;
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
    if !crate::bindings::is_library(&f, "Text::Mk") {
        return None;
    }
    let mut out = Vec::new();
    loop {
        match call(&list)? {
            (n, a) if crate::bindings::is_library(&n, "Nil") && a.is_empty() => return Some(out),
            (c, a) if crate::bindings::is_library(&c, "Cons") && a.len() == 2 => {
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
