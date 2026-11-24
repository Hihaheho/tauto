//! Reading, expanding and checking source files.

use crate::program::Standard as _;
use crate::surface::Name;
use tauto_surface::identity::Detach as _;
mod runtime;
pub(crate) use runtime::prefix_families;
#[cfg(test)]
mod side_by_side_tests;
mod term_generics;

use crate::program::Loaded;
use crate::surface::{Program, Stmt, SurfaceTerm};
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use tauto_kernel::check::{self, *};
use tauto_message::{Message, msg};
use tauto_parol::Span;
use tauto_parse::parse_program_unresolved_at;

pub fn parse_program(source: &str) -> Result<Program, Message> {
    tauto_parse::install();
    let program = parse_program_at(source, 0)?;
    let mut program = crate::types::expand_classes(program, 1 << 30);
    tauto_surface::resolve::Resolver::default().statements(&mut program.stmts);
    Ok(program)
}

/// Parses a whole program whose spans start at `base`.
pub fn parse_program_at(source: &str, base: u32) -> Result<Program, Message> {
    tauto_parse::install();
    expand_program(parse_program_unresolved_at(source, base)?, true)
}

/// [`parse_program`] of the prelude itself, whose names are its own.
pub fn parse_prelude(source: &str) -> Result<Program, Message> {
    tauto_parse::install();
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
    Ok(crate::types::expand_library(program, 1 << 30))
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
    tauto_parse::install();
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
        let mut qualified =
            crate::surface::qualify::files_before_macros(&mut files, &modules, None, None, None).0;
        qualified.extend(crate::surface::qualify::written_pairs(&files));
        qualified
    } else {
        crate::surface::qualify::record_bases(&mut files)
    };
    // The prelude's own declarations are the library's designated
    // references (`library_definition_bindings`) in the macros' resolver
    // too: otherwise a declaration a macro pass resolves (an enum's
    // constructors) takes fresh identities that the references to it, read
    // later with the library's, do not match.
    let library = (!qualify).then(|| {
        tauto_surface::resolve::Resolver::new(tauto_surface::bindings::library_definition_bindings())
    });
    let mut out = crate::macros::expand::expand_files_resuming_bound(
        files,
        &crate::macros::Options::default(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        None,
        None,
        library,
        Vec::new(),
    )
    .0;
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
    tauto_parse::install();
    // The kernel expands the classes of a program itself (`check/classes.rs`),
    // as it does for a file; the types pass's class expansion of
    // `parse_program` is for that pass, and a theorem calling a law of its
    // `where` class does not survive it. Coercions and indexed effects are
    // still expanded.
    let mut program = parse_program_at(source, 0)?;
    crate::types::expand_coercions(&mut program, &mut []);
    crate::types::indices::expand_indices(&mut program, &mut [], &[], false);
    tauto_surface::resolve::Resolver::default().statements(&mut program.stmts);
    if program
        .stmts
        .iter()
        .any(|s| matches!(s, Stmt::Import { .. }))
    {
        return Err(msg!("tauto-imports-need-path"));
    }
    // Its `inductive struct`s and `inductive enum`s are families, as a
    // file's are (`runtime::as_families`).
    program.stmts = runtime::prefix_families(&program.stmts);
    let mut kernel = Kernel::new();
    check::declare_prelude(&mut kernel)?;
    Ok(kernel.declare_program(&program))
}

pub fn check_types(source: &str) -> Result<crate::types::TypeReport, Message> {
    tauto_parse::install();
    let program = parse_program(source)?;
    Ok(crate::types::check_program(&program))
}

pub fn check_rows(source: &str) -> Result<crate::rows::RowReport, Message> {
    tauto_parse::install();
    let program = parse_program(source)?;
    Ok(crate::rows::check_program_rows(&program))
}

pub fn check_lin(source: &str) -> Result<Vec<crate::lin::LinError>, Message> {
    tauto_parse::install();
    Ok(crate::lin::check_lin_program(&parse_program(source)?)?)
}

/// Checks a file and, first, every file it imports (once each, relative to
/// the importing file). Declarations are told apart by their full names
/// (`surface::qualify`).
pub fn check_file(path: &std::path::Path) -> Result<Vec<FileEntry>, Message> {
    tauto_parse::install();
    check_file_with(path, None)
}

/// [`check_file`] with the text of `path` itself given instead of read: a
/// candidate edit is checked without touching the file. Its imports are
/// still read relative to `path`.
pub fn check_file_with(
    path: &std::path::Path,
    text: Option<&str>,
) -> Result<Vec<FileEntry>, Message> {
    tauto_parse::install();
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
    tauto_parse::install();
    check_file_lib(path, text).map(|(entries, expansions, _)| (entries, expansions))
}

/// [`check_file_full`] and the constants known at the end, by name.
pub fn check_file_lib(
    path: &std::path::Path,
    text: Option<&str>,
) -> Result<(Vec<FileEntry>, Vec<ExpansionInfo>, Vec<LibEntry>), Message> {
    tauto_parse::install();
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
    tauto_parse::install();
    let given = text.and_then(|t| Some((crate::program::canonicalize(path).ok()?, t.to_string())));
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
    tauto_parse::install();
    let (entries, expansions, library, timings, _) = check_file_sourced_with_names(path, source)?;
    Ok((entries, expansions, library, timings))
}

pub(crate) type SourceNames =
    std::collections::BTreeMap<std::path::PathBuf, tauto_parse::source_names::SourceNames>;

/// What [`check_file_timed_with_names`] gives: the entries, the macro runs,
/// the library, the timings and the names of the sources, and, when it was
/// asked for and the files are all source files, what the kernel's check
/// gives extraction ([`check_files_for_extraction`] of the file).
pub(crate) type FileCheck = (
    Vec<FileEntry>,
    Vec<ExpansionInfo>,
    Vec<LibEntry>,
    Vec<Timing>,
    SourceNames,
    Option<ExtractionInput>,
);

/// Checks `path` as [`check_file_timed`] does. With `for_extraction` and no
/// `text`, the same check also gives what extracting the file's program
/// takes, as [`check_files_for_extraction`] of `[path]` would give it: `tauto
/// check` reads that program for its Nib errors, and checking the file and
/// what it reads a second time for it doubled the time of the check.
pub(crate) fn check_file_timed_with_names(
    path: &std::path::Path,
    text: Option<&str>,
    for_extraction: bool,
) -> Result<FileCheck, Message> {
    let given =
        text.and_then(|text| Some((crate::program::canonicalize(path).ok()?, text.to_string())));
    check_file_sourced_in(
        path,
        &|path| match &given {
            Some((own, text)) if own == path => Some(Ok(text.clone())),
            _ => None,
        },
        for_extraction && text.is_none(),
    )
}

/// What extracting the program of `path` takes, as
/// [`check_files_for_extraction`] of `[path]` gives it, with the text of some
/// files given by `source`. Extraction says what in the check fails.
pub(crate) fn check_file_for_extraction_sourced(
    path: &std::path::Path,
    source: &crate::program::Source<'_>,
) -> Result<ExtractionInput, Message> {
    let (_, _, _, _, _, input) = check_file_sourced_in(path, source, true)?;
    // No input only when a file read is not a source file.
    input.ok_or_else(|| {
        msg!(
            "tauto-tote-source-extension",
            file = path.display().to_string()
        )
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
    let (entries, expansions, library, timings, names, _) =
        check_file_sourced_in(path, source, false)?;
    Ok((entries, expansions, library, timings, names))
}

pub(crate) fn check_file_sourced_in(
    path: &std::path::Path,
    source: &crate::program::Source<'_>,
    for_extraction: bool,
) -> Result<FileCheck, Message> {
    tauto_parse::install();
    let mut kernel = Kernel::new();
    let prelude_names = check::declare_prelude(&mut kernel)?;
    if for_extraction {
        kernel.record_ctor_sites();
    }
    kernel.use_cache();
    let timeout = std::env::var("TAUTO_TIMEOUT")
        .ok()
        .and_then(|s| s.parse::<f64>().ok())
        .filter(|s| s.is_finite() && *s > 0.0)
        .map(std::time::Duration::from_secs_f64);
    kernel.set_timeout(timeout);
    let mut loaded = crate::program::load_with_source_in(path, source)?;
    let expansions = expansion_infos_of(&loaded);
    // Extraction reads the statements as the kernel was given them, classes
    // as written (`check_files_for_extraction`); a Nib file is not extracted.
    let for_extraction = for_extraction
        && loaded
            .files
            .iter()
            .all(|f| crate::program::is_source_file(&f.path));
    let sources: Option<Vec<_>> = for_extraction.then(|| {
        loaded
            .files
            .iter()
            .cloned()
            .zip(loaded.kernel_files.clone())
            .collect()
    });
    // A program's functions that only run, such as one calling the
    // prelude's `concat`, are taken out as `run` takes them out, so that
    // `check` and `run` agree on what the kernel is given.
    let mut fns_of = Vec::new();
    for stmts in &loaded.per_file {
        let mut fns = Vec::new();
        fn_names(stmts, &mut fns);
        fns_of.push(fns);
    }
    let (runtime, effectful, why) = if for_extraction {
        runtime::separate(&mut loaded)?
    } else {
        let (runtime, why) = for_kernel(&mut loaded)?;
        (runtime, HashSet::new(), why)
    };
    let mut out = declare_loaded(&mut kernel, &loaded)?;
    runtime::explain_undefined(&mut out, &why);
    let declared = for_extraction.then(|| out.clone());
    let seen: HashSet<Name> = out.iter().map(|e| e.entry.name.clone()).collect();
    for (file, fns) in loaded.files.iter().zip(fns_of) {
        for name in fns {
            // A function the compiler made (named with `@`, as the fuel of a
            // recursive type's `Debug`) is no declaration of the file.
            if runtime.contains(&name)
                && !seen.contains(&name)
                && !name.as_str().starts_with("debug@fuel@")
            {
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
    fail_row_holes(&mut out, &loaded);
    let library = kernel.library();
    let timings = kernel.timings().to_vec();
    let names = loaded.source_names();
    let input = match (sources, declared) {
        (Some(sources), Some(declared)) => Some(extraction_input(
            kernel,
            prelude_names,
            loaded,
            sources,
            declared,
            (runtime, effectful, why),
        )?),
        _ => None,
    };
    Ok((out, expansions, library, timings, names, input))
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

/// A function written `fn f(): T !?` leaves its row to be written: that is an error of its own
/// (`tauto check` exits 1, and the program does not run). `tauto check --fix` writes the row its
/// body performs in place of `!?` (the empty row takes the `!?` away), and the note of the error
/// says which row that is. A function whose row cannot be found, or that calls itself or a later
/// `!?`, gets the error without that fix: its row is written by hand. The kernel does not see
/// rows, so this is read from the declarations; a function the kernel set apart to run as
/// written fails all the same.
pub(crate) fn fail_row_holes(out: &mut Vec<FileEntry>, loaded: &crate::program::Loaded) {
    fn collect(stmts: &[Stmt], found: &mut HashMap<Name, Span>) {
        for s in stmts {
            match s {
                Stmt::Fn(f) => {
                    if let Some(at) = f.row_hole {
                        found.insert(f.name.clone(), at);
                    }
                }
                Stmt::Mutual { items, .. } => collect(items, found),
                _ => {}
            }
        }
    }
    let mut holes = HashMap::new();
    collect(&loaded.program.stmts, &mut holes);
    for stmts in &loaded.per_file {
        collect(stmts, &mut holes);
    }
    if holes.is_empty() {
        return;
    }
    let types = crate::types::check_program(&loaded.program_with_imports());
    let rows = loaded.check_rows_with_types(crate::rows::Target::Rust, &types);
    // A function set apart to run as written has no entry of the kernel's.
    for (name, at) in &holes {
        if out.iter().any(|e| &e.entry.name == name) {
            continue;
        }
        if let Some(file) = loaded.files.iter().rev().find(|f| f.base <= at.start) {
            out.push(FileEntry {
                file: crate::program::canonical_path(&file.path),
                entry: check::Entry {
                    name: name.clone(),
                    verdict: Verdict::Skipped(msg!("tauto-skipped-runs")),
                },
            });
        }
    }
    // The edit that writes the row of each `!?` function: the file it is in, the place in that
    // file's text, what to write there, and whether the function is in a cycle (it calls itself
    // or a later `!?` function: its row is found as the fixed point the rows check settles on).
    struct Candidate {
        file: usize,
        start: usize,
        stop: usize,
        text: String,
        title: String,
        cycle: bool,
    }
    let mut candidates: HashMap<Name, Candidate> = HashMap::new();
    for (name, &at) in &holes {
        let Some(file) = loaded.files.iter().rposition(|f| f.base <= at.start) else {
            continue;
        };
        let base = loaded.files[file].base;
        let text = &loaded.files[file].text;
        let Some(written) = rows
            .declarations
            .iter()
            .find(|f| &f.name == name)
            .and_then(|f| rows.written_row(&f.inferred))
        else {
            continue;
        };
        let mut start = (at.start - base) as usize;
        let stop = (at.end - base) as usize;
        let (new_text, title) = if written.is_empty() {
            // `T !?` is `T`: the space before goes with it.
            while start > 0 && text[..start].ends_with([' ', '\t']) {
                start -= 1;
            }
            (String::new(), msg!("tauto-row-hole-fix-empty").to_string())
        } else {
            (
                format!("! {written}"),
                msg!("tauto-row-hole-fix", row = written.as_str()).to_string(),
            )
        };
        candidates.insert(
            name.clone(),
            Candidate {
                file,
                start,
                stop,
                text: new_text,
                title,
                cycle: rows.row_hole_cycles.contains(name),
            },
        );
    }
    // The row of a function in a cycle is a guess at a fixed point: it stays only when the
    // program with every row written passes the rows check as it is.
    if candidates.values().any(|c| c.cycle) && {
        let edits: Vec<(usize, usize, usize, String)> = candidates
            .values()
            .map(|c| (c.file, c.start, c.stop, c.text.clone()))
            .collect();
        !rows_pass_with(loaded, &rows, &edits)
    } {
        candidates.retain(|_, c| !c.cycle);
    }
    for e in out.iter_mut() {
        let Some(&at) = holes.get(&e.entry.name) else {
            continue;
        };
        if matches!(e.entry.verdict, Verdict::Failed(_)) {
            continue;
        }
        let Some(file) = loaded
            .files
            .iter()
            .find(|f| crate::program::canonical_path(&f.path) == e.file)
        else {
            continue;
        };
        let name = e.entry.name.to_string();
        let mut d = Diagnostic::new(msg!("rows-row-hole", name = name.as_str()), Some(at));
        match candidates.get(&e.entry.name) {
            Some(c) if loaded.files[c.file].base == file.base => {
                d.fix = Some(crate::check::Fix {
                    title: c.title.clone(),
                    span: Span::new(file.base + c.start as u32, file.base + c.stop as u32),
                    text: c.text.clone(),
                });
            }
            _ => d.help = Some(msg!("tauto-row-hole-by-hand")),
        }
        let mut verdict = Verdict::Failed(d);
        localize(loaded, file, &mut verdict);
        e.entry.verdict = verdict;
    }
}

/// Whether the rows check of `loaded` with `edits` made in the texts of its files (file, start,
/// end, what to write) finds nothing it did not find before, `baseline` being what it found:
/// the errors of `!?` aside, which the edits take away.
fn rows_pass_with(
    loaded: &crate::program::Loaded,
    baseline: &crate::rows::RowReport,
    edits: &[(usize, usize, usize, String)],
) -> bool {
    let Some(entry) = loaded.files.last().map(|f| f.path.clone()) else {
        return false;
    };
    let mut texts: std::collections::BTreeMap<PathBuf, String> = std::collections::BTreeMap::new();
    for (i, f) in loaded.files.iter().enumerate() {
        let mut mine: Vec<&(usize, usize, usize, String)> =
            edits.iter().filter(|e| e.0 == i).collect();
        if mine.is_empty() {
            continue;
        }
        mine.sort_by_key(|e| std::cmp::Reverse(e.1));
        let mut text = f.text.clone();
        for (_, start, stop, with) in mine {
            if *stop > text.len() || !text.is_char_boundary(*start) || !text.is_char_boundary(*stop)
            {
                return false;
            }
            text.replace_range(*start..*stop, with);
        }
        texts.insert(crate::program::canonical_path(&f.path), text);
    }
    let source = |p: &Path| {
        texts
            .get(&crate::program::canonical_path(p))
            .map(|t| Ok(t.clone()))
    };
    let Ok(patched) = crate::program::load_with_source_in(&entry, &source) else {
        return false;
    };
    let types = crate::types::check_program(&patched.program_with_imports());
    let rows = patched.check_rows_with_types(crate::rows::Target::Rust, &types);
    let mut had: Vec<String> = baseline
        .errors
        .iter()
        .filter(|e| e.message.id.to_string() != "rows-row-hole")
        .map(|e| e.message.to_string())
        .collect();
    rows.errors.iter().all(|e| {
        let text = e.message.to_string();
        match had.iter().position(|h| *h == text) {
            Some(i) => {
                had.swap_remove(i);
                true
            }
            None => false,
        }
    })
}

/// Checks `path` without the proof cache, and gives the term each body
/// elaborated to: implicit arguments, instances and motives filled in, macros
/// expanded. What the kernel checks, not what was written.
pub fn elaborate_file(
    path: &std::path::Path,
) -> Result<(Vec<FileEntry>, Vec<(Name, SurfaceTerm)>), Message> {
    tauto_parse::install();
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
    tauto_parse::install();
    loaded
        .files
        .iter()
        .map(|f| crate::manifest::time_limit(&f.path))
        .collect()
}

/// How many files may be declared at once: `TAUTO_JOBS`, or the machine's
/// cores. With 1, every file is declared in turn on one kernel.
fn jobs() -> usize {
    std::env::var("TAUTO_JOBS")
        .ok()
        .and_then(|j| j.parse().ok())
        .filter(|j| *j > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()))
}

/// The level of each file of `loaded`: one more than the highest of the
/// files it imports (a file outside the standard library imports every file
/// of the library read), 0 for a file that imports none of them. None when the
/// files cannot be declared side by side: they were read without imports, or
/// a file imports one read after it.
fn levels(loaded: &crate::program::Loaded) -> Option<(Vec<usize>, Vec<Vec<usize>>)> {
    let n = loaded.files.len();
    if loaded.imports.len() != n {
        return None;
    }
    let at: HashMap<PathBuf, usize> = loaded
        .files
        .iter()
        .enumerate()
        .map(|(i, f)| (crate::program::canonical_path(&f.path), i))
        .collect();
    // A file outside the standard library names its types (`Text`, `U64`)
    // without importing the files that declare them, so it waits for every
    // file of the library that was read; those are read first.
    let std_root = Path::new(crate::stdlib::ROOT);
    let library: Vec<PathBuf> = loaded
        .files
        .iter()
        .filter(|f| f.path.starts_with(std_root))
        .map(|f| f.path.clone())
        .collect();
    let mut level = vec![0usize; n];
    let mut imports = vec![Vec::new(); n];
    for i in 0..n {
        let mut l = 0;
        let implicit = if loaded.files[i].path.starts_with(std_root) {
            &[][..]
        } else {
            &library[..]
        };
        for p in loaded.imports[i].iter().chain(implicit) {
            match at.get(&crate::program::canonical_path(p)) {
                Some(&d) if d >= i => return None,
                Some(&d) => {
                    l = l.max(level[d] + 1);
                    imports[i].push(d);
                }
                None => {}
            }
        }
        level[i] = l;
    }
    Some((level, imports))
}

pub(crate) fn inference_root(path: &Path) -> PathBuf {
    let std_root = Path::new(crate::stdlib::ROOT);
    let path = crate::program::canonical_path(path);
    if path.starts_with(crate::program::canonical_path(std_root)) {
        return crate::program::canonical_path(std_root);
    }
    path.ancestors()
        .skip(1)
        .find(|dir| dir.join("Tauto.eure").is_file())
        .map_or_else(|| path.clone(), Path::to_path_buf)
}

/// Whether an [`inference_root`] is the standard library's: the one tauto
/// comes with, or the source of the tote named `std`, which reads its own
/// files ([`crate::stdlib::import_target`]) and owns the prelude's types alike.
pub(crate) fn is_std_root(root: &Path) -> bool {
    *root == crate::program::canonical_path(Path::new(crate::stdlib::ROOT))
        || (root.join("Tauto.eure").is_file()
            && crate::manifest::read(root).is_ok_and(|m| {
                m.package.name == tauto_surface::surface::qualify::STD_ROOT
            }))
}

/// The types the prelude declares, by their names.
fn prelude_types() -> &'static HashSet<String> {
    static TYPES: std::sync::OnceLock<HashSet<String>> = std::sync::OnceLock::new();
    TYPES.get_or_init(|| {
        let mut types = HashSet::new();
        for (_, text) in crate::nibstd::PRELUDE_FILES {
            if let Ok(program) = parse_program_unresolved_at(text, 0) {
                let mut names = HashSet::new();
                declared_types(&program.stmts, &mut names);
                types.extend(names.iter().map(|n| n.as_str().to_string()));
            }
        }
        types
    })
}

/// The standard library owns the types of its prelude: it ships them, so its
/// instances may be inferred from them (`for` over a `List`). Adds to `owners`
/// the references to those types that `stmts` hold.
pub(crate) fn own_prelude_types(stmts: &[Stmt], owners: &mut HashSet<Name>) {
    let types = prelude_types();
    for stmt in stmts {
        let mut stmt = stmt.clone();
        tauto_surface::surface::walk::stmt(&mut stmt, &mut |t| {
            if let crate::surface::TermKind::Var(n) = &*t.kind
                && matches!(n, Name::Global(_))
                && types.contains(n.as_str())
            {
                owners.insert(n.clone());
            }
        });
    }
}

pub(crate) fn declared_types(stmts: &[Stmt], into: &mut HashSet<Name>) {
    for stmt in stmts {
        match stmt {
            Stmt::Inductive(decl) => {
                into.insert(decl.name.clone());
            }
            Stmt::Struct(decl) | Stmt::Enum(decl) => {
                into.insert(decl.name.clone());
            }
            Stmt::Mutual { items, .. } => declared_types(items, into),
            _ => {}
        }
    }
}

pub(crate) fn has_inference(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Instance(instance) => instance.infer_from.is_some(),
        Stmt::Mutual { items, .. } => has_inference(items),
        _ => false,
    })
}

fn declare_file(
    kernel: &mut Kernel,
    loaded: &crate::program::Loaded,
    limits: &[std::time::Duration],
    index: usize,
) -> Vec<Entry> {
    let (file, stmts) = (&loaded.files[index], &loaded.kernel_files[index]);
    let inference_owners = if has_inference(stmts) {
        let current_root = inference_root(&file.path);
        let mut owners = HashSet::new();
        let in_std = is_std_root(&current_root);
        for (source, statements) in loaded.files.iter().zip(&loaded.kernel_files) {
            if inference_root(&source.path) == current_root {
                declared_types(statements, &mut owners);
                if in_std {
                    own_prelude_types(statements, &mut owners);
                }
            }
        }
        Some(owners)
    } else {
        None
    };
    for (spelling, reference) in standard_aliases(file, stmts) {
        kernel.source_alias(&spelling, &reference);
    }
    let shown = file.path.display().to_string();
    kernel.set_file_limit(Some((&shown, limits[index])));
    let program = Program {
        stmts: stmts.clone(),
        errors: Vec::new(),
    };
    let started = tauto_kernel::clock::Instant::now();
    let progress = Progress::get();
    if progress.each {
        eprintln!(
            "{}",
            msg!("tauto-check-progress-file", file = shown.as_str())
        );
    }
    kernel.set_inference_owners(inference_owners);
    let entries = kernel.declare_program(&program);
    kernel.set_inference_owners(None);
    kernel.set_file_limit(None);
    let took = started.elapsed();
    if progress.each || took >= SLOW_FILE {
        eprintln!(
            "{}",
            msg!(
                "tauto-check-progress-took",
                file = shown.as_str(),
                seconds = format!("{:.1}", took.as_secs_f64())
            )
        );
    }
    entries
}

/// A file whose declarations take this long is named on stderr as it is done,
/// so that a long check is not silent until the end.
const SLOW_FILE: std::time::Duration = std::time::Duration::from_secs(5);

/// What `check` says on stderr while it runs: with `each` (stderr is a
/// terminal, or `TAUTO_PROGRESS=1`), every file as it starts and ends;
/// otherwise only the files that took [`SLOW_FILE`] or longer.
#[derive(Clone, Copy)]
struct Progress {
    each: bool,
}

impl Progress {
    fn get() -> Self {
        use std::io::IsTerminal;
        let each = match std::env::var("TAUTO_PROGRESS").as_deref() {
            Ok("1") => true,
            Ok("0") => false,
            _ => std::io::stderr().is_terminal(),
        };
        Progress { each }
    }
}

/// Declares the files of `loaded` on copies of `kernel`, `jobs` at a time,
/// and takes what each declared into `kernel`. None, and `kernel` as it was,
/// when a file fails or writes what a file it does not
/// import writes too (a name both declare, `Kernel::absorb`): the files are then declared in turn, so that what is reported
/// is what declaring them in turn reports.
///
/// A file is declared as soon as the files it imports are taken in, on a
/// copy of `kernel` as it is then: what other files are in it depends on how
/// fast they were declared, which changes nothing a file's declarations
/// check, since a proof's key names only what the proof reaches
/// (`tauto_kernel` cache). The copies are made and taken in on this thread,
/// and what the files recorded is added in the files' order.
fn declare_scheduled(
    kernel: &mut Kernel,
    loaded: &crate::program::Loaded,
    limits: &[std::time::Duration],
    jobs: usize,
) -> Option<Vec<Vec<Entry>>> {
    use std::sync::{Mutex, mpsc};
    let (_, imports) = levels(loaded)?;
    let n = loaded.files.len();
    // How many of its imports each file waits for, and the files that wait
    // for each.
    let mut waiting: Vec<usize> = vec![0; n];
    let mut waiters: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, ds) in imports.iter().enumerate() {
        let ds: std::collections::BTreeSet<usize> = ds.iter().copied().collect();
        waiting[i] = ds.len();
        for d in ds {
            waiters[d].push(i);
        }
    }
    let pristine = kernel.clone();
    type Job = (usize, std::sync::Arc<Kernel>);
    // None: declaring the file panicked; declaring in turn panics the same way.
    type Done = (
        usize,
        Option<(Kernel, tauto_kernel::check::ForkMark, Vec<Entry>)>,
    );
    let (job_tx, job_rx) = mpsc::channel::<Job>();
    let (done_tx, done_rx) = mpsc::channel::<Done>();
    let job_rx = Mutex::new(job_rx);
    let outcome = std::thread::scope(|scope| {
        for _ in 0..jobs {
            let (job_rx, done_tx) = (&job_rx, done_tx.clone());
            std::thread::Builder::new()
                .stack_size(256 << 20)
                .spawn_scoped(scope, move || {
                    loop {
                        let job = job_rx.lock().map(|rx| rx.recv());
                        let Ok(Ok((index, base))) = job else {
                            break;
                        };
                        let declared =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                let (mut copy, mut mark) = Kernel::fork_of(&base, index);
                                let entries = declare_file(&mut copy, loaded, limits, index);
                                copy.settle();
                                copy.subtract(&base, &mut mark);
                                (copy, mark, entries)
                            }));
                        drop(base);
                        if done_tx.send((index, declared.ok())).is_err() {
                            break;
                        }
                    }
                })
                .expect("a thread to declare files on");
        }
        drop(done_tx);
        let mut entries: Vec<Option<Vec<Entry>>> = vec![None; n];
        let mut logs: Vec<Option<tauto_kernel::check::Logs>> = (0..n).map(|_| None).collect();
        let mut clean = true;
        // The longest files first, so that they do not come last; the files
        // that became ready are sent together on one copy. A copy costs a
        // copy of the kernel's maps, so it is made only when a thread has
        // nothing left to take: until then the ready files wait, and more
        // join them.
        let send = |kernel: &mut Kernel, mut ready: Vec<usize>| {
            ready.sort_by_key(|&i| std::cmp::Reverse(loaded.files[i].text.len()));
            // The files' text literals are declared here, once, and not by
            // the copies, which would each declare the ones they share.
            for &i in &ready {
                kernel.declare_text_literals(&loaded.kernel_files[i]);
            }
            let base = std::sync::Arc::new(kernel.snapshot());
            ready
                .into_iter()
                .all(|i| job_tx.send((i, base.clone())).is_ok())
        };
        let mut ready: Vec<usize> = (0..n).filter(|&i| waiting[i] == 0).collect();
        let mut sent = ready.len();
        if !send(kernel, std::mem::take(&mut ready)) {
            clean = false;
        }
        let mut taken = 0;
        // The files that ran out of time beside others, to be declared
        // again with no other file being declared; and the one that is.
        let mut late: Vec<usize> = Vec::new();
        let mut retried: HashSet<usize> = HashSet::new();
        let mut alone: Option<usize> = None;
        while clean && taken < n {
            let Ok((index, done)) = done_rx.recv() else {
                clean = false;
                break;
            };
            let Some((copy, mark, declared)) = done else {
                clean = false;
                break;
            };
            if alone == Some(index) {
                alone = None;
            }
            // A file says what failed in its own entries, as it does in
            // turn: what a file declares depends only on the files it
            // imports, which are taken in before it is declared. The time a
            // file takes does not: beside other files, its thread's CPU time
            // grows with the cores they share. A file that ran out of time
            // is declared again once no other file is being declared, and
            // only one that runs out of time then too has every file
            // declared again in turn.
            if copy.gave_up() {
                if !retried.insert(index) {
                    clean = false;
                    break;
                }
                late.push(index);
                sent -= 1;
            } else if !copy.declared_states().is_empty() {
                // The file declared a state family the kernel lacked, as
                // other files may have: the family is declared once here,
                // and the file again on a copy that has it.
                if !kernel.declare_states(copy.declared_states()) {
                    clean = false;
                    break;
                }
                ready.push(index);
                sent -= 1;
            } else {
                entries[index] = Some(declared);
                let log = kernel.absorb(copy, mark);
                // Two files that do not import one another wrote the same
                // thing: which stands would depend on which was declared first.
                if !log.alone() {
                    clean = false;
                    break;
                }
                logs[index] = Some(log);
                taken += 1;
                for &w in &waiters[index] {
                    waiting[w] -= 1;
                    if waiting[w] == 0 {
                        ready.push(w);
                    }
                }
            }
            if alone.is_none() && !ready.is_empty() && sent - taken < jobs {
                sent += ready.len();
                if !send(kernel, std::mem::take(&mut ready)) {
                    clean = false;
                }
            }
            if alone.is_none() && sent == taken && ready.is_empty() {
                if let Some(index) = late.pop() {
                    alone = Some(index);
                    sent += 1;
                    if !send(kernel, vec![index]) {
                        clean = false;
                    }
                }
            }
        }
        drop(job_tx);
        // What is still being declared is waited for, so that no thread is
        // left running.
        while done_rx.recv().is_ok() {}
        if !clean {
            // Everything is declared again in turn: said, since it can take as long again.
            eprintln!("{}", msg!("tauto-check-progress-in-turn"));
            return None;
        }
        Some((entries, logs))
    });
    let restore = |kernel: &mut Kernel| *kernel = pristine.clone();
    let Some((entries, logs)) = outcome else {
        restore(kernel);
        return None;
    };
    let entries: Vec<Vec<Entry>> = entries.into_iter().map(Option::unwrap_or_default).collect();
    // A name declared by two files is reported by declaring them in turn.
    let mut names = std::collections::HashSet::new();
    if !entries
        .iter()
        .flatten()
        .all(|e| names.insert(e.name.clone()))
    {
        restore(kernel);
        return None;
    }
    for l in logs.into_iter().flatten() {
        kernel.append_logs(l);
    }
    Some(entries)
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
    let mut roots: HashMap<String, String> = HashMap::new();
    let jobs = jobs();
    let side = if jobs > 1 && loaded.files.len() > 1 {
        declare_scheduled(kernel, loaded, &limits, jobs)
    } else {
        None
    };
    let declared: Vec<Option<Vec<Entry>>> = match side {
        Some(entries) => entries.into_iter().map(Some).collect(),
        None => (0..loaded.files.len())
            .map(|index| {
                kernel.declare_text_literals(&loaded.kernel_files[index]);
                Some(declare_file(kernel, loaded, &limits, index))
            })
            .collect(),
    };
    for (index, entries) in declared.into_iter().enumerate() {
        let (file, stmts) = (&loaded.files[index], &loaded.kernel_files[index]);
        for entry in entries.unwrap_or_default() {
            // A call whose macro failed is reported where the macro was.
            if !keeps_entry(loaded, &entry) {
                continue;
            }
            let mut entry = entry;
            if !already_defined_elsewhere(loaded, index, stmts, &declared_in, &mut entry) {
                declared_in.entry(entry.name.clone()).or_insert(index);
            }
            localize(&loaded, file, &mut entry.verdict);
            // A recursion that is not structural fails whatever the types: a
            // function that may not terminate says so with `div`.
            if loaded.tentative.contains(&entry.name)
                && let Verdict::Failed(d) = &entry.verdict
                && !crate::said::says(&d.message, &["kernel-calls-itself"])
            {
                // What a declaration's own failure was, so that what uses it
                // names that and not only that it did not check.
                let why = match crate::said::ends_with(&d.message, &["kernel-uses-failed"])
                    .and_then(|m| crate::said::text_arg(m, "name"))
                    .and_then(|used| roots.get(used))
                {
                    Some(root) => msg!(
                        "tauto-uses-unchecked-root",
                        name = crate::said::ends_with(&d.message, &["kernel-uses-failed"])
                            .and_then(|m| crate::said::text_arg(m, "name"))
                            .unwrap_or_default(),
                        why = root.as_str()
                    )
                    .to_string(),
                    None => d.to_string(),
                };
                roots.insert(entry.name.to_string(), why.clone());
                entry.verdict = Verdict::Skipped(msg!("tauto-skipped-tentative", why = why));
            }
            out.push(FileEntry {
                file: crate::program::canonical_path(&file.path),
                entry,
            });
        }
    }
    kernel.set_file_limit(None);
    name_unchecked_roots(&roots, &mut out);
    attach_failures(loaded, &mut out);
    // A copy of a standard library file read by path next to the standard
    // library's own declares everything twice. That may still check, but
    // where it does not, the two copies fail where they meet (a `calc!` in
    // `std::nat` reads `add` from the wrong one): each failure says first
    // that the file is read twice.
    if let Some((path, module)) = std_read_twice(loaded) {
        for e in &mut out {
            // A declaration found twice already says which file is the copy.
            if let Verdict::Failed(d) = &mut e.entry.verdict
                && !crate::said::says(&d.message, ALREADY_DEFINED)
            {
                d.message = msg!(
                    "tauto-std-read-twice",
                    message = d.message.clone(),
                    path = path.as_str(),
                    module = module
                );
            }
        }
    }
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

/// A file read by path that is a copy of a standard library file the
/// program also reads as the standard library's.
fn std_read_twice(loaded: &crate::program::Loaded) -> Option<(String, &'static str)> {
    let own = |f: &crate::program::SourceFile| f.path.starts_with(crate::stdlib::ROOT);
    loaded.files.iter().filter(|f| !own(f)).find_map(|f| {
        let module = crate::stdlib::std_copy(&f.path, &f.text)?;
        loaded
            .files
            .iter()
            // The library's own file of that module, not one of the same name
            // in a directory of it (`prelude/std.taut` is not `std.taut`).
            .any(|g| {
                g.path
                    .strip_prefix(crate::stdlib::ROOT)
                    .is_ok_and(|rel| rel == Path::new(&format!("{module}.taut")))
            })
            .then(|| (f.path.display().to_string(), module))
    })
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
    failures_with_files(loaded)
        .into_iter()
        .map(|(entry, _)| entry)
        .collect()
}

/// A name written in a declaration that the name resolution rejects (one the
/// file does not import, a private or an ambiguous one) fails that declaration, so that `ok` of a declaration says it was checked
/// with the names it writes; every other failure of the macros and syntaxes
/// is an entry of its own, as [`macro_failures`] says.
/// A declaration that runs as written because its reading in proofs did not
/// check (a tentative one) is skipped, and what uses it fails with only
/// that it "did not check". Each such use says why the declaration did not
/// check.
fn name_unchecked_roots(roots: &HashMap<String, String>, out: &mut [FileEntry]) {
    for e in out.iter_mut() {
        let Verdict::Failed(d) = &mut e.entry.verdict else {
            continue;
        };
        let Some(m) = crate::said::ends_with(&d.message, crate::said::USES_FAILED) else {
            continue;
        };
        let Some(used) = crate::said::text_arg(m, "name").map(str::to_owned) else {
            continue;
        };
        let Some(why) = roots.get(&used) else {
            continue;
        };
        d.message = match m.get("message") {
            Some(tauto_message::Value::Message(rest)) => msg!(
                "tauto-uses-unchecked-root-then",
                name = used.as_str(),
                why = why.as_str(),
                message = (**rest).clone()
            ),
            _ => msg!(
                "tauto-uses-unchecked-root",
                name = used.as_str(),
                why = why.as_str()
            ),
        };
    }
}

fn attach_failures(loaded: &crate::program::Loaded, out: &mut Vec<FileEntry>) {
    let mut named = std::collections::HashSet::new();
    for (failure, file) in failures_with_files(loaded) {
        let Verdict::Failed(diagnostic) = &failure.entry.verdict else {
            out.push(failure);
            continue;
        };
        let owner = file
            .filter(|_| diagnostic.message.id.starts_with("surface-"))
            .and_then(|file| diagnostic.span.map(|span| (file, span)))
            .and_then(|(file, span)| declaration_at(loaded, file, span.start));
        let Some(name) = owner else {
            // An import the imported file does not declare for other files is
            // the cause of what is reported about the names it brings, so it
            // comes before them, after the other errors of the import lists.
            if diagnostic.message.id == "surface-import-listed-unknown" {
                let at = out
                    .iter()
                    .position(|e| {
                        matches!(&e.entry.verdict, Verdict::Failed(d)
                            if !d.message.id.starts_with("surface-import-"))
                    })
                    .unwrap_or(out.len());
                out.insert(at, failure);
            } else {
                out.push(failure);
            }
            continue;
        };
        // An incremental checker keeps the entries of declarations it did not
        // read again, under the names of the load that made them: the same
        // declaration is found by what it is called in its file.
        let at = out
            .iter()
            .position(|e| e.file == failure.file && e.entry.name == name)
            .or_else(|| {
                out.iter()
                    .position(|e| e.file == failure.file && e.entry.name.as_str() == name.as_str())
            });
        match at {
            // A name the file does not reach is reported before what the
            // kernel says of the declaration, which read it as defined; the
            // names after the first are further uses, as the kernel reports
            // them.
            Some(at) => match &mut out[at].entry.verdict {
                Verdict::Failed(first) if named.contains(&at) => {
                    first.also.push(diagnostic.clone())
                }
                Verdict::Failed(first) => {
                    named.insert(at);
                    let mut kernel = std::mem::replace(first, diagnostic.clone());
                    first.also = std::mem::take(&mut kernel.also);
                    first.also.push(kernel);
                }
                verdict => {
                    named.insert(at);
                    *verdict = failure.entry.verdict;
                }
            },
            None => out.push(FileEntry {
                file: failure.file,
                entry: Entry {
                    name,
                    verdict: failure.entry.verdict,
                },
            }),
        }
    }
}

/// The declaration of `loaded.files[file]` that the byte `at` of that file
/// (a place written there, not one a macro made) is in.
fn declaration_at(loaded: &crate::program::Loaded, file: usize, at: u32) -> Option<Name> {
    fn find(loaded: &crate::program::Loaded, file: usize, stmts: &[Stmt], at: u32) -> Option<Name> {
        stmts.iter().find_map(|s| {
            if let Stmt::Mutual { items, .. } = s
                && let Some(name) = find(loaded, file, items, at)
            {
                return Some(name);
            }
            let name = match s {
                Stmt::Fn(f) => &f.name,
                Stmt::Theorem(t) | Stmt::Def(t) => &t.name,
                _ => return None,
            };
            let span = stmt_span(loaded, file, s)?;
            (span.start <= at && at < span.end).then(|| name.clone())
        })
    }
    [loaded.kernel_files.get(file), loaded.per_file.get(file)]
        .into_iter()
        .flatten()
        .find_map(|stmts| find(loaded, file, stmts, at))
}

fn failures_with_files(loaded: &crate::program::Loaded) -> Vec<(FileEntry, Option<usize>)> {
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
        let index = loaded.files.iter().position(|f| f.base == file.base);
        out.push((
            FileEntry {
                file: crate::program::canonical_path(&file.path),
                entry: Entry {
                    name: "macro".into(),
                    verdict: Verdict::Failed(diagnostic),
                },
            },
            index,
        ));
    }
    out
}

/// A span of the program as a span of `file`: one made by a macro is where the
/// macro was written (or, if that is in another file, where it was called), and
/// the base of the file is taken off.
/// Where `name` is declared in the file at `path`, as `path:line:col`: what
/// a report about a declaration as a whole (one the kernel skipped, say)
/// points at, as a failure points at the term it is about.
pub(crate) fn declaration_place(
    loaded: &crate::program::Loaded,
    path: &std::path::Path,
    name: &Name,
) -> Option<String> {
    fn find(stmts: &[Stmt], name: &Name) -> Option<Span> {
        stmts.iter().find_map(|s| match s {
            Stmt::Fn(f) if &f.name == name => Some(f.span),
            Stmt::Theorem(t) | Stmt::Def(t) if &t.name == name => Some(t.span),
            Stmt::Mutual { items, .. } => find(items, name),
            _ => None,
        })
    }
    let path = crate::program::canonical_path(path);
    loaded.files.iter().enumerate().find_map(|(i, file)| {
        if crate::program::canonical_path(&file.path) != path {
            return None;
        }
        let sp = [loaded.kernel_files.get(i), loaded.per_file.get(i)]
            .into_iter()
            .flatten()
            .find_map(|stmts| find(stmts, name))?;
        let sp = local_span(loaded, file, sp);
        let (l, c) = crate::report::line_col(&file.text, sp.start as usize);
        Some(format!("{}:{l}:{c}", path.display()))
    })
}

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
    // Every span a verdict carries is a place in a file, or one an expansion
    // made and the span map says where it was written. One that is neither
    // would be shown at the end of the file; a build that checks asserts that
    // none is, so a pass that makes terms without registering them is found
    // by the tests, and a release build places it at the top of the file.
    let outside = at.saturating_sub(file.base) as usize > file.text.len();
    debug_assert!(
        !outside,
        "a span at byte {at} is in no file and no expansion made it"
    );
    if outside {
        return Span::new(0, 0);
    }
    let start = at.saturating_sub(file.base);
    let end = if moved {
        start
    } else {
        start + (sp.end - sp.start)
    };
    Span::new(start, end)
}

/// `message` of an error at `start`, with where it comes from said: each expansion it is in
/// (with the byte of the call, when the call is in the file whose base is `file_base`), and,
/// for a node a macro wrote itself (a `quote` of its own file), the place in the macro.
pub(crate) fn expansion_notes(
    loaded: &crate::program::Loaded,
    file_base: u32,
    start: u32,
    mut message: Message,
) -> Message {
    let mut at = start;
    while let Some((written, expansion)) = loaded.spans.origin(at) {
        if let Some(e) = loaded.expansions.iter().find(|e| e.id == expansion) {
            let mut call = e.call.start;
            while let Some((w, _)) = loaded.spans.origin(call) {
                call = w;
            }
            let prev = message.clone();
            message = match loaded.files.iter().rev().find(|f| f.base <= call) {
                Some(f) if f.base == file_base => msg!(
                    "tauto-in-expansion-at",
                    message = prev,
                    name = &e.macro_name,
                    byte = call - f.base
                ),
                _ => msg!("tauto-in-expansion", message = prev, name = &e.macro_name),
            };
        }
        at = written;
    }
    // A node the macro wrote itself (a `quote` of its own file):
    // the place in the macro, which the call's place does not say.
    if at != start
        && let Some(f) = loaded.files.iter().rev().find(|f| f.base <= at)
        && f.base != file_base
        && let Some(before) = f.text.get(..(at - f.base) as usize)
    {
        let line = before.matches('\n').count() + 1;
        let column = before.len() - before.rfind('\n').map_or(0, |i| i + 1) + 1;
        let file = f
            .path
            .file_name()
            .map_or(f.path.display(), |n| std::path::Path::new(n).display())
            .to_string();
        message = msg!(
            "tauto-written-in-macro-at",
            message = message.clone(),
            file = file,
            line = line as u64,
            column = column as u64
        );
    }
    message
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
                d.message = expansion_notes(loaded, file.base, sp.start, d.message.clone());
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
    tauto_parse::install();
    check_files_cached(roots, true)
}

/// [`check_files`], where a proof that was checked before is taken as
/// checked (`crates/tauto-kernel/src/check/cache.rs`) when `cached`; otherwise every proof is
/// checked again.
pub fn check_files_cached(roots: &[PathBuf], cached: bool) -> Result<Checked, Message> {
    tauto_parse::install();
    check_files_mode(roots, cached, false)
}

pub fn check_tote_files(roots: &[PathBuf], cached: bool) -> Result<Checked, Message> {
    tauto_parse::install();
    check_files_mode(roots, cached, true)
}

fn check_files_mode(roots: &[PathBuf], cached: bool, mixed: bool) -> Result<Checked, Message> {
    check_files_for_extraction(roots, None, cached, mixed).map(|input| input.checked)
}

/// The exact expanded source that was presented to the kernel, including
/// executable declarations before they are separated from the proof environment.
pub(crate) struct ExtractionInput {
    pub bindings: tauto_surface::resolve::Resolver,
    pub checked: Checked,
    pub runtime_reasons: HashMap<Name, tauto_message::Message>,
    pub sources: Vec<(crate::program::SourceFile, Vec<Stmt>)>,
    pub loaded: Loaded,
    /// What [`crate::extract`]'s `reachable` found for the roots it was asked about last: the
    /// extraction and the assembly of a tote ask the same of the same input.
    pub(crate) reachable: std::cell::RefCell<Option<(Vec<PathBuf>, HashSet<Name>)>>,
}

/// `entry` is the file whose top level runs; without it, the last file read.
pub(crate) fn check_files_for_extraction(
    roots: &[PathBuf],
    entry: Option<&Path>,
    cached: bool,
    mixed: bool,
) -> Result<ExtractionInput, Message> {
    let mut kernel = Kernel::new();
    let prelude_names = check::declare_prelude(&mut kernel)?;
    kernel.record_ctor_sites();
    if cached {
        kernel.use_cache();
    }
    let mut loaded = crate::program::load_roots_with_entry_in(roots, entry)?;
    crate::phases::mark("loaded");
    // The statements the kernel checks, classes as written: the extracted
    // functions follow the kernel's signatures, whose `where` records a
    // program expanded for Nib has already turned into parameters.
    let mut sources: Vec<_> = loaded
        .files
        .iter()
        .cloned()
        .zip(loaded.kernel_files.clone())
        .collect();
    crate::phases::mark("sources");
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
        // Every file is the kernel's, and its `inductive struct` and
        // `inductive enum` are families to it, as `tauto check` gives them.
        runtime::families_only(&mut loaded);
        (HashSet::new(), HashSet::new(), HashMap::new())
    };
    crate::phases::mark("separate");
    let mut out = declare_loaded(&mut kernel, &loaded)?;
    crate::phases::mark("declare");
    runtime::explain_undefined(&mut out, &why);
    fail_row_holes(&mut out, &loaded);
    extraction_input(
        kernel,
        prelude_names,
        loaded,
        sources,
        out,
        (runtime, effectful, why),
    )
}

/// What extraction takes from a kernel that has declared `loaded`: `sources`
/// are its statements as the kernel was given them, `out` the kernel's
/// entries, and `separated` what [`runtime::separate`] set apart.
fn extraction_input(
    mut kernel: Kernel,
    prelude_names: Vec<Name>,
    mut loaded: Loaded,
    mut sources: Vec<(crate::program::SourceFile, Vec<Stmt>)>,
    mut out: Vec<FileEntry>,
    separated: (HashSet<Name>, HashSet<Name>, runtime::Why),
) -> Result<ExtractionInput, Message> {
    let (mut runtime, effectful, why) = separated;
    let files = loaded
        .files
        .iter()
        .map(|f| crate::program::canonicalize(&f.path).unwrap_or_else(|_| f.path.clone()))
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
    crate::phases::mark("input_resolve");
    // A declaration that failed to check is reported as it failed. Reading the
    // native calls on top of it would put an error about a call the failure
    // left uninferable ahead of the failure itself.
    if !out
        .iter()
        .any(|entry| matches!(entry.entry.verdict, Verdict::Failed(_)))
    {
        term_generics::specialize(&mut kernel, &mut sources, &mut loaded, &runtime, &mut out)?;
    }
    crate::phases::mark("input_specialize");
    let bindings = kernel.binding_session();
    // A function whose signature the kernel reads but whose body it does not
    // (`kernel-body-executable`: a text literal where `Text` is not the
    // kernel's, say) is executable code: it runs as written, and so Nib
    // checks it. Left out, neither checker would read its body.
    // Each function with the declarations its body refers to: a function
    // that calls one found to run as written below runs as written too.
    let uses: HashMap<Name, Vec<Name>> = loaded
        .program
        .stmts
        .iter()
        .flat_map(|s| match s {
            Stmt::Mutual { items, .. } => items.iter().collect::<Vec<_>>(),
            s => vec![s],
        })
        .filter_map(|s| match s {
            Stmt::Fn(f) => Some((
                kernel.resolve_declaration(&f.name),
                crate::lin::free_vars(&f.body)
                    .iter()
                    .filter(|n| !f.params.contains(n) && !f.generics.contains(n))
                    .map(|n| kernel.resolve_declaration(n))
                    .collect(),
            )),
            _ => None,
        })
        .collect();
    crate::phases::mark("input_uses");
    let functions: HashSet<Name> = uses.keys().cloned().collect();
    let mut checked = check::checked_entries(kernel, files, out, prelude_names);
    crate::phases::mark("input_entries");
    for e in &checked.entries {
        let body_executable = matches!(&e.entry.verdict, Verdict::Skipped(reason)
            if reason.id == "kernel-body-executable")
            && functions.contains(&e.entry.name);
        if (effectful.contains(&e.entry.name) || body_executable)
            && matches!(e.entry.verdict, Verdict::Skipped(_))
        {
            runtime.insert(e.entry.name.clone());
            if let Verdict::Skipped(reason) = &e.entry.verdict {
                runtime_reasons
                    .entry(e.entry.name.clone())
                    .or_insert_with(|| reason.clone());
            }
        }
    }
    // Runtime code reaches its callers through the call graph: a function
    // the kernel skipped because it calls one that runs as written (one
    // with a `while` loop, say) runs as written too, as do its own callers.
    loop {
        let mut grew = false;
        for e in &checked.entries {
            if runtime.contains(&e.entry.name) || !matches!(e.entry.verdict, Verdict::Skipped(_)) {
                continue;
            }
            let Some(used) = uses
                .get(&e.entry.name)
                .and_then(|refs| refs.iter().filter(|n| runtime.contains(*n)).min())
            else {
                continue;
            };
            let reason = match runtime_reasons.get(used) {
                Some(w) => msg!(
                    "tauto-why-uses-because",
                    name = used.as_str(),
                    why = w.clone()
                ),
                None => msg!("tauto-why-uses", name = used.as_str()),
            };
            runtime_reasons
                .entry(e.entry.name.clone())
                .or_insert(reason);
            runtime.insert(e.entry.name.clone());
            grew = true;
        }
        if !grew {
            break;
        }
    }
    checked.runtime = runtime;
    crate::phases::mark("input_runtime");
    let sources = with_class_dictionaries(sources, &mut checked)?;
    crate::phases::mark("input_dictionaries");
    let mut sources = with_derived(sources, &checked.derived);
    // A `ghost fn` is read by the kernel and nothing more: extraction never sees it, so no
    // program holds it, and a call that reaches one is refused by name.
    fn without_ghosts(stmts: &mut Vec<Stmt>, ghosts: &mut HashSet<Name>) {
        stmts.retain_mut(|s| match s {
            Stmt::Fn(f) if f.ghost => {
                ghosts.insert(f.name.clone());
                false
            }
            Stmt::Mutual { items, .. } => {
                without_ghosts(items, ghosts);
                true
            }
            _ => true,
        });
    }
    for (_, statements) in &mut sources {
        without_ghosts(statements, &mut checked.ghosts);
    }
    without_ghosts(&mut loaded.program.stmts, &mut checked.ghosts);
    without_ghosts(&mut loaded.imported_top, &mut checked.ghosts);
    for statements in loaded.per_file.iter_mut().chain(&mut loaded.kernel_files) {
        without_ghosts(statements, &mut checked.ghosts);
    }
    for (_, statements) in &mut sources {
        crate::extract::selected_references(&checked, statements)?;
    }
    crate::phases::mark("input_selected");
    Ok(ExtractionInput {
        runtime_reasons,
        bindings,
        checked,
        sources,
        loaded,
        reachable: std::cell::RefCell::new(None),
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
                ..
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
            // A width family at a width (`UInt(64)`) is one type, as `u64` is.
            crate::surface::TermKind::App { function, arguments }
                if matches!(&*function.kind, crate::surface::TermKind::Var(_))
                    && arguments
                        .iter()
                        .all(|a| matches!(&*a.kind, crate::surface::TermKind::Nat(_))) =>
            {
                true
            }
            crate::surface::TermKind::App { function, arguments } => {
                matches!(&*function.kind, crate::surface::TermKind::Var(_))
                    && arguments.iter().enumerate().all(|(index, argument)| {
                        matches!(&*argument.kind, crate::surface::TermKind::Var(name)
                            if generics.contains(name) && !arguments[..index].iter().any(|earlier| earlier.kind == argument.kind))
                    })
            }
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
    let std = crate::extract::StdNames::new(&sources);
    let mut nodes = HashSet::new();
    let mut class_names = HashSet::new();
    for statement in &statements {
        match statement {
            Stmt::Class(class) => {
                nodes.insert(class.name.clone());
                class_names.insert(class.name.clone());
                // Polymorphic fields generally use the checked dictionary
                // representation. The standard key class has a Nib method
                // telescope and can use the executable class expander.
                let checked_polymorphic = checked.classes.contains(&class.name)
                    && !std.native_key_class(&class.name)
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
    tauto_parse::install();
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
    tauto_parse::install();
    entries.retain(|e| keeps_entry(loaded, e));
}

/// [`localize_entries`] of verdicts already kept ([`kept_entries`]), with the expansions
/// `loaded` has now: for the verdicts of a statement that moved while each expansion its
/// messages tell a place of was made again.
pub fn localize_kept(loaded: &Loaded, file: usize, entries: &mut [Entry]) {
    tauto_parse::install();
    for e in entries {
        localize(loaded, &loaded.files[file], &mut e.verdict);
    }
}

/// Where a statement of `loaded.files[file]` starts in that file, as the
/// spans of its verdicts are placed; none when it has no place of its own.
/// Moving a statement moves its verdicts by the change of this.
pub fn anchor_of(loaded: &Loaded, file: usize, stmt: &Stmt) -> Option<u32> {
    tauto_parse::install();
    stmt_span(loaded, file, stmt).map(|s| s.start)
}

/// The text a statement of `loaded.files[file]` was written as, when it has
/// a place of its own. Its verdicts are placed by this text and the anchor
/// alone: two statements that read the same and start at the same place have
/// their holes and errors at the same places. The statement itself does not
/// tell this, as parentheses and spaces leave no trace in it.
pub fn text_of<'a>(loaded: &'a Loaded, file: usize, stmt: &Stmt) -> Option<&'a str> {
    tauto_parse::install();
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
    tauto_parse::install();
    macro_failures(loaded)
}

/// What `check_file` does with the macro and syntax failures after the
/// verdicts: one that fails a declaration is part of its verdict, the rest are
/// entries of their own. An incremental checker ends its list with this.
pub fn attach_macro_failures(loaded: &Loaded, out: &mut Vec<FileEntry>) {
    tauto_parse::install();
    attach_failures(loaded, out)
}

/// What `check --json` says of each macro run.
pub fn expansion_infos(loaded: &Loaded) -> Vec<ExpansionInfo> {
    tauto_parse::install();
    expansion_infos_of(loaded)
}

#[derive(Clone)]
pub struct Checker {
    inner: check::Checker,
}

impl tauto_surface::identity::Detach for Checker {
    /// A copy whose name reservations are its own (`Kernel::detached`): what
    /// is kept for later programs is kept and handed out this way.
    fn detached(&self) -> Self {
        Self {
            inner: self.inner.detached(),
        }
    }
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
    tauto_parse::install();
    let mut kernel = Kernel::new();
    check::declare_prelude(&mut kernel)?;
    kernel.use_cache();
    let loaded = crate::program::load_with_text_in(path, None)?;
    declare_loaded(&mut kernel, &loaded)?;
    let term = tauto_parse::parse_expr_at(expr, 0)
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
