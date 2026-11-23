//! A Nib program of several files (`docs/design/self-host.md`). The files are read
//! in an order that puts what a file imports before it, each one with spans
//! starting where the one before ended, and their statements are joined into
//! one [`Program`] consumed by the checkers and the lowering to NIR.

use crate::surface::Name;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use tauto_message::{Message, msg};

mod expansions;
pub mod include;
pub mod inputs;
pub use expansions::{keep_expansions, keeps_expansions};
pub use inputs::Inputs;

use tauto_parol::Span;

use crate::macros::{Expansion, origin::SpanMap};
use crate::surface::{PRELUDE_BASE, ParseError, Program, Stmt};
use tauto_parse::parse_program_unresolved_at;

use tauto_parse::parse_program_located_at;
use tauto_surface::sources::locate;
pub use tauto_surface::sources::{SourceFile, SourceMap};

pub(crate) trait Standard {
    fn is_standard(&self) -> bool;
}

impl Standard for SourceFile {
    fn is_standard(&self) -> bool {
        self.path.starts_with(crate::stdlib::ROOT)
            || crate::stdlib::FILES
                .iter()
                .any(|(_, text)| *text == self.text)
            || crate::stdlib::is_std_file_by_path(&self.path)
    }
}

#[derive(Clone)]
pub struct Loaded {
    pub program: Program,
    registered_program: Option<Program>,
    pub files: Vec<SourceFile>,
    pub per_file: Vec<Vec<Stmt>>,
    /// The same before the classes are expanded for running: what the
    /// kernel reads, which has classes of its own.
    pub kernel_files: Vec<Vec<Stmt>>,
    /// The statements the top levels of the imported files would run. An
    /// import brings declarations, so they are not in the program and never
    /// run; they are checked all the same ([`Loaded::program_with_imports`]).
    pub imported_top: Vec<Stmt>,
    pub(crate) generated_executable: HashSet<Name>,
    /// The declarations the kernel is given only because they could be read
    /// (`read::runtime::separate`): one that fails to check is skipped and
    /// runs as written, as a function with effects does.
    pub(crate) tentative: HashSet<Name>,
    pub spans: SpanMap,
    pub expansions: Vec<Expansion>,
    pub warnings: Vec<(Message, Span)>,
    pub fixes: Vec<(Span, crate::check::Fix)>,
    /// For each use of a name the file does not import, the imports that would make it seen,
    /// one for each file that declares the name: a name only one file declares has its edit
    /// in `fixes` too, which makes it; one that several declare is left to the one who
    /// writes the file.
    pub import_choices: Vec<(Span, Vec<crate::check::Fix>)>,
    /// The names an import lists that the file does not use: taking them out
    /// changes nothing the program means.
    pub import_warnings: Vec<(Message, Span)>,
    /// A short name read as a module's own declaration though a declaration of that name
    /// outside every module is in the program and not imported.
    pub module_warnings: Vec<(Message, Span)>,
    pub literals: Vec<crate::syntax::LiteralUse>,
    pub registrations: Vec<crate::syntax::Registration>,
    /// The functions that run only while the program is expanded
    /// (`macros::expand::expansion_only`): no backend writes them.
    pub expansion_only: std::collections::HashSet<crate::surface::Name>,
    /// The methods of the instances the program writes, read before the
    /// class expansion makes them functions: what `TOTE::*` exports of them.
    pub instance_methods: Vec<tauto_nibcheck::types::InstanceMethod>,
    pub included: Vec<PathBuf>,
    /// Local include paths attempted, including files that could not be read.
    pub include_inputs: Vec<PathBuf>,
    /// The files each file imports, by their paths; empty when the files
    /// were read without their imports.
    pub imports: Vec<Vec<PathBuf>>,
    /// The directories the program was read from: where its syntaxes'
    /// tables were found. A run reads `syn_parse`'s tables from the same
    /// place, on whatever thread it runs.
    pub syntax_dirs: Vec<PathBuf>,
    /// Extraction evidence belongs to this complete expanded program. Public
    /// AST edits invalidate it, including edits to declarations a total function calls.
    extracted: Option<(Program, HashSet<Name>)>,
    pub(crate) bindings: tauto_surface::resolve::Resolver,
    /// What reading the files depended on when they were first read
    /// ([`read_dependencies`]): extraction and the separation of runtime code
    /// leave out files that the program was nonetheless read from.
    reads: Vec<PathBuf>,
    source_names: std::collections::BTreeMap<PathBuf, tauto_parse::source_names::SourceNames>,
}

/// Whether a file's top level runs `s`: it is not a declaration.
pub(crate) fn runs_at_top_level(s: &Stmt) -> bool {
    match s {
        Stmt::Let { .. }
        | Stmt::Var { .. }
        | Stmt::Assign { .. }
        | Stmt::While { .. }
        | Stmt::Expr(_) => true,
        Stmt::Attributed { stmt, .. } => runs_at_top_level(stmt),
        _ => false,
    }
}

/// The effects the statements `top` would ask of the host, with where each
/// is asked: all but `div` and the entries (`main`, `test`). The statements
/// are read with the declarations of `program`.
fn top_asks(program: &Program, top: &[Stmt]) -> Vec<(String, Span)> {
    if top.is_empty() {
        return Vec::new();
    }
    let mut stmts: Vec<Stmt> = program
        .stmts
        .iter()
        .filter(|s| !runs_at_top_level(s))
        .cloned()
        .collect();
    stmts.extend(top.iter().cloned());
    let with = Program {
        stmts,
        errors: Vec::new(),
    };
    let mut asks = Vec::new();
    for (row, span) in &crate::rows::check_program_rows(&with).top_rows {
        for effect in row.iter().filter(|e| {
            !["div", "budget", "budget_memory", "overflow", "divzero", "test", "main"]
                .iter()
                .any(|name| tauto_surface::bindings::is_library_effect(e, name))
                // What the row check could not follow is not known to be asked.
                && !e.starts_with('?')
                // What the body of an entry performs (`test@^wait`) is the
                // entry's, not the top level's.
                && !crate::types::indices::split_index_label(e)
                    .is_some_and(|(family, _)| family == "main" || family == "test")
        }) {
            asks.push((effect.to_string(), *span));
        }
    }
    asks
}

/// Whether the top level of `top` performs an entry (`main` or `test`).
fn performs_entry(program: &Program, top: &[Stmt]) -> bool {
    let mut stmts: Vec<Stmt> = program
        .stmts
        .iter()
        .filter(|s| !runs_at_top_level(s))
        .cloned()
        .collect();
    stmts.extend(top.iter().cloned());
    crate::rows::check_program_rows(&Program {
        stmts,
        errors: Vec::new(),
    })
    .entries
}

/// Whether the file at `path` is a module by where it is: a file of a
/// tote's sources (`src` and `additional-sources`), its `main` among them,
/// which performs `main`. Every other file is a script: what is beside the
/// sources (an example, a benchmark, a test, the `main` of a command), a file
/// of no tote.
/// Nothing but the place decides, so a file is the same thing however it is
/// read and whatever imports it.
pub fn is_module_file(path: &Path) -> bool {
    if path.starts_with(crate::stdlib::ROOT) {
        return true;
    }
    let path = canonical_path(path);
    let Some(dir) = path
        .ancestors()
        .skip(1)
        .find(|d| d.join("Tauto.eure").is_file())
    else {
        return false;
    };
    thread_local! {
        static SOURCES: std::cell::RefCell<HashMap<PathBuf, Vec<PathBuf>>> = Default::default();
    }
    SOURCES.with(|sources| {
        let mut sources = sources.borrow_mut();
        let dirs = sources.entry(dir.to_path_buf()).or_insert_with(|| {
            crate::manifest::read(dir)
                .map(|m| {
                    m.package
                        .source_paths()
                        .into_iter()
                        .map(|s| {
                            if s == "." {
                                dir.to_path_buf()
                            } else {
                                dir.join(s)
                            }
                        })
                        .collect()
                })
                .unwrap_or_default()
        });
        dirs.iter().any(|d| path.starts_with(d))
    })
}

/// The statements the top levels of the files before `entry` would run.
pub(crate) fn imported_top_of(per_file: &[Vec<Stmt>], entry: usize) -> Vec<Stmt> {
    per_file
        .iter()
        .take(entry)
        .flatten()
        .filter(|s| runs_at_top_level(s))
        .cloned()
        .collect()
}

/// Whether `wrapped` is the wrapping of `program` (`host::wrap`). Each
/// wrapping binds its `let _` to a fresh name, so two wrappings of one program
/// differ in that name alone; it is read as the same. The statements the
/// wrapper runs may also differ (the tests among them are run by `run_test`
/// in a build): the evidence is about the declarations, which must be the
/// same, and what the wrapper runs is checked without it either way.
fn same_wrapping(program: &Program, wrapped: &Program) -> bool {
    [false, true].into_iter().any(|entries| {
        let Some(again) = crate::host::wrap(program, entries) else {
            return false;
        };
        match (again.stmts.split_last(), wrapped.stmts.split_last()) {
            (Some((Stmt::Let { .. }, declarations)), Some((Stmt::Let { .. }, written))) => {
                declarations == written
            }
            _ => false,
        }
    })
}

impl Loaded {
    /// The origins of each standard effect `rows` says the top level asks
    /// of the host, spelled with their modules (`app::store::save`): what a
    /// run's permissions are granted to (`docs/design/host-effects.md`
    /// 「Origins」). The top level is its file's module.
    pub fn host_origins(
        &self,
        rows: &crate::rows::RowReport,
    ) -> std::collections::BTreeMap<String, std::collections::BTreeSet<String>> {
        // A tote's sources are under its `src`, which is not part of what a
        // reader names the tote's modules by (`time::datetime`).
        let modules: Vec<String> = module_names(&self.files)
            .into_iter()
            .map(|m| match m.split_once("::src::") {
                Some((tote, rest)) if !tote.contains("::") => format!("{tote}::{rest}"),
                _ => m,
            })
            .collect();
        let module = |at: u32| {
            self.files
                .iter()
                .zip(&modules)
                .rev()
                .find(|(f, _)| f.base <= at)
                .map(|(_, m)| m.as_str())
                .unwrap_or("")
        };
        rows.host_origins
            .iter()
            .map(|(effect, origins)| {
                let names = origins
                    .iter()
                    .map(|o| match &o.name {
                        Some(n) if n.contains("::") => n.clone(),
                        Some(n) => format!("{}::{n}", module(o.span.start)),
                        None => module(o.span.start).to_string(),
                    })
                    .collect();
                (effect.clone(), names)
            })
            .collect()
    }

    /// The binding session the program was bound in.
    pub(crate) fn bindings(&self) -> &tauto_surface::resolve::Resolver {
        &self.bindings
    }

    /// The executable representation used to validate and call syntax registrations.
    pub fn registration_program(&self) -> &Program {
        self.registered_program.as_ref().unwrap_or(&self.program)
    }

    pub fn source_names(
        &self,
    ) -> std::collections::BTreeMap<PathBuf, tauto_parse::source_names::SourceNames> {
        self.source_names.clone()
    }

    /// Binds the executable views in one session after source expansion.
    /// Existing references and extraction evidence retain their identities.
    pub fn resolve_runtime(&mut self) {
        let mut bindings =
            tauto_surface::resolve::Resolver::new(tauto_surface::bindings::library_bindings());
        bindings.statements(&mut self.program.stmts);
        for statements in &mut self.per_file {
            bindings.statements(statements);
        }
        bindings.statements(&mut self.imported_top);
    }
    /// The program with the statements the imported files' top levels would
    /// run, before those of the entry: what the types are checked of. Those
    /// statements are never run, and a type error in one is an error all the
    /// same.
    pub fn program_with_imports(&self) -> std::borrow::Cow<'_, Program> {
        if self.imported_top.is_empty() {
            return std::borrow::Cow::Borrowed(&self.program);
        }
        let at = self
            .program
            .stmts
            .iter()
            .position(runs_at_top_level)
            .unwrap_or(self.program.stmts.len());
        let mut stmts = self.program.stmts[..at].to_vec();
        stmts.extend(self.imported_top.iter().cloned());
        stmts.extend(self.program.stmts[at..].iter().cloned());
        std::borrow::Cow::Owned(Program {
            stmts,
            errors: self.program.errors.clone(),
        })
    }
    /// Effect checking with kernel-checked extraction evidence, when this is
    /// still the exact program produced by the extraction loader.
    pub fn check_rows(&self, target: crate::rows::Target) -> crate::rows::RowReport {
        match &self.extracted {
            Some((program, total)) if program == &self.program => {
                crate::rows::check_program_rows_trusted(&self.program, total, target)
            }
            _ if target == crate::rows::Target::JavaScript => {
                crate::rows::check_program_rows_javascript(&self.program)
            }
            _ => crate::rows::check_program_rows(&self.program),
        }
    }
    /// Effect checking using an existing type report. Extraction evidence is
    /// valid only for the complete program checked by the extraction loader.
    pub fn check_rows_with_types(
        &self,
        target: crate::rows::Target,
        types: &crate::types::TypeReport,
    ) -> crate::rows::RowReport {
        match &self.extracted {
            Some((program, total)) if program == &self.program => {
                crate::rows::check_program_rows_trusted_with_types(
                    &self.program,
                    total,
                    target,
                    types,
                )
            }
            _ if target == crate::rows::Target::JavaScript => {
                crate::rows::check_program_rows_javascript_with_types(&self.program, types)
            }
            _ => crate::rows::check_program_rows_with_types(&self.program, types),
        }
    }
    /// Effect checking of `wrapped`, the program with its top-level
    /// statements run under `Entry::run`. The wrapper changes no declaration's
    /// recursion, so the extraction evidence still holds when `wrapped` is
    /// exactly the wrapping of the extracted program.
    pub fn check_wrapped_rows_with_types(
        &self,
        wrapped: &Program,
        target: crate::rows::Target,
        types: &crate::types::TypeReport,
    ) -> crate::rows::RowReport {
        match &self.extracted {
            Some((program, total))
                if program == &self.program && same_wrapping(program, wrapped) =>
            {
                crate::rows::check_program_rows_trusted_with_types(wrapped, total, target, types)
            }
            _ if target == crate::rows::Target::JavaScript => {
                crate::rows::check_program_rows_javascript_with_types(wrapped, types)
            }
            _ => crate::rows::check_program_rows_with_types(wrapped, types),
        }
    }
    /// A span's position as its source file, line and column, counted from 1.
    /// Macro-generated spans are followed to the source that produced them.
    pub fn locate(&self, offset: u32) -> Option<(&Path, usize, usize)> {
        locate(&self.files, &self.spans, offset)
    }

    pub fn source_map(&self) -> SourceMap {
        SourceMap {
            files: self.files.clone(),
            spans: self.spans.clone(),
        }
    }

    /// Text with exactly the offsets assigned by the file reader. The separator
    /// after every file occupies one byte even when that file ends in a newline.
    pub fn source_text(&self) -> String {
        let mut source = String::new();
        for file in &self.files {
            debug_assert_eq!(source.len(), file.base as usize);
            source.push_str(&file.text);
            source.push('\n');
        }
        source
    }
}

/// Reads `entry` and the files it imports, relative to the importing file.
/// Each file is read once; a cycle is an error.
pub fn load(entry: &Path) -> Result<Loaded, String> {
    tauto_parse::install();
    load_in(entry).map_err(|e| e.to_string())
}

fn load_in(entry: &Path) -> Result<Loaded, Message> {
    load_with_text_in(entry, None)
}

pub fn load_with_text(entry: &Path, text: Option<&str>) -> Result<Loaded, String> {
    tauto_parse::install();
    load_with_text_in(entry, text).map_err(|e| e.to_string())
}

pub(crate) fn load_with_text_in(entry: &Path, text: Option<&str>) -> Result<Loaded, Message> {
    let given = text.and_then(|t| Some((canonicalize(&entry).ok()?, t.to_string())));
    load_with_source_in(entry, &|path: &Path| match &given {
        Some((own, text)) if own == path => Some(Ok(text.clone())),
        _ => None,
    })
    .map_err(Message::from)
}

/// Where a file's text comes from when it is not read from disk: `Some` is the
/// text (or why it cannot be had) of the file at this canonical path, `None`
/// leaves the file to the disk. An editor's unsaved buffers, and the files an
/// incremental checker holds, are given this way.
pub type Source<'a> = dyn Fn(&Path) -> Option<Result<String, String>> + 'a;

/// [`load`] with the text of some files given by `source`. A file that is
/// given need not exist on disk; its path is then taken as written, made
/// absolute and without `.` and `..`.
pub fn load_with_source(entry: &Path, source: &Source<'_>) -> Result<Loaded, LoadError> {
    tauto_parse::install();
    load_with_source_in(entry, source)
}

pub(crate) fn load_with_source_in(entry: &Path, source: &Source<'_>) -> Result<Loaded, LoadError> {
    load_with_bindings(entry, source, None)
}

/// Loads an edit in the same declaration and lexical binding session.
/// Visibility is rebuilt; retaining an identity does not retain checked evidence.
pub fn load_revision(
    entry: &Path,
    source: &Source<'_>,
    previous: &Loaded,
) -> Result<Loaded, LoadError> {
    tauto_parse::install();
    load_with_bindings(entry, source, Some(previous.bindings.next_revision()))
}

fn load_with_bindings(
    entry: &Path,
    source: &Source<'_>,
    bindings: Option<tauto_surface::resolve::Resolver>,
) -> Result<Loaded, LoadError> {
    crate::surface::parsed::begin_reading();
    let mut order = Order {
        done: HashSet::new(),
        stack: Vec::new(),
        files: Vec::new(),
        source,
    };
    order.visit(entry)?;
    crate::phases::mark("read");
    let stage = expand_stage(
        order.files,
        entry.parent(),
        true,
        source,
        None,
        bindings,
        None,
    )?;
    Ok(finish(stage, &HashMap::new(), None)?)
}

/// The program of `entry` (its text given, when it is) read and its macros expanded, without
/// being resolved and checked: what an editor colours the literals of the file by.
pub struct Expanded {
    pub files: Vec<SourceFile>,
    pub literals: Vec<crate::syntax::LiteralUse>,
    pub registrations: Vec<crate::syntax::Registration>,
    pub syntax_dirs: Vec<PathBuf>,
    /// What it was read from.
    pub inputs: Inputs,
}

pub fn expand_with_text(entry: &Path, text: Option<&str>) -> Result<Expanded, String> {
    tauto_parse::install();
    expand_with_text_in(entry, text).map_err(|e| e.to_string())
}

fn expand_with_text_in(entry: &Path, text: Option<&str>) -> Result<Expanded, Message> {
    let source = given(entry, text);
    crate::surface::parsed::begin_reading();
    let texts = inputs::order(entry, &source)?;
    crate::phases::mark("read");
    let stage = expand_stage(
        texts.clone(),
        entry.parent(),
        true,
        &source,
        None,
        None,
        None,
    )?;
    let inputs = inputs::of(&texts, &stage.included.inputs);
    Ok(Expanded {
        files: stage.files,
        literals: stage.out.literals,
        registrations: stage.out.registrations,
        syntax_dirs: stage.syntax_dirs,
        inputs,
    })
}

/// The inputs now of the program of `entry` (its text given, when it is), read before with the
/// inputs `before`.
pub fn current_inputs(entry: &Path, text: Option<&str>, before: &Inputs) -> Result<Inputs, String> {
    tauto_parse::install();
    current_inputs_in(entry, text, before).map_err(|e| e.to_string())
}

fn current_inputs_in(entry: &Path, text: Option<&str>, before: &Inputs) -> Result<Inputs, Message> {
    crate::surface::parsed::begin_reading();
    inputs::current(entry, &given(entry, text), before)
}

/// The program of the first `n` of the files `inputs` holds (of the program of `entry`), as
/// [`load`] reads it.
pub fn load_first(entry: &Path, inputs: &Inputs, n: usize) -> Result<Loaded, String> {
    tauto_parse::install();
    load_first_in(entry, inputs, n).map_err(|e| e.to_string())
}

fn load_first_in(entry: &Path, inputs: &Inputs, n: usize) -> Result<Loaded, Message> {
    let files = inputs.files[..n.min(inputs.files.len())].to_vec();
    let held = files.clone();
    assemble(files, entry.parent(), true, &move |p: &Path| {
        held.iter()
            .find(|(q, _)| canonical_path(q) == p)
            .map(|(_, t)| Ok(t.clone()))
    })
}

fn given(entry: &Path, text: Option<&str>) -> impl Fn(&Path) -> Option<Result<String, String>> {
    let given = text.and_then(|t| Some((canonicalize(&entry).ok()?, t.to_string())));
    move |path: &Path| match &given {
        Some((own, text)) if own == path => Some(Ok(text.clone())),
        _ => None,
    }
}

/// [`load`] of several entries as one program: each file once, a file
/// before the ones that import it.
pub fn load_roots(entries: &[PathBuf]) -> Result<Loaded, String> {
    tauto_parse::install();
    load_roots_in(entries).map_err(|e| e.to_string())
}

pub(crate) fn load_roots_in(entries: &[PathBuf]) -> Result<Loaded, Message> {
    load_roots_with_entry_in(entries, None)
}

/// [`load_roots`], where `entry` is the file whose top level runs: the other
/// files are imported, whatever order they are read in. Without `entry`, it is
/// the last file read.
pub(crate) fn load_roots_with_entry_in(
    entries: &[PathBuf],
    entry: Option<&Path>,
) -> Result<Loaded, Message> {
    load_roots_with_source_in(entries, entry, &|_| None)
}

fn load_roots_with_source_in(
    entries: &[PathBuf],
    entry: Option<&Path>,
    source: &Source<'_>,
) -> Result<Loaded, Message> {
    let mut order = Order {
        done: HashSet::new(),
        stack: Vec::new(),
        files: Vec::new(),
        source,
    };
    for entry in entries {
        order.visit(entry)?;
    }
    // The standard library first, as one entry that imports it reads it: a
    // tote's files are read in the same order whichever of them names the
    // library, so `run DIR` and `run FILE` check the same program. A file of
    // `std` imports only files of `std`, so their order among themselves
    // holds.
    let std_root = Path::new(crate::stdlib::ROOT);
    let (mut files, rest): (Vec<_>, Vec<_>) = order
        .files
        .into_iter()
        .partition(|(path, _)| path.starts_with(std_root));
    files.extend(rest);
    let stage = expand_stage(files, None, true, source, None, None, entry)?;
    finish(stage, &HashMap::new(), None)
}

/// The program of `entry` together with every file it could import: the files of its tote and
/// the tote's dependencies, or, outside a tote, the source files under its directory that
/// belong to no tote. The texts `source` gives stand for the files. What the files of the
/// program say of a name `entry` uses without importing it is in [`Loaded::import_choices`].
pub fn load_home_with_source(entry: &Path, source: &Source<'_>) -> Result<Loaded, LoadError> {
    tauto_parse::install();
    let entry = canonical_path(entry);
    let tote = |p: &Path| {
        p.ancestors()
            .skip(1)
            .find(|d| d.join("Tauto.eure").is_file())
            .map(Path::to_path_buf)
    };
    let mut files: Vec<PathBuf> = match tote(&entry) {
        Some(dir) => tote_order(&dir)?.files,
        None => {
            let dir = entry.parent().unwrap_or(Path::new("")).to_path_buf();
            let mut all = Vec::new();
            source_files(&dir, &mut all)?;
            all.retain(|p| tote(p).is_none());
            all
        }
    };
    files.retain(|p| canonical_path(p) != entry);
    files.push(entry.clone());
    Ok(load_roots_with_source_in(&files, Some(&entry), source)?)
}

/// Reads the files, in this order, as one program. An `import` in them is
/// not followed.
pub fn load_files(paths: &[PathBuf]) -> Result<Loaded, String> {
    tauto_parse::install();
    load_files_in(paths).map_err(|e| e.to_string())
}

fn load_files_in(paths: &[PathBuf]) -> Result<Loaded, Message> {
    let mut files = Vec::new();
    for path in paths {
        let text = std::fs::read_to_string(path).map_err(|e| failed_at(path.display(), e))?;
        files.push((path.clone(), text));
    }
    assemble(files, None, false, &|_| None)
}

/// Expands already ordered runtime source texts, retaining each file's macro
/// stage and source positions. Imports must have been resolved by the loader
/// and removed by extraction; this reader does not follow or reorder them.
pub fn load_texts(texts: Vec<(PathBuf, String)>) -> Result<Loaded, String> {
    tauto_parse::install();
    load_texts_in(texts).map_err(|e| e.to_string())
}

fn load_texts_in(texts: Vec<(PathBuf, String)>) -> Result<Loaded, Message> {
    assemble(texts, None, false, &|_| None)
}

struct Order<'a> {
    done: HashSet<PathBuf>,
    stack: Vec<PathBuf>,
    files: Vec<(PathBuf, String)>,
    source: &'a Source<'a>,
}

/// The canonical path of a file, or, when it is not on disk, the path made
/// absolute and without `.` and `..` (a buffer that was never saved).
pub fn canonical_path(path: &Path) -> PathBuf {
    tauto_parse::install();
    if let Ok(p) = canonicalize(path) {
        return p;
    }
    lexical_path(path)
}

/// `path` made absolute and without `.` and `..`, by its text alone.
fn lexical_path(path: &Path) -> PathBuf {
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().unwrap_or_default().join(path)
    };
    let mut out = PathBuf::new();
    for part in absolute.components() {
        match part {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out
}

/// [`Path::canonicalize`], except where the platform has no such thing (WASI
/// hosts answer "not supported"): there the path is made absolute and
/// without `.` and `..` by its text. A file that is missing is still an
/// error.
pub fn canonicalize(path: &Path) -> std::io::Result<PathBuf> {
    match path.canonicalize() {
        Err(e) if e.kind() == std::io::ErrorKind::Unsupported => Ok(lexical_path(path)),
        other => other,
    }
}

impl Order<'_> {
    /// `shown` is the path as written (the one messages use); the file is
    /// told apart from others by its canonical path.
    fn visit(&mut self, shown: &Path) -> Result<(), LoadError> {
        let given = match crate::stdlib::text(shown) {
            Some(text) => Some(Ok(text.to_string())),
            None => (self.source)(&canonical_path(shown)),
        };
        let path = match &given {
            Some(_) if crate::stdlib::text(shown).is_some() => shown.to_path_buf(),
            Some(_) => canonical_path(shown),
            None => canonicalize(shown).map_err(|e| failed_at(shown.display(), e))?,
        };
        if self.done.contains(&path) {
            return Ok(());
        }
        if self.stack.contains(&path) {
            return Err(msg!(
                "tauto-program-import-cycle",
                file = shown.display().to_string()
            )
            .into());
        }
        let text = match given {
            Some(text) => text.map_err(|e| failed_at(shown.display(), e))?,
            None => std::fs::read_to_string(&path).map_err(|e| failed_at(shown.display(), e))?,
        };
        let program = parse_program_located_at(&text, 0)
            .map_err(|e| parse_error(&path, &shown.display().to_string(), &text, 0, e))?;
        self.stack.push(path.clone());
        for target in proof_literal_imports(&path, &text, &program.stmts) {
            self.visit(&target)?;
        }
        // What a file depends on is every import it writes, those at the head of a
        // declaration's body included.
        let written = program.stmts.iter().flat_map(|stmt| {
            std::iter::once(stmt)
                .filter(|s| matches!(s, Stmt::Import { .. }))
                .chain(tauto_surface::surface::scoped::nested_imports(stmt))
        });
        for stmt in written {
            if let Stmt::Import {
                path: rel, module, ..
            } = stmt
            {
                let target = crate::stdlib::import_target(shown, rel, *module).map_err(|e| {
                    msg!(
                        "tauto-program-failed-at",
                        place = shown.display().to_string(),
                        why = e
                    )
                })?;
                self.visit(&target)?;
            }
        }
        self.stack.pop();
        self.done.insert(path);
        self.files.push((shown.to_path_buf(), text));
        Ok(())
    }
}

/// Why a program did not load, and where in which file when that is known:
/// a file that does not parse has its place, a missing import has none.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadError {
    pub message: Message,
    pub place: Option<Place>,
}

/// A place in a file the program reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Place {
    /// The file as it was read.
    pub path: PathBuf,
    /// The file as messages name it.
    pub shown: String,
    /// The byte in the file, from 0.
    pub offset: u32,
    /// The line and the column (in characters), both from 1.
    pub line: usize,
    pub col: usize,
}

impl Place {
    fn of(path: &Path, shown: &str, text: &str, offset: u32) -> Place {
        let before = text.get(..offset as usize).unwrap_or(text);
        Place {
            path: path.to_path_buf(),
            shown: shown.to_string(),
            offset: before.len() as u32,
            line: before.matches('\n').count() + 1,
            col: before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1,
        }
    }
}

/// `path:line:col: message`, or the message alone without a place.
impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.place {
            Some(p) => write!(f, "{}:{}:{}: {}", p.shown, p.line, p.col, self.message),
            None => write!(f, "{}", self.message),
        }
    }
}

impl From<Message> for LoadError {
    fn from(message: Message) -> LoadError {
        LoadError {
            message,
            place: None,
        }
    }
}

impl From<String> for LoadError {
    fn from(text: String) -> LoadError {
        Message::text(text).into()
    }
}

/// The error as text, its place written in it.
impl From<LoadError> for Message {
    fn from(e: LoadError) -> Message {
        match e.place {
            None => e.message,
            Some(_) => Message::text(e.to_string()),
        }
    }
}

impl From<LoadError> for String {
    fn from(e: LoadError) -> String {
        e.to_string()
    }
}

/// The failure to parse `text` (spans from `base`), read from `path` and
/// named `shown`, at its place in the file.
fn parse_error(path: &Path, shown: &str, text: &str, base: u32, error: ParseError) -> LoadError {
    let place = error
        .at
        .and_then(|at| at.checked_sub(base))
        .map(|offset| Place::of(path, shown, text, offset));
    LoadError {
        message: Message::text(error.message),
        place,
    }
}

/// Reads each file with spans from its base and joins the statements.
/// `root` is what the file names in messages are relative to; `source` gives
/// the text of a file `include_text!` reads, when it is not read from disk.
fn assemble(
    texts: Vec<(PathBuf, String)>,
    root: Option<&Path>,
    imports: bool,
    source: &Source<'_>,
) -> Result<Loaded, Message> {
    assemble_keeping(texts, root, imports, source, &HashMap::new(), None)
}

/// [`assemble`], keeping of each file's macro-made declarations, in order,
/// those `generated` says to keep; a file it does not name keeps them all.
fn assemble_keeping(
    texts: Vec<(PathBuf, String)>,
    root: Option<&Path>,
    imports: bool,
    source: &Source<'_>,
    generated: &HashMap<PathBuf, Vec<bool>>,
    graph: Option<&HashMap<PathBuf, Vec<PathBuf>>>,
) -> Result<Loaded, Message> {
    let stage = expand_stage(texts, root, imports, source, graph, None, None)?;
    finish(stage, generated, graph)
}

/// The files read and their macros expanded: what [`finish`] makes a [`Loaded`] of.
struct Stage {
    files: Vec<SourceFile>,
    imported: Vec<Vec<PathBuf>>,
    included: include::Included,
    qualified: Vec<(Message, Span)>,
    /// The names one import would make seen, and where each file's last import ends.
    missing: Vec<crate::surface::qualify::MissingImport>,
    /// The warnings of reading the modules of the files.
    module_warnings: Vec<(Message, Span)>,
    last_import: Vec<Option<u32>>,
    /// Whether each file sees the library's prelude only through its imports.
    bare: Vec<bool>,
    modules: Vec<String>,
    imports: Option<Vec<Vec<usize>>>,
    /// Each file's imports with what their lists bring.
    lists: Vec<Vec<crate::surface::qualify::ImportList>>,
    below: Vec<HashSet<usize>>,
    /// The names the quotes of each file write, read before the macros.
    quoted: crate::surface::qualify::Quoted,
    /// What the files write and may not see, found before the macros run.
    written_visibility: Vec<(Message, Span)>,
    /// Source alias declarations erased by expansion, retained for import-list checking.
    effect_set_declarations: Vec<Vec<Stmt>>,
    out: crate::macros::Output,
    syntax_dirs: Vec<PathBuf>,
    /// The index of the entry file, whose top level runs.
    entry: usize,
}

fn expand_stage(
    texts: Vec<(PathBuf, String)>,
    root: Option<&Path>,
    imports: bool,
    source: &Source<'_>,
    graph: Option<&HashMap<PathBuf, Vec<PathBuf>>>,
    bindings: Option<tauto_surface::resolve::Resolver>,
    entry: Option<&Path>,
) -> Result<Stage, LoadError> {
    // The entry is the file named, when it is read; otherwise the last file read.
    let entry = {
        let named = entry.map(canonical_path);
        let last = texts.len().saturating_sub(1);
        named
            .and_then(|e| texts.iter().position(|(p, _)| canonical_path(p) == e))
            .unwrap_or(last)
    };
    let imports_given = imports || graph.is_some();
    let mut files = Vec::new();
    let mut imported: Vec<Vec<PathBuf>> = Vec::new();
    // Each file's imports as written: the imported file, how it is written, its list and span.
    #[allow(clippy::type_complexity)]
    let mut written: Vec<Vec<(PathBuf, String, Option<Vec<(String, Span)>>, Span, bool)>> =
        Vec::new();
    // The files each file imports at the head of a declaration's body.
    let mut body_imported: Vec<Vec<PathBuf>> = Vec::new();
    // The imports written where no import may be.
    let mut misplaced: Vec<(Message, Span)> = Vec::new();
    let mut included = include::Included::default();
    let mut last_import: Vec<Option<u32>> = Vec::new();
    let mut per_file: Vec<Vec<Stmt>> = Vec::new();
    let mut base = 0u32;
    for (path, text) in texts {
        let shown = |p: &Path| {
            root.and_then(|r| p.strip_prefix(r).ok())
                .unwrap_or(p)
                .display()
                .to_string()
        };
        let mut program = parse_program_located_at(&text, base)
            .map_err(|e| parse_error(&path, &shown(&path), &text, base, e))?;
        include::read_includes(&mut program.stmts, &path, source, &mut included);
        let mut stmts = Vec::new();
        imported.push(if imports {
            proof_literal_imports(&path, &text, &program.stmts)
        } else {
            Vec::new()
        });
        last_import.push(None);
        written.push(Vec::new());
        body_imported.push(Vec::new());
        misplaced.extend(
            tauto_surface::surface::scoped::misplaced(&program.stmts)
                .into_iter()
                .map(|at| (msg!("surface-import-misplaced"), at)),
        );
        // An import at the head of a declaration's body: the file depends on what it
        // names, which only that body sees.
        for stmt in &program.stmts {
            for import in tauto_surface::surface::scoped::head_imports(stmt) {
                let Stmt::Import {
                    path: rel,
                    module,
                    names,
                    span,
                } = import
                else {
                    continue;
                };
                if !imports {
                    return Err(msg!(
                        "tauto-program-tote-imports",
                        file = shown(&path).to_string()
                    )
                    .into());
                }
                let target = match crate::stdlib::import_target(&path, rel, *module) {
                    Ok(named) if crate::stdlib::text(&named).is_some() => named,
                    Ok(named) => canonical_path(&named),
                    Err(_) => canonical_path(&path.parent().unwrap_or(Path::new(".")).join(rel)),
                };
                let spelling = if *module {
                    rel.clone()
                } else {
                    crate::surface::print::quoted(rel)
                };
                written.last_mut().unwrap().push((
                    target.clone(),
                    spelling,
                    names.clone(),
                    *span,
                    true,
                ));
                body_imported.last_mut().unwrap().push(target);
            }
        }
        for stmt in program.stmts {
            match &stmt {
                Stmt::Import {
                    path: rel,
                    module,
                    names,
                    span,
                } if imports => {
                    let last = last_import.last_mut().unwrap();
                    *last = Some(last.map_or(span.end, |e: u32| e.max(span.end)));
                    // A dependency's module is its file, as the loader read it:
                    // what a file imports from a dependency is what it reaches.
                    let target = match crate::stdlib::import_target(&path, rel, *module) {
                        Ok(named) if crate::stdlib::text(&named).is_some() => named,
                        Ok(named) => canonical_path(&named),
                        Err(_) => {
                            canonical_path(&path.parent().unwrap_or(Path::new(".")).join(rel))
                        }
                    };
                    let spelling = if *module {
                        rel.clone()
                    } else {
                        crate::surface::print::quoted(rel)
                    };
                    written.last_mut().unwrap().push((
                        target.clone(),
                        spelling,
                        names.clone(),
                        *span,
                        false,
                    ));
                    imported.last_mut().unwrap().push(target);
                    continue;
                }
                Stmt::Import { .. } => {
                    return Err(msg!(
                        "tauto-program-tote-imports",
                        file = shown(&path).to_string()
                    )
                    .into());
                }
                _ => {}
            }
            stmts.push(stmt);
        }
        per_file.push(stmts);
        let next = base as u64 + text.len() as u64 + 1;
        if next >= PRELUDE_BASE as u64 {
            return Err(msg!("tauto-program-too-large").into());
        }
        files.push(SourceFile { path, base, text });
        base = next as u32;
    }
    crate::phases::mark("parse");
    // The directories of the files, then the ones the caller asked tables to be read from (a program
    // given as text has no directory of its own).
    let dirs: Vec<PathBuf> = files
        .iter()
        .filter_map(|f: &SourceFile| f.path.parent().map(Path::to_path_buf))
        .chain(crate::syntax::search_dirs())
        .collect();
    let syntax_dirs = dirs.clone();
    // Each name means one declaration before the macros run, so that a
    // macro's function means what its file means, and again after, for what
    // the macros declared.
    std_tote_alone(&files)?;
    let modules = modules_of(&files);
    let paths: Vec<PathBuf> = files
        .iter()
        .map(|f| match crate::stdlib::text(&f.path) {
            Some(_) => f.path.clone(),
            None => canonical_path(&f.path),
        })
        .collect();
    let imports: Vec<Vec<usize>> = imported
        .iter()
        .map(|targets| {
            targets
                .iter()
                .filter_map(|t| paths.iter().position(|p| p == t))
                .collect()
        })
        .collect();
    let _alone = crate::surface::qualify::StandaloneFiles::of(standalone_flags(&paths));
    let unseen = if imports_given {
        let standard: Vec<bool> = files.iter().map(SourceFile::is_standard).collect();
        unseen_files(&paths, &imports, &standard)
    } else {
        Vec::new()
    };
    let imports = imports_given.then_some(imports.as_slice());
    // The files read again to run (`graph`) are held to the lists where they were checked.
    let lists: Vec<Vec<crate::surface::qualify::ImportList>> = written
        .into_iter()
        .map(|file| {
            file.into_iter()
                .filter(|_| graph.is_none())
                .map(
                    |(target, spelling, names, span, body)| crate::surface::qualify::ImportList {
                        target: paths.iter().position(|p| *p == target),
                        spelling,
                        names,
                        span,
                        body,
                    },
                )
                .collect()
        })
        .collect();
    let mut per_file = per_file;
    let below = totes_below(&files);
    let bare = without_prelude(&files);
    let quoted = crate::surface::qualify::Quoted::default();
    let (mut qualified, seeing, missing, module_warnings, scopes) = {
        let spell = import_spellings(&files, &modules);
        crate::surface::qualify::files_before_macros_listed(
            &mut per_file,
            &modules,
            imports,
            Some(&below),
            Some(&spell),
            &lists,
            &bare,
            &quoted,
        )
    };
    qualified.extend(misplaced);
    qualified.extend(crate::surface::qualify::effect_set_visibility(
        &per_file, &modules,
    ));
    qualified.extend(crate::surface::qualify::written_pairs(&per_file));
    // What the files write is held to what they may see before the macros run.
    // Expansion binds every name of a program that has macros to its declaration,
    // and a bound name is not read again (`docs/design/macro.md`, hygiene 3): a
    // macro's `quote` sees what its own file sees, so after expansion a private
    // declaration it names is no longer told apart from one another file names.
    let written_visibility = if graph.is_none() {
        crate::surface::qualify::written_visibility(&per_file, &modules)
    } else {
        Vec::new()
    };
    let effect_set_declarations = per_file
        .iter()
        .map(|statements| {
            statements
                .iter()
                .filter(|s| matches!(s, Stmt::Effect(e) if e.set.is_some()))
                .cloned()
                .collect()
        })
        .collect();
    // The expansion of a file takes at most the time the check of it may
    // (`Tauto.eure`'s `check`); the expansion and the check are counted
    // apart, each from its own start. A manifest that cannot be read is
    // reported by the check, so the default limit stands in for it here.
    let time_limits: Vec<(String, std::time::Duration)> = files
        .iter()
        .map(|f| {
            let limit =
                crate::manifest::time_limit(&f.path).unwrap_or(crate::manifest::DEFAULT_TIME_LIMIT);
            (f.path.display().to_string(), limit)
        })
        .collect();
    tauto_macro::macros::expand::set_scopes(scopes);
    tauto_macro::macros::expand::set_sources(
        files
            .iter()
            .map(|f| {
                tauto_syntax::sha256_hex(format!("{}\0{}", f.path.display(), f.text).as_bytes())
            })
            .collect(),
    );
    let mut out = crate::syntax::with_search_dirs(dirs, || {
        expansions::expand(
            per_file,
            seeing,
            modules.clone(),
            time_limits,
            bindings,
            files.iter().map(SourceFile::is_standard).collect(),
            unseen,
        )
    });
    tauto_kernel::check::Kernel::new().set_file_limit(None);
    crate::phases::mark("expand");
    // What each file depends on: its imports, those at the head of a declaration's body
    // included.
    let imported: Vec<Vec<PathBuf>> = imported
        .into_iter()
        .zip(body_imported)
        .map(|(mut all, body)| {
            for target in body {
                if !all.contains(&target) {
                    all.push(target);
                }
            }
            all
        })
        .collect();
    Ok(Stage {
        files,
        imported,
        included,
        qualified,
        missing,
        module_warnings,
        last_import,
        modules,
        imports: imports.map(<[_]>::to_vec),
        lists,
        quoted,
        written_visibility,
        effect_set_declarations,
        below,
        bare,
        out,
        syntax_dirs,
        entry,
    })
}

/// The expanded files resolved and joined into one program.
fn finish(
    stage: Stage,
    generated: &HashMap<PathBuf, Vec<bool>>,
    graph: Option<&HashMap<PathBuf, Vec<PathBuf>>>,
) -> Result<Loaded, Message> {
    let Stage {
        files,
        imported,
        mut included,
        mut qualified,
        mut missing,
        module_warnings,
        last_import,
        modules,
        imports,
        lists,
        quoted,
        written_visibility,
        effect_set_declarations,
        below,
        bare,
        mut out,
        syntax_dirs,
        entry,
    } = stage;
    let imports = imports.as_deref();
    for (file, stmts) in files.iter().zip(&mut out.files) {
        if let Some(keep) = generated.get(&file.path) {
            let mut made = keep.iter();
            stmts.retain(|s| !crate::extract::macro_made(s) || *made.next().unwrap_or(&true));
        }
    }
    let models = crate::surface::qualify::split_models(&mut out.files, &modules, imports);
    for (statements, aliases) in out.files.iter_mut().zip(&effect_set_declarations) {
        statements.extend(aliases.iter().cloned());
    }
    crate::surface::qualify::quote_written(
        &quoted,
        out.written
            .iter()
            .map(|(file, _, written, at)| (*file, written.clone(), *at)),
    );
    let (after, seeing, more, list_fixes, import_warnings) =
        crate::surface::qualify::files_after_macros_listed(
            &mut out.files,
            &modules,
            imports,
            Some(&below),
            Some(&import_spellings(&files, &modules)),
            &lists,
            &bare,
            &quoted,
        );
    qualified.extend(after);
    for statements in out.files.iter_mut() {
        tauto_surface::surface::scoped::strip(statements);
    }
    for (statements, aliases) in out.files.iter_mut().zip(&effect_set_declarations) {
        let retained = statements.len() - aliases.len();
        assert!(
            statements[retained..]
                .iter()
                .all(|s| matches!(s, Stmt::Effect(e) if e.set.is_some()))
        );
        statements.truncate(retained);
    }
    missing.extend(more);
    let import_choices = import_fixes(&files, &last_import, missing);
    out.fixes.extend(
        import_choices
            .iter()
            .filter(|(_, choices)| choices.len() == 1)
            .map(|(at, choices)| (*at, choices[0].clone())),
    );
    out.fixes.extend(list_fixes);
    qualified.extend(crate::surface::qualify::sealed_externs(
        &out.files,
        &totes_of(&files),
    ));
    qualified.extend(crate::surface::qualify::std_models(&out.files, &modules));
    // The files read again to run were held to what they may see when they
    // were checked; `extracted.taut` writes out what the kernel accepted.
    // So were their names: `extracted.taut` holds the declarations of the
    // files it was made from, and is not declaring them again.
    let mut sealed_unsure = Vec::new();
    // A record without a name is one struct for the whole program. It is
    // declared before the field reads are judged, so that `x.f` of a record
    // is not taken for the field `f` of the one type another file seals.
    tauto_surface::records::declare(&mut out.files);
    if graph.is_none() {
        // What a macro writes into a file, by a name it does not bind, is held to
        // that file. What the file wrote itself was also checked before expansion;
        // where both found a use, the one read after expansion names it in full.
        let (after, unsure) =
            crate::surface::qualify::sealed_visibility_typed(&out.files, &modules);
        sealed_unsure = unsure;
        let at: HashSet<Span> = after.iter().map(|(_, span)| *span).collect();
        qualified.extend(
            written_visibility
                .into_iter()
                .filter(|(_, span)| !at.contains(span)),
        );
        qualified.extend(after);
    } else {
        // The text in the installed language is matched, because `tauto-surface`
        // does not give these errors as messages with an id.
        qualified.retain(|(m, _)| {
            !m.as_text()
                .is_some_and(|t| t.contains("is already declared as"))
        });
    }
    // An import brings a file's declarations: the statements a file's top
    // level runs are the entry's alone.
    out.stmts = out
        .files
        .iter()
        .enumerate()
        .flat_map(|(i, file)| {
            file.iter()
                .filter(move |s| i == entry || !runs_at_top_level(s))
                .cloned()
        })
        .collect();
    // The pass runs before the macros and again after: what it finds in a
    // file the macros left alone, it finds twice.
    let mut said = std::collections::HashSet::new();
    qualified.retain(|e| said.insert(e.clone()));
    out.errors.extend(qualified);
    // A file's rows may name the sets of effects another file declares.
    let mut sets = crate::surface::effect_sets::Sets::new();
    for f in &out.files {
        crate::surface::effect_sets::collect(f, &mut sets);
    }
    let mut known: Vec<String> = out
        .files
        .iter()
        .flat_map(|f| crate::surface::modules::declared(f))
        .collect();
    known.extend(prelude_module_names().iter().cloned());
    let per_file = out
        .files
        .into_iter()
        .map(|f| crate::surface::modules::resolve_with(f, &sets, &known).0)
        .collect();
    let mut per_file: Vec<Vec<Stmt>> = per_file;
    let (mut stmts, mut errors) = crate::surface::modules::resolve_joined_files(
        out.stmts,
        &crate::surface::effect_sets::Sets::new(),
        &known,
    );
    // The models `split_models` named apart, in the file that declares each
    // and in the program, where that file's statements are the ones that
    // declare what it declares.
    for (j, file) in per_file.iter_mut().enumerate() {
        let these: Vec<_> = models.iter().filter(|m| m.file == j).cloned().collect();
        if these.is_empty() {
            continue;
        }
        let declared: HashSet<String> = file.iter().filter_map(stmt_name).collect();
        crate::surface::qualify::rename_models(file, &these);
        for s in stmts.iter_mut() {
            if stmt_name(s).is_some_and(|n| declared.contains(&n)) {
                crate::surface::qualify::rename_models(std::slice::from_mut(s), &these);
            }
        }
    }
    // What the reader could not include comes before what the macros did.
    let mut first = std::mem::take(&mut included.errors);
    first.append(&mut errors);
    let mut errors = first;
    errors.extend(out.errors);
    let mut program = Program { stmts, errors };
    let mut read = HashSet::new();
    included.files.retain(|p| read.insert(p.clone()));
    crate::phases::mark("resolve");
    let mut bindings = out.bindings;
    bindings.reserve_declarations(&mut program.stmts);
    bindings.source_modules(&modules);
    for (statements, visible) in per_file.iter_mut().zip(&seeing) {
        bindings.statements_visible(statements, visible);
    }
    tauto_surface::surface::superclasses::expand(&mut per_file, &mut program.errors);
    // An import brings a file's declarations: the statements a file's top
    // level runs are the entry's alone, which is the last file read.
    let entry = per_file.len().saturating_sub(1);
    // A module is a module by where its file is, read as the entry or not:
    // its top level says which entries it has and asks nothing else. A
    // script's statements run when it is the entry; importing one runs
    // nothing, so an import of a script that asks something is refused.
    let is_module: Vec<bool> = files.iter().map(|f| is_module_file(&f.path)).collect();
    let is_imported: Vec<bool> = match imports {
        Some(imports) => {
            let mut imported = vec![false; per_file.len()];
            for &i in imports.iter().flatten() {
                if let Some(slot) = imported.get_mut(i) {
                    *slot = true;
                }
            }
            imported
        }
        None => vec![true; per_file.len()],
    };
    let mut module_top = Vec::new();
    let mut imported_top = Vec::new();
    let mut entry_top = Vec::new();
    program.stmts = Vec::new();
    for (i, file) in per_file.iter().enumerate() {
        for s in file {
            if !runs_at_top_level(s) {
                program.stmts.push(s.clone());
            } else if i == entry {
                program.stmts.push(s.clone());
                if is_module[i] {
                    entry_top.push(s.clone());
                }
            } else if is_module[i] {
                module_top.push(s.clone());
            } else if is_imported[i] {
                imported_top.push(s.clone());
            }
        }
    }
    // The kernel reads a `coerce` field's coercions as the fields they read.
    crate::types::expand_coercions(&mut program, &mut per_file);
    let kernel_files = per_file.clone();
    // The terms the class expansion makes follow the macros' in the span
    // map, each one standing at the occurrence it was made for, so that an
    // error found in generated code is placed where that is written.
    let imported_now = imported_top_of(&per_file, entry);
    // The registered functions run on the bytecode machine, which expands
    // the classes of what it is given itself, as a macro's functions are.
    // The registered functions run on the bytecode machine, which compiles
    // what it is given, classes and all: they are given the program from
    // before its classes are expanded, and of its declarations only those
    // the functions reach, as a macro's functions see only what is before
    // their use. A declaration nothing of theirs names (the code that uses
    // the syntax, something unfinished) is not theirs to compile.
    let before_classes = (!out.registrations.is_empty()).then(|| {
        let short = |n: &str| n.rsplit("::").next().unwrap_or("").to_string();
        let mut before = program.clone();
        let declared: Vec<Vec<String>> = before
            .stmts
            .iter()
            .map(|s| {
                tauto_surface::bindings::declared_names(std::slice::from_ref(s))
                    .iter()
                    .map(|n| short(n.as_str()))
                    .collect()
            })
            .collect();
        let words: Vec<HashSet<String>> = before
            .stmts
            .iter()
            .map(|s| {
                // The names its terms use.
                let mut names = HashSet::new();
                let mut s = s.clone();
                crate::surface::walk::stmt(&mut s, &mut |t| {
                    if let crate::surface::TermKind::Var(n) = &*t.kind {
                        names.insert(short(n.as_str()));
                    }
                });
                // The classes a declaration asks of its types (`where Key(K)`) and the class an
                // instance is of are names it uses as well, though they are no term.
                let mut classes = |f: &crate::surface::FnDecl| {
                    names.extend(f.where_.iter().map(|c| short(c.class.as_str())));
                };
                match &s {
                    Stmt::Fn(f) => classes(f),
                    Stmt::Instance(i) => {
                        names.insert(short(i.class.as_str()));
                        names.extend(i.where_.iter().map(|c| short(c.class.as_str())));
                        i.methods.iter().for_each(|m| {
                            names.extend(m.where_.iter().map(|c| short(c.class.as_str())))
                        });
                    }
                    Stmt::Class(c) => {
                        c.methods.iter().for_each(&mut classes);
                    }
                    _ => {}
                }
                names
            })
            .collect();
        let mut wanted: HashSet<String> = out
            .registrations
            .iter()
            .map(|r| short(r.function.as_str()))
            .collect();
        // Imports, classes, instances, effects and externs are kept; a
        // macro, or a statement the top level runs, is not theirs.
        let mut keep: Vec<bool> = before
            .stmts
            .iter()
            .zip(&declared)
            .map(|(s, d)| {
                // An effect declares a name, but a function names it in a `perform` or a row,
                // not as a term, so it is kept like the rest.
                matches!(s, Stmt::Effect(_))
                    || d.is_empty()
                        && matches!(
                            s,
                            Stmt::Import { .. }
                                | Stmt::Class(_)
                                | Stmt::Instance(_)
                                | Stmt::Extern { .. }
                                | Stmt::Syntax { .. }
                                | Stmt::Mutual { .. }
                                | Stmt::Module { .. }
                        )
            })
            .collect();
        loop {
            let mut grew = false;
            for (i, names) in declared.iter().enumerate() {
                if !keep[i] && names.iter().any(|n| wanted.contains(n)) {
                    keep[i] = true;
                    grew = true;
                    wanted.extend(words[i].iter().cloned());
                }
            }
            if !grew {
                break;
            }
        }
        // What is kept regardless (imports, syntaxes, classes) names things too.
        for (i, k) in keep.iter().enumerate() {
            if *k {
                wanted.extend(words[i].iter().cloned());
            }
        }
        loop {
            let mut grew = false;
            for (i, names) in declared.iter().enumerate() {
                if !keep[i] && names.iter().any(|n| wanted.contains(n)) {
                    keep[i] = true;
                    grew = true;
                    wanted.extend(words[i].iter().cloned());
                }
            }
            if !grew {
                break;
            }
        }
        // The errors of what is left out are not theirs either.
        before.errors.clear();
        let mut i = 0;
        before.stmts.retain(|_| {
            i += 1;
            keep[i - 1]
        });
        before
    });
    let instance_methods = tauto_nibcheck::types::instance_methods(&program, &per_file);
    let made = crate::types::expand_loaded(
        &mut program,
        &mut per_file,
        &imported_now,
        crate::macros::EXPANSION_BASE + out.spans.len() as u32,
    );
    for written in made {
        out.spans.fresh(written.start, u32::MAX, written.start);
    }
    bindings.statements(&mut program.stmts);
    for statements in &mut per_file {
        bindings.statements(statements);
    }
    // The kernel reads `decreasing_by` as written; a program that runs does not.
    crate::surface::walk::strip_proofs_in(&mut program.stmts);
    let registered_program = if out.registrations.is_empty() {
        None
    } else {
        let standard = files
            .iter()
            .zip(&per_file)
            .filter(|(file, _)| file.is_standard())
            .flat_map(|(_, statements)| tauto_surface::bindings::declared_names(statements))
            .cloned()
            .collect();
        crate::registered::executable(
            before_classes.as_ref().unwrap_or(&program),
            &out.registrations,
            &standard,
        )
    };
    let wrong = crate::registered::validate(
        registered_program.as_ref().unwrap_or(&program),
        &out.registrations,
    );
    program.errors.extend(wrong);
    crate::phases::mark("classes");
    let source_names = files
        .iter()
        .zip(&seeing)
        .map(|(file, visible)| {
            (
                canonical_path(&file.path),
                tauto_parse::source_names::SourceNames::new(&bindings, visible),
            )
        })
        .collect();
    crate::phases::mark("source_names");
    let sealed = sealed_by_types(&program, &bindings, sealed_unsure);
    program.errors.extend(sealed);
    program
        .errors
        .extend(tauto_surface::surface::extern_blocks::validate_extern_blocks(
            &program.stmts,
        ));
    crate::phases::mark("sealed");
    // The entry's own top level, when it performs an entry, is held to the
    // same by the row check (`rows-entry-top-level`).
    if !entry_top.is_empty() && !performs_entry(&program, &entry_top) {
        module_top.extend(entry_top);
    }
    for (effect, span) in top_asks(&program, &module_top) {
        program
            .errors
            .push((msg!("rows-module-top-level", effect = effect), span));
    }
    for (effect, span) in top_asks(&program, &imported_top) {
        program
            .errors
            .push((msg!("rows-import-top-level", effect = effect), span));
    }
    crate::phases::mark("top_asks");
    let reads = reads_of(&files, &included.files, &included.inputs, &syntax_dirs);
    crate::phases::mark("reads");
    let checked_top = imported_top_of(&per_file, entry);
    crate::phases::mark("imported_top");
    Ok(Loaded {
        program,
        registered_program,
        files,
        per_file,
        kernel_files,
        imported_top: checked_top,
        generated_executable: out.generated_executable,
        tentative: HashSet::new(),
        spans: out.spans,
        expansions: out.expansions,
        warnings: out.warnings,
        fixes: out.fixes,
        import_choices,
        import_warnings,
        module_warnings,
        literals: out.literals,
        registrations: out.registrations,
        expansion_only: out.expansion_only,
        instance_methods,
        included: included.files,
        include_inputs: included.inputs,
        imports: imported,
        reads,
        syntax_dirs,
        extracted: None,
        bindings,
        source_names,
    })
}

/// Of each file, the files of the totes its tote depends on directly, by the
/// dependencies of its tote's `Tauto.eure`. A tote a dependency depends on
/// is that dependency's business: its names do not reach this tote.
fn totes_below(files: &[SourceFile]) -> Vec<HashSet<usize>> {
    let std_root = Path::new(crate::stdlib::ROOT);
    let manifests: Vec<Option<crate::manifest::Manifest>> = files
        .iter()
        .map(|f| {
            if f.path.starts_with(std_root) {
                return None;
            }
            canonical_path(&f.path)
                .ancestors()
                .skip(1)
                .find(|d| d.join("Tauto.eure").is_file())
                .and_then(|d| crate::manifest::read(d).ok())
        })
        .collect();
    let mut deps: HashMap<&str, Vec<&str>> = HashMap::new();
    for m in manifests.iter().flatten() {
        deps.entry(m.package.name.as_str())
            .or_insert_with(|| m.dependencies.iter().map(|(n, _)| n.as_str()).collect());
    }
    manifests
        .iter()
        .map(|m| {
            let Some(m) = m else {
                return HashSet::new();
            };
            let own = m.package.name.as_str();
            let seen: HashSet<&str> = deps
                .get(own)
                .into_iter()
                .flatten()
                .copied()
                .filter(|&t| t != own)
                .collect();
            manifests
                .iter()
                .enumerate()
                .filter(|(_, o)| {
                    o.as_ref()
                        .is_some_and(|o| seen.contains(o.package.name.as_str()))
                })
                .map(|(j, _)| j)
                .collect()
        })
        .collect()
}

/// Whether each file sees the library's prelude only through its imports: a file of the
/// standard library, and a file of the sources of a tote whose `Tauto.eure` says
/// `prelude = false`, but a file of the prelude itself (`std/prelude/std.taut`).
fn without_prelude(files: &[SourceFile]) -> Vec<bool> {
    files
        .iter()
        .map(|f| sees_prelude_only_by_imports(&f.path, &f.text))
        .collect()
}

/// [`without_prelude`] of the file at `path` with `text`.
fn sees_prelude_only_by_imports(path: &Path, text: &str) -> bool {
    let std_root = Path::new(crate::stdlib::ROOT);
    // The prelude's own files are the prelude.
    let prelude = crate::nibstd::PRELUDE_FILES
        .iter()
        .any(|(p, t)| path.ends_with(p) && *t == text);
    path.starts_with(std_root)
        || !prelude && {
            let path = canonical_path(path);
            path.ancestors()
                .skip(1)
                .find(|d| d.join("Tauto.eure").is_file())
                .and_then(|d| Some((d, crate::manifest::read(d).ok()?)))
                .is_some_and(|(d, m)| {
                    m.package.no_prelude
                        && m.package
                            .source_paths()
                            .iter()
                            .any(|s| path.starts_with(d.join(s)))
                })
        }
}

/// The proof models a file reads without writing their import. The literals a
/// program writes are core: a text literal is a `Text` and a float literal a
/// `Float` in every file that sees the prelude (`docs/design/visibility.md`
/// 「Prelude」). The kernel reads one as a term only once the model
/// (`std/text.taut`, `std/float.taut`) is declared, so a file whose theorem
/// states one reads that model as if it had written `import std::text` or
/// `import std::float`; a file without the prelude writes the import itself.
/// The runtime meaning of the literal never needs the model, so a file with no
/// such theorem reads nothing more.
fn proof_literal_imports(path: &Path, text: &str, stmts: &[Stmt]) -> Vec<PathBuf> {
    fn literals(stmts: &[Stmt], found: &mut (bool, bool)) {
        for s in stmts {
            match s {
                Stmt::Theorem(d) | Stmt::Def(d) => {
                    let mut terms = vec![d.ty.clone()];
                    terms.extend(d.params.iter().map(|(_, t)| t.clone()));
                    terms.extend(d.body.clone());
                    for mut t in terms {
                        tauto_surface::surface::walk::term(&mut t, &mut |t| match &*t.kind {
                            crate::surface::TermKind::Text(_) => found.0 = true,
                            crate::surface::TermKind::Float(_) => found.1 = true,
                            _ => {}
                        });
                    }
                }
                Stmt::Attributed { stmt, .. } => literals(std::slice::from_ref(&**stmt), found),
                _ => {}
            }
        }
    }
    let mut found = (false, false);
    literals(stmts, &mut found);
    let for_loop = tauto_surface::surface::loops::has_for(stmts);
    if (found == (false, false) && !for_loop) || sees_prelude_only_by_imports(path, text) {
        return Vec::new();
    }
    // A file that already imports the model by its path (`import "../std/text.taut"`) reads it.
    let written = |file: &str| {
        stmts.iter().any(|s| {
            matches!(s, Stmt::Import { path: rel, module: false, .. }
                if Path::new(rel).file_name().is_some_and(|n| n == file))
        })
    };
    // A `for` expands to `for_each` and `IterationControl`: the file reads the
    // modules that declare them, with no import of its own.
    [
        (found.0, "std::text", "text.taut"),
        (found.1, "std::float", "float.taut"),
        (for_loop, "std::iterator", "iterator.taut"),
        (for_loop, "std::finite_iteration", "finite_iteration.taut"),
    ]
    .into_iter()
    .filter(|(wanted, _, file)| *wanted && !written(file))
    .filter_map(|(_, module, _)| crate::stdlib::import_path(module).ok())
    .collect()
}

/// How each file writes the import of another, by the paths the files are read
/// from (`spell(here, target)`): a file of the standard library by its module
/// (`std::list`); a file of a tote that the tote of `here` lists in its
/// dependencies by the dependency's name and the file's path in it, from `src`
/// for a file of `src` (`compiler::compiler`) and from the tote's root for one
/// of an additional source (`compiler::proof::compiler`); any other file by its
/// path from the directory of `here`, quoted (`"catalog-data.taut"`,
/// `"../../myapp/src/signal.taut"`). A path that a module cannot name (a part
/// that is not a name) is written as a path too.
fn import_spellings(files: &[SourceFile], modules: &[String]) -> impl Fn(usize, usize) -> String {
    let std_root = Path::new(crate::stdlib::ROOT);
    let paths: Vec<PathBuf> = files.iter().map(|f| canonical_path(&f.path)).collect();
    let library: Vec<bool> = files
        .iter()
        .map(|f| {
            f.path.starts_with(std_root)
                || crate::stdlib::text(&f.path).is_some()
                || f.path == Path::new(crate::extract::EXTRACTED_PATH)
        })
        .collect();
    let totes: Vec<Option<(PathBuf, crate::manifest::Manifest)>> = paths
        .iter()
        .zip(&library)
        .map(|(p, &lib)| {
            if lib {
                return None;
            }
            let dir = p
                .ancestors()
                .skip(1)
                .find(|d| d.join("Tauto.eure").is_file())?;
            Some((dir.to_path_buf(), crate::manifest::read(dir).ok()?))
        })
        .collect();
    let modules = modules.to_vec();
    move |here: usize, target: usize| {
        if library[target] {
            return modules[target].clone();
        }
        if let (Some((_, from)), Some((dir, to))) = (&totes[here], &totes[target]) {
            let name = &to.package.name;
            let depends =
                from.package.name != *name && from.dependencies.iter().any(|(n, _)| n == name);
            if depends && let Some(module) = module_in_tote(&paths[target], dir) {
                let name = crate::manifest::import_name_of_tote(name);
                return format!("{name}::{module}");
            }
        }
        let dir = paths[here].parent().unwrap_or(Path::new(""));
        format!("\"{}\"", relative_path(dir, &paths[target]))
    }
}

/// The module path a dependency gives its file `file` (`proof::compiler`), the
/// tote's root being `dir`: from `src` for a file of `src`, else from `dir`.
/// `None` when a part of it is not a name.
fn module_in_tote(file: &Path, dir: &Path) -> Option<String> {
    let rel = file.strip_prefix(dir).ok()?;
    let rel = rel
        .strip_prefix(crate::manifest::DEFAULT_SOURCE)
        .ok()
        .filter(|r| r.components().count() > 0)
        .unwrap_or(rel);
    let stem = rel.with_extension("");
    let parts: Vec<&str> = stem
        .components()
        .map(|c| c.as_os_str().to_str())
        .collect::<Option<_>>()?;
    let name = |p: &&str| {
        p.chars()
            .next()
            .is_some_and(tauto_parol::unicode::is_ident_start)
            && p.chars().all(tauto_parol::unicode::is_ident_continue)
    };
    (!parts.is_empty() && parts.iter().all(name)).then(|| parts.join("::"))
}

/// The path of `to` from the directory `from`, with `/` between its parts.
fn relative_path(from: &Path, to: &Path) -> String {
    let a: Vec<_> = from.components().collect();
    let b: Vec<_> = to.components().collect();
    let common = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    std::iter::repeat_n("..".to_string(), a.len() - common)
        .chain(
            b[common..]
                .iter()
                .map(|c| c.as_os_str().to_string_lossy().into_owned()),
        )
        .collect::<Vec<_>>()
        .join("/")
}

/// A program that reads files of the tote named `std` (the standard
/// library's source, whose files are the modules `std::…` with the library's
/// privileges) beside files of another tote or of none reads each of them as
/// tauto comes with it: that tote depends on nothing, so another file beside
/// it is one that reached it, by a dependency or a path, and a text of its own
/// would hand its declarations the library's privileges. The library is
/// trusted as what tauto comes with, or as the tote being checked by itself.
fn std_tote_alone(files: &[SourceFile]) -> Result<(), Message> {
    let std_root = Path::new(crate::stdlib::ROOT);
    let extracted = Path::new(crate::extract::EXTRACTED_PATH);
    let mut std_files: Vec<(&SourceFile, PathBuf)> = Vec::new();
    let mut other: Option<&Path> = None;
    let mut named: HashMap<PathBuf, Option<String>> = HashMap::new();
    for f in files {
        if f.path.starts_with(std_root) || f.path == extracted {
            continue;
        }
        let path = canonical_path(&f.path);
        let tote = path
            .ancestors()
            .skip(1)
            .find(|d| d.join("Tauto.eure").is_file())
            .map(|d| {
                let name = named
                    .entry(d.to_path_buf())
                    .or_insert_with(|| Some(crate::manifest::read(d).ok()?.package.name));
                (d.to_path_buf(), name.clone())
            });
        match tote {
            Some((dir, Some(name))) if name == STD_TOTE => {
                let rel = path
                    .strip_prefix(&dir)
                    .map(Path::to_path_buf)
                    .unwrap_or(path);
                std_files.push((f, rel));
            }
            _ => other = other.or(Some(&f.path)),
        }
    }
    let Some(other) = other else {
        return Ok(());
    };
    let as_tauto_has_it = |f: &SourceFile, rel: &Path| {
        let rel = rel.to_string_lossy().replace('\\', "/");
        crate::stdlib::FILES
            .iter()
            .any(|(name, text)| *name == rel && *text == f.text)
    };
    match std_files.iter().find(|(f, rel)| !as_tauto_has_it(f, rel)) {
        Some((f, _)) => Err(msg!(
            "tauto-std-tote-read-by-another",
            file = f.path.display().to_string(),
            other = other.display().to_string()
        )),
        None => Ok(()),
    }
}

/// The name of the tote that is the standard library's source.
const STD_TOTE: &str = tauto_surface::surface::qualify::STD_ROOT;

/// The tote of each file, by the nearest `Tauto.eure` above it; `None` for
/// the standard library and for a file of no tote.
fn totes_of(files: &[SourceFile]) -> Vec<Option<String>> {
    let std_root = Path::new(crate::stdlib::ROOT);
    files
        .iter()
        .map(|f| {
            if f.path.starts_with(std_root) {
                return None;
            }
            let p = canonical_path(&f.path);
            p.ancestors()
                .skip(1)
                .find(|d| d.join("Tauto.eure").is_file())
                .and_then(|d| Some(crate::manifest::read(d).ok()?.package.name))
        })
        .collect()
}

/// The module of each file, in the full names of its declarations: the
/// standard library's `std::list`, a tote's file its tote's name and its
/// path in the tote (`text.src.text`), and any other file its path
/// without its extension from the directory that holds all of them
/// (`app::List`).
fn modules_of(files: &[SourceFile]) -> Vec<String> {
    module_names(files)
}

/// The module of each file, as [`Loaded`] qualified the names of its declarations.
pub fn module_names(files: &[SourceFile]) -> Vec<String> {
    tauto_parse::install();
    let std_root = Path::new(crate::stdlib::ROOT);
    let extracted = |f: &SourceFile| f.path == Path::new(crate::extract::EXTRACTED_PATH);
    let own: Vec<PathBuf> = files
        .iter()
        .filter(|f| !f.path.starts_with(std_root) && !extracted(f))
        .map(|f| canonical_path(&f.path))
        .collect();
    let mut common = own
        .first()
        .and_then(|p| p.parent())
        .map(Path::to_path_buf)
        .unwrap_or_default();
    for p in &own {
        while !p.starts_with(&common) {
            if !common.pop() {
                break;
            }
        }
    }
    files
        .iter()
        .map(|f| {
            // The extracted declarations are of no tote, wherever the
            // program is run from: their names are resolved already.
            if extracted(f) {
                return "extracted".to_string();
            }
            let (prefix, rel) = match f.path.strip_prefix(std_root) {
                Ok(rel) => (Some("std".to_string()), rel.to_path_buf()),
                Err(_) => {
                    let p = canonical_path(&f.path);
                    let tote = p.ancestors().skip(1).find_map(|d| {
                        let package = crate::manifest::read(d).ok()?.package;
                        Some((package.name, d.to_path_buf()))
                    });
                    match tote {
                        Some((name, root)) if root.join("Tauto.eure").is_file() => {
                            // The tote named `std` is the library's source:
                            // a file of it is the library's module
                            // (`std::text`), never one of the tote's own.
                            match (name == STD_TOTE)
                                .then(|| p.strip_prefix(&root).ok())
                                .flatten()
                            {
                                Some(rel) => (Some("std".to_string()), rel.to_path_buf()),
                                None => {
                                    let rel =
                                        p.strip_prefix(&root).map(Path::to_path_buf).unwrap_or(p);
                                    (Some(name), rel)
                                }
                            }
                        }
                        _ => (
                            None,
                            p.strip_prefix(&common).map(Path::to_path_buf).unwrap_or(p),
                        ),
                    }
                }
            };
            let parts: Vec<String> = prefix
                .into_iter()
                .chain(rel.iter().map(|c| c.to_string_lossy().into_owned()))
                .collect();
            let parts: Vec<&str> = parts.iter().map(String::as_str).collect();
            crate::surface::qualify::module_of(&parts)
        })
        .collect()
}

pub fn load_tote(dir: &Path) -> Result<Loaded, String> {
    tauto_parse::install();
    load_tote_in(dir).map_err(|e| e.to_string())
}

pub(crate) fn load_tote_in(dir: &Path) -> Result<Loaded, Message> {
    load_extracted_tote(tote_texts_mode(dir)?)
}

/// Reads a tote for a build, as [`load_tote`] does, preserving the
/// extraction evidence across file expansion.
pub fn load_tote_for_build(dir: &Path) -> Result<Loaded, String> {
    tauto_parse::install();
    load_tote(dir)
}

/// Reads `entry` and its imports as `load_tote` reads a tote: the proofs are
/// checked and the proof-language declarations extracted, so that a single
/// file can run code written with inductive types (`Succ`, a constructor).
/// Another file (Nib) is read as [`load`] reads it.
pub fn load_extracted(entry: &Path) -> Result<Loaded, String> {
    tauto_parse::install();
    load_extracted_in(entry).map_err(|e| e.to_string())
}

pub(crate) fn load_extracted_in(entry: &Path) -> Result<Loaded, Message> {
    if !entry
        .extension()
        .is_some_and(|e| e == "taut" || e == "tauto")
    {
        return load_in(entry);
    }
    let roots = vec![entry.to_path_buf()];
    // Only what `entry` reaches is run, and what the files it imports
    // declare is checked all the same, as `tauto check` checks it: a program
    // `check` rejects is not one `run` runs.
    let extracted = on_deep_stack(
        move || {
            crate::extract::extract_tote_in_checking_imports(&roots, |all| {
                match first_error(&load_extracted_tote(all)?) {
                    Some(error) => Err(error),
                    None => Ok(()),
                }
            })
        },
        || msg!("tauto-checking-panicked"),
    )??;
    load_extracted_tote(extracted)
}

/// The first type, effect or use error of `loaded`, in the order `tauto check`
/// reports them, at the place it is written.
fn first_error(loaded: &Loaded) -> Option<Message> {
    let mut loaded = loaded.clone();
    loaded.resolve_runtime();
    let types = crate::types::check_program(&loaded.program_with_imports());
    if let Some(e) = types.errors.first() {
        return Some(Message::from(e.to_string()));
    }
    let rows = loaded.check_rows_with_types(crate::rows::Target::Rust, &types);
    let (message, at, used) = match rows.errors.first() {
        Some(e) => (Message::from(e.message.clone()), e.span.start, false),
        None => {
            let (m, at) = crate::exec::errors_before_run(&loaded.program, &rows)
                .into_iter()
                .next()?;
            (m, at, true)
        }
    };
    let message = if used {
        msg!("nir-use-error", error = message.to_string())
    } else {
        message
    };
    Some(match loaded.locate(at) {
        Some((file, line, col)) => {
            Message::from(format!("{}:{line}:{col}: {message}", file.display()))
        }
        None => message,
    })
}

/// [`load_extracted`] with the text of some files given by `source`
/// ([`load_with_source`]): an editor's buffers, or files that are not on any
/// disk (a page built for `wasm32-unknown-unknown`). A file `source` gives is
/// not read from disk; the others are read as [`load_extracted`] reads them.
/// It runs on the caller's stack, which should be deep, as for
/// [`crate::check::check_file_sourced`].
pub fn load_extracted_with_source(entry: &Path, source: &Source<'_>) -> Result<Loaded, String> {
    tauto_parse::install();
    load_extracted_with_source_in(entry, source).map_err(|e| e.to_string())
}

pub(crate) fn load_extracted_with_source_in(
    entry: &Path,
    source: &Source<'_>,
) -> Result<Loaded, Message> {
    if !is_source_file(entry) {
        return load_with_source_in(entry, source).map_err(Message::from);
    }
    // Run on the caller's thread, as `check_file_sourced` is: `source` need
    // not be shared with another, and a target without threads has none.
    let input = crate::read::check_file_for_extraction_sourced(entry, source)?;
    load_extracted_input(input, entry)
}

/// Runs `f` on a thread with a deep stack. A thread that keeps what it expands
/// ([`keep_expansions`]) is such a thread already (the command's), and runs `f` itself, so
/// that what `f` expands is what an earlier reading of the same files left: what is kept is
/// the thread's own.
fn on_deep_stack<T: Send + 'static>(
    f: impl FnOnce() -> T + Send + 'static,
    panicked: impl FnOnce() -> Message,
) -> Result<T, Message> {
    if keeps_expansions() {
        // A panic is answered as the thread's would be: `panicked()`. What
        // this thread kept may be half made then, so it is let go.
        return std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).map_err(|_| {
            keep_expansions(false);
            keep_expansions(true);
            panicked()
        });
    }
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .map_err(|e| msg!("tauto-thread-failed", error = e.to_string()))?
        .join()
        .map_err(|_| panicked())
}

/// Keeps what the files of the programs read expand to ([`keep_expansions`]) until it is
/// dropped, then restores the thread's setting: one command that reads the same files several
/// times (the kernel's check, then the program the files make) expands them once.
pub(crate) struct KeepExpansions(bool);

thread_local! {
    /// The files read in this thread's checks that stand alone (`StandaloneFiles`).
    static STANDALONE: std::cell::RefCell<Option<HashSet<PathBuf>>> =
        const { std::cell::RefCell::new(None) };
}

/// While kept, the files given (by canonical path) are read as files of their own, checked
/// beside one another: each imports what it uses, so the declarations of one that another
/// neither imports nor is imported by are not given to the other's macros. Checked alone, it
/// would not have them; checked beside many such files, each macro of a file would otherwise
/// declare again every file before it.
pub(crate) struct StandaloneFiles(Option<HashSet<PathBuf>>);

impl StandaloneFiles {
    pub(crate) fn of(files: &[PathBuf]) -> Self {
        let set = files.iter().map(|p| canonical_path(p)).collect();
        StandaloneFiles(STANDALONE.with(|s| s.replace(Some(set))))
    }
}

impl Drop for StandaloneFiles {
    fn drop(&mut self) {
        let before = self.0.take();
        STANDALONE.with(|s| *s.borrow_mut() = before);
    }
}

/// Which of the files are standalone (`StandaloneFiles`).
fn standalone_flags(paths: &[PathBuf]) -> Vec<bool> {
    STANDALONE.with(|s| match s.borrow().as_ref() {
        Some(standalone) => paths.iter().map(|p| standalone.contains(p)).collect(),
        None => Vec::new(),
    })
}

/// For each file, the files before it that it does not import, even through the files it
/// imports, and that it would not be read with if it were checked alone: of a standalone file
/// (`StandaloneFiles`), every such file but those of the standard library; of any other file,
/// the standalone ones.
fn unseen_files(paths: &[PathBuf], imports: &[Vec<usize>], standard: &[bool]) -> Vec<Vec<usize>> {
    STANDALONE.with(|s| {
        let s = s.borrow();
        let Some(standalone) = s.as_ref() else {
            return Vec::new();
        };
        let alone: Vec<bool> = paths.iter().map(|p| standalone.contains(p)).collect();
        (0..paths.len())
            .map(|i| {
                let mut seen = vec![false; paths.len()];
                let mut stack = vec![i];
                while let Some(f) = stack.pop() {
                    if std::mem::replace(&mut seen[f], true) {
                        continue;
                    }
                    stack.extend(imports.get(f).into_iter().flatten().copied());
                }
                (0..i)
                    .filter(|&j| {
                        !seen[j]
                            && (alone[j] || alone[i] && !standard.get(j).copied().unwrap_or(true))
                    })
                    .collect()
            })
            .collect()
    })
}

impl KeepExpansions {
    pub(crate) fn on() -> Self {
        let before = keeps_expansions();
        keep_expansions(true);
        KeepExpansions(before)
    }
}

impl Drop for KeepExpansions {
    fn drop(&mut self) {
        keep_expansions(self.0);
    }
}

/// The program of `entry` as `tauto check` reads it for its Nib errors: extracted from the check
/// of `entry`, with what it imports, and not stopped by the first error of that program (the error
/// is what the check reports). `entry` that is not a source file reads as [`load`] does.
pub fn load_extracted_for_check(entry: &Path) -> Result<Loaded, String> {
    tauto_parse::install();
    if !is_source_file(entry) {
        return load(entry);
    }
    let entry = entry.to_path_buf();
    let input = on_deep_stack(
        {
            let entry = entry.clone();
            move || crate::read::check_file_timed_with_names(&entry, None, true)
        },
        || msg!("tauto-checking-panicked"),
    )
    .and_then(|r| r)
    .map_err(|e| e.to_string())?
    .5
    .ok_or_else(|| format!("{}: not a source file", entry.display()))?;
    load_extracted_input_with_imports(input, &entry).map_err(|e| e.to_string())
}

/// The program of `entry` alone as [`load_extracted_in`] reads it, extracted
/// from a check of it that has been made already.
pub(crate) fn load_extracted_input(
    input: crate::read::ExtractionInput,
    entry: &Path,
) -> Result<Loaded, Message> {
    let roots = vec![entry.to_path_buf()];
    let extracted = on_deep_stack(
        move || crate::extract::extract_input(input, &roots),
        || msg!("tauto-checking-panicked"),
    )??;
    load_extracted_tote(extracted)
}

/// The program of `entry` and of every file it imports that is not the
/// standard library's, extracted from a check of them that has been made
/// already, for `tauto check`: what `entry` imports and does not use is
/// checked all the same, so that a file whose imports do not check does not
/// check either. [`load_extracted_input`] keeps only what `entry` reaches, as
/// `run` does.
pub(crate) fn load_extracted_input_with_imports(
    input: crate::read::ExtractionInput,
    entry: &Path,
) -> Result<Loaded, Message> {
    let own = canonical_path(entry);
    let mut roots: Vec<PathBuf> = input
        .loaded
        .files
        .iter()
        .filter(|f| !f.is_standard() && is_source_file(&f.path))
        .map(|f| canonical_path(&f.path))
        .filter(|f| *f != own)
        .collect();
    let mut seen = HashSet::new();
    roots.retain(|f| seen.insert(f.clone()));
    roots.push(entry.to_path_buf());
    let extracted = on_deep_stack(
        move || crate::extract::extract_input(input, &roots),
        || msg!("tauto-checking-panicked"),
    )??;
    load_extracted_tote(extracted)
}

/// Whether the program of the tote in `dir` ([`load_tote_in`]) reads the
/// files `loaded` read for one of them: the tote's files, those of its
/// dependencies and what they import are those files, and `file` is one of
/// the tote's. The files of a tote
/// and its dependencies are in an order where each comes after what it
/// imports, so the two readings are the same program.
pub(crate) fn tote_reads_the_same(dir: &Path, file: &Path, loaded: &Loaded) -> bool {
    let Ok(order) = tote_order(dir) else {
        return false;
    };
    let file = canonical_path(file);
    let read: HashSet<PathBuf> = loaded
        .files
        .iter()
        .map(|f| canonical_path(&f.path))
        .collect();
    // The tote's own `main` reads what the file read when the file is among
    // the tote's files and every file the tote reads was read for the file:
    // what each file imports was read with it.
    order.files.iter().any(|f| canonical_path(f) == file)
        && order
            .files
            .iter()
            .all(|f| read.contains(&canonical_path(f)))
}

pub(crate) fn load_extracted_tote(extracted: crate::extract::Extracted) -> Result<Loaded, Message> {
    let mut loaded = extracted.loaded;
    loaded.extracted = Some((loaded.program.clone(), extracted.total));
    Ok(loaded)
}

pub fn tote_texts(dir: &Path) -> Result<Vec<(PathBuf, String)>, String> {
    tauto_parse::install();
    tote_texts_in(dir).map_err(|e| e.to_string())
}

fn tote_texts_in(dir: &Path) -> Result<Vec<(PathBuf, String)>, Message> {
    let extracted = tote_texts_mode(dir)?;
    Ok(vec![(
        PathBuf::from(crate::extract::EXTRACTED_PATH),
        crate::extract::write_source(&extracted.loaded)?,
    )])
}

/// The extraction of `entry` and its imports written as source, as
/// [`tote_texts`] gives a tote's: `entry` stays the entry, whose top level runs.
pub fn entry_texts(entry: &Path) -> Result<Vec<(PathBuf, String)>, String> {
    tauto_parse::install();
    let roots = vec![entry.to_path_buf()];
    let extracted = on_deep_stack(
        move || crate::extract::extract_tote_in(&roots),
        || msg!("tauto-checking-panicked"),
    )
    .map_err(|e| e.to_string())?
    .map_err(|e| e.to_string())?;
    Ok(vec![(
        PathBuf::from(crate::extract::EXTRACTED_PATH),
        crate::extract::write_source(&extracted.loaded).map_err(|e| e.to_string())?,
    )])
}

/// The files [`load_tote_in`] reads `dir` from, before their imports.
pub(crate) fn tote_files(dir: &Path) -> Result<Vec<PathBuf>, Message> {
    Ok(tote_order(dir)?.files)
}

fn tote_texts_mode(dir: &Path) -> Result<crate::extract::Extracted, Message> {
    let order = tote_order(dir)?;
    on_deep_stack(
        move || crate::extract::extract_tote_in(&order.files),
        || msg!("tauto-tote-panicked"),
    )?
}

/// Every file of the tote and its dependencies that `load_tote` reads:
/// the `.taut` and `.tauto` files, including imports, and the local paths `include_text!`
/// attempts to read. Missing include paths remain dependency inputs.
pub fn tote_inputs(dir: &Path) -> Result<Vec<PathBuf>, String> {
    tauto_parse::install();
    tote_inputs_in(dir).map_err(|e| e.to_string())
}

/// The source files of the tote in `dir` and its dependencies, in dependency
/// order, as the manifests select them; nothing is read or expanded.
pub fn tote_sources(dir: &Path) -> Result<Vec<PathBuf>, String> {
    tauto_parse::install();
    Ok(tote_order(dir).map_err(|e| e.to_string())?.files)
}

/// The totes `load_tote` reads from `dir`, by name, each with its directory
/// (canonical): the tote of `dir` and its dependencies.
pub fn tote_dirs(dir: &Path) -> Result<Vec<(String, PathBuf)>, String> {
    tauto_parse::install();
    let order = tote_order(dir).map_err(|e| e.to_string())?;
    let mut dirs: Vec<(String, PathBuf)> = order.named.into_iter().collect();
    dirs.sort();
    Ok(dirs)
}

fn tote_inputs_in(dir: &Path) -> Result<Vec<PathBuf>, Message> {
    let order = tote_order(dir)?;
    let loaded = load_roots(&order.files)?;
    let mut out: Vec<PathBuf> = loaded.files.into_iter().map(|f| f.path).collect();
    out.extend(loaded.include_inputs);
    let mut seen = HashSet::new();
    out.retain(|path| seen.insert(path.clone()));
    Ok(out)
}

/// Reads the command `name` of the tote in `tote` as the project in `project`
/// runs it: the tote's sources and its dependencies, then the command's
/// `main`. The project is the root of every trust decision: its `Tauto::lock`
/// fixes the Git dependencies and its `trust.extern` says which dependencies
/// may declare `extern` functions. A tote other than the project is read as a
/// dependency, so its own externs need the project's trust too; the project's
/// own sources are read only when the command is the project's.
pub fn load_command(project: &Path, tote: &Path, name: &str) -> Result<Loaded, String> {
    tauto_parse::install();
    load_command_in(project, tote, name).map_err(|e| e.to_string())
}

pub(crate) fn load_command_in(project: &Path, tote: &Path, name: &str) -> Result<Loaded, Message> {
    let project_manifest = crate::manifest::read(project)?;
    let manifest = crate::manifest::read(tote)?;
    let command = manifest.commands.get(name).ok_or_else(|| {
        msg!(
            "tauto-no-command",
            tote = &manifest.package.name,
            name = name
        )
        .to_string()
    })?;
    let main = command_main(tote, &manifest, name, &command.main)?;
    let canonical_project = canonical_path(project);
    let own = canonical_path(tote) == canonical_project;
    let mut order = ToteOrder {
        mains: false,
        done: HashSet::new(),
        stack: Vec::new(),
        files: Vec::new(),
        project: canonical_project,
        named: HashMap::new(),
        trust_extern: project_manifest.trust_extern,
        check_externs: true,
    };
    order.visit(tote, own)?;
    order.files.push(main.clone());
    let files = order.files;
    let extracted = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || crate::extract::extract_command(&files, &main))
        .map_err(|e| e.to_string())?
        .join()
        .map_err(|_| msg!("tauto-tote-panicked"))??;
    load_extracted_tote(extracted)
}

/// The file of the command `name` whose `main` the manifest of the tote in
/// `dir` writes: a source file of this tote, not of a tote inside it, and
/// outside its sources.
pub fn command_main(
    dir: &Path,
    manifest: &crate::manifest::Manifest,
    name: &str,
    main: &str,
) -> Result<PathBuf, String> {
    tauto_parse::install();
    command_main_in(dir, manifest, name, main).map_err(|e| e.to_string())
}

fn command_main_in(
    dir: &Path,
    manifest: &crate::manifest::Manifest,
    name: &str,
    main: &str,
) -> Result<PathBuf, Message> {
    let tote = manifest.package.name.as_str();
    let path = dir.join(main);
    if !path.is_file() {
        return Err(msg!(
            "tauto-command-main-missing",
            name = name,
            tote = tote,
            main = main,
            dir = dir.display().to_string()
        ));
    }
    let real = canonical_path(&path);
    let root = canonical_path(dir);
    let owner = real
        .ancestors()
        .skip(1)
        .find(|d| d.join("Tauto.eure").is_file());
    if !real.starts_with(&root) || owner != Some(root.as_path()) {
        return Err(msg!(
            "tauto-command-main-elsewhere",
            name = name,
            tote = tote,
            main = main
        ));
    }
    if manifest_sources(dir, manifest)?
        .iter()
        .any(|s| canonical_path(s) == real)
    {
        return Err(msg!(
            "tauto-command-main-is-source",
            name = name,
            tote = tote,
            main = main
        ));
    }
    Ok(path)
}

fn tote_order(dir: &Path) -> Result<ToteOrder, Message> {
    let mut order = ToteOrder {
        mains: true,
        done: HashSet::new(),
        stack: Vec::new(),
        files: Vec::new(),
        project: PathBuf::new(),
        named: HashMap::new(),
        trust_extern: Vec::new(),
        check_externs: true,
    };
    order.visit(dir, true)?;
    Ok(order)
}

struct ToteOrder {
    /// Whether the entry tote's `main` files are read: not when a command of
    /// it is the entry instead.
    mains: bool,
    done: HashSet<PathBuf>,
    /// The names of the totes being visited, for a cycle's message.
    stack: Vec<(PathBuf, String)>,
    files: Vec<PathBuf>,
    /// The entry tote, whose `Tauto::lock` fixes the Git dependencies.
    project: PathBuf,
    /// Where the tote of each name is: a project has one of each.
    named: HashMap<String, PathBuf>,
    /// The entry tote's `trust.extern`: the dependencies allowed to declare
    /// `extern` functions.
    trust_extern: Vec<String>,
    /// Whether a dependency's `extern`s are refused when the project does not
    /// trust it: not when only the files are wanted.
    check_externs: bool,
}

impl ToteOrder {
    fn visit(&mut self, dir: &Path, entry: bool) -> Result<(), Message> {
        let canonical = canonicalize(dir).map_err(|e| failed_at(dir.display(), e))?;
        let manifest = crate::manifest::read(dir)?;
        if let Some(at) = self.stack.iter().position(|(p, _)| *p == canonical) {
            let mut names: Vec<&str> = self.stack[at..].iter().map(|(_, n)| n.as_str()).collect();
            names.push(&self.stack[at].1);
            return Err(msg!("tauto-tote-cycle", totes = names.join(" -> ")));
        }
        if self.done.contains(&canonical) {
            return Ok(());
        }
        // A command's tote is read with the project its run belongs to.
        // The lock root is the affiliated workspace root, not necessarily
        // this tote (docs/design/workspace.md).
        if entry && self.mains {
            self.project = crate::workspace::lock_root(dir)?;
            self.trust_extern = manifest.trust_extern.clone();
        }
        match self.named.get(&manifest.package.name) {
            Some(other) if *other != canonical => {
                return Err(msg!(
                    "tauto-tote-named-twice",
                    name = &manifest.package.name,
                    first = other.display().to_string(),
                    second = canonical.display().to_string()
                ));
            }
            _ => {
                self.named
                    .insert(manifest.package.name.clone(), canonical.clone());
            }
        }
        crate::project::note(&canonical, &self.project);
        // A tote is named by its manifest, whatever its directory is called.
        self.stack
            .push((canonical.clone(), manifest.package.name.clone()));
        let mut dependencies = manifest.dependencies.clone();
        dependencies.sort();
        for (name, dependency) in &dependencies {
            let target = crate::manifest::dependency_dir(dir, name, dependency)
                .map_err(|e| failed_at(&manifest.package.name, e))?;
            let found = crate::manifest::read(&target).map_err(|e| {
                msg!(
                    "tauto-dep-of-error",
                    name = name.as_str(),
                    tote = &manifest.package.name,
                    error = e
                )
                .to_string()
            })?;
            if found.package.name != *name {
                return Err(msg!(
                    "tauto-dep-misnamed",
                    tote = &manifest.package.name,
                    name = name.as_str(),
                    dir = target.display().to_string(),
                    found = &found.package.name
                ));
            }
            self.visit(&target, false)?;
        }
        self.stack.pop();
        self.done.insert(canonical);
        // A dependency is read for what it offers a program: its sources. Its
        // additional sources (tests, proofs, examples) are the tote's own to
        // check, and a program that does not import them does not read them.
        let files = manifest_sources_of(dir, &manifest, entry)?;
        if self.check_externs && !entry && !self.trust_extern.contains(&manifest.package.name) {
            refuse_untrusted_externs(&manifest.package.name, &files)?;
        }
        // The entry (`package.entry`, `src/main.taut` when not written) is last; a
        // dependency's entry is not read.
        let main = manifest.package.entry_file(dir).map(|p| canonical_path(&p));
        let is_main = |p: &PathBuf| main.as_ref().is_some_and(|m| canonical_path(p) == *m);
        let (mut mains, others): (Vec<_>, Vec<_>) = files.into_iter().partition(is_main);
        self.files.extend(others);
        if entry && self.mains {
            // An entry written outside the sources is read all the same.
            if mains.is_empty()
                && let Some(main) = main.filter(|m| m.is_file())
            {
                mains.push(main);
            }
            self.files.extend(mains);
        }
        Ok(())
    }
}

/// An `extern` runs host code that no effect row shows, so `--allow-*` does
/// not cover it (Safe by Default). A dependency may declare one only when the
/// project names it in `trust { extern = [...] }`.
fn refuse_untrusted_externs(tote: &str, files: &[PathBuf]) -> Result<(), Message> {
    let found: Vec<String> = externs_in(files)?
        .into_iter()
        .map(|(name, path, line)| format!("  extern {name} ({}:{line})", path.display()))
        .collect();
    if found.is_empty() {
        return Ok(());
    }
    Err(msg!(
        "tauto-untrusted-externs",
        tote = tote,
        externs = found.join("\n")
    ))
}

/// The `extern` functions the sources of the tote in `dir` declare, with
/// their lines.
pub fn extern_names(dir: &Path) -> Result<Vec<(String, usize)>, String> {
    tauto_parse::install();
    extern_names_in(dir).map_err(|e| e.to_string())
}

fn extern_names_in(dir: &Path) -> Result<Vec<(String, usize)>, Message> {
    Ok(externs_in(&package_source_files(dir)?)?
        .into_iter()
        .map(|(name, _, line)| (name, line))
        .collect())
}

/// The extern types (`extern { type T }`) of the tote in `dir`, with their
/// files and lines.
pub fn extern_type_names(dir: &Path) -> Result<Vec<(String, PathBuf, usize)>, String> {
    tauto_parse::install();
    extern_type_names_in(dir).map_err(|e| e.to_string())
}

fn extern_type_names_in(dir: &Path) -> Result<Vec<(String, PathBuf, usize)>, Message> {
    let mut out = Vec::new();
    for path in package_source_files(dir)? {
        let source = std::fs::read_to_string(&path).map_err(|e| failed_at(path.display(), e))?;
        let Ok(program) = crate::surface::parse_program(&source) else {
            continue;
        };
        for stmt in &program.stmts {
            if let crate::surface::Stmt::Extern { types, .. } = stmt {
                for t in types {
                    let line = source[..(t.span.start as usize).min(source.len())]
                        .matches('\n')
                        .count()
                        + 1;
                    out.push((t.name.to_string(), path.clone(), line));
                }
            }
        }
    }
    Ok(out)
}

fn externs_in(files: &[PathBuf]) -> Result<Vec<(String, PathBuf, usize)>, Message> {
    let mut found = Vec::new();
    for path in files {
        let source = std::fs::read_to_string(path).map_err(|e| failed_at(path.display(), e))?;
        let Ok(program) = crate::read::parse_program_unexpanded(&source) else {
            continue;
        };
        for stmt in &program.stmts {
            if let crate::surface::Stmt::Extern { fns, .. } = stmt {
                for f in fns {
                    let line = source[..(f.span.start as usize).min(source.len())]
                        .matches('\n')
                        .count()
                        + 1;
                    found.push((f.name.to_string(), path.clone(), line));
                }
            }
        }
    }
    Ok(found)
}

/// Source files selected by this package's manifest, without loading imports or
/// elaborating syntax. The compiler and syntax-table generation share this list.
pub fn package_source_files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    tauto_parse::install();
    package_source_files_in(dir).map_err(|e| e.to_string())
}

fn package_source_files_in(dir: &Path) -> Result<Vec<PathBuf>, Message> {
    manifest_sources(dir, &crate::manifest::read(dir)?)
}

fn manifest_sources(
    dir: &Path,
    manifest: &crate::manifest::Manifest,
) -> Result<Vec<PathBuf>, Message> {
    manifest_sources_of(dir, manifest, true)
}

/// [`manifest_sources`], with the additional sources only when `additional`.
fn manifest_sources_of(
    dir: &Path,
    manifest: &crate::manifest::Manifest,
    additional: bool,
) -> Result<Vec<PathBuf>, Message> {
    let mut files = Vec::new();
    for source in manifest.package.source_paths() {
        if !additional && manifest.package.additional_sources.contains(&source) {
            continue;
        }
        // `.`: the tote's own directory (the library's, in the tote `std`).
        let path = match source.as_str() {
            "." => dir.to_path_buf(),
            _ => dir.join(&source),
        };
        // `src` is the default: a tote without the directory has none.
        if source == crate::manifest::DEFAULT_SOURCE && !path.exists() {
            continue;
        }
        source_files(&path, &mut files)?;
    }
    let prelude = own_prelude_dirs(dir, manifest);
    files.retain(|p| !prelude.iter().any(|d| p.starts_with(d)));
    files.sort();
    Ok(files)
}

/// The prelude's directories in the tote named `std` (`std/prelude` and
/// `std/builtin`, the files of [`crate::nibstd::PRELUDE`]). `import std::prelude::…`
/// and `import std::builtin::…` read tauto's own prelude even there
/// (`stdlib::import_target`), so the tote's copy is not one of its files:
/// reading it as well would declare every name of the prelude a second time,
/// under identities of its own that are not the prelude's, and checking the
/// tote as a whole would fail where checking any one of its files does not.
fn own_prelude_dirs(dir: &Path, manifest: &crate::manifest::Manifest) -> Vec<PathBuf> {
    if manifest.package.name == STD_TOTE {
        vec![dir.join("prelude"), dir.join("builtin")]
    } else {
        Vec::new()
    }
}

/// The `.taut` and `.tauto` files of the tote in `dir` outside its sources:
/// its proofs, examples and tests. A directory with its own `Tauto.eure` is
/// another tote, and hidden directories and `target` hold no files of the tote.
pub fn package_other_files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    tauto_parse::install();
    package_other_files_in(dir).map_err(|e| e.to_string())
}

fn package_other_files_in(dir: &Path) -> Result<Vec<PathBuf>, Message> {
    let sources: HashSet<PathBuf> = package_source_files(dir)?
        .iter()
        .map(|p| canonical_path(p))
        .collect();
    let mut files = Vec::new();
    other_files(dir, true, &mut files)?;
    let prelude = own_prelude_dirs(dir, &crate::manifest::read(dir)?);
    files.retain(|p| {
        !sources.contains(&canonical_path(p)) && !prelude.iter().any(|d| p.starts_with(d))
    });
    files.sort();
    Ok(files)
}

fn other_files(dir: &Path, root: bool, out: &mut Vec<PathBuf>) -> Result<(), Message> {
    if !root && dir.join("Tauto.eure").is_file() {
        return Ok(());
    }
    let entries = std::fs::read_dir(dir).map_err(|e| failed_at(dir.display(), e))?;
    for entry in entries {
        let path = entry.map_err(|e| failed_at(dir.display(), e))?.path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if path.is_dir() {
            if !name.starts_with('.') && name != "target" {
                other_files(&path, false, out)?;
            }
        } else if is_source_file(&path) {
            out.push(path);
        }
    }
    Ok(())
}

pub fn is_source_file(path: &Path) -> bool {
    tauto_parse::install();
    matches!(
        path.extension().and_then(|e| e.to_str()),
        Some("taut" | "tauto")
    )
}

/// The `.taut` and `.tauto` source files under `dir`; reject legacy extensions.
fn source_files(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), Message> {
    let entries = std::fs::read_dir(dir).map_err(|e| failed_at(dir.display(), e))?;
    for entry in entries {
        let path = entry.map_err(|e| failed_at(dir.display(), e))?.path();
        if path.is_dir() {
            source_files(&path, out)?;
        } else if path.extension().is_some_and(|e| e == "nib") {
            return Err(msg!(
                "tauto-program-source-extension",
                file = path.display().to_string()
            ));
        } else if is_source_file(&path) {
            out.push(path);
        }
    }
    Ok(())
}

/// The functions and theorems of the modules of the prelude (`Nat::lt`, `Eq::sym`, `List::append`):
/// every file of a program may name them.
pub(crate) fn prelude_module_names() -> &'static [String] {
    static NAMES: std::sync::OnceLock<Vec<String>> = std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        let mut names = Vec::new();
        if let Ok(p) = tauto_parse::parse_builtin_at(crate::nibstd::PRELUDE, PRELUDE_BASE) {
            names.extend(crate::surface::modules::declared(&p.stmts));
        }
        if let Ok(p) = crate::check::kernel_prelude() {
            names.extend(crate::surface::modules::declared_flat(&p.stmts));
        }
        names
    })
}

fn stmt_name(s: &Stmt) -> Option<String> {
    match s {
        Stmt::Fn(f) => Some(f.name.to_string()),
        Stmt::Theorem(t) | Stmt::Def(t) => Some(t.name.to_string()),
        Stmt::Inductive(d) => Some(d.name.to_string()),
        _ => None,
    }
}

/// The edits that write the import a name needs ([`crate::surface::qualify::MissingImport`]),
/// one for each file that declares the name, by where the name is written: after the last
/// import of the file, or at its start when it has none.
fn import_fixes(
    files: &[SourceFile],
    last_import: &[Option<u32>],
    missing: Vec<crate::surface::qualify::MissingImport>,
) -> Vec<(Span, Vec<crate::check::Fix>)> {
    missing
        .into_iter()
        .filter_map(|m| {
            let file = files.get(m.file)?;
            let fixes: Vec<crate::check::Fix> = m
                .spellings
                .iter()
                .map(|spelling| {
                    let line = format!("import {spelling}");
                    let (at, text) = match last_import.get(m.file).copied().flatten() {
                        Some(end) => (end, format!("\n{line}")),
                        None => (file.base, format!("{line}\n")),
                    };
                    crate::check::Fix {
                        title: line,
                        span: Span::new(at, at),
                        text,
                    }
                })
                .collect();
            (!fixes.is_empty()).then_some((m.at, fixes))
        })
        .collect()
}

/// What went wrong at a file or directory: `place: why`.
fn failed_at(place: impl std::fmt::Display, why: impl ToString) -> Message {
    msg!(
        "tauto-program-failed-at",
        place = place.to_string(),
        why = why.to_string()
    )
}

/// The files the tote in `dir` is read from as `load_tote_for_build` reads it,
/// in that order, with the directories of the totes they belong to: the part
/// of what a build reads that a directory's contents decide (a file added to
/// a tote's sources is read by the next build).
pub fn tote_build_order(dir: &Path) -> Result<(Vec<PathBuf>, Vec<PathBuf>), String> {
    tauto_parse::install();
    // Only the files are wanted: the build that reads them refuses untrusted
    // externs, and a result kept for the same files was made by one that did.
    let mut order = ToteOrder {
        mains: true,
        done: HashSet::new(),
        stack: Vec::new(),
        files: Vec::new(),
        project: PathBuf::new(),
        named: HashMap::new(),
        trust_extern: Vec::new(),
        check_externs: false,
    };
    order.visit(dir, true).map_err(|e| e.to_string())?;
    let mut totes: Vec<PathBuf> = order.done.into_iter().collect();
    totes.sort();
    Ok((order.files, totes))
}

/// Every path whose contents reading `loaded` depended on, besides the order
/// of a tote's files (`tote_build_order`): the files it read (the standard
/// library is part of tauto itself and is left out), the files
/// `include_text!` read or looked for, each place a `Tauto.eure` was looked
/// for above them, and each `.tauto-syntax` directory syntax tables may be
/// read from. A result made from `loaded` is the same while these are.
pub fn read_dependencies(loaded: &Loaded) -> Vec<PathBuf> {
    tauto_parse::install();
    let mut out = reads_of(
        &loaded.files,
        &loaded.included,
        &loaded.include_inputs,
        &loaded.syntax_dirs,
    );
    out.extend(loaded.reads.iter().cloned());
    out.sort();
    out.dedup();
    out
}

fn reads_of(
    files: &[SourceFile],
    included: &[PathBuf],
    include_inputs: &[PathBuf],
    syntax_dirs: &[PathBuf],
) -> Vec<PathBuf> {
    let std_root = Path::new(crate::stdlib::ROOT);
    let files: Vec<&Path> = files
        .iter()
        .map(|f| f.path.as_path())
        .filter(|p| !p.starts_with(std_root))
        .collect();
    let mut out: Vec<PathBuf> = files.iter().map(|p| canonical_path(p)).collect();
    out.extend(included.iter().cloned());
    out.extend(include_inputs.iter().cloned());
    for path in &files {
        for dir in canonical_path(path).ancestors().skip(1) {
            out.push(dir.join("Tauto.eure"));
        }
    }
    for dir in syntax_dirs {
        if dir.starts_with(std_root) {
            continue;
        }
        for d in canonical_path(dir).ancestors() {
            out.push(d.join(".tauto-syntax"));
        }
    }
    out.sort();
    out.dedup();
    out
}

/// Settles the field reads whose names alone do not tell whether they are
/// seen ([`crate::surface::qualify::sealed_visibility_typed`]) by the type the
/// checker gives the value read: `x.value` is sealed where `x` is of the type
/// another file declares without `pub(open)`, whatever other type has a field
/// of that name. The types are checked only where there is such a read.
pub(crate) fn sealed_by_types(
    program: &Program,
    bindings: &tauto_surface::resolve::Resolver,
    unsure: Vec<crate::surface::qualify::SealedRead>,
) -> Vec<(tauto_message::Message, tauto_parol::Span)> {
    if unsure.is_empty() {
        return Vec::new();
    }
    let report = crate::types::check_program(program);
    let declarations = bindings.declarations();
    unsure
        .into_iter()
        .filter_map(|read| {
            // The owner and each sealed type are compared as declarations:
            // two types displayed alike are two types.
            let owner = report.field_owners.get(&read.span)?.as_global()?;
            read.sealed
                .into_iter()
                .find(|(ty, _)| declarations.get(ty) == Some(owner))
                .map(|(_, message)| (message, read.span))
        })
        .collect()
}

/// The `exports` list of a file entry's build, with the totes it reads: the
/// `exports` of the tote that holds `entry` (the nearest `Tauto.eure` above
/// it) and the `added` names (`--export`). `None` when neither names anything.
fn file_export_list(
    entry: &Path,
    added: &[String],
) -> Result<Option<(Vec<String>, Vec<(String, PathBuf)>)>, String> {
    let tote = crate::manifest::enclosing_tote_dir(entry);
    let mut list: Option<Vec<String>> = match &tote {
        Some(dir) => crate::manifest::load(dir).map_err(|e| e.to_string())?.exports,
        None => None,
    };
    if !added.is_empty() {
        list.get_or_insert_with(Vec::new).extend(added.iter().cloned());
    }
    let Some(list) = list else { return Ok(None) };
    let totes = match &tote {
        Some(dir) => tote_dirs(dir)?,
        None => Vec::new(),
    };
    Ok(Some((list, totes)))
}

/// The functions a file entry's build exports ([`file_export_list`]), each
/// `TOTE::*` read against the totes that tote reads.
pub fn select_file_exports(
    loaded: &Loaded,
    entry: &Path,
    added: &[String],
) -> Result<Option<tauto_nibcheck::lower::ExportSelection>, String> {
    match file_export_list(entry, added)? {
        Some((list, totes)) => tauto_nibcheck::lower::select_exports(loaded, &list, &totes, entry.parent()).map(Some),
        None => Ok(None),
    }
}

/// The sources of the totes a `TOTE::*` of `list` names, read for a file
/// entry's build though the entry imports none of them: a dependency of the
/// entry's tote is exported as when it is imported. The entry tote's own
/// entry (`src/main.taut`) and a dependency's entry are not among them.
fn star_tote_sources(
    entry: &Path,
    list: &[String],
    totes: &[(String, PathBuf)],
) -> Result<Vec<PathBuf>, String> {
    let named: Vec<&PathBuf> = list
        .iter()
        .filter_map(|e| e.strip_suffix("::*"))
        .filter_map(|t| totes.iter().find(|(n, _)| n == t).map(|(_, d)| d))
        .collect();
    let Some(dir) = crate::manifest::enclosing_tote_dir(entry) else { return Ok(Vec::new()) };
    if named.is_empty() {
        return Ok(Vec::new());
    }
    let mut order = ToteOrder {
        mains: false,
        done: HashSet::new(),
        stack: Vec::new(),
        files: Vec::new(),
        project: PathBuf::new(),
        named: HashMap::new(),
        // A dependency's `extern`s need the entry tote's trust, as when
        // the entry imports it.
        trust_extern: crate::manifest::read(&dir).map_err(|e| e.to_string())?.trust_extern,
        check_externs: true,
    };
    order.visit(&dir, true).map_err(|e| e.to_string())?;
    let entry = canonical_path(entry);
    Ok(order
        .files
        .into_iter()
        .filter(|f| {
            let f = canonical_path(f);
            if f == entry {
                return false;
            }
            // A file belongs to the tote of the innermost directory holding it.
            let owner = totes
                .iter()
                .filter(|(_, d)| f.starts_with(d))
                .max_by_key(|(_, d)| d.components().count())
                .map(|(_, d)| d);
            owner.is_some_and(|o| named.contains(&o))
        })
        .collect())
}

/// [`load_extracted`] for a build that exports functions: a function of an
/// imported file that an `exports` entry names is kept though nothing the
/// entry runs calls it, and so is each `pub` function of a `TOTE::*`.
pub fn load_extracted_exporting(entry: &Path, added: &[String]) -> Result<Loaded, String> {
    tauto_parse::install();
    let Some((list, totes)) = file_export_list(entry, added)? else {
        return load_extracted(entry);
    };
    if !is_source_file(entry) {
        return load_extracted(entry);
    }
    let roots = vec![entry.to_path_buf()];
    let read = star_tote_sources(entry, &list, &totes)?;
    let extracted = on_deep_stack(
        move || {
            crate::extract::extract_tote_in_checking_imports_exporting(
                &roots,
                &read,
                &list,
                &totes,
                |all| match first_error(&load_extracted_tote(all)?) {
                    Some(error) => Err(error),
                    None => Ok(()),
                },
            )
        },
        || msg!("tauto-checking-panicked"),
    )
    .and_then(|r| r)
    .and_then(load_extracted_tote)
    .map_err(|e| e.to_string())?;
    Ok(extracted)
}
