//! A Nib program of several files (`docs/design/self-host.md`). The files are read
//! in an order that puts what a file imports before it, each one with spans
//! starting where the one before ended, and their statements are joined into
//! one [`Program`] consumed by the checkers and `tauto-eval`.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use tauto_message::msg;

mod expansions;
pub mod include;
pub mod inputs;
pub use expansions::{keep_expansions, keeps_expansions};
pub use inputs::Inputs;

use tauto_parol::Span;

use crate::macros::{Expansion, origin::SpanMap};
use crate::surface::{PRELUDE_BASE, Program, Stmt, parse_program_unresolved_at};

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: PathBuf,
    pub base: u32,
    pub text: String,
}

pub struct Loaded {
    pub program: Program,
    pub files: Vec<SourceFile>,
    pub per_file: Vec<Vec<Stmt>>,
    /// The same before the classes are expanded for running: what the
    /// kernel reads, which has classes of its own.
    pub kernel_files: Vec<Vec<Stmt>>,
    pub spans: SpanMap,
    pub expansions: Vec<Expansion>,
    pub warnings: Vec<(String, Span)>,
    pub fixes: Vec<(Span, crate::check::Fix)>,
    pub literals: Vec<crate::syntax::LiteralUse>,
    pub registrations: Vec<crate::syntax::Registration>,
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
    extracted: Option<(Program, HashSet<String>)>,
}

#[derive(Debug, Clone, Default)]
pub struct SourceMap {
    pub files: Vec<SourceFile>,
    pub spans: SpanMap,
}

impl SourceMap {
    pub fn locate(&self, offset: u32) -> Option<(&Path, usize, usize)> {
        locate(&self.files, &self.spans, offset)
    }
}

fn locate<'a>(
    files: &'a [SourceFile],
    spans: &SpanMap,
    mut offset: u32,
) -> Option<(&'a Path, usize, usize)> {
    while let Some((written, _)) = spans.origin(offset) {
        offset = written;
    }
    let file = files.iter().rev().find(|f| f.base <= offset)?;
    let at = (offset - file.base) as usize;
    let before = file.text.get(..at)?;
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    Some((&file.path, line, col))
}

impl Loaded {
    /// Effect checking with kernel-checked extraction evidence, when this is
    /// still the exact program produced by the extraction loader.
    pub fn check_rows(&self, javascript: bool) -> crate::rows::RowReport {
        match &self.extracted {
            Some((program, total)) if program == &self.program => {
                crate::rows::check_program_rows_trusted(&self.program, total, javascript)
            }
            _ if javascript => crate::rows::check_program_rows_javascript(&self.program),
            _ => crate::rows::check_program_rows(&self.program),
        }
    }
    /// Effect checking using an existing type report. Extraction evidence is
    /// valid only for the complete program checked by the extraction loader.
    pub fn check_rows_with_types(
        &self,
        javascript: bool,
        types: &crate::types::TypeReport,
    ) -> crate::rows::RowReport {
        match &self.extracted {
            Some((program, total)) if program == &self.program => {
                crate::rows::check_program_rows_trusted_with_types(
                    &self.program,
                    total,
                    javascript,
                    types,
                )
            }
            _ if javascript => {
                crate::rows::check_program_rows_javascript_with_types(&self.program, types)
            }
            _ => crate::rows::check_program_rows_with_types(&self.program, types),
        }
    }
    /// Effect checking of `wrapped`, the program with its top-level
    /// statements run under `host_run`. The wrapper changes no declaration's
    /// recursion, so the extraction evidence still holds when `wrapped` is
    /// exactly the wrapping of the extracted program.
    pub fn check_wrapped_rows_with_types(
        &self,
        wrapped: &Program,
        javascript: bool,
        types: &crate::types::TypeReport,
    ) -> crate::rows::RowReport {
        match &self.extracted {
            Some((program, total))
                if program == &self.program
                    && crate::host::wrap(program).as_ref() == Some(wrapped) =>
            {
                crate::rows::check_program_rows_trusted_with_types(
                    wrapped, total, javascript, types,
                )
            }
            _ if javascript => {
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
    load_with_text(entry, None)
}

pub fn load_with_text(entry: &Path, text: Option<&str>) -> Result<Loaded, String> {
    let given = text.and_then(|t| Some((entry.canonicalize().ok()?, t.to_string())));
    load_with_source(entry, &|path: &Path| match &given {
        Some((own, text)) if own == path => Some(Ok(text.clone())),
        _ => None,
    })
}

/// Where a file's text comes from when it is not read from disk: `Some` is the
/// text (or why it cannot be had) of the file at this canonical path, `None`
/// leaves the file to the disk. An editor's unsaved buffers, and the files an
/// incremental checker holds, are given this way.
pub type Source<'a> = dyn Fn(&Path) -> Option<Result<String, String>> + 'a;

/// [`load`] with the text of some files given by `source`. A file that is
/// given need not exist on disk; its path is then taken as written, made
/// absolute and without `.` and `..`.
pub fn load_with_source(entry: &Path, source: &Source<'_>) -> Result<Loaded, String> {
    crate::surface::parsed::begin_reading();
    let mut order = Order {
        done: HashSet::new(),
        stack: Vec::new(),
        files: Vec::new(),
        source,
    };
    order.visit(entry)?;
    crate::phases::mark("read");
    assemble(order.files, entry.parent(), true, source)
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
    let source = given(entry, text);
    crate::surface::parsed::begin_reading();
    let texts = inputs::order(entry, &source)?;
    crate::phases::mark("read");
    let stage = expand_stage(texts.clone(), entry.parent(), true, &source, None)?;
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
    crate::surface::parsed::begin_reading();
    inputs::current(entry, &given(entry, text), before)
}

/// The program of the first `n` of the files `inputs` holds (of the program of `entry`), as
/// [`load`] reads it.
pub fn load_first(entry: &Path, inputs: &Inputs, n: usize) -> Result<Loaded, String> {
    let files = inputs.files[..n.min(inputs.files.len())].to_vec();
    let held = files.clone();
    assemble(files, entry.parent(), true, &move |p: &Path| {
        held.iter()
            .find(|(q, _)| canonical_path(q) == p)
            .map(|(_, t)| Ok(t.clone()))
    })
}

fn given(entry: &Path, text: Option<&str>) -> impl Fn(&Path) -> Option<Result<String, String>> {
    let given = text.and_then(|t| Some((entry.canonicalize().ok()?, t.to_string())));
    move |path: &Path| match &given {
        Some((own, text)) if own == path => Some(Ok(text.clone())),
        _ => None,
    }
}

/// [`load`] of several entries as one program: each file once, a file
/// before the ones that import it.
pub fn load_roots(entries: &[PathBuf]) -> Result<Loaded, String> {
    let mut order = Order {
        done: HashSet::new(),
        stack: Vec::new(),
        files: Vec::new(),
        source: &|_| None,
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
    assemble(files, None, true, &|_| None)
}

/// Reads the files, in this order, as one program. An `import` in them is
/// not followed.
pub fn load_files(paths: &[PathBuf]) -> Result<Loaded, String> {
    let mut files = Vec::new();
    for path in paths {
        let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        files.push((path.clone(), text));
    }
    assemble(files, None, false, &|_| None)
}

/// Expands already ordered runtime source texts, retaining each file's macro
/// stage and source positions. Imports must have been resolved by the loader
/// and removed by extraction; this reader does not follow or reorder them.
pub fn load_texts(texts: Vec<(PathBuf, String)>) -> Result<Loaded, String> {
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
    if let Ok(p) = path.canonicalize() {
        return p;
    }
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

impl Order<'_> {
    /// `shown` is the path as written (the one messages use); the file is
    /// told apart from others by its canonical path.
    fn visit(&mut self, shown: &Path) -> Result<(), String> {
        let given = match crate::stdlib::text(shown) {
            Some(text) => Some(Ok(text.to_string())),
            None => (self.source)(&canonical_path(shown)),
        };
        let path = match &given {
            Some(_) if crate::stdlib::text(shown).is_some() => shown.to_path_buf(),
            Some(_) => canonical_path(shown),
            None => shown
                .canonicalize()
                .map_err(|e| format!("{}: {e}", shown.display()))?,
        };
        if self.done.contains(&path) {
            return Ok(());
        }
        if self.stack.contains(&path) {
            return Err(format!(
                "{}: imports itself through a cycle",
                shown.display()
            ));
        }
        let text = match given {
            Some(text) => text.map_err(|e| format!("{}: {e}", shown.display()))?,
            None => {
                std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", shown.display()))?
            }
        };
        let program = parse_program_unresolved_at(&text, 0)
            .map_err(|e| parse_error(&shown.display().to_string(), &text, 0, &e))?;
        self.stack.push(path.clone());
        for stmt in &program.stmts {
            if let Stmt::Import {
                path: rel, module, ..
            } = stmt
            {
                let target = crate::stdlib::import_target(shown, rel, *module)
                    .map_err(|e| format!("{}: {e}", shown.display()))?;
                self.visit(&target)?;
            }
        }
        self.stack.pop();
        self.done.insert(path);
        self.files.push((shown.to_path_buf(), text));
        Ok(())
    }
}

/// `message at byte N` from parsing `text` (spans from `base`) becomes
/// `path:line:col: message`.
fn parse_error(path: &str, text: &str, base: u32, error: &str) -> String {
    let at = error
        .rsplit_once(" at byte ")
        .and_then(|(m, n)| Some((m, n.parse::<u32>().ok()?.checked_sub(base)?)));
    match at {
        Some((message, offset)) => {
            let before = text.get(..offset as usize).unwrap_or(text);
            let line = before.matches('\n').count() + 1;
            let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
            format!("{path}:{line}:{col}: {message}")
        }
        None => format!("{path}: {error}"),
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
) -> Result<Loaded, String> {
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
) -> Result<Loaded, String> {
    let stage = expand_stage(texts, root, imports, source, graph)?;
    finish(stage, generated, graph)
}

/// The files read and their macros expanded: what [`finish`] makes a [`Loaded`] of.
struct Stage {
    files: Vec<SourceFile>,
    imported: Vec<Vec<PathBuf>>,
    included: include::Included,
    qualified: Vec<(String, Span)>,
    /// The names one import would make seen, and where each file's last import ends.
    missing: Vec<crate::surface::qualify::MissingImport>,
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
    out: crate::macros::Output,
    syntax_dirs: Vec<PathBuf>,
}

fn expand_stage(
    texts: Vec<(PathBuf, String)>,
    root: Option<&Path>,
    imports: bool,
    source: &Source<'_>,
    graph: Option<&HashMap<PathBuf, Vec<PathBuf>>>,
) -> Result<Stage, String> {
    let imports_given = imports || graph.is_some();
    let mut files = Vec::new();
    let mut imported: Vec<Vec<PathBuf>> = Vec::new();
    // Each file's imports as written: the imported file, how it is written, its list and span.
    #[allow(clippy::type_complexity)]
    let mut written: Vec<Vec<(PathBuf, String, Option<Vec<(String, Span)>>, Span)>> = Vec::new();
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
        let mut program = parse_program_unresolved_at(&text, base)
            .map_err(|e| parse_error(&shown(&path), &text, base, &e))?;
        include::read_includes(&mut program.stmts, &path, source, &mut included);
        let mut stmts = Vec::new();
        imported.push(Vec::new());
        last_import.push(None);
        written.push(Vec::new());
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
                    written
                        .last_mut()
                        .unwrap()
                        .push((target.clone(), spelling, names.clone(), *span));
                    imported.last_mut().unwrap().push(target);
                    continue;
                }
                Stmt::Import { .. } => {
                    return Err(format!(
                        "{}: a tote does not import; list the tote in dependencies",
                        shown(&path)
                    ));
                }
                _ => {}
            }
            stmts.push(stmt);
        }
        if let Some(graph) = graph {
            *imported.last_mut().unwrap() = graph
                .get(&path)
                .into_iter()
                .flatten()
                .map(|p| match crate::stdlib::text(p) {
                    Some(_) => p.clone(),
                    None => canonical_path(p),
                })
                .collect();
        }
        per_file.push(stmts);
        let next = base as u64 + text.len() as u64 + 1;
        if next >= PRELUDE_BASE as u64 {
            return Err(msg!("tauto-program-too-large").to_string());
        }
        files.push(SourceFile { path, base, text });
        base = next as u32;
    }
    crate::phases::mark("parse");
    let dirs: Vec<PathBuf> = files
        .iter()
        .filter_map(|f: &SourceFile| f.path.parent().map(Path::to_path_buf))
        .collect();
    let syntax_dirs = dirs.clone();
    // Each name means one declaration before the macros run, so that a
    // macro's function means what its file means, and again after, for what
    // the macros declared.
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
    let imports = imports_given.then_some(imports.as_slice());
    // The files read again to run (`graph`) are held to the lists where they were checked.
    let lists: Vec<Vec<crate::surface::qualify::ImportList>> = written
        .into_iter()
        .map(|file| {
            file.into_iter()
                .filter(|_| graph.is_none())
                .map(
                    |(target, spelling, names, span)| crate::surface::qualify::ImportList {
                        target: paths.iter().position(|p| *p == target),
                        spelling,
                        names,
                        span,
                    },
                )
                .collect()
        })
        .collect();
    let mut per_file = per_file;
    let below = totes_below(&files);
    let bare = without_prelude(&files);
    let quoted = crate::surface::qualify::Quoted::default();
    let (qualified, seeing, missing) = {
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
    let out = crate::syntax::with_search_dirs(dirs, || {
        expansions::expand(per_file, seeing, modules.clone(), time_limits)
    });
    tauto_kernel::check::Kernel::new().set_file_limit(None);
    crate::phases::mark("expand");
    Ok(Stage {
        files,
        imported,
        included,
        qualified,
        missing,
        last_import,
        modules,
        imports: imports.map(<[_]>::to_vec),
        lists,
        quoted,
        below,
        bare,
        out,
        syntax_dirs,
    })
}

/// The expanded files resolved and joined into one program.
fn finish(
    stage: Stage,
    generated: &HashMap<PathBuf, Vec<bool>>,
    graph: Option<&HashMap<PathBuf, Vec<PathBuf>>>,
) -> Result<Loaded, String> {
    let Stage {
        files,
        imported,
        mut included,
        mut qualified,
        mut missing,
        last_import,
        modules,
        imports,
        lists,
        quoted,
        below,
        bare,
        mut out,
        syntax_dirs,
    } = stage;
    let imports = imports.as_deref();
    for (file, stmts) in files.iter().zip(&mut out.files) {
        if let Some(keep) = generated.get(&file.path) {
            let mut made = keep.iter();
            stmts.retain(|s| !crate::extract::macro_made(s) || *made.next().unwrap_or(&true));
        }
    }
    let models = crate::surface::qualify::split_models(&mut out.files, &modules, imports);
    let (after, more, list_fixes) = crate::surface::qualify::files_after_macros_listed(
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
    missing.extend(more);
    out.fixes
        .extend(import_fixes(&files, &last_import, missing));
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
    if graph.is_none() {
        qualified.extend(crate::surface::qualify::sealed_visibility(
            &out.files, &modules,
        ));
    } else {
        // The text in the installed language is matched, because `tauto-surface`
        // does not give these errors as messages with an id.
        qualified.retain(|(m, _)| !m.contains("is already declared as"));
    }
    out.stmts = out.files.concat();
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
    let (mut stmts, mut errors) = crate::surface::modules::resolve_with(
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
    let kernel_files = per_file.clone();
    crate::phases::mark("resolve");
    crate::types::expand_loaded(&mut program, &mut per_file, 1 << 30);
    // The kernel reads `decreasing_by` as written; a program that runs does not.
    crate::surface::walk::strip_proofs_in(&mut program.stmts);
    let wrong = crate::registered::validate(&program, &out.registrations);
    program.errors.extend(wrong);
    crate::phases::mark("classes");
    Ok(Loaded {
        program,
        files,
        per_file,
        kernel_files,
        spans: out.spans,
        expansions: out.expansions,
        warnings: out.warnings,
        fixes: out.fixes,
        literals: out.literals,
        registrations: out.registrations,
        included: included.files,
        include_inputs: included.inputs,
        imports: imported,
        syntax_dirs,
        extracted: None,
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
/// `prelude = false`, but a file of the prelude itself (`std/prelude/Std.taut`).
fn without_prelude(files: &[SourceFile]) -> Vec<bool> {
    let std_root = Path::new(crate::stdlib::ROOT);
    files
        .iter()
        .map(|f| {
            // The prelude's own files are the prelude.
            let prelude = crate::nibstd::PRELUDE_FILES
                .iter()
                .any(|(p, t)| f.path.ends_with(p) && *t == f.text);
            f.path.starts_with(std_root)
                || !prelude && {
                    let path = canonical_path(&f.path);
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
        })
        .collect()
}

/// How each file writes the import of another, by the paths the files are read
/// from (`spell(here, target)`): a file of the standard library by its module
/// (`std::List`); a file of a tote that the tote of `here` lists in its
/// dependencies by the dependency's name and the file's path in it, from `src`
/// for a file of `src` (`compiler::compiler`) and from the tote's root for one
/// of an additional source (`compiler::proof::compiler`); any other file by its
/// path from the directory of `here`, quoted (`"catalog-data.taut"`,
/// `"../../bikkuri/src/signal.taut"`). A path that a module cannot name (a part
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
            let dir = p.ancestors().skip(1).find(|d| d.join("Tauto.eure").is_file())?;
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
            let depends = from.package.name != *name
                && from.dependencies.iter().any(|(n, _)| n == name);
            if depends && let Some(module) = module_in_tote(&paths[target], dir) {
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
        p.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
            && p.chars().all(|c| c.is_alphanumeric() || c == '_')
    };
    (!parts.is_empty() && parts.iter().all(name)).then(|| parts.join("::"))
}

/// The path of `to` from the directory `from`, with `/` between its parts.
fn relative_path(from: &Path, to: &Path) -> String {
    let a: Vec<_> = from.components().collect();
    let b: Vec<_> = to.components().collect();
    let common = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    std::iter::repeat_n("..".to_string(), a.len() - common)
        .chain(b[common..].iter().map(|c| c.as_os_str().to_string_lossy().into_owned()))
        .collect::<Vec<_>>()
        .join("/")
}

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
/// standard library's `std::List`, a tote's file its tote's name and its
/// path in the tote (`text.src.text`), and any other file its path
/// without its extension from the directory that holds all of them
/// (`app::List`).
fn modules_of(files: &[SourceFile]) -> Vec<String> {
    module_names(files)
}

/// The module of each file, as [`Loaded`] qualified the names of its declarations.
pub fn module_names(files: &[SourceFile]) -> Vec<String> {
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
                        let name = crate::manifest::read(d).ok()?.package.name;
                        Some((name, d.to_path_buf()))
                    });
                    match tote {
                        Some((name, root)) if root.join("Tauto.eure").is_file() => {
                            let rel = p.strip_prefix(&root).map(Path::to_path_buf).unwrap_or(p);
                            (Some(name), rel)
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
    load_extracted_tote(tote_texts_mode(dir, true)?)
}

/// Reads a build manifest without requiring its package name to match its
/// directory, preserving the extraction evidence across file expansion.
pub fn load_tote_for_build(dir: &Path) -> Result<Loaded, String> {
    load_extracted_tote(tote_texts_mode(dir, false)?)
}

/// Reads `entry` and its imports as `load_tote` reads a tote: the proofs are
/// checked and the proof-language declarations extracted, so that a single
/// file can run code written with inductive types (`Succ`, a constructor).
/// Another file (Nib) is read as [`load`] reads it.
pub fn load_extracted(entry: &Path) -> Result<Loaded, String> {
    if !entry
        .extension()
        .is_some_and(|e| e == "taut" || e == "tauto")
    {
        return load(entry);
    }
    let roots = vec![entry.to_path_buf()];
    let extracted = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || crate::extract::extract_tote(&roots))
        .map_err(|e| e.to_string())?
        .join()
        .map_err(|_| "checking panicked".to_string())??;
    load_extracted_tote(extracted)
}

fn load_extracted_tote(extracted: crate::extract::Extracted) -> Result<Loaded, String> {
    // Read as the check read the files: with their imports, so that a name
    // of a dependency never comes to mean a declaration of its dependent.
    let mut loaded = assemble_keeping(
        extracted.texts,
        None,
        true,
        &|_| None,
        &extracted.generated,
        Some(&extracted.imports),
    )?;
    // The files read again to run are only some of those checked, and
    // `extracted.taut` is in no directory: the run looks for tables where
    // every checked file is.
    for dir in extracted.syntax_dirs {
        if !loaded.syntax_dirs.contains(&dir) {
            loaded.syntax_dirs.push(dir);
        }
    }
    loaded
        .program
        .errors
        .extend(crate::extract::dependent_visibility(
            &loaded,
            &extracted.protected,
        ));
    loaded.extracted = Some((loaded.program.clone(), extracted.total));
    Ok(loaded)
}

pub fn tote_texts(dir: &Path) -> Result<Vec<(PathBuf, String)>, String> {
    tote_texts_mode(dir, false).map(|extracted| extracted.texts)
}

fn tote_texts_mode(dir: &Path, directory_names: bool) -> Result<crate::extract::Extracted, String> {
    let order = tote_order(dir, directory_names)?;
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || crate::extract::extract_tote(&order.files))
        .map_err(|e| e.to_string())?
        .join()
        .map_err(|_| "tote checking panicked".to_string())?
}

/// Every file of the tote and its dependencies that `load_tote` reads:
/// the `.taut` and `.tauto` files, including imports, and the local paths `include_text!`
/// attempts to read. Missing include paths remain dependency inputs.
pub fn tote_inputs(dir: &Path) -> Result<Vec<PathBuf>, String> {
    let order = tote_order(dir, false)?;
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
        directory_names: false,
        mains: false,
        done: HashSet::new(),
        stack: Vec::new(),
        files: Vec::new(),
        project: canonical_project,
        named: HashMap::new(),
        trust_extern: project_manifest.trust_extern,
    };
    order.visit(tote, own)?;
    order.files.push(main);
    let files = order.files;
    let extracted = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || crate::extract::extract_tote(&files))
        .map_err(|e| e.to_string())?
        .join()
        .map_err(|_| msg!("tauto-tote-panicked").to_string())??;
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
    let tote = manifest.package.name.as_str();
    let path = dir.join(main);
    if !path.is_file() {
        return Err(msg!(
            "tauto-command-main-missing",
            name = name,
            tote = tote,
            main = main,
            dir = dir.display().to_string()
        )
        .to_string());
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
        )
        .to_string());
    }
    if manifest_sources(dir, manifest)?
        .iter()
        .any(|s| canonical_path(s) == real)
    {
        return Err(format!(
            "the command {name} of {tote} runs {main}, which is one of its sources; \
             a command's main is outside the sources, so that the tote's dependents never read it"
        ));
    }
    Ok(path)
}

fn tote_order(dir: &Path, directory_names: bool) -> Result<ToteOrder, String> {
    let mut order = ToteOrder {
        directory_names,
        mains: true,
        done: HashSet::new(),
        stack: Vec::new(),
        files: Vec::new(),
        project: PathBuf::new(),
        named: HashMap::new(),
        trust_extern: Vec::new(),
    };
    order.visit(dir, true)?;
    Ok(order)
}

struct ToteOrder {
    // Named `run --tote` keeps its directory convention; a build may use a
    // manifest in any directory (including an external build system's scratch path).
    directory_names: bool,
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
}

impl ToteOrder {
    fn visit(&mut self, dir: &Path, entry: bool) -> Result<(), String> {
        let canonical = dir
            .canonicalize()
            .map_err(|e| format!("{}: {e}", dir.display()))?;
        let manifest = crate::manifest::read(dir)?;
        if let Some(at) = self.stack.iter().position(|(p, _)| *p == canonical) {
            let mut names: Vec<&str> = self.stack[at..].iter().map(|(_, n)| n.as_str()).collect();
            names.push(&self.stack[at].1);
            return Err(msg!("tauto-tote-cycle", totes = names.join(" -> ")).to_string());
        }
        if self.done.contains(&canonical) {
            return Ok(());
        }
        // A command's tote is read with the project its run belongs to.
        if entry && self.mains {
            self.project = canonical.clone();
            self.trust_extern = manifest.trust_extern.clone();
        }
        match self.named.get(&manifest.package.name) {
            Some(other) if *other != canonical => {
                return Err(msg!(
                    "tauto-tote-named-twice",
                    name = &manifest.package.name,
                    first = other.display().to_string(),
                    second = canonical.display().to_string()
                )
                .to_string());
            }
            _ => {
                self.named
                    .insert(manifest.package.name.clone(), canonical.clone());
            }
        }
        crate::project::note(&canonical, &self.project);
        let directory_name = canonical.file_name().and_then(|n| n.to_str()).unwrap_or("");
        // A dependency is named by its manifest, wherever it is checked out.
        if self.directory_names && entry && manifest.package.name != directory_name {
            // A directory such as `.` is shown by its own name, which is
            // what has to match.
            return Err(format!(
                "the tote in {} ({}) is named {} in its Tauto.eure, but a tote's directory \
                 has the name of its package; rename the directory to {} or set \
                 `name = \"{directory_name}\"` in its Tauto.eure",
                dir.display(),
                canonical.display(),
                manifest.package.name,
                manifest.package.name
            ));
        }
        self.stack
            .push((canonical.clone(), manifest.package.name.clone()));
        let mut dependencies = manifest.dependencies.clone();
        dependencies.sort();
        for (name, dependency) in &dependencies {
            let target = crate::manifest::dependency_dir(dir, name, dependency)
                .map_err(|e| format!("{}: {e}", manifest.package.name))?;
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
                )
                .to_string());
            }
            self.visit(&target, false)?;
        }
        self.stack.pop();
        self.done.insert(canonical);
        let files = manifest_sources(dir, &manifest)?;
        if !entry && !self.trust_extern.contains(&manifest.package.name) {
            refuse_untrusted_externs(&manifest.package.name, &files)?;
        }
        // The entry module is last; a dependency's entry is not read.
        let is_main = |p: &PathBuf| is_source_file(p) && p.file_stem().is_some_and(|n| n == "main");
        let (mains, others): (Vec<_>, Vec<_>) = files.into_iter().partition(is_main);
        self.files.extend(others);
        if entry && self.mains {
            self.files.extend(mains);
        }
        Ok(())
    }
}

/// An `extern` runs host code that no effect row shows, so `--allow-*` does
/// not cover it (Safe by Default). A dependency may declare one only when the
/// project names it in `trust { extern = [...] }`.
fn refuse_untrusted_externs(tote: &str, files: &[PathBuf]) -> Result<(), String> {
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
    )
    .to_string())
}

/// The `extern` functions the sources of the tote in `dir` declare, with
/// their lines.
pub fn extern_names(dir: &Path) -> Result<Vec<(String, usize)>, String> {
    Ok(externs_in(&package_source_files(dir)?)?
        .into_iter()
        .map(|(name, _, line)| (name, line))
        .collect())
}

/// The extern types (`extern { type T }`) of the tote in `dir`, with their
/// files and lines.
pub fn extern_type_names(dir: &Path) -> Result<Vec<(String, PathBuf, usize)>, String> {
    let mut out = Vec::new();
    for path in package_source_files(dir)? {
        let source =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
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
                    out.push((t.name.clone(), path.clone(), line));
                }
            }
        }
    }
    Ok(out)
}

fn externs_in(files: &[PathBuf]) -> Result<Vec<(String, PathBuf, usize)>, String> {
    let mut found = Vec::new();
    for path in files {
        let source =
            std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
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
    manifest_sources(dir, &crate::manifest::read(dir)?)
}

fn manifest_sources(
    dir: &Path,
    manifest: &crate::manifest::Manifest,
) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    for source in manifest.package.source_paths() {
        let path = dir.join(&source);
        // `src` is the default: a tote without the directory has none.
        if source == crate::manifest::DEFAULT_SOURCE && !path.exists() {
            continue;
        }
        source_files(&path, &mut files)?;
    }
    files.sort();
    Ok(files)
}

/// The `.taut` and `.tauto` files of the tote in `dir` outside its sources:
/// its proofs, examples and tests. A directory with its own `Tauto.eure` is
/// another tote, and hidden directories and `target` hold no files of the tote.
pub fn package_other_files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    let sources: HashSet<PathBuf> = package_source_files(dir)?
        .iter()
        .map(|p| canonical_path(p))
        .collect();
    let mut files = Vec::new();
    other_files(dir, true, &mut files)?;
    files.retain(|p| !sources.contains(&canonical_path(p)));
    files.sort();
    Ok(files)
}

fn other_files(dir: &Path, root: bool, out: &mut Vec<PathBuf>) -> Result<(), String> {
    if !root && dir.join("Tauto.eure").is_file() {
        return Ok(());
    }
    let entries = std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| format!("{}: {e}", dir.display()))?.path();
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
    matches!(
        path.extension().and_then(|e| e.to_str()),
        Some("taut" | "tauto")
    )
}

/// The `.taut` and `.tauto` source files under `dir`; reject legacy extensions.
fn source_files(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| format!("{}: {e}", dir.display()))?.path();
        if path.is_dir() {
            source_files(&path, out)?;
        } else if path.extension().is_some_and(|e| e == "nib") {
            return Err(format!(
                "{}: tote sources must use .taut or .tauto",
                path.display()
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
        if let Ok(p) = parse_program_unresolved_at(crate::nibstd::PRELUDE, PRELUDE_BASE) {
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
        Stmt::Fn(f) => Some(f.name.clone()),
        Stmt::Theorem(t) | Stmt::Def(t) => Some(t.name.clone()),
        Stmt::Inductive(d) => Some(d.name.clone()),
        _ => None,
    }
}

/// The edit that writes the import a name needs ([`crate::surface::qualify::MissingImport`]),
/// by where the name is written: after the last import of the file, or at its start when it
/// has none.
fn import_fixes(
    files: &[SourceFile],
    last_import: &[Option<u32>],
    missing: Vec<crate::surface::qualify::MissingImport>,
) -> Vec<(Span, crate::check::Fix)> {
    missing
        .into_iter()
        .filter_map(|m| {
            let file = files.get(m.file)?;
            let line = format!("import {}", m.spelling);
            let (at, text) = match last_import.get(m.file).copied().flatten() {
                Some(end) => (end, format!("\n{line}")),
                None => (file.base, format!("{line}\n")),
            };
            Some((
                m.at,
                crate::check::Fix {
                    title: line,
                    span: Span::new(at, at),
                    text,
                },
            ))
        })
        .collect()
}
