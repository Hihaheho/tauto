//! Lowering: the checked program to NIR.
//!
//! The work list starts at the top-level statements and grows by the
//! functions they call, one instance per function and per tier of its row
//! variables.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use crate::rows::{Row, RowReport, Target, check_program_rows};
use crate::types::{Datas, Kind, Param as TParam, ParamId, Quant, Ty as TTy, TypeReport};
use tauto_surface::surface::{BudgetLimit, FnDecl, Program, Stmt, SurfaceTerm, TermKind};

#[allow(unused_imports)]
use tauto_message::{Message, msg};
use tauto_nir::*;

mod buffered;
mod expr;
pub(crate) mod handle;
mod pat;
mod specialize;
mod syntax;
mod tail_resumptive;
#[cfg(test)]
mod test_load;
mod ty;
#[cfg(test)]
pub(crate) use test_load::{compile, compile_javascript, compile_targets, compile_with};

pub(crate) type R<T> = Result<T, Unsupported>;

pub(crate) fn unsupported<T>(what: Message, span: Span) -> R<T> {
    Err(Unsupported {
        what,
        span: Some(span),
    })
}

#[derive(Clone, Copy)]
pub struct LowerInput<'a> {
    pub program: &'a Program,
    pub types: &'a TypeReport,
    pub rows: &'a RowReport,
    pub lib: bool,
    /// The functions that run only while the program is expanded
    /// (`Loaded::expansion_only`), which a library does not export.
    pub expansion_only: Option<&'a HashSet<tauto_surface::identity::Name>>,
}

pub struct Lowered {
    pub package: Package,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CompileError {
    /// The front end rejected it (syntax, types, rows, use check).
    Front(String),
    /// The lowered package of the selected entries failed a check that only
    /// those entries determine (`let(stack)`, …). Another entry of the same
    /// program may still lower.
    Package(String),
    Unsupported(Unsupported),
    /// An error that `tauto build` reports (`Decimal`, no binding, …).
    Build(String),
}

impl From<Unsupported> for CompileError {
    fn from(u: Unsupported) -> Self {
        CompileError::Unsupported(u)
    }
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::Front(m) | CompileError::Package(m) | CompileError::Build(m) => {
                write!(f, "{m}")
            }
            CompileError::Unsupported(u) => write!(f, "{u}"),
        }
    }
}

/// Whether a type is one the expansion makes for a method with generics, or
/// has a type constructor variable in it.
fn poly(t: &crate::types::Ty) -> bool {
    use crate::types::Ty;
    match t {
        Ty::Poly(..) | Ty::App(..) => true,
        Ty::Fn(ps, r, _) => ps.iter().any(poly) || poly(r),
        Ty::Union(ts) => ts.iter().any(poly),
        Ty::Named(_, args) => args.iter().any(poly),
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) => poly(t),
        _ => false,
    }
}

/// Sequential boundaries of compilation; parsing includes expansion and name resolution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompilePhase {
    ParseExpand,
    Check,
    Lower,
}

/// A program as it was read: what lowering asks of the reader that read it.
/// The reader implements it; lowering never reads files itself.
thread_local! {
    static FOR_EXPANSION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Lowers in `f` for a macro's run: the operations only the expander
/// answers (`Syn::global`) are lowered as the host's builtins.
pub fn lowering_for_expansion<T>(f: impl FnOnce() -> T) -> T {
    let before = FOR_EXPANSION.with(|c| c.replace(true));
    let out = f();
    FOR_EXPANSION.with(|c| c.set(before));
    out
}

pub(crate) fn for_expansion() -> bool {
    FOR_EXPANSION.with(std::cell::Cell::get)
}

/// A shape every entry of the program would hit again (class methods with
/// generics, `borrows` of a field path). During expansion it is `Front` so
/// the macro-vm library cache remembers it once; otherwise it stays
/// `Unsupported` for the CLI's backend message.
fn library_unsupported(u: Unsupported) -> CompileError {
    if for_expansion() {
        CompileError::Front(u.to_string())
    } else {
        CompileError::Unsupported(u)
    }
}

pub trait LoadedProgram {
    /// The expanded program, whose top level runs.
    fn program(&self) -> &Program;
    /// The program with the statements the imported files' top levels would
    /// run: what the types are checked of.
    fn program_with_imports(&self) -> std::borrow::Cow<'_, Program>;
    /// A copy with the names of its runtime views bound.
    fn resolved(&self) -> Box<dyn LoadedProgram + '_>;
    /// The directories the program's syntaxes' tables are found in.
    fn search_dirs(&self) -> Vec<std::path::PathBuf>;
    fn check_rows_with_types(&self, target: Target, types: &TypeReport) -> RowReport;
    /// The rows of `wrapped`, the program with its top level run by the host.
    fn check_wrapped_rows_with_types(
        &self,
        wrapped: &Program,
        target: Target,
        types: &TypeReport,
    ) -> RowReport;
    fn locate(&self, offset: u32) -> Option<(&std::path::Path, usize, usize)>;
    fn source_map(&self) -> tauto_surface::sources::SourceMap;
    /// The functions that run only while the program is expanded.
    fn expansion_only(&self) -> &HashSet<tauto_surface::identity::Name>;
    /// The methods of the instances the program writes, as the class
    /// expansion names their functions.
    fn instance_methods(&self) -> &[crate::types::InstanceMethod] {
        &[]
    }
    /// The file whose statements declare the function `name`: for one a
    /// macro made, the file that holds the attribute, not the macro's.
    fn declaring_file(&self, _name: &tauto_surface::identity::Name) -> Option<&std::path::Path> {
        None
    }
}

/// The functions an `exports` list names, as lowering takes them in
/// `entries`. An element is a function's name, or `TOTE::*`: every `pub`
/// function of that tote without generics. `totes` are the totes the program
/// reads, by name, each with its directory: a file belongs to the tote of the
/// innermost directory that holds it. A name that is not a function, is generic, or is listed
/// twice, and a tote that is not read, are errors.
pub struct ExportSelection {
    pub names: BTreeSet<String>,
    /// The generic `pub` functions of a `TOTE::*` that are not exported.
    pub skipped: Vec<String>,
    /// The name a host finds each of `names` by: `TOTE::MODULE::FUNCTION`,
    /// with the tote's `name` as its `Tauto.eure` writes it, the module's path
    /// in the tote's `src` (or the tote's directory) and the function's own
    /// name. It does not depend on what else the program declares. A file
    /// outside every tote is written `MODULE::FUNCTION`, its path from
    /// `entry_dir`, the directory of the entry.
    pub public: BTreeMap<String, String>,
    /// Each of `names` once, in the order the exports are written: the
    /// entries in the order the list gives them; a `TOTE::*` brings its
    /// functions and instance methods by module path, and in a module in the
    /// order they are written. A function two entries bring is where the
    /// first one puts it.
    pub order: Vec<String>,
}

impl ExportSelection {
    /// Writes each export under its [`public`](Self::public) name, in
    /// [`order`](Self::order).
    pub fn name_exports(&self, exports: &mut [tauto_nir::Export]) {
        name_exports(&self.public, &self.order, exports);
    }
}

/// Puts the exports in `order` and writes each under the name `public` gives
/// it. An export `order` does not name stays after those it names.
pub fn name_exports(
    public: &BTreeMap<String, String>,
    order: &[String],
    exports: &mut [tauto_nir::Export],
) {
    let at: HashMap<&str, usize> = order
        .iter()
        .enumerate()
        .map(|(i, n)| (n.as_str(), i))
        .collect();
    exports.sort_by_key(|e| at.get(e.name.as_str()).copied().unwrap_or(usize::MAX));
    for e in exports {
        if let Some(name) = public.get(&e.name) {
            e.name = name.clone();
        }
    }
}

/// A type as an instance's export name writes it: each name as `name` gives it.
fn shown_type(t: &SurfaceTerm, name: &dyn Fn(&tauto_surface::identity::Name) -> String) -> String {
    let list = |ts: &mut dyn Iterator<Item = &SurfaceTerm>| {
        ts.map(|t| shown_type(t, name))
            .collect::<Vec<_>>()
            .join(", ")
    };
    match &*t.kind {
        TermKind::Var(n) => name(n),
        TermKind::App {
            function,
            arguments,
        } => {
            format!(
                "{}({})",
                shown_type(function, name),
                list(&mut arguments.iter())
            )
        }
        TermKind::Pi { params, result, .. } => {
            format!(
                "fn({}) -> {}",
                list(&mut params.iter().map(|(_, p)| p)),
                shown_type(result, name)
            )
        }
        TermKind::Nat(v) => v.clone(),
        TermKind::Text(v) => format!("{v:?}"),
        TermKind::Bool(b) => b.to_string(),
        _ => "_".to_string(),
    }
}

pub fn select_exports(
    loaded: &dyn LoadedProgram,
    list: &[String],
    totes: &[(String, std::path::PathBuf)],
    entry_dir: Option<&std::path::Path>,
) -> Result<ExportSelection, String> {
    let tote_entry = |file: &std::path::Path| -> Option<&(String, std::path::PathBuf)> {
        let file = std::fs::canonicalize(file).unwrap_or_else(|_| file.to_path_buf());
        totes
            .iter()
            .filter(|(_, dir)| file.starts_with(dir))
            .max_by_key(|(_, dir)| dir.components().count())
    };
    let tote_of = |file: &std::path::Path| tote_entry(file).map(|(name, _)| name.as_str());
    let entry_dir = entry_dir.map(|d| std::fs::canonicalize(d).unwrap_or_else(|_| d.to_path_buf()));
    // `TOTE::MODULE`: the file `file`, as an export names where it is.
    let path_of = |file: &std::path::Path| -> Vec<String> {
        let file = std::fs::canonicalize(file).unwrap_or_else(|_| file.to_path_buf());
        let (tote, base) = match tote_entry(&file) {
            Some((name, dir)) => {
                let src = dir.join("src");
                (
                    Some(name.clone()),
                    if file.starts_with(&src) {
                        src
                    } else {
                        dir.clone()
                    },
                )
            }
            None => (None, entry_dir.clone().unwrap_or_default()),
        };
        let rel = file.strip_prefix(&base).unwrap_or(&file).with_extension("");
        let mut parts: Vec<String> = tote.into_iter().collect();
        parts.extend(
            rel.components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned()),
        );
        parts
    };
    let own_name = |n: &tauto_surface::identity::Name| -> String {
        n.as_str()
            .rsplit("::")
            .next()
            .unwrap_or(n.as_str())
            .to_string()
    };
    let public_name = |f: &FnDecl| -> String {
        let own = own_name(&f.name);
        let Some(file) = loaded
            .declaring_file(&f.name)
            .or_else(|| loaded.locate(f.span.start).map(|(file, _, _)| file))
        else {
            return own;
        };
        let mut parts = path_of(file);
        parts.push(own);
        parts.join("::")
    };
    let program = loaded.program();
    let fns: Vec<&FnDecl> = program
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Fn(f) if !crate::types::is_made_instance(f.span) => Some(f),
            _ => None,
        })
        .filter(|f| !loaded.expansion_only().contains(&f.name))
        .collect();
    // Each method of an instance the program writes, under the name its
    // export line gives it: `TOTE::MODULE::instance CLASS(TYPE, ..)::METHOD`,
    // where the instance is written, the class and each type named as an
    // export names a declaration, `TOTE::MODULE::NAME`.
    let declared: HashMap<String, u32> = program
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Struct(d) | Stmt::Enum(d) => Some((d.name.to_string(), d.span.start)),
            _ => None,
        })
        .collect();
    let qualified = |n: &tauto_surface::identity::Name, at: Option<&u32>| -> String {
        let own = own_name(n);
        match at.and_then(|start| loaded.locate(*start)) {
            Some((file, _, _)) => {
                let mut parts = path_of(file);
                parts.push(own);
                parts.join("::")
            }
            None => own,
        }
    };
    let ty = |n: &tauto_surface::identity::Name| qualified(n, declared.get(&n.to_string()));
    let instances: Vec<(String, String, bool, Option<&std::path::Path>)> = loaded
        .instance_methods()
        .iter()
        .map(|m| {
            // One a macro made is where its attribute is written, as a function is.
            let file = loaded
                .declaring_file(&m.function)
                .or_else(|| loaded.locate(m.span.start).map(|(file, _, _)| file));
            let heads: Vec<String> = m.heads.iter().map(|t| shown_type(t, &ty)).collect();
            let mut parts = file.map(path_of).unwrap_or_default();
            parts.push(format!(
                "instance {}({})",
                qualified(&m.class, Some(&m.class_span.start)),
                heads.join(", ")
            ));
            parts.push(m.method.to_string());
            (m.function.to_string(), parts.join("::"), m.generic, file)
        })
        .collect();
    // Where each function is written: its module's path, then its place among
    // the module's statements.
    let stmt_at: HashMap<String, usize> = program
        .stmts
        .iter()
        .enumerate()
        .filter_map(|(i, s)| match s {
            Stmt::Fn(f) => Some((f.name.to_string(), i)),
            _ => None,
        })
        .collect();
    let written_at = |function: &str, file: Option<&std::path::Path>| -> (Vec<String>, usize) {
        (
            file.map(path_of).unwrap_or_default(),
            stmt_at.get(function).copied().unwrap_or(usize::MAX),
        )
    };
    let mut names = BTreeSet::new();
    let mut order = Vec::new();
    let mut skipped = Vec::new();
    let mut seen = BTreeSet::new();
    for item in list {
        if !seen.insert(item.as_str()) {
            return Err(msg!("nibcheck-export-twice", name = item.as_str()).to_string());
        }
        if let Some(tote) = item.strip_suffix("::*") {
            if !totes.iter().any(|(t, _)| t == tote) {
                let known: Vec<&str> = totes.iter().map(|(t, _)| t.as_str()).collect();
                let known = if known.is_empty() {
                    "none".to_string()
                } else {
                    known.join(", ")
                };
                return Err(
                    msg!("nibcheck-export-unknown-tote", tote = tote, known = known).to_string(),
                );
            }
            let mut brought: Vec<((Vec<String>, usize), String)> = Vec::new();
            for f in &fns {
                if f.vis == tauto_surface::surface::Vis::Private {
                    continue;
                }
                let Some((file, _, _)) = loaded.locate(f.span.start) else {
                    continue;
                };
                if tote_of(file) != Some(tote) {
                    continue;
                }
                if f.generics.is_empty() {
                    let file = loaded.declaring_file(&f.name).unwrap_or(file);
                    brought.push((written_at(f.name.as_str(), Some(file)), f.name.to_string()));
                } else {
                    skipped.push(f.name.to_string());
                }
            }
            // An instance has no `pub`: each one the tote writes is exported.
            for (function, public, generic, file) in &instances {
                if file.and_then(tote_of) != Some(tote) {
                    continue;
                }
                if *generic {
                    skipped.push(public.clone());
                } else {
                    brought.push((written_at(function, *file), function.clone()));
                }
            }
            brought.sort();
            for (_, name) in brought {
                if names.insert(name.clone()) {
                    order.push(name);
                }
            }
            continue;
        }
        // A bare name stands for the one function that ends in it: `steer`
        // for `a::steer` when no other file declares a `steer`.
        let found = fns.iter().find(|f| f.name.as_str() == item).or_else(|| {
            let suffix = format!("::{item}");
            let ends: Vec<&&FnDecl> = fns
                .iter()
                .filter(|f| f.name.as_str().ends_with(&suffix))
                .collect();
            match ends[..] {
                [one] => Some(one),
                _ => None,
            }
        });
        if found.is_none() {
            let suffix = format!("::{item}");
            let mut ends: Vec<String> = fns
                .iter()
                .filter(|f| f.name.as_str().ends_with(&suffix))
                .map(|f| f.name.to_string())
                .collect();
            if ends.len() > 1 {
                ends.sort();
                return Err(msg!(
                    "nibcheck-export-ambiguous",
                    name = item.as_str(),
                    candidates = ends.join(", ")
                )
                .to_string());
            }
        }
        match found {
            None => return Err(msg!("nibcheck-export-unknown", name = item.as_str()).to_string()),
            Some(f) if !f.generics.is_empty() => {
                return Err(msg!("nibcheck-export-generic", name = item.as_str()).to_string());
            }
            Some(f) => {
                if names.insert(f.name.to_string()) {
                    order.push(f.name.to_string());
                }
            }
        }
    }
    let public = fns
        .iter()
        .filter(|f| names.contains(f.name.as_str()))
        .map(|f| (f.name.to_string(), public_name(f)))
        .chain(
            instances
                .iter()
                .filter(|(function, ..)| names.contains(function))
                .map(|(function, public, ..)| (function.clone(), public.clone())),
        )
        .collect();
    Ok(ExportSelection {
        names,
        skipped,
        public,
        order,
    })
}

/// Checks and lowers an expanded, file-aware program. Reading and expansion
/// have already completed; the observer starts at the checking boundary.
pub fn compile_loaded_with_observer(
    loaded: &dyn LoadedProgram,
    lib: bool,
    target: Target,
    observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    compile_loaded_entries_with_observer(loaded, lib, target, None, observe)
}

/// Checks and lowers a loaded program, limiting library roots to the named entries.
/// Calls and function values reachable from those entries are lowered normally.
pub fn compile_loaded_entries_with_observer(
    loaded: &dyn LoadedProgram,
    lib: bool,
    target: Target,
    entries: Option<&BTreeSet<String>>,
    observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    let loaded = loaded.resolved();
    let loaded = &*loaded;
    let dirs = loaded.search_dirs();
    let mut package = tauto_parse::syntax::with_search_dirs(dirs, || {
        // The statements an imported file's top level would run are checked
        // too, though nothing is compiled of them.
        let report = crate::types::check_program(&loaded.program_with_imports());
        compile_checked(
            loaded.program(),
            Some(report),
            None,
            Some(loaded),
            false,
            false,
            lib,
            target,
            entries,
            observe,
        )
    })?;
    package.sources = Some(loaded.source_map());
    Ok(package)
}

/// A target and how to compile for it: as `compile_loaded_entries_with_observer`
/// takes `lib` and `entries`.
pub struct TargetRequest<'a> {
    pub target: Target,
    pub lib: bool,
    pub entries: Option<&'a BTreeSet<String>>,
}

/// As `compile_loaded_entries_with_observer` for each request in turn, with
/// the program's types checked once.
pub fn compile_loaded_targets(
    loaded: &dyn LoadedProgram,
    requests: &[TargetRequest<'_>],
) -> Vec<Result<Package, CompileError>> {
    let loaded = loaded.resolved();
    let loaded = &*loaded;
    let dirs = loaded.search_dirs();
    tauto_parse::syntax::with_search_dirs(dirs, || {
        // The statements an imported file's top level would run are checked
        // too, though nothing is compiled of them.
        let report = crate::types::check_program(&loaded.program_with_imports());
        requests
            .iter()
            .map(|r| {
                let mut package = compile_checked(
                    loaded.program(),
                    Some(report.clone()),
                    None,
                    Some(loaded),
                    false,
                    false,
                    r.lib,
                    r.target,
                    r.entries,
                    |_| {},
                )?;
                package.sources = Some(loaded.source_map());
                Ok(package)
            })
            .collect()
    })
}

/// The name of the innermost function whose declaration holds `offset`,
/// with the modules it is declared in (`syntax.ident`).
fn enclosing_fn(stmts: &[Stmt], offset: u32) -> Option<String> {
    stmts.iter().find_map(|s| match s {
        Stmt::Fn(f) if f.span.start <= offset && offset < f.span.end => Some(f.name.to_string()),
        Stmt::Module {
            name, items, span, ..
        } if span.start <= offset && offset < span.end => {
            enclosing_fn(items, offset).map(|f| format!("{name}.{f}"))
        }
        _ => None,
    })
}

/// `wrapped`: `program` is the host wrapping of the program `loaded` read.
/// `rewritten`: `program` is not the one `loaded` read but its copy with
/// functions specialized (`specialize`), which is not specialized again.
fn compile_program(
    program: &Program,
    loaded: Option<&dyn LoadedProgram>,
    wrapped: bool,
    rewritten: bool,
    lib: bool,
    target: Target,
    entries: Option<&BTreeSet<String>>,
    observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    compile_checked(
        program, None, None, loaded, wrapped, rewritten, lib, target, entries, observe,
    )
}

/// `compile_program`, given the report of `program` when it was already
/// checked (the specialized copy, checked before it is chosen).
#[allow(clippy::too_many_arguments)]
fn compile_checked(
    program: &Program,
    checked: Option<crate::types::TypeReport>,
    judged: Option<(&RowReport, &HashMap<Name, Name>)>,
    loaded: Option<&dyn LoadedProgram>,
    wrapped: bool,
    rewritten: bool,
    lib: bool,
    target: Target,
    entries: Option<&BTreeSet<String>>,
    mut observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    // The host-wrapped or specialized copy of a program is checked again,
    // inside the one phase the observer already saw begin.
    if !wrapped && !rewritten {
        observe(CompilePhase::Check);
    }
    let report = match checked {
        Some(report) => report,
        None => crate::types::check_program(program),
    };
    if let Some(e) = report.errors.first() {
        let at = loaded.and_then(|l| l.locate(e.span.start));
        let function = enclosing_fn(&program.stmts, e.span.start);
        return Err(CompileError::Front(match (at, function) {
            (Some((file, line, col)), Some(function)) => msg!(
                "nir-type-error-in",
                file = file.display().to_string(),
                line = line,
                col = col,
                function = function,
                error = e.message.clone()
            )
            .to_string(),
            (Some((file, line, col)), None) => msg!(
                "nir-type-error-at",
                file = file.display().to_string(),
                line = line,
                col = col,
                error = e.message.clone()
            )
            .to_string(),
            _ => msg!("nir-type-error", error = e.to_string()).to_string(),
        }));
    }
    // The prelude's operators are in the program's rows too, and what an
    // operator performs (`overflow`) depends on the widths its report knows.
    let report = report.with_prelude_for(program);
    // The rows are checked on the program as written, before any copy below
    // takes its place: a copy runs a function argument directly, so it would
    // no longer see that the value performs more than its type permits.
    let checked_rows = match (judged, loaded) {
        // A copy, or the wrapping of one, is judged with the evidence
        // the program it was made from was judged with.
        (Some((judged, copied_from)), _) => {
            crate::rows::check_copied_rows_with_types(judged, copied_from, program, &report)
        }
        (None, Some(loaded)) if wrapped || rewritten => {
            loaded.check_wrapped_rows_with_types(program, target, &report)
        }
        (None, Some(loaded)) => loaded.check_rows_with_types(target, &report),
        (None, None) if target == Target::JavaScript => {
            crate::rows::check_program_rows_javascript_with_types(program, &report)
        }
        (None, None) => crate::rows::check_program_rows_with_types(program, &report),
    };
    // Every declaration answers to the checks, run or not: a program that
    // `tauto check` rejects is not built either.
    // An effect nobody handles is an error here as it is for `tauto check`,
    // `tauto run` and the JavaScript backend, `resume 0` ones included.
    //
    // When lowering for a macro run, refuse only row errors the selected
    // entries reach on *this* program (including after specialize / wrap).
    // Unreached library failures (host-state cycles, …) stay ignored: the
    // expander already gates macros with the same reachability, and asking
    // again for every unreached error dominated expansion.
    refuse_row_errors(program, &checked_rows, entries)?;
    let rows = add_prelude_rows(program, checked_rows);
    // A method with generics of its own, a type constructor variable: no
    // backend writes these as they are, so each use gets its own copy
    // (`specialize`), which is checked again.
    if report
        .terms
        .values()
        .chain(report.schemes.values().map(|s| &s.ty))
        .any(poly)
    {
        if !rewritten && let Some((copied, copied_from)) = specialize::program(program, &report) {
            let copied_report = crate::types::check_program(&copied);
            if copied_report.errors.is_empty() {
                return compile_checked(
                    &copied,
                    Some(copied_report),
                    Some((&rows, &copied_from)),
                    loaded,
                    wrapped,
                    true,
                    lib,
                    target,
                    entries,
                    observe,
                );
            }
        }
        return Err(library_unsupported(Unsupported {
            what: msg!("nir-class-method-with-generics"),
            span: None,
        }));
    }
    // `borrows(p.a)`: a Rust function borrows its whole argument, so the
    // other fields could not be used while the result lives.
    if target == Target::Rust
        && let Some(f) = program.stmts.iter().find_map(|s| match s {
            Stmt::Fn(f) if f.lends.iter().flatten().any(|l| l.contains('.')) => Some(f),
            _ => None,
        })
    {
        return Err(library_unsupported(Unsupported {
            what: msg!("nir-borrows-field-path", name = f.name.to_string()),
            span: Some(f.span),
        }));
    }
    // A struct field holding a function that returns `Text` is, in the Rust
    // backend, a function that writes into a buffer it is given
    // (`buffered`), so no `Text` is made per call. The rewritten program is
    // checked again; one that does not check runs as written.
    if !rewritten
        && target == Target::Rust
        && let Some(copied) = buffered::program(program)
    {
        let copied_report = crate::types::check_program(&copied);
        if copied_report.errors.is_empty() {
            let copied = specialize::program(&copied, &copied_report)
                .and_then(|(again, copied_from)| {
                    let again_report = crate::types::check_program(&again);
                    again_report
                        .errors
                        .is_empty()
                        .then_some((again, again_report, copied_from))
                })
                .unwrap_or((copied, copied_report, HashMap::new()));
            return compile_checked(
                &copied.0,
                Some(copied.1),
                Some((&rows, &copied.2)),
                loaded,
                wrapped,
                true,
                lib,
                target,
                entries,
                observe,
            );
        }
    }
    // A function that takes a function runs, for each call that gives it a
    // declared function, as a copy that calls that function directly
    // (`specialize`): no function value is made or called through. The copy
    // is checked again; a program whose copy does not check runs as written.
    if !rewritten && let Some((copied, copied_from)) = specialize::program(program, &report) {
        let copied_report = crate::types::check_program(&copied);
        if copied_report.errors.is_empty() {
            return compile_checked(
                &copied,
                Some(copied_report),
                Some((&rows, &copied_from)),
                loaded,
                wrapped,
                true,
                lib,
                target,
                entries,
                observe,
            );
        }
    }
    if let Some(e) = crate::lin::check(program, &report, &rows).first() {
        return Err(CompileError::Front(
            msg!("nir-use-error", error = e.to_string()).to_string(),
        ));
    }
    // A program that performs `main` or `test` has its top level put in
    // `Entry::run`, which is checked again. The host's handler is not
    // written around the program: `lower_top` and each `spawn` put it
    // outside the code they lower.
    if !wrapped
        && target != Target::Llvm
        && rows.entries
        && let Some(wrapped) = crate::host::wrap(program, rows.entries)
    {
        let permissions: Vec<String> = crate::host::permissions(rows.host_effects.iter())
            .into_iter()
            .map(str::to_string)
            .collect();
        let no_copies = HashMap::new();
        let mut package = compile_checked(
            &wrapped,
            None,
            rewritten.then_some((&rows, &no_copies)),
            loaded,
            true,
            rewritten,
            lib,
            target,
            entries,
            &mut observe as &mut dyn FnMut(CompilePhase),
        )?;
        package.permissions = permissions;
        return Ok(package);
    }
    observe(CompilePhase::Lower);
    let pruned = prune_dead(program, &report);
    let package = lower_entries(
        LowerInput {
            program: pruned.as_ref().unwrap_or(program),
            types: &report,
            rows: &rows,
            lib,
            expansion_only: loaded.map(|l| l.expansion_only()),
        },
        entries,
    )?;
    let mut package = package;
    if !wrapped && target != Target::Llvm {
        package.permissions = crate::host::permissions(rows.host_effects.iter())
            .into_iter()
            .map(str::to_string)
            .collect();
    }
    Ok(package)
}

/// The program without what never runs, which therefore gets no NIR: the
/// `match` arms no value reaches (`TypeReport::redundant_arms`) and the
/// statements after a `return` in a block ([`dead_after_return`]). `None`
/// when there is none.
/// A function nothing calls needs no pruning: only the functions the
/// program's statements (or a library's exports) reach are lowered.
fn prune_dead(program: &Program, types: &TypeReport) -> Option<Program> {
    let mut pruned = program.clone();
    let mut any = false;
    for stmt in &mut pruned.stmts {
        tauto_surface::surface::walk::stmt(stmt, &mut |t| match &*t.kind {
            TermKind::Match { arms, .. }
                if arms
                    .iter()
                    .any(|a| types.redundant_arms.contains_key(&a.body.id())) =>
            {
                let TermKind::Match { arms, .. } = std::sync::Arc::make_mut(&mut t.kind) else {
                    unreachable!()
                };
                arms.retain(|a| !types.redundant_arms.contains_key(&a.body.id()));
                any = true;
            }
            TermKind::Block(stmts) if dead_after_return(stmts).is_some() => {
                let TermKind::Block(stmts) = std::sync::Arc::make_mut(&mut t.kind) else {
                    unreachable!()
                };
                let dead = dead_after_return(stmts).expect("dead statements");
                stmts.drain(dead);
                any = true;
            }
            _ => {}
        });
    }
    any.then_some(pruned)
}

fn dead_after_return(stmts: &[Stmt]) -> Option<std::ops::Range<usize>> {
    let from = stmts.iter().position(|s| matches!(s, Stmt::Return(_)))? + 1;
    (from < stmts.len()).then_some(from..stmts.len())
}

/// Row failures the compile must refuse before prelude merge / expansion clear.
fn refuse_row_errors(
    program: &Program,
    rows: &RowReport,
    entries: Option<&BTreeSet<String>>,
) -> Result<(), CompileError> {
    if for_expansion() {
        let Some(selected) = entries else {
            return Ok(());
        };
        for entry in selected {
            let Some(name) = entry_fn_name(program, entry) else {
                continue;
            };
            if let Some((_path, why)) = crate::rows::row_error_reached(program, rows, name) {
                let shown = rows
                    .errors
                    .iter()
                    .find(|e| e.message.to_string() == why)
                    .map(|e| e.to_string())
                    .unwrap_or(why);
                // Selected-entry reachability: not a failure of the whole
                // library program (the macro-vm caches `Front` as library-wide).
                return Err(CompileError::Package(shown));
            }
        }
        return Ok(());
    }
    if let Some(e) = rows.errors.iter().find(|e| !in_macro_function(program, e)) {
        return Err(CompileError::Front(format!("{e}")));
    }
    Ok(())
}

fn entry_fn_name<'a>(program: &'a Program, entry: &str) -> Option<&'a Name> {
    program.stmts.iter().find_map(|s| match s {
        Stmt::Fn(f) if f.name.as_str() == entry || f.name.to_string() == entry => Some(&f.name),
        _ => None,
    })
}

/// Whether row error `e` is only that a function registered as a macro, or
/// one only a macro can run (its row has `macro_error` or `elab`), may
/// perform an operator's effect (`overflow`, `divzero`) its row leaves out:
/// the expander allows that, as one performed while the macro runs is that
/// macro's error, and the function never runs with the program.
pub fn in_macro_function(program: &Program, e: &crate::rows::RowDiagnostic) -> bool {
    let operator = e.message.args.iter().any(|(key, value)| {
        key == "effect"
            && matches!(value, tauto_message::Value::Text(t) if t == "overflow" || t == "divzero")
    });
    let macros: Vec<&str> = program
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Macro { function, .. } => Some(function.as_str()),
            _ => None,
        })
        .collect();
    operator
        && program.stmts.iter().any(|s| match s {
            Stmt::Fn(f) => {
                (macros.contains(&f.name.as_str())
                    || f.effects.as_ref().is_some_and(|row| {
                        row.iter()
                            .any(|e| e.as_str() == "macro_error" || e.as_str() == "elab")
                    }))
                    && f.span.start <= e.span.start
                    && e.span.start < f.body.span.end.max(f.span.end)
            }
            _ => false,
        })
}

/// The rows of a program, and what the library's functions perform.
fn add_prelude_rows(program: &Program, mut rows: RowReport) -> RowReport {
    // The prelude is one of two programs fixed for the process: check its rows once each.
    static PLAIN: std::sync::OnceLock<RowReport> = std::sync::OnceLock::new();
    static RESOLVED: std::sync::OnceLock<RowReport> = std::sync::OnceLock::new();
    let prelude = crate::types::prelude_for(program);
    let cell = if std::ptr::eq(prelude, crate::types::prelude()) {
        &PLAIN
    } else {
        &RESOLVED
    };
    rows.merge_prelude(cell.get_or_init(|| check_program_rows(prelude)).clone());
    if for_expansion() {
        rows.keep_own_calls();
    }
    rows
}

/// Backend row variables use declaration-local source tokens. Resolve that
/// view only after checking each private binder's exact lexical owner; a
/// captured row must not become an unrelated same-named parameter.
fn normalized_rows(rows: &RowReport) -> Result<RowReport, CompileError> {
    let unsupported_row = |what| Unsupported { what, span: None };
    let mut normalized = rows.clone();
    normalized.calls = rows
        .normalized_calls()
        .map_err(|(what, span)| Unsupported { what, span })?;
    for declaration in &mut normalized.declarations {
        rows.declaration_row(&declaration.name, declaration.body)
            .map_err(unsupported_row)?;
        declaration.row = rows
            .normalize_row(&declaration.row, Some(declaration.owner))
            .map_err(unsupported_row)?;
        declaration.inferred = rows
            .normalize_row(&declaration.inferred, Some(declaration.owner))
            .map_err(unsupported_row)?;
    }
    Ok(normalized)
}

pub fn lower(input: LowerInput<'_>) -> Result<Package, CompileError> {
    lower_entries(input, None)
}

fn lower_entries(
    input: LowerInput<'_>,
    entries: Option<&BTreeSet<String>>,
) -> Result<Package, CompileError> {
    // `struct &T` is checked, but no backend writes it yet.
    let mut rows = normalized_rows(input.rows)?;
    tail_resumptive::promote(input.program, &mut rows);
    let input = LowerInput {
        rows: &rows,
        ..input
    };
    let mut rc_enabled = true;
    let mut carried = HashMap::new();
    loop {
        let mut l = Lowerer::new(input, rc_enabled, carried.clone());
        let result = l.run(entries);
        if l.rc_violation && rc_enabled {
            // Shared cells require cloneable payloads. If a call supplies a payload
            // without `Clone`, lower the package again using owned cells.
            rc_enabled = false;
            continue;
        }
        // A record that carries a row variable a call specializes to a
        // suspending row holds its functions at that tier: lower again with
        // it. Each round raises a tier, so this ends.
        let wanted = l.carried_wanted.take();
        let mut raised = false;
        for (data, tier) in wanted {
            let at = carried.entry(data).or_insert(Tier::S);
            if tier > *at {
                *at = tier;
                raised = true;
            }
        }
        if !raised {
            // `let(stack)`: checked on what lowering decided, apart from the
            // checker's own rule. The package is only the selected entries, so
            // a failure here is not a failure of the whole program's front end.
            if let Ok(package) = &result
                && let Err((message, span)) = tauto_nir::stack::check(package)
            {
                return Err(CompileError::Package(format!(
                    "{message} (byte {})",
                    span.start
                )));
            }
            return result.map(|mut p| {
                p.evidence = tauto_nir::evidence::resolve(&p);
                p
            });
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Origin {
    Program,
    Prelude,
    Builtin,
    Extern,
}

/// Each lexical capture's checked type and passing ownership.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct CaptureKey {
    // Lowered local declarations have unique names. The ordinal is their
    // lexical capture order, not a runtime or inference allocation number.
    pub function: Name,
    pub index: usize,
}

#[derive(Clone)]
pub(crate) struct LiftedCap {
    pub name: Name,
    pub key: CaptureKey,
    /// A helper forwards another declaration's environment slot, rather
    /// than introducing this diagnostic name into its source scope.
    pub forwarded: Option<CaptureKey>,
    pub ty: TTy,
    /// Storage ownership at declaration, distinct from passing ownership.
    /// Shared owned captures have their own snapshot, passed by borrow.
    pub source_owned: bool,
    /// An owned nonduplicable capture is transferred to a direct call once.
    pub owned: bool,
    /// The cell of a `var` shared with a closure that may outlive it: the
    /// function is passed the cell itself.
    pub cell: Option<Repr>,
}

pub(crate) struct FnSrc<'a> {
    pub decl: &'a FnDecl,
    pub origin: Origin,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstKey {
    pub name: Name,
    pub rowvars: Vec<(Name, Tier)>,
    /// The instance of the O tier that counts steps for a `budget` it runs
    /// under.
    pub under_budget: bool,
    /// The instance written in continuation-passing style, for a function
    /// whose row is of the O tier called from code of the M tier.
    pub m: bool,
    /// The instance of the M tier that holds no `direct` handler, called
    /// from the body of a `handle` whose `k` is kept (`Cx::detached`).
    pub detached: bool,
}

/// A bound that a call forces on the caller's type parameter.
pub(crate) struct Edge {
    pub callee: InstId,
    pub args: Vec<(String, Ty)>,
}

#[derive(Default)]
pub(crate) struct InstMeta {
    pub generics: Vec<String>,
    /// The scheme's own binders, followed by the fixed types of its captures.
    pub parameters: Vec<(TParam, Kind)>,
    pub own_parameters: usize,
    pub param_names: HashMap<ParamId, String>,
    pub bounds: BTreeMap<String, BTreeSet<Bound>>,
    pub edges: Vec<Edge>,
}

pub(crate) struct Lowerer<'a> {
    pub syntax_parsers: Vec<SyntaxParser>,
    pub declarations: Vec<tauto_surface::identity::DeclRef>,
    pub program: &'a Program,
    pub types: &'a TypeReport,
    pub operation_facts: Option<&'a crate::types::OperationFacts>,
    pub rows: &'a RowReport,
    pub lib: bool,
    pub expansion_only: Option<&'a HashSet<tauto_surface::identity::Name>>,
    pub fns: HashMap<Name, FnSrc<'a>>,
    /// The effect declarations of the library and the program, by name.
    pub effect_decls: HashMap<Name, &'a tauto_surface::surface::EffectDecl>,
    /// The functions written inside another body, and what each of them
    /// captures: a lifted function takes the captures as leading parameters.
    pub nested_fns: HashSet<Name>,
    pub local_caps: HashMap<Name, Vec<LiftedCap>>,
    /// The locals an arm of `show` binds to the value it was given: a value
    /// already shown (`Ty::Shown`).
    pub shown_locals: std::collections::HashSet<u32>,
    /// Declaration and binder order, independent of occurrence allocation.
    pub param_order: HashMap<ParamId, (usize, usize)>,
    /// Output names in the function being lowered; never semantic identities.
    pub param_names: HashMap<ParamId, String>,
    /// Data and operation signatures have their own declaration-local names.
    pub declaration_param_names: HashMap<ParamId, String>,
    /// Generics that stand for one type where they are lowered: the host's
    /// handler answers a top level of `()`.
    pub param_values: HashMap<ParamId, Ty>,
    /// Lowering the host's arms: a generic they mention that is not the
    /// function's own is an arm's operation generic, numbered here.
    pub host_skolems: Option<HashMap<ParamId, usize>>,
    pub datas: Vec<DataDef>,
    pub data_index: HashMap<Name, usize>,
    /// Each data type's row parameters (`row_parameters_of`).
    pub row_params: HashMap<Name, Vec<usize>>,
    /// Recursive generic data whose cells share their tails.
    pub rc_datas: HashSet<Name>,
    /// Whether a `&rc T` is lowered: its box ([`ty::rc_box_def`]) is then
    /// one of the package's data.
    pub rc_box: bool,
    pub rc_enabled: bool,
    pub rc_violation: bool,
    /// The tier each data type holds the functions of its fields at whose
    /// rows have a row variable, when a call specializes that variable to a
    /// suspending row (`carried_row`); the others hold them at the tier of
    /// the row as written.
    pub carried: HashMap<Name, Tier>,
    /// The tiers this lowering found the data types must carry.
    pub carried_wanted: std::cell::RefCell<HashMap<Name, Tier>>,
    pub unions: Vec<UnionDef>,
    pub union_ids: HashMap<Vec<Ty>, UnionId>,
    pub ops: Vec<OpDef>,
    pub op_ids: HashMap<Name, usize>,
    pub insts: Vec<Option<FnInst>>,
    pub inst_keys: HashMap<InstKey, InstId>,
    pub inst_names: Vec<InstKey>,
    pub meta: Vec<InstMeta>,
    pub work: VecDeque<InstId>,
    pub next_local: u32,
    pub next_handle: u32,
    /// The result of the `handle` a continuation `k` (by its local's id)
    /// goes on to: what calling `k` gives, at the tier the `handle` holds it.
    pub cont_results: HashMap<u32, Ty>,
    /// The results of the `handle`s whose arms are being lowered.
    pub handle_results: Vec<Ty>,
    pub spawns: bool,
    pub next_budget: u32,
    /// Whether the program runs a `budget` anywhere
    /// ([`Lowerer::value_tier`]).
    pub has_budget: bool,
    /// Whether a `handle` of the program answers a `uhost` operation
    /// (`uhost_handled`); asked once.
    pub uhost_handlers: std::cell::OnceCell<usize>,
    /// Whether each named function runs a `budget`, itself or through a
    /// call ([`Lowerer::runs_budget`]).
    pub runs_budget: std::cell::RefCell<HashMap<Name, bool>>,
    /// What `tauto build` rejects after the front end (`Decimal`).
    pub build_errors: Vec<String>,
    /// Function whose body is being lowered: seals replaceable extern repr.
    pub current_fn: Option<Name>,
    /// The first construct the Rust backend rejects: a record-carried row
    /// variable specialized above the plain tier, a kept continuation in code
    /// of the M tier.
    pub rust_unsupported: std::cell::RefCell<Option<Unsupported>>,
}

#[derive(Clone)]
pub(crate) struct Binding {
    pub name: Name,
    pub local: Local,
    pub ty: TTy,
    pub mode: Mode,
    /// For a name of function type: the effects its calls perform.
    pub fn_row: Option<Row>,
    /// The function value was lowered with suspendable budget ticks.
    pub budgeted: bool,
    pub celled: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mode {
    Cont,
    /// The same, in an arm of `exceeded`: `k` takes a `BudgetAnswer`.
    ContBudget,
    Owned,
    Var,
    Borrow(bool),
    BorrowClosure,
}

pub(crate) struct CFrame {
    pub base: usize,
    pub captures: Vec<Local>,
}

pub(crate) struct Cx {
    pub bindings: Vec<Binding>,
    /// Nonowning aliases to exact lexical bindings; never source names.
    pub capture_bindings: Vec<(CaptureKey, usize)>,
    /// Owned environment slots and forwarded helper parameters are not
    /// visible to source lookup, even when their diagnostic names coincide.
    pub hidden_bindings: HashSet<u32>,
    pub rowvars: HashMap<Name, Tier>,
    pub tier: Tier,
    pub frames: Vec<CFrame>,
    pub ret: TTy,
    pub inst: InstId,
    /// Inside the body of a `budget`, or of a function that runs under one.
    pub under_budget: bool,
    /// Inside an `m` handle of a function that is not of the M tier: a
    /// `return` would have to leave the handle's driver.
    pub host_m: bool,
    /// A `return` was lowered inside the `m` handle being lowered, which the
    /// handle's driver has to carry out of the function.
    pub host_ret: bool,
    /// Inside a `handle` whose `k` is kept as a value, or a function called
    /// there: the code is part of a continuation that may run after the
    /// handlers around the `handle` are gone, so it holds none of them.
    pub detached: bool,
    /// The types locals are written with, by local id: a declared parameter,
    /// a name a pattern takes out of a value whose type is written. A checked
    /// type has no rows, so the rows of functions inside it are read here.
    pub written: HashMap<u32, SurfaceTerm>,
    /// The types locals of function type are held at, by local id, where
    /// the value gave its own tier: a closure literal, a function item.
    pub held: HashMap<u32, Ty>,
    /// The rows a data type writes on the parameters of the function of a
    /// field, for the closure literal lowered next as that field
    /// (`Lowerer::closure` takes them): a parameter called there as a
    /// callback has a known row.
    pub lam_param_rows: Vec<Option<Row>>,
    /// Whether that field's data carries a suspending row: its function's
    /// parameters are then taken at the tiers of their rows.
    pub lam_params_carried: bool,
    /// The `Succ(p)` patterns on a `nat` in the arm being lowered: the name the
    /// value is bound to, `p`, and whether the name borrows. The arm's guard
    /// tests them and its body binds what `p` names.
    pub nat_tests: Vec<(Local, tauto_surface::surface::Pattern, bool)>,
}

fn collect_nested<'a>(t: &'a SurfaceTerm, out: &mut Vec<&'a FnDecl>) {
    tauto_surface::surface::walk::values(t, &mut |node| {
        if let tauto_surface::surface::walk::Node::Stmt(Stmt::Fn(f)) = node {
            out.push(f);
        }
    });
}

impl<'a> Lowerer<'a> {
    fn new(input: LowerInput<'a>, rc_enabled: bool, carried: HashMap<Name, Tier>) -> Self {
        let mut fns: HashMap<Name, FnSrc<'a>> = HashMap::new();
        let mut effect_decls: HashMap<Name, &'a tauto_surface::surface::EffectDecl> =
            HashMap::new();
        let lib: &'static Program = crate::types::prelude_for(input.program);
        for (stmts, own) in [(&lib.stmts, false), (&input.program.stmts, true)] {
            for s in stmts {
                match s {
                    Stmt::Fn(f) => {
                        fns.insert(
                            f.name.clone(),
                            FnSrc {
                                decl: f,
                                origin: if own {
                                    Origin::Program
                                } else {
                                    Origin::Prelude
                                },
                            },
                        );
                    }
                    Stmt::Effect(e) => {
                        effect_decls.insert(e.name.clone(), e);
                    }
                    Stmt::Extern {
                        fns: fs,
                        instances,
                        types,
                        structs,
                        enums,
                        ..
                    } => {
                        let replaceable = tauto_surface::surface::extern_is_replaceable(
                            fs, instances, types, structs, enums,
                        );
                        for f in fs {
                            fns.insert(
                                f.name.clone(),
                                FnSrc {
                                    decl: f,
                                    origin: if !own {
                                        Origin::Builtin
                                    } else if replaceable {
                                        // Fallback bodies lower like program code;
                                        // host selection may rewrite them later.
                                        Origin::Program
                                    } else {
                                        Origin::Extern
                                    },
                                },
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        // A function written inside another body that mentions nothing of it
        // is a top-level function by another name; it is lowered as one.
        let mut nested = Vec::new();
        for s in &input.program.stmts {
            match s {
                Stmt::Fn(f) => collect_nested(&f.body, &mut nested),
                Stmt::Extern {
                    fns,
                    instances,
                    types,
                    structs,
                    enums,
                    ..
                } if tauto_surface::surface::extern_is_replaceable(
                    fns, instances, types, structs, enums,
                ) =>
                {
                    for f in fns {
                        collect_nested(&f.body, &mut nested);
                    }
                }
                _ => {}
            }
        }
        let mut seen: HashMap<&tauto_surface::identity::Name, usize> = HashMap::new();
        for f in &nested {
            *seen.entry(&f.name).or_insert(0) += 1;
        }
        let mut nested_fns = HashSet::new();
        for f in nested {
            if seen[&f.name] > 1 || fns.contains_key(&f.name) {
                continue;
            }
            nested_fns.insert(f.name.clone());
            fns.insert(
                f.name.clone(),
                FnSrc {
                    decl: f,
                    origin: Origin::Program,
                },
            );
        }
        let mut param_order = HashMap::new();
        let mut declaration = 0;
        for program in [lib, input.program] {
            for stmt in &program.stmts {
                tauto_surface::surface::walk::values_stmt(stmt, &mut |node| {
                    let tauto_surface::surface::walk::Node::Stmt(Stmt::Fn(f)) = node else {
                        return;
                    };
                    let owner = declaration;
                    declaration += 1;
                    if fns
                        .get(&f.name)
                        .is_some_and(|src| std::ptr::eq(src.decl, f))
                        && let Some(scheme) = input.types.scheme(&f.name)
                    {
                        for (index, (param, _)) in scheme.generics.iter().enumerate() {
                            param_order.insert(param.id().clone(), (owner, index));
                        }
                    }
                });
            }
        }
        let declaration_param_names = input
            .types
            .datas
            .decls
            .values()
            .flat_map(|data| data.parameters())
            .chain(
                input
                    .types
                    .effects
                    .values()
                    .flat_map(|effect| effect.generics.clone()),
            )
            .map(|p| (p.id().clone(), p.name().to_string()))
            .collect();
        Lowerer {
            syntax_parsers: Vec::new(),
            declarations: Vec::new(),
            program: input.program,
            row_params: tauto_surface::surface::row_parameters_of(
                input.program.stmts.iter().filter_map(|s| match s {
                    Stmt::Struct(d) | Stmt::Enum(d) => Some(d),
                    _ => None,
                }),
            ),
            types: input.types,
            operation_facts: input.types.operation_instances_for(input.program),
            rows: input.rows,
            lib: input.lib,
            expansion_only: input.expansion_only,
            fns,
            effect_decls,
            nested_fns,
            local_caps: HashMap::new(),
            shown_locals: std::collections::HashSet::new(),
            param_order,
            param_names: HashMap::new(),
            declaration_param_names,
            param_values: HashMap::new(),
            host_skolems: None,
            datas: Vec::new(),
            data_index: HashMap::new(),
            rc_datas: HashSet::new(),
            rc_box: false,
            rc_enabled,
            rc_violation: false,
            carried,
            carried_wanted: Default::default(),
            unions: Vec::new(),
            union_ids: HashMap::new(),
            ops: Vec::new(),
            op_ids: HashMap::new(),
            insts: Vec::new(),
            inst_keys: HashMap::new(),
            inst_names: Vec::new(),
            meta: Vec::new(),
            work: VecDeque::new(),
            next_local: 0,
            next_handle: 0,
            cont_results: HashMap::new(),
            handle_results: Vec::new(),
            spawns: false,
            next_budget: 0,
            has_budget: {
                let mut found = false;
                for s in &input.program.stmts {
                    tauto_surface::surface::walk::values_stmt(s, &mut |n| {
                        if let tauto_surface::surface::walk::Node::Term(t) = n {
                            if matches!(&*t.kind, TermKind::Budget { .. }) {
                                found = true;
                            }
                        }
                    });
                }
                found
            },
            uhost_handlers: std::cell::OnceCell::new(),
            runs_budget: std::cell::RefCell::new(HashMap::new()),
            build_errors: Vec::new(),
            current_fn: None,
            rust_unsupported: std::cell::RefCell::new(None),
        }
    }

    fn run(&mut self, entries: Option<&BTreeSet<String>>) -> Result<Package, CompileError> {
        self.build_datas()?;
        // A `Decimal` anywhere in a signature is an error, called or not.
        let sigs: Vec<(TTy, Vec<(TParam, Kind)>)> = self
            .program
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Fn(f) => self
                    .types
                    .scheme(&f.name)
                    .map(|s| (s.ty.clone(), s.generics.clone())),
                _ => None,
            })
            .collect();
        for (t, parameters) in &sigs {
            self.param_names = parameters
                .iter()
                .map(|(p, _)| (p.id().clone(), p.name().to_string()))
                .collect();
            self.conv(t);
        }
        self.param_names.clear();
        let top = self.lower_top()?;
        let mut exports = Vec::new();
        if self.lib {
            for s in &self.program.stmts {
                let Stmt::Fn(f) = s else { continue };
                // A function the compiler made for a type (the `Debug`
                // instance of each type) is not the library's to export: it
                // is reached through the class, and a host's value (an
                // extern type) has no machine to carry its borrow.
                if !f.generics.is_empty()
                    || crate::types::is_made_instance(f.span)
                    || self.expansion_only.is_some_and(|e| e.contains(&f.name))
                    || entries.is_some_and(|names| !names.contains(f.name.as_str()))
                {
                    continue;
                }
                let id = self.instance(&f.name, BTreeMap::new(), false, false, false)?;
                let names: Vec<_> = match self
                    .rows
                    .declaration_row(&f.name, f.body.id())
                    .expect("declaration rows were checked before lowering")
                {
                    Some(declaration) => declaration.inferred.iter().cloned().collect(),
                    None => self
                        .rows
                        .functions
                        .iter()
                        .find(|(n, _)| *n == f.name)
                        .map(|(_, r)| r.iter().cloned().collect())
                        .unwrap_or_default(),
                };
                let row: Vec<String> = names.iter().map(ToString::to_string).collect();
                let foreign_row: Vec<String> = names
                    .iter()
                    .filter(|n| !export_may_perform(n))
                    .map(ToString::to_string)
                    .collect();
                exports.push(Export {
                    inst: id,
                    name: f.name.to_string(),
                    row,
                    foreign_row,
                    pure_borrow_callbacks: self.types.scheme(&f.name).map(|s| {
                        let TTy::Fn(params, _, _) = &s.ty else { return Vec::new() };
                        params.iter().enumerate().filter_map(|(i, ty)| {
                            let shared = matches!(ty, TTy::Borrow(inner, false) if matches!(**inner, TTy::Fn(..)));
                            let pure = f.param_types.get(i).and_then(Option::as_ref)
                                .and_then(pi_effects).is_some_and(|row| row.is_empty());
                            (shared && pure).then_some(i)
                        }).collect()
                    }).unwrap_or_default(),
                });
            }
        }
        while let Some(id) = self.work.pop_front() {
            self.lower_inst(id)?;
        }
        self.settle_bounds();
        let externs = self.extern_defs();
        let replaceable_externs = self.replaceable_extern_blocks();
        if let Some(e) = self.build_errors.first() {
            return Err(CompileError::Build(e.clone()));
        }
        let fns: Vec<FnInst> = std::mem::take(&mut self.insts)
            .into_iter()
            .map(|f| f.expect("an instance is lowered"))
            .collect();
        if self.rc_box {
            self.datas.push(ty::rc_box_def());
        }
        let mut pkg = Package {
            declarations: std::mem::take(&mut self.declarations),
            sources: None,
            syntax_parsers: std::mem::take(&mut self.syntax_parsers),
            datas: std::mem::take(&mut self.datas),
            unions: std::mem::take(&mut self.unions),
            ops: std::mem::take(&mut self.ops),
            fns,
            top: Some(top),
            exports,
            externs,
            replaceable_externs,
            host_omitted_fns: Default::default(),
            host_omitted_datas: Default::default(),
            host_omitted_unions: Default::default(),
            // `TAUTO_SYNC=1` builds a program that starts no task with `Arc`
            // too, for a host that moves its values between threads.
            sync: self.spawns || std::env::var_os("TAUTO_SYNC").is_some(),
            permissions: Vec::new(),
            rust_unsupported: self.rust_unsupported.take(),
            evidence: Default::default(),
        };
        tauto_nir::arms::instantiate(&mut pkg);
        // `TAUTO_KEEP_RECURSION=1` turns off the accumulators
        // (`accumulate.rs`): a function adding to its own result stays as
        // written.
        if std::env::var_os("TAUTO_KEEP_RECURSION").is_none() {
            tauto_nir::accumulate::introduce(&mut pkg, &mut |name, repr| {
                self.fresh_local(name, repr)
            });
        }
        // `TAUTO_KEEP_OWNED=1` turns off the borrowed parameters
        // (`borrow.rs`): every parameter stays owned.
        if std::env::var_os("TAUTO_KEEP_OWNED").is_none() {
            tauto_nir::borrow::infer(&mut pkg);
        }
        // `TAUTO_KEEP_CLONES=1` turns off the moves at the last use
        // (`last_use.rs`): every clone stays in.
        if std::env::var_os("TAUTO_KEEP_CLONES").is_none() {
            tauto_nir::last_use::elide(&mut pkg);
        }
        // After the borrowed parameters, which decide which parameters a
        // self call in tail position must pass on unchanged.
        tauto_nir::tail::mark(&mut pkg);
        Ok(pkg)
    }

    fn replaceable_extern_blocks(&self) -> Vec<tauto_nir::ReplaceableExternBlock> {
        let mut out = Vec::new();
        for s in &self.program.stmts {
            let Stmt::Extern {
                fns,
                instances,
                types,
                structs,
                enums,
                span,
            } = s
            else {
                continue;
            };
            if !tauto_surface::surface::extern_is_replaceable(fns, instances, types, structs, enums)
            {
                continue;
            }
            out.push(tauto_nir::ReplaceableExternBlock {
                id: tauto_surface::surface::extern_block_id(fns, types, structs, enums),
                fn_names: fns.iter().map(|f| f.name.clone()).collect(),
                fn_waits: fns
                    .iter()
                    .map(|f| {
                        f.effects.as_ref().is_some_and(|row| {
                            row.iter()
                                .any(|e| tauto_surface::bindings::is_library(e, "wait"))
                        })
                    })
                    .collect(),
                data_names: structs
                    .iter()
                    .chain(enums.iter())
                    .map(|d| d.name.clone())
                    .collect(),
                span: *span,
            });
        }
        out
    }

    fn extern_defs(&mut self) -> Vec<ExternDef> {
        let mut out = Vec::new();
        for s in &self.program.stmts {
            let Stmt::Extern {
                fns,
                instances,
                types,
                structs,
                enums,
                ..
            } = s
            else {
                continue;
            };
            // Replaceable blocks are not required host externs until selected.
            if tauto_surface::surface::extern_is_replaceable(fns, instances, types, structs, enums)
            {
                continue;
            }
            for f in fns {
                let Some(scheme) = self.types.scheme(&f.name) else {
                    continue;
                };
                let TTy::Fn(ps, ret, _) = scheme.ty.clone() else {
                    continue;
                };
                let generics = f.generics.clone();
                self.param_names = scheme
                    .generics
                    .iter()
                    .map(|(p, _)| (p.id().clone(), p.name().to_string()))
                    .collect();
                let mut params = Vec::new();
                for (i, name) in f.params.iter().enumerate() {
                    let t = ps.get(i).cloned().unwrap_or(TTy::Var(0));
                    let pass = match &t {
                        TTy::Borrow(_, true) => Pass::RefMut,
                        TTy::Borrow(_, false) => Pass::Ref,
                        _ => Pass::Value,
                    };
                    let inner = t.unborrowed().clone();
                    let mut nty = self.conv(&inner);
                    if let Some(effects) = f
                        .param_types
                        .get(i)
                        .and_then(|d| d.as_ref())
                        .and_then(pi_effects)
                    {
                        let row: Row = effects.into_iter().collect();
                        let tier = self.value_tier(&row, &HashMap::new());
                        ty::set_fn_tier(&mut nty, tier);
                    }
                    params.push((name.clone(), nty, pass));
                }
                let ret = self.conv(&ret);
                self.param_names.clear();
                out.push(ExternDef {
                    name: f.name.clone(),
                    generics: generics.into_iter().map(|n: Name| n.to_string()).collect(),
                    params: params
                        .into_iter()
                        .map(|(n, t, p): (Name, Ty, Pass)| (n.to_string(), t, p))
                        .collect(),
                    ret,
                    lends: f.lends.as_ref().map(|lends| {
                        f.params
                            .iter()
                            .map(|p| {
                                lends
                                    .iter()
                                    .any(|l| l.split('.').next() == Some(p.as_str()))
                            })
                            .collect()
                    }),
                    waits: f.effects.as_ref().is_some_and(|row| {
                        row.iter()
                            .any(|e| tauto_surface::bindings::is_library(e, "wait"))
                    }),
                    span: f.span,
                });
            }
        }
        out
    }

    pub fn fresh_local(&mut self, name: &str, repr: Repr) -> Local {
        self.next_local += 1;
        Local {
            id: self.next_local,
            name: sanitize(name),
            repr,
        }
    }

    pub fn kind_of(&self, t: &TTy) -> Kind {
        match t {
            TTy::Param(_, k) => *k,
            t => self.types.datas.kind(t),
        }
    }

    // ---- rows and tiers ------------------------------------------------

    pub fn quant(&self, effect: &Name) -> Quant {
        self.rows
            .quants
            .get(effect)
            .copied()
            .or_else(|| self.types.quants.get(effect).copied())
            .unwrap_or(Quant::AtMostOne)
    }

    pub fn effect_tier(&self, effect: &Name, rowvars: &HashMap<Name, Tier>) -> Tier {
        if let Some(v) = effect.row_variable() {
            if let Some(tier) = carried_tier(&v) {
                return tier;
            }
            return rowvars.get(&v).copied().unwrap_or(Tier::S);
        }
        // The LLVM backend does not suspend: what the host would wait for or
        // answer by running the entry's body, it answers where it is
        // performed, or refuses there.
        if self.rows.target == Target::Llvm
            && (tauto_surface::bindings::is_library(&effect, "main")
                || crate::host::HOST_EFFECTS
                    .iter()
                    .any(|l| tauto_surface::bindings::is_library(&effect, l)))
        {
            return Tier::S;
        }
        // `spawn` is lowered to a call of the body (`handle.rs`).
        if effect.starts_with('?')
            || tauto_surface::bindings::is_divergence(&effect)
            || tauto_surface::bindings::is_library(&effect, "budget")
            || tauto_surface::bindings::is_library(&effect, "budget_memory")
            || tauto_surface::bindings::is_library(&effect, "spawn")
        {
            return Tier::S;
        }
        if tauto_surface::bindings::is_library(&effect, "exceeded") {
            return Tier::O;
        }
        match self.quant(effect) {
            Quant::Direct => Tier::S,
            Quant::Zero => Tier::A,
            Quant::AtMostOne | Quant::One => Tier::O,
            Quant::Many => Tier::M,
        }
    }

    /// Refuses, for the LLVM backend, `t`: a call of a function value that
    /// performs a `direct` operation where no `direct` handler is held
    /// (`Cx::detached`). The LLVM backend cannot answer it.
    pub fn refuse_detached_direct(&self, cx: &Cx, t: &SurfaceTerm, what: Message) {
        if self.rows.target == Target::Llvm && cx.detached && self.has_direct(&self.term_row(t)) {
            self.rust_unsupported
                .borrow_mut()
                .get_or_insert_with(|| Unsupported {
                    what: msg!("nir-in-a-kept-continuation", what = what),
                    span: Some(t.span),
                });
        }
    }

    /// Whether `row` has a `direct` operation (row variables aside).
    pub fn has_direct(&self, row: &Row) -> bool {
        row.iter().any(|e| {
            !e.row_variable().is_some() && !e.starts_with('?') && self.quant(e) == Quant::Direct
        })
    }

    pub fn row_tier(&self, row: &Row, rowvars: &HashMap<Name, Tier>) -> Tier {
        row.iter()
            .map(|e| self.effect_tier(e, rowvars))
            .max()
            .unwrap_or(Tier::S)
    }

    /// A divergent call can suspend at a budget tick. Its function value
    /// therefore uses the same future ABI as an at-most-once operation.
    pub fn row_tier_in(&self, row: &Row, cx: &Cx) -> Tier {
        let tier = self.row_tier(row, &cx.rowvars);
        if cx.under_budget && row.contains(&tauto_surface::bindings::divergence()) {
            tier.max(Tier::O)
        } else {
            tier
        }
    }

    /// The tier of a function value whose type is written with `row`. In a
    /// program that runs a `budget`, a divergent function value may be made
    /// outside one and called inside one, or the other way round, and where
    /// it goes is not followed: it is held at the O tier, which counts the
    /// steps of a budget it runs under and the host's outside any (called
    /// where nothing suspends, it is run to its end there).
    pub fn value_tier(&self, row: &Row, rowvars: &HashMap<Name, Tier>) -> Tier {
        let tier = self.row_tier(row, rowvars);
        if self.has_budget && row.contains(&tauto_surface::bindings::divergence()) {
            tier.max(Tier::O)
        } else {
            tier
        }
    }

    /// [`Lowerer::value_tier`] where `cx` gives the row variables.
    pub fn value_tier_in(&self, row: &Row, cx: &Cx) -> Tier {
        self.value_tier(row, &cx.rowvars)
            .max(self.row_tier_in(row, cx))
    }

    /// Whether `name` runs a `budget`, in its body or through a function it
    /// calls by name. Such a function ticks even when its row has no `div`,
    /// so called under a budget it counts the outer budget's steps, and must
    /// be able to stop where that one runs out: it is given the instance of
    /// the O tier, as a divergent function is.
    pub fn runs_budget(&self, name: &Name) -> bool {
        if let Some(known) = self.runs_budget.borrow().get(name) {
            return *known;
        }
        let Some(src) = self.fns.get(name) else {
            return false;
        };
        // A recursive call does not decide it: the rest of the body does.
        self.runs_budget.borrow_mut().insert(name.clone(), false);
        let mut found = false;
        let mut callees = Vec::new();
        tauto_surface::surface::walk::value_terms(&src.decl.body, &mut |t| match &*t.kind {
            TermKind::Budget { .. } => found = true,
            TermKind::Var(n) => callees.push(n.clone()),
            _ => {}
        });
        let found = found || callees.iter().any(|c| c != name && self.runs_budget(c));
        self.runs_budget.borrow_mut().insert(name.clone(), found);
        found
    }

    /// The row callers of `name` see: the written one, else the inferred one.
    pub fn fn_row(&self, name: &Name) -> Row {
        let Some(src) = self.fns.get(name) else {
            return Row::new();
        };
        if let Some(declaration) = self
            .rows
            .declaration_row(name, src.decl.body.id())
            .expect("declaration rows were checked before lowering")
        {
            return declaration.row.clone();
        }
        match &src.decl.effects {
            Some(w) => w.iter().cloned().collect(),
            None => self
                .rows
                .functions
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, r)| r.clone())
                .unwrap_or_default(),
        }
    }

    /// The row variables this backend can specialize, with their exact
    /// declaration owner checked before reducing them to source tokens.
    pub fn row_vars(&self, decl: &FnDecl) -> R<Vec<Name>> {
        fn note(effects: &[Name], vars: &mut Vec<Name>) {
            for effect in effects {
                if let Some(var) = effect.row_variable()
                    && !vars.iter().any(|known| known == &var)
                {
                    vars.push(var);
                }
            }
        }
        // `supplied`: whether the caller gives the function written at `t`,
        // so that the body calls it. Below a parameter of a function type
        // the body gives it instead: `part` in `lift: (part: () -> Unit !
        // e) -> Unit` is a function the body makes. Such a function is made
        // at the tier `e` is specialized to and passed on as any function
        // value is; only a function the body receives must be called at the
        // tier it was made at, so only a supplied one that is not a direct
        // callback parameter keeps `e` from being read off one.
        fn type_vars(
            t: &SurfaceTerm,
            direct: bool,
            supplied: bool,
            vars: &mut Vec<Name>,
            nested: &mut HashSet<Name>,
        ) {
            match &*t.kind {
                TermKind::Pi {
                    params,
                    result,
                    effects,
                    ..
                } => {
                    if let Some(effects) = effects {
                        note(effects, vars);
                        if !direct && supplied {
                            nested.extend(effects.iter().filter_map(Name::row_variable));
                        }
                    }
                    for (_, param) in params {
                        type_vars(param, false, !supplied, vars, nested);
                    }
                    type_vars(result, false, supplied, vars, nested);
                }
                TermKind::Borrow { term, .. }
                | TermKind::Tagged { term, .. }
                | TermKind::FnKind { ty: term, .. } => {
                    type_vars(term, direct, supplied, vars, nested)
                }
                TermKind::App {
                    function,
                    arguments,
                } => {
                    // A data type's argument is read as both: its fields
                    // may be functions either side gives.
                    type_vars(function, false, true, vars, nested);
                    for argument in arguments {
                        type_vars(argument, false, true, vars, nested);
                    }
                }
                TermKind::Union(types) => {
                    for ty in types {
                        type_vars(ty, false, true, vars, nested);
                    }
                }
                _ => {}
            }
        }
        let mut vars = Vec::new();
        let mut nested = HashSet::new();
        let mut inferable = HashSet::new();
        if let Some(effects) = &decl.effects {
            note(effects, &mut vars);
        }
        for ty in decl.param_types.iter().flatten() {
            if let Some(effects) = pi_effects(ty) {
                inferable.extend(effects.iter().filter_map(Name::row_variable));
            }
            type_vars(ty, true, true, &mut vars, &mut nested);
        }
        if let Some(result) = &decl.result {
            type_vars(result, true, true, &mut vars, &mut nested);
        }
        // A row variable given to a data type (`l: Lift(e)`) is one too: the
        // records of that type hold their functions at the tier a call gives
        // it (`Lowerer::data_arg_row_tier`).
        let row_generics: Vec<&Name> = decl
            .generics
            .iter()
            .zip(&decl.rows)
            .filter(|(_, row)| **row)
            .map(|(g, _)| g)
            .collect();
        let mut data_args = Vec::new();
        for ty in decl.param_types.iter().flatten().chain(&decl.result) {
            data_row_args(ty, &row_generics, &mut data_args);
        }
        let data_args: Vec<Name> = data_args
            .into_iter()
            .filter(|v| !vars.contains(v))
            .collect();
        vars.extend(data_args.iter().cloned());
        if vars.is_empty() {
            return Ok(vars);
        }
        let assumed = assumed_row_vars(decl);
        let declaration = self
            .rows
            .declaration_row(&decl.name, decl.body.id())
            .map_err(|what| Unsupported {
                what,
                span: Some(decl.span),
            })?
            .ok_or_else(|| Unsupported {
                what: msg!("nir-effect-row-owner", decl = decl.name.as_str()),
                span: Some(decl.span),
            })?;
        for var in &vars {
            if !self
                .rows
                .row_variables
                .values()
                .any(|binding| binding.owner == declaration.owner && binding.name == *var)
            {
                return unsupported(
                    msg!(
                        "nir-row-variable-of-is-not-owned",
                        var = var.to_string(),
                        decl = decl.name.to_string()
                    ),
                    decl.span,
                );
            }
            // A row variable outside a direct callback parameter, such as one
            // carried by a record, is specialized from the instantiated row
            // of each call, so it must be in the function's own row.
            let in_own_row = decl
                .effects
                .iter()
                .flatten()
                .any(|effect| effect.row_variable().as_ref() == Some(var));
            if (nested.contains(var) || !inferable.contains(var))
                && !in_own_row
                && !assumed.contains(var)
                && !data_args.contains(var)
            {
                return unsupported(
                    msg!(
                        "nir-row-variable-of-cannot-be-specialized",
                        var = var.to_string(),
                        decl = decl.name.to_string()
                    ),
                    decl.span,
                );
            }
        }
        Ok(vars)
    }

    /// The effects a term performs: from the calls `rows.rs` recorded,
    /// without what a `handle` inside answers, and not looking inside a
    /// closure.
    pub fn term_row(&self, t: &SurfaceTerm) -> Row {
        let mut row = Row::new();
        self.term_row_into(t, &mut row);
        row
    }

    fn term_row_into(&self, t: &SurfaceTerm, row: &mut Row) {
        use tauto_surface::surface::{Handler, Pattern};
        match &*t.kind {
            TermKind::App { .. } if let Some(members) = t.product_value_members() => {
                members.iter().for_each(|v| self.term_row_into(v, row))
            }
            TermKind::Perform { args, .. } => {
                args.iter().for_each(|a| self.term_row_into(a, row));
                if let Some(r) = self.rows.calls.get(&t.id()) {
                    row.extend(r.iter().cloned());
                }
            }
            TermKind::App {
                function,
                arguments,
            } => {
                // A call is first what it performs itself.
                if let Some(r) = self.rows.calls.get(&t.id()) {
                    row.extend(r.iter().cloned());
                }
                // The call report may omit a top-level lambda's divergence;
                // named recursion still requires budget instrumentation.
                if let TermKind::Var(name) = &*function.kind
                    && self
                        .fn_row(name)
                        .contains(&tauto_surface::bindings::divergence())
                {
                    row.insert(tauto_surface::bindings::divergence());
                }
                self.term_row_into(function, row);
                arguments.iter().for_each(|a| self.term_row_into(a, row));
            }
            TermKind::Handle { body, handlers } => {
                let mut inner = Row::new();
                self.term_row_into(body, &mut inner);
                for h in handlers {
                    if let Handler::Operation {
                        effect,
                        patterns,
                        guard: None,
                        ..
                    } = h
                        && patterns
                            .iter()
                            .all(|p| matches!(p, Pattern::Wild | Pattern::Bind { .. }))
                    {
                        if tauto_surface::bindings::is_library(&effect, "exceeded") {
                            inner.remove(&tauto_surface::bindings::library_name("exceeded"));
                        } else {
                            inner.remove(effect);
                        }
                    }
                }
                row.extend(inner);
                for h in handlers {
                    match h {
                        Handler::Return { body, .. } => self.term_row_into(body, row),
                        Handler::Operation { body, guard, .. } => {
                            if let Some(g) = guard {
                                self.term_row_into(g, row);
                            }
                            self.term_row_into(body, row);
                        }
                    }
                }
            }
            TermKind::Budget { limit, steps, body } => {
                self.term_row_into(steps, row);
                let mut inner = Row::new();
                self.term_row_into(body, &mut inner);
                // Only steps stop a body that does not: a memory budget
                // leaves `div` in the row.
                if *limit == BudgetLimit::Steps {
                    inner.remove(&tauto_surface::bindings::divergence());
                }
                row.extend(inner);
                row.insert(tauto_surface::bindings::library_name("exceeded"));
            }
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } => {}
            TermKind::Block(stmts) => {
                for s in stmts {
                    match s {
                        Stmt::Let { value, .. }
                        | Stmt::Var { value, .. }
                        | Stmt::Assign { value, .. } => self.term_row_into(value, row),
                        Stmt::Expr(e) | Stmt::Return(Some(e)) => self.term_row_into(e, row),
                        Stmt::While { condition, body } => {
                            self.term_row_into(condition, row);
                            self.term_row_into(body, row);
                            row.insert(tauto_surface::bindings::divergence());
                        }
                        // `lower_fors` / `lower_loops` expand them where the program is read.
                        Stmt::For { .. } | Stmt::Loop { .. } | Stmt::Break(_) | Stmt::Continue => {}
                        _ => {}
                    }
                }
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.term_row_into(condition, row);
                self.term_row_into(then, row);
                if let Some(o) = otherwise {
                    self.term_row_into(o, row);
                }
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                self.term_row_into(scrutinee, row);
                for a in arms {
                    if let Some(g) = &a.guard {
                        self.term_row_into(g, row);
                    }
                    self.term_row_into(&a.body, row);
                }
            }
            TermKind::Field { base, .. } => self.term_row_into(base, row),
            TermKind::Tagged { term, .. } | TermKind::Borrow { term, .. } => {
                self.term_row_into(term, row)
            }
            TermKind::Record { fields, .. } => {
                fields.iter().for_each(|(_, v)| self.term_row_into(v, row))
            }
            _ => {}
        }
    }

    pub fn instance(
        &mut self,
        name: &Name,
        rowvars: BTreeMap<Name, Tier>,
        under_budget: bool,
        m: bool,
        detached: bool,
    ) -> R<InstId> {
        let decl = self.fns[name].decl;
        let row_parameters = self.row_vars(decl)?;
        for var in &row_parameters {
            if !rowvars.contains_key(var) {
                return unsupported(
                    msg!(
                        "nir-row-variable-of-has-no-checked",
                        var = var.to_string(),
                        name = name.to_string()
                    ),
                    decl.span,
                );
            }
        }
        // A row variable only a record carries (`Handlers(!{key | e})`), or
        // one given to a data type's row parameter (`App(R, e)`, which the
        // data type erases), is no Rust type either.
        let mut row_parameters = row_parameters;
        for (parameter, row) in decl.generics.iter().zip(&decl.rows) {
            if *row && !row_parameters.contains(parameter) {
                row_parameters.push(parameter.clone());
            }
        }
        let data_rows = &self.row_params;
        for ty in decl.param_types.iter().flatten().chain(&decl.result) {
            let mut ty = ty.clone();
            tauto_surface::surface::walk::term(&mut ty, &mut |t| {
                let mut add = |v: &Name| {
                    if !row_parameters.iter().any(|r| r == v) {
                        row_parameters.push(v.clone());
                    }
                };
                match &*t.kind {
                    TermKind::Row(effects) => effects
                        .iter()
                        .filter_map(Name::row_variable)
                        .for_each(|v| add(&v)),
                    TermKind::App {
                        function,
                        arguments,
                    } => {
                        let TermKind::Var(head) = &*function.kind else {
                            return;
                        };
                        for i in data_rows.get(head).into_iter().flatten() {
                            if let Some(TermKind::Var(v)) = arguments.get(*i).map(|a| &*a.kind) {
                                add(v);
                            }
                        }
                    }
                    _ => {}
                }
            });
        }
        let key = InstKey {
            name: name.clone(),
            rowvars: rowvars.into_iter().collect(),
            under_budget,
            m,
            detached,
        };
        if let Some(id) = self.inst_keys.get(&key) {
            return Ok(*id);
        }
        let id = self.insts.len();
        self.insts.push(None);
        self.inst_keys.insert(key.clone(), id);
        self.inst_names.push(key);
        let decl = self.fns[name].decl;
        let Some(scheme) = self.types.scheme(name) else {
            return unsupported(msg!("nir-no-type-for", name = name.to_string()), decl.span);
        };
        // Row binders specialize tiers, not Rust value types. The checked
        // declaration owner above makes this source-signature bridge local
        // to this exact scheme; subsequent maps remain identity-keyed.
        let mut parameters: Vec<_> = scheme
            .generics
            .iter()
            .filter(|(param, _)| !row_parameters.iter().any(|row| row == param.reference()))
            .cloned()
            .collect();
        let own_parameters = parameters.len();
        let mut captured = Vec::new();
        for cap in self.local_caps.get(name).into_iter().flatten() {
            collect_parameters(&cap.ty, &mut captured);
        }
        captured.retain(|(p, _)| !parameters.iter().any(|(own, _)| own.id() == p.id()));
        for (p, _) in &captured {
            if !self.param_order.contains_key(p.id()) {
                return unsupported(
                    msg!(
                        "nir-the-declaration-of-captured-type-parameter",
                        p = p.name().to_string()
                    ),
                    decl.span,
                );
            }
        }
        captured.sort_by_key(|(p, _)| self.param_order[p.id()]);
        parameters.extend(captured);
        let reserved: HashSet<&str> = parameters.iter().map(|(p, _)| p.name()).collect();
        let mut used = HashSet::new();
        let mut param_names = HashMap::new();
        let mut generics = Vec::new();
        for (index, (p, _)) in parameters.iter().enumerate() {
            let mut output = p.name().to_string();
            if used.contains(&output) {
                output = format!("{}__p{index}", p.name());
                while reserved.contains(output.as_str()) || used.contains(&output) {
                    output.push('_');
                }
            }
            used.insert(output.clone());
            param_names.insert(p.id().clone(), output.clone());
            generics.push(output);
        }
        self.meta.push(InstMeta {
            generics,
            parameters,
            own_parameters,
            param_names,
            ..InstMeta::default()
        });
        self.work.push_back(id);
        Ok(id)
    }

    pub fn inst_tier(&self, name: &Name, rowvars: &[(Name, Tier)]) -> Tier {
        let map: HashMap<Name, Tier> = rowvars.iter().cloned().collect();
        self.row_tier(&self.fn_row(name), &map)
    }

    fn lower_inst(&mut self, id: InstId) -> R<()> {
        let key = self.inst_names[id].clone();
        let src = &self.fns[&key.name];
        let decl = src.decl;
        let origin = src.origin;
        self.current_fn = Some(key.name.clone());
        if matches!(origin, Origin::Builtin | Origin::Extern) {
            // Reached through a function value.
            return unsupported(
                msg!("nir-the-extern", decl = decl.name.to_string()),
                decl.span,
            );
        }
        let mut tier = self.inst_tier(&key.name, &key.rowvars);
        if key.under_budget {
            tier = tier.max(Tier::O);
        }
        if key.m || key.detached {
            tier = Tier::M;
        }
        let Some(scheme) = self.types.scheme(&decl.name) else {
            return unsupported(
                msg!("nir-no-type-for", name = decl.name.to_string()),
                decl.span,
            );
        };
        let TTy::Fn(ptys, ret, _) = scheme.ty.clone() else {
            return unsupported(
                msg!("nir-is-not-a-function", decl = decl.name.to_string()),
                decl.span,
            );
        };
        self.param_names = self.meta[id].param_names.clone();
        let rowvars: HashMap<Name, Tier> = key.rowvars.iter().cloned().collect();
        let mut cx = Cx {
            bindings: Vec::new(),
            capture_bindings: Vec::new(),
            hidden_bindings: HashSet::new(),
            rowvars,
            tier,
            frames: Vec::new(),
            ret: (*ret).clone(),
            inst: id,
            under_budget: key.under_budget,
            host_m: false,
            host_ret: false,
            detached: key.detached,
            written: HashMap::new(),
            held: HashMap::new(),
            lam_param_rows: Vec::new(),
            lam_params_carried: false,
            nat_tests: Vec::new(),
        };
        let mut params = Vec::new();
        for cap in self.local_caps.get(&decl.name).cloned().unwrap_or_default() {
            let binding = cx.bindings.len();
            if let Some(repr) = cap.cell {
                let inner = self.conv(&cap.ty);
                let local = self.fresh_local(&cap.name, repr);
                let cell = match repr {
                    Repr::SharedVar(true) => Ty::SharedVar(true, Box::new(inner)),
                    _ => Ty::SharedVar(false, Box::new(inner)),
                };
                cx.bindings.push(Binding {
                    name: cap.name.clone(),
                    local: local.clone(),
                    ty: cap.ty.clone(),
                    mode: Mode::Var,
                    fn_row: None,
                    budgeted: cx.under_budget,
                    celled: true,
                });
                params.push(Param {
                    local,
                    ty: Ty::Ref(Box::new(cell)),
                });
            } else {
                let (local, nty) = self.bind_param(&mut cx, &cap.name, &cap.ty, None);
                params.push(Param { local, ty: nty });
                if cap.source_owned {
                    // Borrowing is the shared helper's ABI, not the
                    // source ownership of its declaration-time snapshot.
                    cx.bindings[binding].ty = cap.ty.unborrowed().clone();
                    cx.bindings[binding].mode = Mode::Owned;
                }
            }
            if let Some(forwarded) = cap.forwarded {
                cx.hidden_bindings.insert(cx.bindings[binding].local.id);
                cx.capture_bindings.push((forwarded, binding));
            }
            cx.capture_bindings.push((cap.key, binding));
        }
        for (i, name) in decl.params.iter().enumerate() {
            let pty = ptys.get(i).cloned().unwrap_or(TTy::Var(0));
            let declared = decl.param_types.get(i).and_then(|t| t.as_ref());
            let (local, nty) = self.bind_param(&mut cx, name, &pty, declared);
            params.push(Param { local, ty: nty });
        }
        // The body gives the result at the tiers the written result type
        // holds its functions at (`conv_in`): a closure it returns is made
        // for that tier, as a caller of this instance receives it.
        let ret_ty = self.conv_in(&cx, &ret, decl.result.as_ref());
        let body = self.expr_expect(&mut cx, &decl.body, &ret)?;
        let body = self.coerce(body, &ret_ty);
        let generics = self.meta[id].generics.clone();
        // A cell of shared data is cloned to be taken apart: `Clone` for what
        // fills it.
        let mut in_shared = HashSet::new();
        for t in ptys.iter().chain(std::iter::once(&*ret)) {
            self.shared_params(t, &mut in_shared);
        }
        for cap in self.local_caps.get(&decl.name).into_iter().flatten() {
            self.shared_params(&cap.ty, &mut in_shared);
        }
        for (p, k) in self.meta[id].parameters.clone() {
            if k.dup() || in_shared.contains(p.id()) {
                let output = self
                    .param_name(&p)
                    .expect("instance parameter name")
                    .to_string();
                self.meta[id]
                    .bounds
                    .entry(output)
                    .or_default()
                    .insert(Bound::Clone);
            }
        }
        self.insts[id] = Some(FnInst {
            id,
            source: decl.name.clone(),
            tier,
            generics: generics.into_iter().map(|g| (g, BTreeSet::new())).collect(),
            params,
            ret: ret_ty,
            fn_region: false,
            lends: decl.lends.as_ref().map(|lends| {
                decl.params
                    .iter()
                    .map(|p| {
                        lends
                            .iter()
                            .any(|l| l.split('.').next() == Some(p.as_str()))
                    })
                    .collect()
            }),
            body,
            span: decl.span,
        });
        self.param_names.clear();
        Ok(())
    }

    fn shared_params(&self, t: &TTy, out: &mut HashSet<ParamId>) {
        fn params(t: &TTy, out: &mut HashSet<ParamId>) {
            match t {
                TTy::Param(p, _) => {
                    out.insert(p.id().clone());
                }
                TTy::Named(_, args) => args.iter().for_each(|a| params(a, out)),
                TTy::Fn(ps, r, _) => {
                    ps.iter().for_each(|a| params(a, out));
                    params(r, out);
                }
                TTy::Union(ts) => ts.iter().for_each(|a| params(a, out)),
                TTy::Tagged(_, t) | TTy::Info(t) | TTy::Borrow(t, _) => params(t, out),
                _ => {}
            }
        }
        match t {
            TTy::Named(n, args) => {
                if self.rc_datas.contains(n) {
                    args.iter().for_each(|a| params(a, out));
                }
                args.iter().for_each(|a| self.shared_params(a, out));
            }
            TTy::Fn(ps, r, _) => {
                ps.iter().for_each(|a| self.shared_params(a, out));
                self.shared_params(r, out);
            }
            TTy::Union(ts) => ts.iter().for_each(|a| self.shared_params(a, out)),
            TTy::Tagged(_, t) | TTy::Info(t) | TTy::Borrow(t, _) => self.shared_params(t, out),
            _ => {}
        }
    }

    pub fn bind_param(
        &mut self,
        cx: &mut Cx,
        name: &Name,
        ty: &TTy,
        declared: Option<&SurfaceTerm>,
    ) -> (Local, Ty) {
        let nty = self.conv_in(cx, ty, declared);
        let is_fn = matches!(ty.unborrowed(), TTy::Fn(..));
        let repr = match ty {
            TTy::Borrow(inner, _) if matches!(**inner, TTy::Fn(..)) => Repr::FnRef,
            TTy::Borrow(_, false) | TTy::Orig(_) => Repr::Ref,
            TTy::Borrow(_, true) => Repr::RefMut,
            _ => Repr::Plain,
        };
        let local = self.fresh_local(name, repr);
        if let Some(d) = declared {
            cx.written.insert(local.id, d.clone());
        }
        let fn_row = if is_fn {
            declared.map(|d| pi_effects(d).into_iter().flatten().collect::<Row>())
        } else {
            None
        };
        cx.bindings.push(Binding {
            name: name.clone(),
            local: local.clone(),
            ty: ty.clone(),
            mode: match ty {
                TTy::Borrow(_, m) => Mode::Borrow(*m),
                _ => Mode::Owned,
            },
            fn_row,
            budgeted: cx.under_budget,
            celled: false,
        });
        (local, nty)
    }

    fn lower_top(&mut self) -> R<InstId> {
        // What reaches the top level is the host's: a `wait` there makes the
        // top level a future the host runs (`tauto_rt::o::run_top`).
        // The host's handler waits for what may take a while (`sleep`,
        // `net`): the top level it is put outside of is a future too.
        let hosted = self.hosted();
        let tier = if (self.rows.host_waits || hosted) && self.rows.target != Target::Llvm {
            Tier::O
        } else {
            Tier::S
        };
        let id = self.insts.len();
        self.insts.push(None);
        let top: Name = tauto_surface::identity::DeclRef::fresh("<top>").into();
        self.inst_names.push(InstKey {
            name: top.clone(),
            rowvars: Vec::new(),
            under_budget: false,
            m: false,
            detached: false,
        });
        self.meta.push(InstMeta::default());
        let mut cx = Cx {
            bindings: Vec::new(),
            capture_bindings: Vec::new(),
            hidden_bindings: HashSet::new(),
            rowvars: HashMap::new(),
            tier,
            frames: Vec::new(),
            ret: TTy::Unit,
            inst: id,
            under_budget: false,
            host_m: false,
            host_ret: false,
            detached: false,
            written: HashMap::new(),
            held: HashMap::new(),
            lam_param_rows: Vec::new(),
            lam_params_carried: false,
            nat_tests: Vec::new(),
        };
        let stmts: Vec<&Stmt> = self.program.stmts.iter().collect();
        let block = self.block_of(&mut cx, &stmts, true, &TTy::Unit)?;
        let span = Span::new(0, 0);
        let mut body = Expr {
            kind: ExprKind::Block(block),
            ty: Ty::Unit,
            span,
        };
        // The host is the outermost handler: what reaches the top level
        // unanswered, its direct arms answer where it is performed. What
        // the host's handler leaves to the host (`wait`) the backend's
        // driver answers (`tauto_rt::o::run_top`), so a top level that
        // reaches only `wait` gets no handler, which would bring every host
        // primitive into a target that has none of them (the browser).
        if hosted && self.rows.host_effects.iter().any(|e| e.as_str() != "wait") {
            // The arms of the standard effects that reach the top level;
            // the bodies of entries may perform any of them.
            let mut answered = (!self.rows.entries).then(|| self.rows.host_effects.clone());
            if self.rows.target == Target::Llvm
                && let Some(a) = &mut answered
            {
                a.retain(|e| Self::llvm_hosted(&Name::from(e.as_str())));
            }
            body = self.host_handle(&mut cx, body, answered.as_ref())?;
        }
        self.insts[id] = Some(FnInst {
            fn_region: false,
            lends: None,
            id,
            source: top,
            tier,
            generics: Vec::new(),
            params: Vec::new(),
            ret: Ty::Unit,
            body,
            span,
        });
        Ok(id)
    }

    /// Closes the bounds over the calls: a callee's type parameter needs
    /// `Show` / `==` of what the caller passes for it, so the caller's
    /// parameters in that type need it too.
    fn settle_bounds(&mut self) {
        self.seed_static();
        loop {
            let mut changed = false;
            for caller in 0..self.meta.len() {
                let edges: Vec<(InstId, Vec<(String, Ty)>)> = self.meta[caller]
                    .edges
                    .iter()
                    .map(|e| (e.callee, e.args.clone()))
                    .collect();
                for (callee, args) in edges {
                    for (param, ty) in args {
                        let needs: Vec<Bound> = self.meta[callee]
                            .bounds
                            .get(&param)
                            .map(|b| b.iter().copied().collect())
                            .unwrap_or_default();
                        if needs.is_empty() {
                            continue;
                        }
                        if needs.contains(&Bound::Clone) && !self.cloneable(&ty) {
                            self.rc_violation = true;
                        }
                        let mut ps = BTreeSet::new();
                        ty.params(&mut ps);
                        for p in ps {
                            for b in &needs {
                                if self.meta[caller]
                                    .bounds
                                    .entry(p.clone())
                                    .or_default()
                                    .insert(*b)
                                {
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for (i, f) in self.insts.iter_mut().enumerate() {
            let Some(f) = f else { continue };
            for (g, bounds) in &mut f.generics {
                if let Some(b) = self.meta[i].bounds.get(g) {
                    bounds.extend(b.iter().copied());
                }
            }
        }
    }

    /// Marks `Static` on every type parameter of an instance that builds a
    /// function value, performs or handles an effect, runs a budget, starts a
    /// task or calls an extern: what
    /// such an instance carries leaves the reach of a lifetime the host can
    /// name. Its callers then need `Static` of what they pass, through the
    /// calls, as for the other bounds.
    fn seed_static(&mut self) {
        let mut candidates = Vec::new();
        for (i, f) in self.insts.iter().enumerate() {
            let Some(f) = f else { continue };
            if f.generics.is_empty() {
                continue;
            }
            let mut carries = false;
            f.body.walk_with_handlers(&mut |e| {
                carries |= matches!(
                    e.kind,
                    ExprKind::Closure(_)
                        | ExprKind::FnValue { .. }
                        | ExprKind::FnCast(_)
                        | ExprKind::Perform(_)
                        | ExprKind::Handle(_)
                        | ExprKind::Inject { .. }
                        | ExprKind::Remap { .. }
                        | ExprKind::Budget(_)
                ) || matches!(&e.kind, ExprKind::Call(c) if match &c.callee {
                    // A task's body runs past the caller, and an extern's
                    // wrapper takes `'static` of its type parameters.
                    Callee::Builtin(b) => matches!(b.as_str(), "pending_spawn" | "Os::offload"),
                    Callee::Extern(_) => true,
                    _ => false,
                });
            });
            if carries {
                candidates.push(i);
            }
        }
        // An instance that only builds function values and keeps them inside
        // its call gives them a region of its own instead of `'static`.
        let mut region: BTreeSet<InstId> = candidates
            .iter()
            .copied()
            .filter(|&i| self.insts[i].as_ref().is_some_and(fn_values_only))
            .collect();
        loop {
            let before = region.len();
            let kept: BTreeSet<InstId> = region
                .iter()
                .copied()
                .filter(|&i| {
                    let f = self.insts[i].as_ref().unwrap();
                    let mut ok = true;
                    f.body.walk_with_handlers(&mut |e| {
                        if let ExprKind::Call(c) = &e.kind
                            && c.args.iter().any(|a| a.ty.has_fn())
                        {
                            ok &= match &c.callee {
                                Callee::Inst(callee) => region.contains(callee),
                                Callee::Local(_) | Callee::Value(_) => true,
                                _ => false,
                            };
                        }
                    });
                    ok
                })
                .collect();
            region = kept;
            if region.len() == before {
                break;
            }
        }
        for i in candidates {
            if region.contains(&i) {
                if let Some(f) = self.insts[i].as_mut() {
                    f.fn_region = true;
                }
                continue;
            }
            let gs: Vec<String> = self.insts[i]
                .as_ref()
                .map(|f| f.generics.iter().map(|(g, _)| g.clone()).collect())
                .unwrap_or_default();
            for g in gs {
                self.meta[i]
                    .bounds
                    .entry(g)
                    .or_default()
                    .insert(Bound::Static);
            }
        }
    }

    fn cloneable(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Vec(a) | Ty::Array(a) | Ty::Option(a) => self.cloneable(a),
            Ty::Std(n, _) => !n.taken_once(),
            Ty::Result(a, b) | Ty::Pair(a, b) => self.cloneable(a) && self.cloneable(b),
            Ty::Data(n, args) => {
                self.data_index.get(n).is_none_or(|i| self.datas[*i].clone)
                    && args.iter().all(|a| self.cloneable(a))
            }
            Ty::Fn(f) => f.kind.dup(),
            _ => true,
        }
    }

    pub fn need(&mut self, cx: &Cx, ty: &Ty, bound: Bound) {
        let mut ps = BTreeSet::new();
        ty.params(&mut ps);
        for p in ps {
            self.meta[cx.inst]
                .bounds
                .entry(p)
                .or_default()
                .insert(bound);
        }
    }
}

/// The free parameter identities held by a checked type, in encounter order.
fn collect_parameters(t: &TTy, out: &mut Vec<(TParam, Kind)>) {
    match t {
        TTy::Param(p, k) => {
            if !out.iter().any(|(present, _)| present.id() == p.id()) {
                out.push((p.clone(), *k));
            }
        }
        TTy::Fn(ps, r, _) => {
            ps.iter().for_each(|p| collect_parameters(p, out));
            collect_parameters(r, out);
        }
        TTy::Named(_, args) | TTy::Union(args) => {
            args.iter().for_each(|a| collect_parameters(a, out));
        }
        TTy::Tagged(_, t) | TTy::Info(t) | TTy::Borrow(t, _) => collect_parameters(t, out),
        TTy::App(f, a) => {
            collect_parameters(f, out);
            collect_parameters(a, out);
        }
        TTy::Poly(bound, body) => {
            let mut inner = Vec::new();
            collect_parameters(body, &mut inner);
            for (p, k) in inner {
                if !bound.iter().any(|(b, _)| b.id() == p.id())
                    && !out.iter().any(|(present, _)| present.id() == p.id())
                {
                    out.push((p, k));
                }
            }
        }
        _ => {}
    }
}

/// The row variables a function's parameters carry only where an argument
/// assumes them, inside a parameter of a callback parameter
/// (`run: (() -> A ! {|e}) -> B`), and its result does not carry. No argument
/// gives evidence for them, so each call instantiates them with the empty row
/// (as the row checker does) and they are specialized to the synchronous tier.
pub(crate) fn assumed_row_vars(decl: &FnDecl) -> HashSet<Name> {
    fn walk(t: &SurfaceTerm, supplied: bool, out: &mut [HashSet<Name>; 2]) {
        match &*t.kind {
            TermKind::Pi {
                params,
                result,
                effects,
                ..
            } => {
                for effect in effects.iter().flatten() {
                    if let Some(var) = effect.row_variable() {
                        out[usize::from(supplied)].insert(var);
                    }
                }
                for (_, param) in params {
                    walk(param, !supplied, out);
                }
                walk(result, supplied, out);
            }
            TermKind::Borrow { term, .. }
            | TermKind::Tagged { term, .. }
            | TermKind::FnKind { ty: term, .. } => walk(term, supplied, out),
            _ => {
                // Anything else, a type application or a written row, is
                // read as supplying every row variable inside it.
                let mut t = t.clone();
                tauto_surface::surface::walk::term(&mut t, &mut |t| match &*t.kind {
                    TermKind::Row(effects)
                    | TermKind::Pi {
                        effects: Some(effects),
                        ..
                    } => out[1].extend(effects.iter().filter_map(Name::row_variable)),
                    _ => {}
                });
            }
        }
    }
    let mut out = [HashSet::new(), HashSet::new()];
    for ty in decl.param_types.iter().flatten() {
        walk(ty, true, &mut out);
    }
    if let Some(result) = &decl.result {
        let mut in_result = [HashSet::new(), HashSet::new()];
        walk(result, true, &mut in_result);
        out[1].extend(in_result.into_iter().flatten());
    }
    let [assumed, supplied] = out;
    assumed.difference(&supplied).cloned().collect()
}

/// The effects written in a function type (`(A) -> B ! {fail | e}`), under
/// the kind or borrow written on it.
/// The row variables among `generics` that `t` gives a data type as its
/// row argument, `Lift(e)` or `Lift(!{log | e})`.
fn data_row_args(t: &SurfaceTerm, generics: &[&Name], vars: &mut Vec<Name>) {
    match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } => {
            data_row_args(function, generics, vars);
            for a in arguments {
                let found: Vec<Name> = match &*a.kind {
                    TermKind::Var(n) if generics.contains(&n) => vec![n.clone()],
                    TermKind::Row(es) => es.iter().filter_map(Name::row_variable).collect(),
                    _ => Vec::new(),
                };
                for v in found {
                    if !vars.contains(&v) {
                        vars.push(v);
                    }
                }
                data_row_args(a, generics, vars);
            }
        }
        TermKind::Borrow { term, .. }
        | TermKind::Tagged { term, .. }
        | TermKind::FnKind { ty: term, .. } => data_row_args(term, generics, vars),
        _ => {}
    }
}

pub(crate) fn pi_effects(t: &SurfaceTerm) -> Option<Vec<Name>> {
    match &*t.kind {
        TermKind::FnKind { ty, .. } | TermKind::Borrow { term: ty, .. } => pi_effects(ty),
        TermKind::Pi { effects, .. } => Some(effects.clone().unwrap_or_default()),
        _ => None,
    }
}

/// The row variable a field's row is read with when its data type carries
/// a suspending row (`Lowerer::carried`): it stands for any row of that tier.
pub(crate) fn carried_row(tier: Tier) -> String {
    format!("|@{tier:?}")
}

fn carried_tier(v: &str) -> Option<Tier> {
    match v {
        "@A" => Some(Tier::A),
        "@O" => Some(Tier::O),
        "@M" => Some(Tier::M),
        _ => None,
    }
}

pub(crate) fn sanitize(name: &str) -> String {
    let mut s: String = name
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if s.is_empty() || s.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        s.insert(0, '_');
    }
    s
}

#[cfg(test)]
mod scoped_generic_tests {
    use super::*;

    fn compile_both(source: &str) -> Result<(Package, Package), CompileError> {
        let mut program = tauto::surface::parse_program(source)
            .map_err(|error| CompileError::Front(error.to_string()))?;
        tauto_surface::resolve::Resolver::default().statements(&mut program.stmts);
        let package = compile_program(
            &program,
            None,
            false,
            false,
            false,
            Target::Rust,
            None,
            |_| {},
        )?;
        let mut javascript = compile_program(
            &program,
            None,
            false,
            false,
            false,
            Target::JavaScript,
            None,
            |_| {},
        )?;
        // The synthetic entry belongs to its compilation, not to the source tree.
        if let (Some(a), Some(b)) = (package.top, javascript.top) {
            let source = package
                .fns
                .iter()
                .find(|f| f.id == a)
                .unwrap()
                .source
                .clone();
            javascript
                .fns
                .iter_mut()
                .find(|f| f.id == b)
                .unwrap()
                .source = source;
        }
        Ok((package, javascript))
    }

    fn source(case: &str) -> &'static str {
        Box::leak(tauto_case_inputs::source("types/scoped-generics.eure", case).into_boxed_str())
    }

    #[test]
    fn row_tokens_require_their_exact_lexical_owner() {
        tauto_messages::install();
        let input = r#"effect choose(): Bool resume ω
fn apply<!e>(f: () -> i64 ! e): i64 ! e { f() }
let r := handle { apply(() => if perform choose() { 1 } else { 2 }) } with {
  choose(), k => k(true) + k(false)
}
"#;
        let program = tauto::surface::parse_program(input).unwrap();
        let rows = check_program_rows(&program);
        assert!(rows.errors.is_empty(), "{:?}", rows.errors);
        let declaration = rows
            .declarations
            .iter()
            .find(|d| d.name.as_str() == "apply")
            .unwrap();
        let key = rows
            .row_variables
            .iter()
            .find(|(_, variable)| {
                variable.owner == declaration.owner && variable.name.as_str() == "e"
            })
            .map(|(key, _)| key)
            .unwrap();
        let token = key.in_row();
        let call = *rows
            .calls
            .iter()
            .find(|(_, row)| row.contains(&token))
            .map(|(id, _)| id)
            .unwrap();
        let normalized = normalized_rows(&rows).unwrap();
        assert_eq!(normalized.calls[&call], Row::from([token.clone()]));
        assert!(normalized.calls[&call].contains(&key.in_row()));

        let mut foreign = rows.clone();
        foreign.call_owners.insert(call, None);
        assert!(matches!(
            normalized_rows(&foreign),
            Err(CompileError::Unsupported(Unsupported { what, .. }))
                if what.id == "rows-captured-variable-needs-owner" && what.get("var") == Some(&"e".into())
        ));
        let mut missing = rows.clone();
        missing.call_owners.remove(&call);
        assert!(matches!(
            normalized_rows(&missing),
            Err(CompileError::Unsupported(Unsupported { what, .. }))
                if what.id == "rows-call-no-owner"
        ));
        let mut ambiguous = rows.clone();
        ambiguous.declarations.push(declaration.clone());
        assert!(matches!(
            normalized_rows(&ambiguous),
            Err(CompileError::Unsupported(Unsupported { what, .. }))
                if what.id == "rows-ambiguous-declaration" && what.get("name") == Some(&"apply".into())
        ));
    }

    #[test]
    fn implicit_callback_rows_keep_their_higher_tiers() {
        tauto_messages::install();
        for (case, name, tier) in [
            (
                "implicit-row-direct-call-keeps-suspension",
                "apply",
                Tier::O,
            ),
            (
                "implicit-row-direct-call-keeps-many-resumptions",
                "apply",
                Tier::M,
            ),
            (
                "local-owned-row-shadows-outer-direct-bound-at-runtime",
                "inner",
                Tier::O,
            ),
        ] {
            let input = tauto_case_inputs::source("check/local-function-rows.eure", case);
            let (package, javascript) =
                compile_both(&input).unwrap_or_else(|error| panic!("{case}: {error}"));
            assert_eq!(format!("{package:?}"), format!("{javascript:?}"));
            let function = package
                .fns
                .iter()
                .find(|f| f.source.as_str() == name)
                .unwrap();
            assert_eq!(function.tier, tier, "{case}");
            assert!(matches!(&function.params[0].ty, Ty::Fn(callback) if callback.tier == tier));
        }
        let foreign = r#"fn outer<!e>(captured: () -> Text ! e): Text ! e {
  fn inner(own: () -> Text ! {}): Text ! e {
    captured()
    own()
  }
  let alias := inner
  alias(() => "ok")
}
"#;
        assert!(
            matches!(compile(foreign), Err(CompileError::Unsupported(Unsupported { what, .. }))
            if what.id == "rows-captured-variable-needs-owner" && what.get("var") == Some(&"e".into()))
        );
    }

    #[test]
    fn row_polymorphic_function_values_require_a_checked_specialization() {
        tauto_messages::install();
        let input = r#"
effect ask(): Text
fn apply<!e>(f: () -> Text ! e): Text ! e { f() }
fn caller(): Text ! {ask} {
  let run := apply
  run(() => perform ask())
}
"#;
        assert!(
            matches!(compile_with(input, true), Err(CompileError::Unsupported(Unsupported { what, .. }))
            if what.id == "nir-the-row-polymorphic-function-used-as" && what.get("name") == Some(&"apply".into()))
        );
    }

    #[test]
    fn record_carried_rows_specialize_from_the_call() {
        tauto_messages::install();
        let plain = r#"effect ask(): i64 direct
struct View(!e) { callback: () -> i64 ! e }
fn apply<!e: direct>(value: View(e)): i64 ! e { value.callback() }
let result := handle { apply(View { callback: () => perform ask() }) } with {
  ask(), k => k(42)
  return value => value
}
show(&result)
"#;
        assert!(compile(plain).unwrap().rust_unsupported.is_none());
        let suspending = r#"effect ask(n: i64): i64 resume 1
struct Handlers(!e) { on_key: (k: i64) -> i64 ! e }
fn dispatch<!e>(h: &Handlers(e), k: i64): i64 ! e { (h.on_key)(k) }
let r := handle {
  let h := Handlers { on_key: (k) => perform ask(k) + 1 }
  dispatch(&h, 3)
} with { ask(n), k => { let v := k(n); v * 10 } }
show(&r)
"#;
        // The record holds its function at the tier of the row the call
        // gives its row variable. (The arm is not a tail form, so `ask`
        // suspends.)
        let package = compile(suspending).unwrap();
        assert!(package.rust_unsupported.is_none());
        assert!(package.datas.iter().any(|d| {
            d.name.as_str() == "Handlers"
                && d.generics.is_empty()
                && d.ctors[0]
                    .fields
                    .iter()
                    .any(|f| matches!(&f.ty, Ty::Fn(f) if f.tier == Tier::O))
        }));
        // A field cannot hold a function that resumes more than once.
        let many = r#"effect pick(): i64 resume ω
struct Handlers(!e) { on_key: (k: i64) -> i64 ! e }
fn dispatch<!e>(h: Handlers(e), k: i64): i64 ! e { (h.on_key)(k) }
let r := handle {
  dispatch(Handlers { on_key: (k) => perform pick() + k }, 3)
} with {
  pick(), k => k(1) + k(2)
  return v => v
}
show(&r)
"#;
        assert!(
            matches!(&compile_javascript(many).unwrap().rust_unsupported, Some(Unsupported { what, .. })
            if what.id == "nir-row-variable-carried-suspending")
        );
    }

    #[test]
    fn specialized_copies_own_their_row_variables() {
        // A call that gives a declared function makes a copy of `show`
        // beside it; each keeps its own `e`.
        tauto_messages::install();
        let input = tauto_case_inputs::source(
            "check/local-function-rows.eure",
            "specialized-copy-owns-its-row-variables",
        );
        compile_both(&input).unwrap();
    }

    #[test]
    fn a_computed_callback_takes_the_row_row_checking_found() {
        tauto_messages::install();
        let input = tauto_case_inputs::source(
            "check/local-function-rows.eure",
            "computed-callback-row-comes-from-row-checking",
        );
        compile_both(&input).unwrap();
    }

    #[test]
    fn unknown_callback_rows_do_not_default_to_plain() {
        tauto_messages::install();
        for (case, message) in [(
            "implicit-row-function-value-requires-backend-evidence",
            "nir-the-row-polymorphic-function-used-as",
        )] {
            let input = tauto_case_inputs::source("check/local-function-rows.eure", case);
            for result in [compile(&input), compile_javascript(&input)] {
                assert!(
                    matches!(result, Err(CompileError::Unsupported(Unsupported { what, .. }))
                    if what.id == message),
                    "{case}"
                );
            }
        }
    }

    #[test]
    fn transitive_generic_captures_keep_own_and_outer_identities() {
        let package = compile(source(
            "transitive-generic-captures-keep-own-and-outer-identities",
        ))
        .unwrap();
        let first = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "first")
            .unwrap();
        let forward = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "forward")
            .unwrap();
        assert_eq!(forward.generics.len(), 2);
        assert_ne!(forward.generics[0].0, forward.generics[1].0);
        let mut calls = 0;
        forward.body.walk(&mut |e| {
            if let ExprKind::Call(call) = &e.kind
                && matches!(call.callee, Callee::Inst(id) if id == first.id)
            {
                assert_eq!(
                    call.targs,
                    vec![
                        Ty::Param(forward.generics[0].0.clone()),
                        Ty::Param(forward.generics[1].0.clone())
                    ]
                );
                assert!(matches!(&call.args[0].kind, ExprKind::Ref(place)
                    if place.local.id == forward.params[0].local.id));
                calls += 1;
            }
        });
        assert_eq!(calls, 1);
    }

    #[test]
    fn lifted_capture_and_own_binder_have_distinct_names_and_bounds() {
        let package = compile(source("nested-same-name-capture-multiple-uses")).unwrap();
        let inner = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "inner")
            .unwrap();
        let outer = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "outer")
            .unwrap();
        assert_eq!(inner.generics.len(), 2);
        let own = &inner.generics[0].0;
        let captured = &inner.generics[1].0;
        assert_eq!(own, "A");
        assert_ne!(own, captured);
        assert_eq!(
            inner.params[0].ty,
            Ty::Ref(Box::new(Ty::Param(captured.clone())))
        );
        assert_eq!(inner.params[1].ty, Ty::Param(own.clone()));
        assert_eq!(inner.ret, Ty::Param(own.clone()));
        assert!(inner.generics[0].1.contains(&Bound::Clone));
        assert!(inner.generics[1].1.contains(&Bound::Clone));
        assert!(outer.generics[0].1.contains(&Bound::Clone));
        let mut calls = Vec::new();
        let mut snapshots = 0;
        outer.body.walk(&mut |e| {
            if let ExprKind::Block(block) = &e.kind {
                for stmt in &block.stmts {
                    if let tauto_nir::Stmt::Let { local, init, .. } = stmt
                        && matches!(&init.kind, ExprKind::Read { local: source, how: Use::Clone }
                            if source.id == outer.params[0].local.id && source.id != local.id)
                    {
                        snapshots += 1;
                    }
                }
            }
            if let ExprKind::Call(call) = &e.kind
                && matches!(call.callee, Callee::Inst(id) if id == inner.id)
            {
                calls.push(call.targs.clone());
                if let ExprKind::Ref(capture) = &call.args[0].kind {
                    call.args[1].walk(&mut |arg| {
                        assert!(
                            !matches!(&arg.kind, ExprKind::Read { local, how: Use::Move }
                            if local.id == capture.local.id)
                        );
                    });
                }
            }
        });
        assert_eq!(calls.len(), 2);
        assert!(calls.contains(&vec![Ty::Int(Width::W64), Ty::Param("A".into())]));
        assert!(calls.contains(&vec![Ty::Param("A".into()), Ty::Param("A".into())]));
        // The declaration owns a shared snapshot; a final explicit use of
        // the source cannot invalidate that separately borrowed storage.
        assert_eq!(snapshots, 1);
    }

    #[test]
    fn owned_capture_storage_is_inside_the_declaration_block() {
        let input = r#"struct(affine) Probe {}
extern { fn Probe::new(name: &Text): Probe }
fn outer(): Unit ! {Show} {
  let captured := Probe::new("captured")
  {
    fn unused(): Probe { captured }
    #()
  }
  show(&1)
}
outer()
"#;
        let package = compile(input).unwrap();
        let outer = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "outer")
            .unwrap();
        let ExprKind::Block(body) = &outer.body.kind else {
            panic!("outer block")
        };
        let original = body
            .stmts
            .iter()
            .find_map(|stmt| match stmt {
                tauto_nir::Stmt::Let { local, .. } if local.name.as_str() == "captured" => {
                    Some(local.id)
                }
                _ => None,
            })
            .unwrap();
        let mut stored = 0;
        for stmt in &body.stmts {
            if let tauto_nir::Stmt::Expr(Expr {
                kind: ExprKind::Block(inner),
                ..
            }) = stmt
            {
                for stmt in &inner.stmts {
                    if let tauto_nir::Stmt::Let { local, init, .. } = stmt
                        && matches!(&init.kind, ExprKind::Read { local: source, how: Use::Move }
                            if source.id == original && local.id != original)
                    {
                        stored += 1;
                    }
                }
            }
        }
        assert_eq!(stored, 1);
    }

    #[test]
    fn named_capture_origins_survive_source_shadowing_and_forwarding() {
        for case in [
            "named-owned-capture-keeps-declaration-binding",
            "generic-named-owned-capture-keeps-declaration-binding",
            "named-shared-capture-keeps-declaration-binding",
            "named-borrowed-capture-keeps-declaration-binding",
            "named-mutable-capture-keeps-declaration-cell",
            "transitive-shared-capture-keeps-declaration-binding",
            "transitive-owned-capture-keeps-declaration-binding",
            "recursive-shared-capture-keeps-declaration-binding",
        ] {
            let (package, javascript) =
                compile_both(source(case)).unwrap_or_else(|error| panic!("{case}: {error}"));
            assert_eq!(format!("{package:?}"), format!("{javascript:?}"), "{case}");
            if case.starts_with("transitive-") {
                let forward = package
                    .fns
                    .iter()
                    .find(|f| f.source.as_str() == "forward")
                    .unwrap();
                let captured = forward.params[0].local.id;
                let mut forwarded = 0;
                forward.body.walk(&mut |e| {
                    if let ExprKind::Call(call) = &e.kind
                        && matches!(call.callee, Callee::Inst(id)
                            if matches!(package.fns[id].source.as_str(), "read" | "take"))
                    {
                        let local = match &call.args[0].kind {
                            ExprKind::Read { local, .. } => local.id,
                            ExprKind::Ref(place) | ExprKind::RefMut(place) => place.local.id,
                            _ => panic!("forwarded capture argument"),
                        };
                        assert_eq!(local, captured);
                        forwarded += 1;
                    }
                });
                assert_eq!(forwarded, 1);
            }
            if case.starts_with("recursive-") {
                let read = package
                    .fns
                    .iter()
                    .find(|f| f.source.as_str() == "read")
                    .unwrap();
                let mut recursive = 0;
                read.body.walk(&mut |e| {
                    if let ExprKind::Call(call) = &e.kind
                        && matches!(call.callee, Callee::Inst(id) if id == read.id)
                    {
                        assert!(matches!(&call.args[0].kind, ExprKind::Ref(place)
                            if place.local.id == read.params[0].local.id));
                        recursive += 1;
                    }
                });
                assert_eq!(recursive, 1);
            }
        }
    }

    #[test]
    fn local_scheme_arguments_are_instantiated_independently() {
        for case in [
            "nested-generic-instantiates-at-each-use",
            "local-generic-inferred-result-is-instantiated",
        ] {
            let package = compile(source(case)).unwrap();
            let identity = package
                .fns
                .iter()
                .find(|f| f.source.as_str() == "identity")
                .unwrap();
            assert_eq!(identity.generics.len(), 1);
            let mut calls = Vec::new();
            for function in &package.fns {
                function.body.walk(&mut |e| {
                    if let ExprKind::Call(call) = &e.kind
                        && matches!(call.callee, Callee::Inst(id) if id == identity.id)
                    {
                        calls.push(call.targs.clone());
                    }
                });
            }
            assert_eq!(calls.len(), 2);
            assert!(calls.contains(&vec![Ty::Int(Width::W64)]));
            assert!(calls.contains(&vec![Ty::Text]));
        }
    }

    #[test]
    fn union_reordering_uses_the_checked_instantiation() {
        let input = source("local-generic-union-order-keeps-authoritative-type-arguments");
        let program = tauto::surface::parse_program(input).unwrap();
        let types = crate::types::check_program(&program);
        assert!(types.errors.is_empty(), "{:?}", types.errors);
        let scheme = types
            .schemes
            .iter()
            .chain(types.local_schemes.iter())
            .find(|(name, _)| name.as_str() == "observe")
            .unwrap()
            .1;
        let b = scheme.generics[0].0.id();
        let a = scheme.generics[1].0.id();
        assert!(types.instantiations.values().any(|arguments| {
            arguments.get(b) == Some(&TTy::Text) && arguments.get(a) == Some(&TTy::Int(Width::W64))
        }));
        let package = compile(input).unwrap();
        let observe = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "observe")
            .unwrap();
        let mut calls = 0;
        for function in &package.fns {
            function.body.walk(&mut |e| {
                if let ExprKind::Call(call) = &e.kind
                    && matches!(call.callee, Callee::Inst(id) if id == observe.id)
                {
                    assert_eq!(call.targs, vec![Ty::Text, Ty::Int(Width::W64)]);
                    calls += 1;
                }
            });
        }
        assert_eq!(calls, 1);
    }

    #[test]
    fn function_value_wrapper_keeps_the_source_capture_type() {
        let package = compile(source(
            "captured-source-name-does-not-shadow-function-value-wrapper",
        ))
        .unwrap();
        let inner = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "inner")
            .unwrap();
        let outer = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "outer")
            .unwrap();
        let mut calls = Vec::new();
        outer.body.walk(&mut |e| {
            if let ExprKind::Call(call) = &e.kind
                && matches!(call.callee, Callee::Inst(id) if id == inner.id)
            {
                calls.push(call.targs.clone());
            }
        });
        assert_eq!(
            calls,
            vec![vec![Ty::Int(Width::W64), Ty::Param("A".into())]]
        );
    }

    #[test]
    fn function_values_propagate_their_generic_bounds() {
        let package = compile(source("local-function-value-keeps-generic-bound-edges")).unwrap();
        let outer = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "outer")
            .unwrap();
        assert_eq!(outer.generics.len(), 1);
        assert!(outer.generics[0].1.contains(&Bound::Clone));
        let echo = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "echo")
            .unwrap();
        let mut values = Vec::new();
        outer.body.walk(&mut |e| {
            if let ExprKind::FnValue { inst, targs } = &e.kind
                && *inst == echo.id
            {
                values.push(targs.clone());
            }
        });
        assert_eq!(values, vec![vec![Ty::Param("A".into())]]);
    }

    #[test]
    fn direct_calls_move_owned_affine_captures_once() {
        for case in [
            "named-owned-affine-capture-single-use",
            "generic-named-owned-affine-capture-single-use",
        ] {
            let package = compile(source(case)).unwrap();
            let consume = package
                .fns
                .iter()
                .find(|f| f.source.as_str() == "consume")
                .unwrap();
            assert_eq!(consume.params[0].ty, Ty::Buf);
            assert_eq!(consume.params[0].local.repr, Repr::Plain);
            let mut calls = 0;
            for function in &package.fns {
                function.body.walk(&mut |e| {
                    if let ExprKind::Call(call) = &e.kind
                        && matches!(call.callee, Callee::Inst(id) if id == consume.id)
                    {
                        assert!(matches!(
                            call.args[0].kind,
                            ExprKind::Read { how: Use::Move, .. }
                        ));
                        calls += 1;
                    }
                });
            }
            assert_eq!(calls, 1);
        }
    }

    #[test]
    fn owned_outer_generic_keeps_its_identity_and_kind() {
        let package = compile(source(
            "owned-outer-generic-capture-keeps-its-identity-and-kind",
        ))
        .unwrap();
        let inner = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "inner")
            .unwrap();
        let outer = package
            .fns
            .iter()
            .find(|f| f.source.as_str() == "outer")
            .unwrap();
        assert_eq!(inner.generics.len(), 2);
        assert_ne!(inner.generics[0].0, inner.generics[1].0);
        assert!(inner.generics[0].1.contains(&Bound::Clone));
        assert!(!inner.generics[1].1.contains(&Bound::Clone));
        assert!(!outer.generics[0].1.contains(&Bound::Clone));
        let capture = Ty::Param(inner.generics[1].0.clone());
        assert_eq!(inner.params[0].ty, capture);
        assert_eq!(inner.params[0].local.repr, Repr::Plain);
        assert_eq!(inner.ret, capture);
        let mut calls = 0;
        outer.body.walk(&mut |e| {
            if let ExprKind::Call(call) = &e.kind
                && matches!(call.callee, Callee::Inst(id) if id == inner.id)
            {
                assert!(matches!(
                    call.args[0].kind,
                    ExprKind::Read { how: Use::Move, .. }
                ));
                assert_eq!(call.targs, vec![Ty::Int(Width::W64), Ty::Param("A".into())]);
                calls += 1;
            }
        });
        assert_eq!(calls, 1);
    }

    #[test]
    fn borrowed_and_mutable_captures_remain_reusable() {
        for (case, name) in [
            (
                "generic-named-borrowed-affine-capture-can-be-read-repeatedly",
                "read",
            ),
            ("generic-named-mutable-cell-capture-stays-shared", "next"),
        ] {
            let package = compile(source(case)).unwrap();
            let callee = package
                .fns
                .iter()
                .find(|f| f.source.as_str() == name)
                .unwrap();
            assert!(matches!(callee.params[0].ty, Ty::Ref(_) | Ty::RefMut(_)));
            let mut calls = 0;
            for function in &package.fns {
                function.body.walk(&mut |e| {
                    if let ExprKind::Call(call) = &e.kind
                        && matches!(call.callee, Callee::Inst(id) if id == callee.id)
                    {
                        assert!(matches!(
                            call.args[0].kind,
                            ExprKind::Ref(_) | ExprKind::RefMut(_)
                        ));
                        calls += 1;
                    }
                });
            }
            assert_eq!(calls, 2);
        }
    }

    #[test]
    fn output_names_do_not_depend_on_prior_occurrence_allocation() {
        let input = source("nested-same-name-capture-multiple-uses");
        let first = compile(input).unwrap();
        let _ = compile(source("var-uses-function-type-parameter")).unwrap();
        let second = compile(input).unwrap();
        let javascript = compile_javascript(input).unwrap();
        let names = |package: &Package| {
            package
                .fns
                .iter()
                .map(|function| (function.source.to_string(), function.tier))
                .collect::<Vec<_>>()
        };
        assert_eq!(names(&first), names(&second));
        assert_eq!(names(&first), names(&javascript));
    }

    #[test]
    fn union_members_use_output_tokens_not_frontend_identity_order() {
        let program =
            tauto::surface::parse_program(source("nested-same-name-capture-multiple-uses"))
                .unwrap();
        let types = crate::types::check_program(&program).with_prelude();
        assert!(types.errors.is_empty(), "{:?}", types.errors);
        let rows = crate::rows::check_program_rows(&program);
        let outer = types
            .schemes
            .iter()
            .find(|(name, _)| name.as_str() == "outer")
            .unwrap()
            .1
            .generics[0]
            .0
            .clone();
        let inner = types
            .local_schemes
            .iter()
            .find(|(name, _)| name.as_str() == "inner")
            .unwrap()
            .1
            .generics[0]
            .0
            .clone();
        assert_ne!(outer.id(), inner.id());
        assert_eq!(outer.name(), inner.name());
        let mut lowerer = Lowerer::new(
            LowerInput {
                program: &program,
                types: &types,
                rows: &rows,
                lib: false,
                expansion_only: None,
            },
            false,
            HashMap::new(),
        );
        lowerer.param_names.insert(inner.id().clone(), "A".into());
        // The same display name cannot stand for an unbound identity.
        assert_eq!(
            lowerer.conv(&TTy::Param(outer.clone(), Kind::Shared)),
            Ty::Never
        );
        assert_eq!(lowerer.build_errors.len(), 1);
        lowerer.build_errors.clear();
        lowerer
            .param_names
            .insert(outer.id().clone(), "A__p1".into());
        let outer = TTy::Param(outer, Kind::Shared);
        let inner = TTy::Param(inner, Kind::Shared);
        let first = lowerer.conv(&TTy::Union(vec![outer.clone(), inner.clone()]));
        let second = lowerer.conv(&TTy::Union(vec![inner, outer]));
        assert_eq!(first, second);
        let Ty::Union(id) = first else {
            panic!("union")
        };
        assert_eq!(
            lowerer.unions[id].members,
            vec![Ty::Param("A".into()), Ty::Param("A__p1".into())]
        );
    }
}

#[cfg(test)]
mod library_entry_tests {
    use super::*;

    // This checks the lowering API's root boundary using surface data, without parsing.
    #[test]
    fn selected_entries_keep_transitive_calls_and_exclude_other_functions() {
        tauto_parse::install();
        let span = Span::new(0, 0);
        let function = |name: &str, body: SurfaceTerm| {
            Stmt::Fn(FnDecl {
                lends: None,
                unused: None,
                unused_params: vec![],
                name: name.into(),
                vis: Default::default(),
                generics: vec![],
                generic_types: vec![],
                rows: vec![],
                bounds: vec![],
                bound_spans: vec![],
                unused_generics: Vec::new(),
                params: vec![],
                borrows: vec![],
                param_types: vec![],
                result: None,
                effects: None,
                written_effects: None,
                row_hole: None,
                where_: vec![],
                span,
                opaque: false,
                ghost: false,
                decreasing_by: None,
                generates: None,
                budget: None,
                body,
            })
        };
        let mut program = Program {
            stmts: vec![
                function("helper", SurfaceTerm::new(TermKind::Bool(true), span)),
                function("entry", SurfaceTerm::app("helper", vec![], span)),
                function("unused", SurfaceTerm::new(TermKind::Bool(false), span)),
            ],
            errors: vec![],
        };
        tauto_surface::resolve::Resolver::default().statements(&mut program.stmts);
        let entries = BTreeSet::from(["entry".to_string()]);
        let package = compile_program(
            &program,
            None,
            false,
            false,
            true,
            Target::JavaScript,
            Some(&entries),
            |_| {},
        )
        .unwrap();
        assert_eq!(
            package
                .exports
                .iter()
                .map(|e| e.name.as_str())
                .collect::<Vec<_>>(),
            ["entry"]
        );
        assert!(package.fns.iter().any(|f| f.source.as_str() == "helper"));
        assert!(!package.fns.iter().any(|f| f.source.as_str() == "unused"));
        let all = compile_program(
            &program,
            None,
            false,
            false,
            true,
            Target::JavaScript,
            None,
            |_| {},
        )
        .unwrap();
        assert_eq!(all.exports.len(), 3);
    }
}

#[cfg(test)]
mod expansion_row_entry_tests {
    use super::*;
    use std::collections::BTreeSet;

    /// A row error reached only from the selected entry is `Package` under
    /// expansion (entry-local for the macro-vm cache), and another entry of
    /// the same program still lowers.
    #[test]
    fn reachable_row_error_is_package_and_does_not_block_sibling_entry() {
        tauto_messages::install();
        let source = r#"
fn leak(): Unit ! {} {
  while true {}
}
fn bad(): Unit ! {div} {
  leak()
}
fn good(): Unit ! {div} {
  ()
}
"#;
        let loaded = test_load::load_text(source).unwrap();
        let bad = BTreeSet::from(["bad".into()]);
        let err = lowering_for_expansion(|| {
            compile_loaded_entries_with_observer(&loaded, true, Target::Rust, Some(&bad), |_| {})
        });
        assert!(
            matches!(&err, Err(CompileError::Package(m)) if m.contains("div")),
            "{err:?}"
        );
        let good = BTreeSet::from(["good".into()]);
        let ok = lowering_for_expansion(|| {
            compile_loaded_entries_with_observer(&loaded, true, Target::Rust, Some(&good), |_| {})
        });
        assert!(ok.is_ok(), "{ok:?}");
    }
}

/// Whether `f` carries values past its call only as function values it builds
/// and keeps: no effect, budget, task or extern, no function value in its
/// result, and none stored in data.
fn fn_values_only(f: &FnInst) -> bool {
    // A `&mut` place of function values would take them out of the call.
    let lent_out = |t: &Ty| matches!(t, Ty::RefMut(a) if a.has_fn());
    if f.tier >= Tier::O || f.ret.has_fn() || f.params.iter().any(|p| lent_out(&p.ty)) {
        return false;
    }
    let mut ok = true;
    f.body.walk_with_handlers(&mut |e| {
        ok &= match &e.kind {
            ExprKind::Perform(_)
            | ExprKind::Handle(_)
            | ExprKind::Inject { .. }
            | ExprKind::Remap { .. }
            | ExprKind::Budget(_) => false,
            ExprKind::Ctor { fields, .. } => !fields.iter().any(|(_, x)| x.ty.has_fn()),
            ExprKind::Call(c) => !matches!(&c.callee, Callee::Extern(_))
                && !matches!(&c.callee, Callee::Builtin(b) if b == "pending_spawn" || b == "Os::offload"),
            _ => true,
        };
    });
    ok
}

/// The library's effects an export may perform: the instance answers them
/// itself, outside `Host::run`.
const EXPORT_EFFECTS: [&str; 21] = [
    "stdout",
    "stdout_flush",
    "div",
    "budget",
    "budget_memory",
    "wait",
    "spawn",
    "ref_new",
    "ref_get",
    "ref_set",
    "weak_of",
    "weak_get",
    "mutex_new",
    "mutex_claim",
    "mutex_take_claimed",
    "mutex_put",
    "mutex_withdraw",
    "atomic_new",
    "atomic_load",
    "atomic_store",
    "atomic_fetch_add",
];

/// Whether an export may perform `effect`, told by identity. An instance of
/// `spawn` (`spawn(u64)`) and the label of a task's row (`spawn@^hash_seed`)
/// are `spawn` and the effects it holds.
fn export_may_perform(effect: &Name) -> bool {
    use crate::types::indices::split_index_label;
    use tauto_surface::bindings::{is_library_effect, is_library_instance};
    let listed = |name: &Name| {
        EXPORT_EFFECTS
            .iter()
            .chain(&["hash_seed"])
            .any(|l| is_library_effect(name, l) || (*l != "div" && is_library_instance(name, l)))
    };
    if let Some((family, member)) = split_index_label(effect) {
        // The spawn label holds an effect of the task's row.
        return family == "spawn"
            && listed(&Name::from(family.as_str()))
            && listed(&Name::from(member.as_str()));
    }
    if listed(effect) {
        return true;
    }
    // A specialization spelled `spawn@u64` of the library's `spawn`.
    let text = effect.to_string();
    matches!(effect, Name::Spelled(_)) && text.split('@').next() == Some("spawn")
}
