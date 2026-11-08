//! Lowering: the checked program to NIR.
//!
//! The work list starts at the top-level statements and grows by the
//! functions they call, one instance per function and per tier of its row
//! variables.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use tauto::rows::{Row, RowReport, check_program_rows};
use tauto::surface::{BudgetLimit, FnDecl, Program, Stmt, SurfaceTerm, TermKind};
use tauto::types::{Datas, Kind, Param as TParam, ParamId, Quant, Ty as TTy, TypeReport};

use crate::*;

mod expr;
pub(crate) mod handle;
mod pat;
mod specialize;
mod syntax;
mod ty;

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
    pub expansion_only: Option<&'a HashSet<tauto::identity::Name>>,
}

pub struct Lowered {
    pub package: Package,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CompileError {
    /// The front end rejected it (syntax, types, rows, use check).
    Front(String),
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
            CompileError::Front(m) | CompileError::Build(m) => write!(f, "{m}"),
            CompileError::Unsupported(u) => write!(f, "{u}"),
        }
    }
}

/// Whether a type is one the expansion makes for a method with generics, or
/// has a type constructor variable in it.
fn poly(t: &tauto::types::Ty) -> bool {
    use tauto::types::Ty;
    match t {
        Ty::Poly(..) | Ty::App(..) => true,
        Ty::Fn(ps, r, _) => ps.iter().any(poly) || poly(r),
        Ty::Union(ts) => ts.iter().any(poly),
        Ty::Named(_, args) => args.iter().any(poly),
        Ty::Tagged(_, t) | Ty::Info(t) | Ty::Borrow(t, _) => poly(t),
        _ => false,
    }
}

pub fn compile(source: &str) -> Result<Package, CompileError> {
    compile_with(source, false)
}

/// As `compile`; with `lib`, every function of the program without type
/// parameters that does not run only while the program is expanded
/// (`Loaded::expansion_only`) is lowered and listed in `Package::exports`
/// (`tauto-build`).
pub fn compile_with(source: &str, lib: bool) -> Result<Package, CompileError> {
    compile_with_observer(source, lib, |_| {})
}
/// JavaScript uses suspendable host callbacks, with the same type and ownership checks.
pub fn compile_javascript(source: &str) -> Result<Package, CompileError> {
    compile_javascript_with_observer(source, |_| {})
}
/// Sequential boundaries of compilation; parsing includes expansion and name resolution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompilePhase {
    ParseExpand,
    Check,
    Lower,
}

/// As `compile_with`, notifying the observer before each phase starts.
/// A returned error belongs to the most recently observed phase.
pub fn compile_with_observer(
    source: &str,
    lib: bool,
    observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    compile_target(source, lib, false, observe)
}

pub fn compile_javascript_with_observer(
    source: &str,
    observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    compile_target(source, false, true, observe)
}

fn compile_target(
    source: &str,
    lib: bool,
    javascript: bool,
    mut observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    observe(CompilePhase::ParseExpand);
    let mut program = tauto::surface::parse_program(source).map_err(|e| {
        CompileError::Front(msg!("nir-syntax-error", error = e.to_string()).to_string())
    })?;
    tauto::resolve::Resolver::default().statements(&mut program.stmts);
    compile_program(&program, None, false, false, lib, javascript, None, observe)
}

/// Checks and lowers an expanded, file-aware program. Reading and expansion
/// have already completed; the observer starts at the checking boundary.
pub fn compile_loaded_with_observer(
    loaded: &tauto::program::Loaded,
    lib: bool,
    javascript: bool,
    observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    compile_loaded_entries_with_observer(loaded, lib, javascript, None, observe)
}

/// Checks and lowers a loaded program, limiting library roots to the named entries.
/// Calls and function values reachable from those entries are lowered normally.
pub fn compile_loaded_entries_with_observer(
    loaded: &tauto::program::Loaded,
    lib: bool,
    javascript: bool,
    entries: Option<&BTreeSet<String>>,
    observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    let mut loaded = loaded.clone();
    loaded.resolve_runtime();
    let dirs = loaded
        .files
        .iter()
        .filter_map(|file| file.path.parent().map(std::path::Path::to_path_buf))
        .collect();
    let mut package = tauto::syntax::with_search_dirs(dirs, || {
        compile_program(
            &loaded.program,
            Some(&loaded),
            false,
            false,
            lib,
            javascript,
            entries,
            observe,
        )
    })?;
    package.sources = Some(loaded.source_map());
    Ok(package)
}

/// The name of the innermost function whose declaration holds `offset`,
/// with the modules it is declared in (`syntax.ident`).
fn enclosing_fn(stmts: &[Stmt], offset: u32) -> Option<String> {
    stmts.iter().find_map(|s| match s {
        Stmt::Fn(f) if f.span.start <= offset && offset < f.span.end => Some(f.name.to_string()),
        Stmt::Module { name, items, span } if span.start <= offset && offset < span.end => {
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
    loaded: Option<&tauto::program::Loaded>,
    wrapped: bool,
    rewritten: bool,
    lib: bool,
    javascript: bool,
    entries: Option<&BTreeSet<String>>,
    mut observe: impl FnMut(CompilePhase),
) -> Result<Package, CompileError> {
    observe(CompilePhase::Check);
    let tested = run_tests(program);
    let program = tested.as_ref().unwrap_or(program);
    let report = tauto::types::check_program(program);
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
    // A method with generics of its own, a type constructor variable: no
    // backend writes these as they are, so each use gets its own copy
    // (`specialize`), which is checked again.
    if report
        .terms
        .values()
        .chain(report.schemes.values().map(|s| &s.ty))
        .any(poly)
    {
        if !rewritten
            && let Some(copied) = specialize::program(program, &report)
            && tauto::types::check_program(&copied).errors.is_empty()
        {
            return compile_program(
                &copied, loaded, wrapped, true, lib, javascript, entries, observe,
            );
        }
        return Err(CompileError::Unsupported(Unsupported {
            what: msg!("nir-class-method-with-generics"),
            span: None,
        }));
    }
    let rows = add_prelude_rows(
        program,
        match loaded {
            Some(loaded) if wrapped || rewritten => {
                loaded.check_wrapped_rows_with_types(program, javascript, &report)
            }
            Some(loaded) => loaded.check_rows_with_types(javascript, &report),
            None if javascript => {
                tauto::rows::check_program_rows_javascript_with_types(program, &report)
            }
            None => tauto::rows::check_program_rows_with_types(program, &report),
        },
    );
    // Only what can run is generated, so only it answers to the checks of
    // generating: an error in a function no root reaches is not reported
    // (`tauto check` has already checked every declaration). The functions
    // lowering actually reaches are compared with these after lowering.
    let live = live_functions(program, lib, entries, loaded.map(|l| &l.expansion_only));
    let mut deferred: Vec<(Name, String)> = Vec::new();
    // An effect nobody handles is an error here as it is for `tauto check`,
    // `tauto run` and the JavaScript backend, `resume 0` ones included.
    for e in &rows.errors {
        match unreached(&program.stmts, &live, e.span.start) {
            Some(name) => deferred.push((name, format!("{e}"))),
            None => return Err(CompileError::Front(format!("{e}"))),
        }
    }
    for e in tauto::lin::check(program, &report, &rows) {
        let message = msg!("nir-use-error", error = e.to_string()).to_string();
        match unreached(&program.stmts, &live, e.span.start) {
            Some(name) => deferred.push((name, message)),
            None => return Err(CompileError::Front(message)),
        }
    }
    // The standard effects that reach the top level (a task's are in the row of its `spawn`):
    // the prelude's `host_run` answers them around the program and around
    // each task, which is checked again. What `host_run` leaves to the host
    // (`wait`) the backend's driver answers (`tauto_rt::o::run_top`), so a
    // program whose top level reaches only `wait` is not wrapped: `host_run`
    // would answer nothing, and its handler would bring every host primitive
    // into a target that has none of them (the browser).
    if !wrapped
        && rows
            .host_effects
            .iter()
            .any(|e| e.as_str() != "wait")
        && let Some(wrapped) = tauto::host::wrap(program)
    {
        let permissions: Vec<String> = tauto::host::permissions(rows.host_effects.iter())
            .into_iter()
            .map(str::to_string)
            .collect();
        let mut package = compile_program(
            &wrapped,
            loaded,
            true,
            rewritten,
            lib,
            javascript,
            entries,
            &mut observe as &mut dyn FnMut(CompilePhase),
        )?;
        package.permissions = permissions;
        return Ok(package);
    }
    let report = report.with_prelude_for(program);
    observe(CompilePhase::Lower);
    let pruned = prune_dead(program, &report);
    let package = lower_entries(
        LowerInput {
            program: pruned.as_ref().unwrap_or(program),
            types: &report,
            rows: &rows,
            lib,
            expansion_only: loaded.map(|l| &l.expansion_only),
        },
        entries,
    )?;
    // A function judged unreachable that lowering reached after all keeps
    // its error: nothing generated escapes the checks.
    if let Some((_, message)) = deferred
        .into_iter()
        .find(|(name, _)| package.fns.iter().any(|f| &f.source == name))
    {
        return Err(CompileError::Front(message));
    }
    Ok(package)
}

/// The functions lowering can reach: from the top-level statements other
/// than functions (and, for a library, the functions it exports, as
/// `Lowerer::run` chooses them), through every name a reached declaration
/// mentions.
fn live_functions(
    program: &Program,
    lib: bool,
    entries: Option<&BTreeSet<String>>,
    expansion_only: Option<&HashSet<Name>>,
) -> HashSet<Name> {
    let fns: HashMap<&Name, &Stmt> = program
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Fn(f) => Some((&f.name, s)),
            _ => None,
        })
        .collect();
    let mut live: HashSet<Name> = HashSet::new();
    let mut pending: Vec<Stmt> = Vec::new();
    for s in &program.stmts {
        match s {
            Stmt::Fn(f) => {
                if lib
                    && f.generics.is_empty()
                    && !expansion_only.is_some_and(|e| e.contains(&f.name))
                    && !entries.is_some_and(|names| !names.contains(f.name.as_str()))
                    && live.insert(f.name.clone())
                {
                    pending.push(s.clone());
                }
            }
            _ => pending.push(s.clone()),
        }
    }
    while let Some(mut s) = pending.pop() {
        let mut found = Vec::new();
        tauto::surface::references::statement(&mut s, &mut |name| {
            if let Some(decl) = fns.get(name)
                && live.insert(name.clone())
            {
                found.push((*decl).clone());
            }
        });
        pending.extend(found);
    }
    live
}

/// The function no root reaches whose declaration holds `offset`.
fn unreached(stmts: &[Stmt], live: &HashSet<Name>, offset: u32) -> Option<Name> {
    stmts.iter().find_map(|s| match s {
        Stmt::Fn(f) if f.span.start <= offset && offset < f.span.end => {
            (!live.contains(&f.name)).then(|| f.name.clone())
        }
        _ => None,
    })
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
        tauto::surface::walk::stmt(stmt, &mut |t| match &*t.kind {
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

/// A backend's host answers only `show`: a top-level `perform test(name, body)`
/// becomes `run_test(name, body)` of the prelude, which prints the result.
fn run_tests(program: &Program) -> Option<Program> {
    fn rewrite(t: &mut SurfaceTerm) -> bool {
        let TermKind::Perform { effect, args } = &*t.kind else {
            return false;
        };
        if !tauto::bindings::is_library(&effect, "test") {
            return false;
        }
        let function = SurfaceTerm::var(&tauto::bindings::library_name("run_test"), t.span);
        let call = TermKind::App {
            function: Box::new(function),
            arguments: args.clone(),
        };
        *t = t.with_kind(call, t.span);
        true
    }
    let mut program = program.clone();
    let mut any = false;
    for stmt in &mut program.stmts {
        match stmt {
            Stmt::Expr(e) => any |= rewrite(e),
            Stmt::Let { value, .. } => any |= rewrite(value),
            _ => {}
        }
    }
    any.then_some(program)
}

/// The rows of a program, and what the library's functions perform.
fn add_prelude_rows(program: &Program, mut rows: RowReport) -> RowReport {
    rows.merge_prelude(check_program_rows(tauto::types::prelude_for(program)));
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
    let rows = normalized_rows(input.rows)?;
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
            return result;
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
    pub declarations: Vec<tauto::identity::DeclRef>,
    pub program: &'a Program,
    pub types: &'a TypeReport,
    pub operation_facts: Option<&'a tauto::types::OperationFacts>,
    pub rows: &'a RowReport,
    pub lib: bool,
    pub expansion_only: Option<&'a HashSet<tauto::identity::Name>>,
    pub fns: HashMap<Name, FnSrc<'a>>,
    /// The functions written inside another body, and what each of them
    /// captures: a lifted function takes the captures as leading parameters.
    pub nested_fns: HashSet<Name>,
    pub local_caps: HashMap<Name, Vec<LiftedCap>>,
    /// Declaration and binder order, independent of occurrence allocation.
    pub param_order: HashMap<ParamId, (usize, usize)>,
    /// Output names in the function being lowered; never semantic identities.
    pub param_names: HashMap<ParamId, String>,
    /// Data and operation signatures have their own declaration-local names.
    pub declaration_param_names: HashMap<ParamId, String>,
    pub datas: Vec<DataDef>,
    pub data_index: HashMap<Name, usize>,
    /// Each data type's row parameters (`row_parameters_of`).
    pub row_params: HashMap<Name, Vec<usize>>,
    /// Recursive generic data whose cells share their tails.
    pub rc_datas: HashSet<Name>,
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
    pub spawns: bool,
    pub next_budget: u32,
    /// Set by the scan for escaping captures: a `var` is mentioned in the
    /// body of a handle that may resume more than once.
    pub m_hit: std::cell::Cell<bool>,
    /// Whether each named function runs a `budget`, itself or through a
    /// call ([`Lowerer::runs_budget`]).
    pub runs_budget: std::cell::RefCell<HashMap<Name, bool>>,
    pub rust_names: HashMap<String, u32>,
    /// What `tauto build` rejects after the front end (`Decimal`).
    pub build_errors: Vec<String>,
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
}

fn collect_nested<'a>(t: &'a SurfaceTerm, out: &mut Vec<&'a FnDecl>) {
    tauto::surface::walk::values(t, &mut |node| {
        if let tauto::surface::walk::Node::Stmt(Stmt::Fn(f)) = node {
            out.push(f);
        }
    });
}

impl<'a> Lowerer<'a> {
    fn new(input: LowerInput<'a>, rc_enabled: bool, carried: HashMap<Name, Tier>) -> Self {
        let mut fns: HashMap<Name, FnSrc<'a>> = HashMap::new();
        let lib: &'static Program = tauto::types::prelude_for(input.program);
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
                    Stmt::Extern { fns: fs, .. } => {
                        for f in fs {
                            fns.insert(
                                f.name.clone(),
                                FnSrc {
                                    decl: f,
                                    origin: if !own {
                                        Origin::Builtin
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
            if let Stmt::Fn(f) = s {
                collect_nested(&f.body, &mut nested);
            }
        }
        let mut seen: HashMap<&tauto::identity::Name, usize> = HashMap::new();
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
                tauto::surface::walk::values_stmt(stmt, &mut |node| {
                    let tauto::surface::walk::Node::Stmt(Stmt::Fn(f)) = node else {
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
            row_params: tauto::surface::row_parameters_of(input.program.stmts.iter().filter_map(
                |s| match s {
                    Stmt::Struct(d) | Stmt::Enum(d) => Some(d),
                    _ => None,
                },
            )),
            types: input.types,
            operation_facts: input.types.operation_instances_for(input.program),
            rows: input.rows,
            lib: input.lib,
            expansion_only: input.expansion_only,
            fns,
            nested_fns,
            local_caps: HashMap::new(),
            param_order,
            param_names: HashMap::new(),
            declaration_param_names,
            datas: Vec::new(),
            data_index: HashMap::new(),
            rc_datas: HashSet::new(),
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
            spawns: false,
            next_budget: 0,
            m_hit: std::cell::Cell::new(false),
            runs_budget: std::cell::RefCell::new(HashMap::new()),
            rust_names: HashMap::new(),
            build_errors: Vec::new(),
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
                if !f.generics.is_empty()
                    || self.expansion_only.is_some_and(|e| e.contains(&f.name))
                    || entries.is_some_and(|names| !names.contains(f.name.as_str()))
                {
                    continue;
                }
                let id = self.instance(&f.name, BTreeMap::new(), false, false, false)?;
                let row = match self
                    .rows
                    .declaration_row(&f.name, f.body.id())
                    .expect("declaration rows were checked before lowering")
                {
                    Some(declaration) => declaration
                        .inferred
                        .iter()
                        .map(ToString::to_string)
                        .collect(),
                    None => self
                        .rows
                        .functions
                        .iter()
                        .find(|(n, _)| *n == f.name)
                        .map(|(_, r)| r.iter().map(ToString::to_string).collect())
                        .unwrap_or_default(),
                };
                exports.push(Export {
                    inst: id,
                    name: f.name.to_string(),
                    row,
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
        if let Some(e) = self.build_errors.first() {
            return Err(CompileError::Build(e.clone()));
        }
        let fns: Vec<FnInst> = std::mem::take(&mut self.insts)
            .into_iter()
            .map(|f| f.expect("an instance is lowered"))
            .collect();
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
            // `TAUTO_SYNC=1` builds a program that starts no task with `Arc`
            // too, for a host that moves its values between threads.
            sync: self.spawns || std::env::var_os("TAUTO_SYNC").is_some(),
            permissions: Vec::new(),
            rust_unsupported: self.rust_unsupported.take(),
        };
        // `TAUTO_KEEP_RECURSION=1` turns off the accumulators
        // (`accumulate.rs`): a function adding to its own result stays as
        // written.
        if std::env::var_os("TAUTO_KEEP_RECURSION").is_none() {
            crate::accumulate::introduce(&mut pkg, &mut |name, repr| self.fresh_local(name, repr));
        }
        // `TAUTO_KEEP_OWNED=1` turns off the borrowed parameters
        // (`borrow.rs`): every parameter stays owned.
        if std::env::var_os("TAUTO_KEEP_OWNED").is_none() {
            crate::borrow::infer(&mut pkg);
        }
        // `TAUTO_KEEP_CLONES=1` turns off the moves at the last use
        // (`last_use.rs`): every clone stays in.
        if std::env::var_os("TAUTO_KEEP_CLONES").is_none() {
            crate::last_use::elide(&mut pkg);
        }
        // After the borrowed parameters, which decide which parameters a
        // self call in tail position must pass on unchanged.
        crate::tail::mark(&mut pkg);
        Ok(pkg)
    }

    fn extern_defs(&mut self) -> Vec<ExternDef> {
        let mut out = Vec::new();
        for s in &self.program.stmts {
            let Stmt::Extern { fns, .. } = s else {
                continue;
            };
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
                        let tier = self.row_tier(&row, &HashMap::new());
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
        // `spawn` is lowered to a call of the body (`handle.rs`).
        if effect.starts_with('?')
            || tauto::bindings::is_library(&effect, "Div")
            || tauto::bindings::is_library(&effect, "spawn")
        {
            return Tier::S;
        }
        if tauto::bindings::is_library(&effect, "Exceeded")
            || tauto::bindings::is_library(&effect, "exceeded")
        {
            return Tier::O;
        }
        match self.quant(effect) {
            Quant::Direct => Tier::S,
            Quant::Zero => Tier::A,
            Quant::AtMostOne | Quant::One => Tier::O,
            Quant::Many => Tier::M,
        }
    }

    /// `t` performs a `direct` operation synchronously where no `direct`
    /// handler is held (`Cx::detached`): the Rust backend cannot answer it.
    pub fn detached_direct(&self, cx: &Cx, t: &SurfaceTerm, what: Message) {
        if cx.detached && self.has_direct(&self.term_row(t)) {
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
            !e.row_variable().is_some()
                && !e.starts_with('?')
                && (tauto::bindings::is_library(&e, "show") || self.quant(e) == Quant::Direct)
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
        if cx.under_budget && row.contains(&tauto::bindings::library_name("Div")) {
            tier.max(Tier::O)
        } else {
            tier
        }
    }

    /// Whether `name` runs a `budget`, in its body or through a function it
    /// calls by name. Such a function ticks even when its row has no `Div`,
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
        tauto::surface::walk::value_terms(&src.decl.body, &mut |t| match &*t.kind {
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
        if src.origin == Origin::Builtin && tauto::host::is_host_primitive(src.decl) {
            return Row::new();
        }
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
        fn type_vars(
            t: &SurfaceTerm,
            direct: bool,
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
                        if !direct {
                            nested.extend(effects.iter().filter_map(Name::row_variable));
                        }
                    }
                    for (_, param) in params {
                        type_vars(param, false, vars, nested);
                    }
                    type_vars(result, false, vars, nested);
                }
                TermKind::Borrow { term, .. }
                | TermKind::Tagged { term, .. }
                | TermKind::FnKind { ty: term, .. } => type_vars(term, direct, vars, nested),
                TermKind::App {
                    function,
                    arguments,
                } => {
                    type_vars(function, false, vars, nested);
                    for argument in arguments {
                        type_vars(argument, false, vars, nested);
                    }
                }
                TermKind::Union(types) => {
                    for ty in types {
                        type_vars(ty, false, vars, nested);
                    }
                }
                _ => {}
            }
        }
        // A row written for a record, `Handlers(!{key | e})`. The Rust
        // backend gives a record's function fields one tier, the synchronous
        // one, and specializes a row variable only from a callback or the
        // function's own row: it cannot run a function whose written row
        // names an effect that suspends, or whose row variable only a record
        // carries. The JavaScript backend runs both alike.
        for ty in decl.param_types.iter().flatten().chain(&decl.result) {
            let mut ty = ty.clone();
            tauto::surface::walk::term(&mut ty, &mut |t| {
                let TermKind::Row(effects) = &*t.kind else {
                    return;
                };
                let named: Row = effects
                    .iter()
                    .filter(|e| !e.row_variable().is_some())
                    .cloned()
                    .collect();
                let carried = effects.iter().filter_map(Name::row_variable).find(|v| {
                    !decl
                        .effects
                        .iter()
                        .flatten()
                        .any(|e| e.row_variable().as_ref() == Some(v))
                });
                let what = if self.row_tier(&named, &HashMap::new()) > Tier::S {
                    msg!("nir-record-row-suspends", decl = decl.name.as_str())
                } else if let Some(v) = carried {
                    msg!(
                        "nir-row-variable-carried-only-by-record",
                        var = v.to_string(),
                        decl = decl.name.as_str()
                    )
                } else {
                    return;
                };
                self.rust_unsupported
                    .borrow_mut()
                    .get_or_insert_with(|| Unsupported {
                        what,
                        span: Some(t.span),
                    });
            });
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
            type_vars(ty, true, &mut vars, &mut nested);
        }
        if let Some(result) = &decl.result {
            type_vars(result, true, &mut vars, &mut nested);
        }
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
        use tauto::surface::{Handler, Pattern};
        match &*t.kind {
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
                        .contains(&tauto::bindings::library_name("Div"))
                {
                    row.insert(tauto::bindings::library_name("Div"));
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
                            .all(|p| matches!(p, Pattern::Wild | Pattern::Bind(_)))
                    {
                        if tauto::bindings::is_library(&effect, "exceeded") {
                            inner.remove(&tauto::bindings::library_name("Exceeded"));
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
                // leaves `Div` in the row.
                if *limit == BudgetLimit::Steps {
                    inner.remove(&tauto::bindings::library_name("Div"));
                }
                row.extend(inner);
                row.insert(tauto::bindings::library_name("Exceeded"));
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
                            row.insert(tauto::bindings::library_name("Div"));
                        }
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
            TermKind::Tuple(members) => members.iter().for_each(|v| self.term_row_into(v, row)),
            _ => {}
        }
    }

    pub fn rust_name(&mut self, source: &str, tier: Tier) -> String {
        let base = format!(
            "{}__{}",
            sanitize(source),
            match tier {
                Tier::S => "s",
                Tier::A => "a",
                Tier::O => "o",
                Tier::M => "m",
            }
        );
        let n = self.rust_names.entry(base.clone()).or_insert(0);
        *n += 1;
        if *n == 1 { base } else { format!("{base}_{n}") }
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
            tauto::surface::walk::term(&mut ty, &mut |t| {
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
        let body = self.expr_expect(&mut cx, &decl.body, &ret)?;
        let ret_ty = self.conv_in(&cx, &ret, decl.result.as_ref());
        let rust_name = self.rust_name(&decl.name, tier);
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
            rust_name,
            tier,
            generics: generics.into_iter().map(|g| (g, BTreeSet::new())).collect(),
            params,
            ret: ret_ty,
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
            TTy::Borrow(_, false) => Repr::Ref,
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
        let tier = if self.rows.host_waits {
            Tier::O
        } else {
            Tier::S
        };
        let id = self.insts.len();
        self.insts.push(None);
        let top: Name = tauto::identity::DeclRef::fresh("<top>").into();
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
        };
        let stmts: Vec<&Stmt> = self.program.stmts.iter().collect();
        let block = self.block_of(&mut cx, &stmts, true, &TTy::Unit)?;
        let span = Span::new(0, 0);
        let body = Expr {
            kind: ExprKind::Block(block),
            ty: Ty::Unit,
            span,
        };
        let rust_name = self.rust_name("top", tier);
        self.insts[id] = Some(FnInst {
            id,
            source: top,
            rust_name,
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

    fn cloneable(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Vec(a) | Ty::Array(a) | Ty::Option(a) => self.cloneable(a),
            Ty::Std(n, _) => !n.taken_once(),
            Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => {
                self.cloneable(a) && self.cloneable(b)
            }
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
                tauto::surface::walk::term(&mut t, &mut |t| match &*t.kind {
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
        tauto::resolve::Resolver::default().statements(&mut program.stmts);
        let package = compile_program(&program, None, false, false, false, false, None, |_| {})?;
        let mut javascript =
            compile_program(&program, None, false, false, false, true, None, |_| {})?;
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
        crate::lower::case_inputs::source_static("types/scoped-generics.eure", case)
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
            let input =
                crate::lower::case_inputs::source_static("check/local-function-rows.eure", case);
            let (package, javascript) =
                compile_both(input).unwrap_or_else(|error| panic!("{case}: {error}"));
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
  fn inner<!e>(own: () -> Text ! e): Text {
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
perform show("value", result)
"#;
        assert!(compile(plain).unwrap().rust_unsupported.is_none());
        let suspending = r#"effect ask(n: i64): i64 resume 1
struct Handlers(!e) { on_key: (k: i64) -> i64 ! e }
fn dispatch<!e>(&h: Handlers(e), k: i64): i64 ! e { (h.on_key)(k) }
let r := handle {
  let h := Handlers { on_key: (k) => perform ask(k) + 1 }
  dispatch(&h, 3)
} with { ask(n), k => k(n * 10) }
perform show("r", r)
"#;
        // The record holds its function at the tier of the row the call
        // gives its row variable.
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
perform show("r", r)
"#;
        assert!(
            matches!(&compile_javascript(many).unwrap().rust_unsupported, Some(Unsupported { what, .. })
            if what.id == "nir-row-variable-carried-suspending")
        );
    }

    #[test]
    fn unknown_callback_rows_do_not_default_to_plain() {
        tauto_messages::install();
        for (case, message) in [
            (
                "computed-callback-row-requires-backend-evidence",
                "nir-callback-row-needed",
            ),
            (
                "implicit-row-function-value-requires-backend-evidence",
                "nir-the-row-polymorphic-function-used-as",
            ),
        ] {
            let input =
                crate::lower::case_inputs::source_static("check/local-function-rows.eure", case);
            for result in [compile(input), compile_javascript(input)] {
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
        assert!(!inner.generics[0].1.contains(&Bound::Show));
        assert!(inner.generics[1].1.contains(&Bound::Show));
        assert!(outer.generics[0].1.contains(&Bound::Show));
        let mut calls = Vec::new();
        let mut snapshots = 0;
        outer.body.walk(&mut |e| {
            if let ExprKind::Block(block) = &e.kind {
                for stmt in &block.stmts {
                    if let crate::Stmt::Let { local, init, .. } = stmt
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
        let input = r#"affine struct Probe {}
module Probe {
  extern { fn new(&name: Text): Probe }
}
fn outer(): Unit {
  let captured := Probe::new("captured")
  {
    fn unused(): Probe { captured }
    #()
  }
  perform show("after_inner", 1)
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
                crate::Stmt::Let { local, .. } if local.name.as_str() == "captured" => {
                    Some(local.id)
                }
                _ => None,
            })
            .unwrap();
        let mut stored = 0;
        for stmt in &body.stmts {
            if let crate::Stmt::Expr(Expr {
                kind: ExprKind::Block(inner),
                ..
            }) = stmt
            {
                for stmt in &inner.stmts {
                    if let crate::Stmt::Let { local, init, .. } = stmt
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
        let types = tauto::types::check_program(&program);
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
        assert!(outer.generics[0].1.contains(&Bound::Show));
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
                .map(|function| function.rust_name.clone())
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
        let types = tauto::types::check_program(&program).with_prelude();
        assert!(types.errors.is_empty(), "{:?}", types.errors);
        let rows = tauto::rows::check_program_rows(&program);
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
            Ty::Infer
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
/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn source_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
            ("types/scoped-generics.eure", "named-mutable-capture-keeps-declaration-cell") => {
                r#"fn outer(): Unit {
  var value: i64 := 0
  fn next(): i64 { value := value + 1; value }
  {
    var value: i64 := 100
    perform show("first", next())
    perform show("shadow", value)
  }
  perform show("second", next())
}
outer()"#
            }
            (
                "types/scoped-generics.eure",
                "captured-source-name-does-not-shadow-function-value-wrapper",
            ) => {
                r#"fn outer<A: Shared>(a0: A): i64 {
  fn inner<B: Shared>(x: B): B {
    perform show("captured", a0)
    x
  }
  let alias := inner
  alias(7)
}
perform show("answer", outer("text"))"#
            }
            ("types/scoped-generics.eure", "nested-same-name-capture-multiple-uses") => {
                r#"fn outer<A: Shared>(value: A): A {
  fn inner<A: Shared>(other: A): A {
    perform show("captured", value)
    let local: A := other
    local
  }
  perform show("number", inner(1))
  inner(value)
}
perform show("answer", outer("text"))"#
            }
            (
                "types/scoped-generics.eure",
                "recursive-shared-capture-keeps-declaration-binding",
            ) => {
                r#"fn outer(): Text {
  let value := "original"
  fn read(count: i64): Text {
    if count == 0 { value } else {
      let value := "shadow"
      read(count - 1)
    }
  }
  read(1)
}
perform show("answer", outer())"#
            }
            (
                "types/scoped-generics.eure",
                "transitive-owned-capture-keeps-declaration-binding",
            ) => {
                r#"fn outer(): Text {
  let original := "original"
  let value := Buf::of(&original)
  fn take(): Buf { value }
  let shadow := "shadow"
  let value := Buf::of(&shadow)
  fn forward(): Text { Text::of(take()) }
  forward()
}
perform show("answer", outer())"#
            }
            ("types/scoped-generics.eure", "named-owned-capture-keeps-declaration-binding") => {
                r#"fn outer(): Text {
  let original := "original"
  let value := Buf::of(&original)
  fn consume(): Text { Text::of(value) }
  let shadow := "shadow"
  let value := Buf::of(&shadow)
  consume()
}
perform show("answer", outer())"#
            }
            (
                "types/scoped-generics.eure",
                "generic-named-owned-capture-keeps-declaration-binding",
            ) => {
                r#"fn outer(): Text {
  let original := "original"
  let value := Buf::of(&original)
  fn consume<A: Shared>(marker: A): Text { Text::of(value) }
  let shadow := "shadow"
  let value := Buf::of(&shadow)
  consume(7)
}
perform show("answer", outer())"#
            }
            ("types/scoped-generics.eure", "local-function-value-keeps-generic-bound-edges") => {
                r#"fn outer<A: Shared>(value: A): A {
  fn echo<B: Shared>(other: B): B {
    perform show("echo", other)
    other
  }
  let alias := echo
  alias(value)
}
perform show("answer", outer("text"))"#
            }
            (
                "types/scoped-generics.eure",
                "transitive-generic-captures-keep-own-and-outer-identities",
            ) => {
                r#"fn outer<A: Shared>(value: A): A {
  fn first<A: Shared>(marker: A) { value }
  fn forward<A: Shared>(marker: A) { first(marker) }
  let number := forward(7)
  forward(true)
}
perform show("answer", outer("original"))"#
            }
            (
                "types/scoped-generics.eure",
                "owned-outer-generic-capture-keeps-its-identity-and-kind",
            ) => {
                r#"fn outer<A>(value: A): A {
  fn inner<A: Shared>(marker: A) { value }
  inner(1)
}
let text := "payload"
let value := Buf::of(&text)
let restored := outer(value)
perform show("answer", Text::of(restored))"#
            }
            ("types/scoped-generics.eure", "named-shared-capture-keeps-declaration-binding") => {
                r#"fn outer(): Text {
  let value := "original"
  fn read(): Text { value }
  let value := "shadow"
  perform show("first", read())
  read()
}
perform show("answer", outer())"#
            }
            ("types/scoped-generics.eure", "generic-named-owned-affine-capture-single-use") => {
                r#"fn outer(): Text {
  let text := "text"
  let value := Buf::of(&text)
  fn consume<A: Shared>(marker: A): Text {
    let local: A := marker
    Text::of(value)
  }
  consume(1)
}
perform show("answer", outer())"#
            }
            (
                "types/scoped-generics.eure",
                "generic-named-borrowed-affine-capture-can-be-read-repeatedly",
            ) => {
                r#"fn outer(&value: Buf): Unit {
  fn read<A: Shared>(marker: A): Text {
    let local: A := marker
    Text::of(Buf::clone(&value))
  }
  perform show("first", read(1))
  perform show("second", read("again"))
}
let text := "text"
let value := Buf::of(&text)
outer(&value)"#
            }
            (
                "types/scoped-generics.eure",
                "local-generic-union-order-keeps-authoritative-type-arguments",
            ) => {
                r#"fn outer(): Text {
  fn observe<B: Shared, A: Shared>(known: B, input: B | A): B { known }
  let number: i64 := 7
  let input := if true { number } else { "unseen" }
  observe("known", input)
}
perform show("answer", outer())"#
            }
            ("types/scoped-generics.eure", "local-generic-inferred-result-is-instantiated") => {
                r#"fn outer(): Unit {
  fn identity<A: Shared>(value: A) { value }
  let number: i64 := identity(7)
  let text: Text := identity("text")
  perform show("number", number)
  perform show("text", text)
}
outer()"#
            }
            ("types/scoped-generics.eure", "named-borrowed-capture-keeps-declaration-binding") => {
                r#"fn outer(&value: Text): Text {
  fn read(): Text { clone(value) }
  let value := "shadow"
  read()
}
perform show("answer", outer("original"))"#
            }
            ("types/scoped-generics.eure", "generic-named-mutable-cell-capture-stays-shared") => {
                r#"fn outer(): i64 {
  var count: i64 := 0
  fn next<A: Shared>(marker: A): i64 {
    let local: A := marker
    count := count + 1
    count
  }
  let first := next("one")
  let second := next(true)
  first + second
}
perform show("answer", outer())"#
            }
            ("types/scoped-generics.eure", "var-uses-function-type-parameter") => {
                r#"fn collect<A: Shared>(first: A, second: A): List(A) {
  var values: Vec(A) := Vec::new()
  Vec::push(&mut values, first)
  Vec::push(&mut values, second)
  Vec::into_list(values)
}
perform show("items", collect("a", "b"))"#
            }
            (
                "types/scoped-generics.eure",
                "transitive-shared-capture-keeps-declaration-binding",
            ) => {
                r#"fn outer(): Text {
  let value := "original"
  fn read(): Text { value }
  let value := "shadow"
  fn forward(): Text { read() }
  forward()
}
perform show("answer", outer())"#
            }
            ("types/scoped-generics.eure", "nested-generic-instantiates-at-each-use") => {
                r#"fn outer(): Unit {
  fn identity<A: Shared>(value: A): A {
    let local: A := value
    local
  }
  perform show("number", identity(7))
  perform show("text", identity("text"))
}
outer()"#
            }
            ("types/scoped-generics.eure", "named-owned-affine-capture-single-use") => {
                r#"fn outer(): Text {
  let text := "text"
  let value := Buf::of(&text)
  fn consume(marker: i64): Text { Text::of(value) }
  consume(1)
}
perform show("answer", outer())"#
            }
            (
                "check/local-function-rows.eure",
                "computed-callback-row-requires-backend-evidence",
            ) => {
                r#"effect ask(): i64
fn apply<!e>(callback: () -> i64 ! e): i64 ! e { callback() }
let result := handle {
  apply(if true { () => perform ask() } else { () => perform ask() })
} with {
  ask(), k => k(42)
  return value => value
}
perform show("value", result)
"#
            }
            ("check/local-function-rows.eure", "implicit-row-direct-call-keeps-suspension") => {
                r#"effect ask(): i64
fn apply<!e>(callback: () -> i64 ! e): i64 ! e { callback() }
let result := handle { apply(() => perform ask()) } with {
  ask(), k => k(42)
  return value => value
}
perform show("value", result)
"#
            }
            (
                "check/local-function-rows.eure",
                "local-owned-row-shadows-outer-direct-bound-at-runtime",
            ) => {
                r#"effect ask(): i64
fn outer<!e: direct>(): i64 ! {ask} {
  fn inner<!e>(callback: () -> i64 ! e): i64 ! e { callback() }
  inner(() => perform ask())
}
let result := handle { outer() } with {
  ask(), k => k(42)
  return value => value
}
perform show("value", result)
"#
            }
            (
                "check/local-function-rows.eure",
                "implicit-row-direct-call-keeps-many-resumptions",
            ) => {
                r#"effect choose(): i64 resume ω
fn apply<!e>(callback: () -> i64 ! e): i64 ! e { callback() }
let result := handle { apply(() => perform choose()) } with {
  choose(), k => k(1) + k(2)
  return value => value
}
perform show("value", result)
"#
            }
            (
                "check/local-function-rows.eure",
                "implicit-row-function-value-requires-backend-evidence",
            ) => {
                r#"effect ask(): i64
fn apply<!e>(callback: () -> i64 ! e): i64 ! e { callback() }
let alias := apply
let result := handle { alias(() => perform ask()) } with {
  ask(), k => k(42)
  return value => value
}
perform show("value", result)
"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn source(file: &str, name: &str) -> String {
        source_static(file, name).to_string()
    }
}

#[cfg(test)]
mod library_entry_tests {
    use super::*;

    // This checks the lowering API's root boundary using surface data, without parsing.
    #[test]
    fn selected_entries_keep_transitive_calls_and_exclude_other_functions() {
        let span = Span::new(0, 0);
        let function = |name: &str, body: SurfaceTerm| {
            Stmt::Fn(FnDecl {
                name: name.into(),
                vis: Default::default(),
                generics: vec![],
                generic_types: vec![],
                rows: vec![],
                bounds: vec![],
                bound_spans: vec![],
                params: vec![],
                borrows: vec![],
                param_types: vec![],
                result: None,
                effects: None,
                where_: vec![],
                span,
                opaque: false,
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
        tauto::resolve::Resolver::default().statements(&mut program.stmts);
        let entries = BTreeSet::from(["entry".to_string()]);
        let package = compile_program(
            &program,
            None,
            false,
            false,
            true,
            true,
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
        let all = compile_program(&program, None, false, false, true, true, None, |_| {}).unwrap();
        assert_eq!(all.exports.len(), 3);
    }
}
