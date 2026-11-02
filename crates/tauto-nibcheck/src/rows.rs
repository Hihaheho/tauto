//! Effect rows of executable code: which effects a function may perform.
//!
//! This follows the rules of `lean/Proto/Nib/Typing.lean` on the surface
//! AST, without deriving effects from erased value types: `perform` adds its effect, a call adds the
//! callee's row, `handle` removes the effects its arms answer *completely*
//! (an irrefutable, unguarded arm) and adds what the arms and the `return`
//! arm perform, `budget` swaps `Div` for `Exceeded`, and a `while` loop or a
//! recursive call adds `Div`.
//!
//! A function without a written row gets its inferred one; a written row must
//! contain the inferred one. A row variable `| e` is a name like any other
//! (`|e`): a function may perform it only by calling a parameter whose type
//! carries it, and a caller instantiates it with the rows of the functions it
//! passes. Whatever cannot be followed (a closure called through a variable
//! of unknown type, an argument of unknown row) is recorded as an
//! *unchecked* effect, `?…`, which no row contains: it is reported, never
//! read as empty. A source-matched value report may resolve a constructor
//! owner; its callable contracts still come from the source declaration.

use std::borrow::Cow;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

use tauto_parol::Span;

use crate::surface::walk;
use crate::surface::{
    BudgetLimit, DataDecl, EffectDecl, FnDecl, Handler, Pattern, Program, Stmt, SurfaceTerm,
    TermId, TermKind,
};
use crate::types::{Quant, TypeReport, prelude};

mod structural;
mod values;

pub type Row = BTreeSet<String>;

/// An executable declaration occurrence, independent of its source spelling
/// and of identities retained by cloned body terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RowOwner(u64);

fn fresh_identity() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    NEXT.fetch_add(1, Ordering::Relaxed)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RowVariable {
    pub name: String,
    pub owner: RowOwner,
    pub bound: Option<String>,
    /// Declared a row variable, `<!e>`. A name written in a row (`e`) that is not declared is
    /// reported; it is not read as a row variable because of how it is used.
    pub declared: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclarationRows {
    pub name: String,
    pub body: TermId,
    pub owner: RowOwner,
    /// The contract callers see: the written row, otherwise the inferred row.
    pub row: Row,
    pub inferred: Row,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RowDiagnostic {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for RowDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (byte {})", self.message, self.span.start)
    }
}

#[derive(Debug, Default, Clone)]
pub struct RowReport {
    pub functions: Vec<(String, Row)>,
    pub errors: Vec<RowDiagnostic>,
    /// What each call and `perform` performs itself (a call: its callee's
    /// row, instantiated; not what its arguments perform), by the term's
    /// occurrence identity. `lin.rs` checks control-flow linearity against it.
    pub calls: HashMap<TermId, Row>,
    pub quants: HashMap<String, Quant>,
    pub declarations: Vec<DeclarationRows>,
    /// The standard effects (`std/prelude/Os.taut`) that reach the top level
    /// unanswered: what the host answers, and so the permissions a run needs.
    pub host_effects: BTreeSet<String>,
    pub call_owners: HashMap<TermId, Option<RowOwner>>,
    pub row_variables: HashMap<String, RowVariable>,
    // Addresses are lookup keys for the borrowed immutable AST only. They
    // never order declarations or appear in diagnostics or generated code.
    owner_sources: HashMap<RowOwner, usize>,
    ambiguous_owners: HashSet<RowOwner>,
    ambiguous_calls: HashSet<TermId>,
    call_sources: HashMap<TermId, usize>,
}

impl RowReport {
    pub fn declaration_row(
        &self,
        name: &str,
        body: TermId,
    ) -> Result<Option<&DeclarationRows>, String> {
        let mut matches = self
            .declarations
            .iter()
            .filter(|d| d.name == name && d.body == body);
        let first = matches.next();
        if matches.next().is_some()
            || first.is_some_and(|d| self.ambiguous_owners.contains(&d.owner))
        {
            return Err(format!("ambiguous effect-row declaration `{name}`"));
        }
        Ok(first)
    }

    /// Convert only variables owned by this declaration to its source names.
    /// A captured row cannot become a same-named quantified row in a backend.
    pub fn normalize_row(&self, row: &Row, owner: Option<RowOwner>) -> Result<Row, String> {
        row.iter()
            .map(|effect| {
                if let Some(what) = effect.strip_prefix('?') {
                    return Err(display_text(&unfollowed(what), &self.row_variables));
                }
                let Some(key) = effect.strip_prefix('|') else {
                    return Ok(effect.clone());
                };
                match self.row_variables.get(key) {
                    Some(var) if Some(var.owner) == owner => Ok(format!("|{}", var.name)),
                    Some(var) => Err(format!(
                        "the captured row variable `{}` needs its lexical owner",
                        var.name
                    )),
                    None if key.starts_with("@row:") => {
                        Err("an effect row has no binder identity".into())
                    }
                    None => Err(format!("the row variable `{key}` has no lexical owner")),
                }
            })
            .collect()
    }

    /// The calls' rows, normalized; what fails says where the call is.
    pub fn normalized_calls(&self) -> Result<HashMap<TermId, Row>, (String, Option<Span>)> {
        if let Some(id) = self
            .ambiguous_calls
            .iter()
            .min_by_key(|id| (id.span().start, id.span().end))
        {
            return Err((
                "ambiguous lexical occurrence of an effect-row call".into(),
                Some(id.span()),
            ));
        }
        let mut calls: Vec<_> = self.calls.iter().collect();
        calls.sort_by_key(|(id, row)| (id.span().start, id.span().end, self.display_row(row)));
        calls
            .into_iter()
            .map(|(id, row)| {
                let owner = self.call_owners.get(id).ok_or_else(|| {
                    (
                        "a call has no lexical effect-row owner".to_string(),
                        Some(id.span()),
                    )
                })?;
                let row = self
                    .normalize_row(row, *owner)
                    .map_err(|e| (e, Some(id.span())))?;
                Ok((*id, row))
            })
            .collect()
    }

    pub fn merge_prelude(&mut self, other: RowReport) {
        for declaration in &other.declarations {
            let source = other.owner_sources.get(&declaration.owner);
            let identical = self.declarations.iter().any(|d| {
                source.is_some()
                    && self.owner_sources.get(&d.owner) == source
                    && d.name == declaration.name
                    && d.body == declaration.body
                    && self
                        .normalize_row(&d.row, Some(d.owner))
                        .ok()
                        .zip(
                            other
                                .normalize_row(&declaration.row, Some(declaration.owner))
                                .ok(),
                        )
                        .is_some_and(|(a, b)| a == b)
                    && self
                        .normalize_row(&d.inferred, Some(d.owner))
                        .ok()
                        .zip(
                            other
                                .normalize_row(&declaration.inferred, Some(declaration.owner))
                                .ok(),
                        )
                        .is_some_and(|(a, b)| a == b)
            });
            if !identical {
                self.declarations.push(declaration.clone());
            }
        }
        for (id, row) in &other.calls {
            if let Some(existing) = self.calls.get(id) {
                let same_source = self.call_sources.get(id).is_some()
                    && self.call_sources.get(id) == other.call_sources.get(id);
                let agrees = same_source
                    && self
                        .call_owners
                        .get(id)
                        .zip(other.call_owners.get(id))
                        .is_some_and(|(a, b)| {
                            self.normalize_row(existing, *a)
                                .ok()
                                .zip(other.normalize_row(row, *b).ok())
                                .is_some_and(|(a, b)| a == b)
                        });
                if !agrees {
                    self.ambiguous_calls.insert(*id);
                }
            } else {
                self.calls.insert(*id, row.clone());
                if let Some(owner) = other.call_owners.get(id) {
                    self.call_owners.insert(*id, *owner);
                }
            }
        }
        self.row_variables.extend(other.row_variables);
        self.owner_sources.extend(other.owner_sources);
        self.ambiguous_calls.extend(other.ambiguous_calls);
        self.ambiguous_owners.extend(other.ambiguous_owners);
        for (id, source) in other.call_sources {
            self.call_sources.entry(id).or_insert(source);
        }
        for (name, row) in other.functions {
            if !self.functions.iter().any(|(n, _)| *n == name) {
                self.functions.push((name, row));
            }
        }
    }

    fn display_row(&self, row: &Row) -> Row {
        display_row(row, &self.row_variables)
    }

    /// The source spelling used by diagnostics, not a substitution key.
    pub fn effect_name(&self, effect: &str) -> String {
        display_text(effect.trim_start_matches('|'), &self.row_variables)
    }

    /// The quantities an effect of a row may have: a declared one's own,
    /// any for a row variable (`<=1` and below when `bounded` says it is
    /// bounded so), none for an effect that cannot be followed (that is
    /// reported already).
    pub fn quants_of(&self, effect: &str, bounded: &dyn Fn(&str) -> bool) -> Vec<Quant> {
        if let Some(var) = effect.strip_prefix('|') {
            if let Some(var) = self.row_variables.get(var) {
                return match var.bound.as_deref() {
                    Some("direct") => vec![Quant::Direct],
                    Some("<=1") => vec![Quant::Zero, Quant::AtMostOne, Quant::One],
                    _ => vec![Quant::Zero, Quant::AtMostOne, Quant::One, Quant::Many],
                };
            }
            return if bounded(var) {
                vec![Quant::Zero, Quant::AtMostOne, Quant::One]
            } else {
                vec![Quant::Zero, Quant::AtMostOne, Quant::One, Quant::Many]
            };
        }
        if effect.starts_with('?') {
            return Vec::new();
        }
        vec![self.quants.get(effect).copied().unwrap_or(Quant::AtMostOne)]
    }
}

/// Check host callbacks against the JavaScript Promise boundary.
pub fn check_program_rows_javascript(program: &Program) -> RowReport {
    let mut analysis = Analysis::new(program);
    analysis.javascript = true;
    analysis.run(program)
}

pub fn check_program_rows(program: &Program) -> RowReport {
    Analysis::new(program).run(program)
}

/// Reuse value checking only to resolve a constructor's nominal owner.
/// Effects and callable contracts still come from source declarations and bodies.
pub fn check_program_rows_with_types(program: &Program, types: &TypeReport) -> RowReport {
    Analysis::new(program).with_types(types).run(program)
}

pub fn check_program_rows_javascript_with_types(
    program: &Program,
    types: &TypeReport,
) -> RowReport {
    let mut analysis = Analysis::new(program).with_types(types);
    analysis.javascript = true;
    analysis.run(program)
}

/// Compiler-internal configuration: `total` must come from checked extraction,
/// not source annotations. Callers that read source use `check_program_rows`;
/// the file facade revalidates extraction evidence before using this entry point.
pub fn check_program_rows_trusted(
    program: &Program,
    total: &HashSet<String>,
    javascript: bool,
) -> RowReport {
    let mut analysis = Analysis::new(program);
    analysis.total.clone_from(total);
    analysis.javascript = javascript;
    analysis.run(program)
}

/// The same checked-extraction boundary as [`check_program_rows_trusted`],
/// with an optional source-matched value report for nominal constructor owners.
pub fn check_program_rows_trusted_with_types(
    program: &Program,
    total: &HashSet<String>,
    javascript: bool,
    types: &TypeReport,
) -> RowReport {
    let mut analysis = Analysis::new(program).with_types(types);
    analysis.total.clone_from(total);
    analysis.javascript = javascript;
    analysis.run(program)
}

/// The report as text, for `totes/nibcheck` to write the same: a line for
/// each function in the order of the report, each error in order, each call
/// sorted by its span and each quantity sorted by the effect's name.
pub fn dump_rows(report: &RowReport) -> String {
    let row = |r: &Row| {
        format!(
            "{{{}}}",
            show(report.display_row(r).iter().map(|s| s.as_str()))
        )
    };
    let mut out = String::new();
    for (name, r) in &report.functions {
        out.push_str(&format!("function {name} {}\n", row(r)));
    }
    for e in &report.errors {
        out.push_str(&format!(
            "error {} {} {}\n",
            e.span.start, e.span.end, e.message
        ));
    }
    let mut calls: Vec<_> = report.calls.iter().collect();
    calls.sort_by_key(|(id, r)| (id.span().start, id.span().end, row(r)));
    for (id, r) in calls {
        let Span { start, end } = id.span();
        out.push_str(&format!("call {start} {end} {}\n", row(r)));
    }
    let mut quants: Vec<_> = report.quants.iter().collect();
    quants.sort_by(|a, b| a.0.cmp(b.0));
    for (effect, q) in quants {
        out.push_str(&format!("quant {effect} {q:?}\n"));
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Latent {
    Known(Callable),
    Named(String, Vec<Latent>),
    Record(String, Vec<(String, Latent)>),
    Plain,
    Effects(Row),
    Borrow(Box<Latent>, bool),
    Unknown,
    /// A type parameter that a constructed value holds nothing of: `None`
    /// is an `Option(A)` for every `A`. Any contract agrees with it.
    Absent,
    /// The `info` of an `exceeded` arm: `info.more(m)` performs what `k`
    /// does, `info.unbounded()` that and `Div`.
    Info,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Callable {
    row: Row,
    params: Vec<Latent>,
    mutable_params: Vec<bool>,
    result: Box<Latent>,
    generics: Vec<(String, Option<String>)>,
    host: bool,
    row_written: bool,
}

impl Callable {
    fn simple(row: Row) -> Self {
        Self {
            row,
            params: Vec::new(),
            mutable_params: Vec::new(),
            result: Box::new(Latent::Unknown),
            generics: Vec::new(),
            host: false,
            row_written: false,
        }
    }
}

impl Latent {
    fn unborrowed(&self) -> &Self {
        match self {
            Self::Borrow(value, _) => value.unborrowed(),
            _ => self,
        }
    }
}

type Locals = Vec<(String, Latent)>;

struct Analysis<'a> {
    program: &'a Program,
    nominal_owners: Option<Cow<'a, HashMap<TermId, String>>>,
    nominal_owners_checked: bool,
    fns: HashMap<&'a str, &'a FnDecl>,
    externs: HashSet<&'a str>,
    datas: HashMap<&'a str, &'a DataDecl>,
    operations: HashMap<&'a str, &'a EffectDecl>,
    expected_result: Option<Latent>,
    memo: HashMap<&'a str, Row>,
    in_progress: HashSet<&'a str>,
    recursive_refs: HashSet<&'a str>,
    /// Recursive functions that call only themselves, on a strict part of
    /// a parameter: they end without a proof.
    structural: HashSet<&'a str>,
    /// Exact declarations certified by the extraction facade.
    total: HashSet<String>,
    quants: HashMap<String, Quant>,
    calls: HashMap<TermId, Row>,
    /// Errors found while following calls, once each.
    found: Vec<RowDiagnostic>,
    /// The innermost written term being followed. A diagnostic on a term
    /// the class expansion made is reported there: its own span is in no
    /// source.
    written: Option<Span>,
    direct_vars: Vec<String>,
    /// The row variables of the calls whose arguments are being read, which
    /// a row the context gives may name before they are solved.
    inferring: Vec<String>,
    /// The `extern` functions the program declares: their rows are empty.
    user_externs: HashSet<&'a str>,
    javascript: bool,
    owners: HashMap<usize, RowOwner>,
    owner_sources: HashMap<RowOwner, usize>,
    owner_order: Vec<RowOwner>,
    declarations: HashMap<RowOwner, DeclarationRows>,
    scopes: HashMap<RowOwner, Vec<(String, String)>>,
    generic_keys: HashMap<RowOwner, Vec<(String, Option<String>)>>,
    scope: Vec<(String, String)>,
    owner: Option<RowOwner>,
    row_variables: HashMap<String, RowVariable>,
    call_owners: HashMap<TermId, Option<RowOwner>>,
    ambiguous_owners: HashSet<RowOwner>,
    ambiguous_calls: HashSet<TermId>,
    call_sources: HashMap<TermId, usize>,
    constructions: HashMap<TermId, (Option<RowOwner>, String)>,
    /// Constructor applications whose arguments are themselves only
    /// constructors and literals: constant data, such as a long list.
    constant_data: HashMap<TermId, bool>,
    /// The value of each constant datum, per owner and expected type. A
    /// datum is visited again from each enclosing constructor, so without
    /// this a list of n items costs n² before the program runs.
    constant_values: HashMap<TermId, Vec<(Option<RowOwner>, Option<Latent>, Latent)>>,
    /// The row last found for each term, and for each statement of a block.
    term_rows: HashMap<TermId, Row>,
    block_rows: HashMap<TermId, Vec<Row>>,
    /// What each operation arm's continuation performs, by handle and arm.
    continuations: HashMap<(TermId, usize), Row>,
}

fn effect_of_op(op: &str) -> String {
    if op == "exceeded" {
        "Exceeded".into()
    } else {
        op.to_string()
    }
}

fn unchecked(what: &str) -> String {
    format!("?{what}")
}

/// What an unchecked row says. A name that is not the program's own is said
/// as such (`!`), not as effects that cannot be followed.
fn unfollowed(what: &str) -> String {
    match what.strip_prefix('!') {
        Some(why) => why.to_string(),
        None => format!("cannot follow the effects of {what}"),
    }
}

fn unfollowed_in(what: &str, owner: &str) -> String {
    match what.strip_prefix('!') {
        Some(why) => format!("in `{owner}`: {why}"),
        None => format!("cannot follow the effects of {what} in `{owner}`"),
    }
}

/// The kernel's own definitions, which a proof sees but extraction maps
/// only inside the functions of the proof language.
const KERNEL_NAMES: &[&str] = &[
    "Nat::eq",
    "Nat::lt",
    "Nat::pred",
    "Nat::sub",
    "Nat::div_nz",
    "Nat::rem_nz",
];

fn display_row(row: &Row, variables: &HashMap<String, RowVariable>) -> Row {
    row.iter()
        .map(|effect| display_text(effect, variables))
        .collect()
}

fn display_text(text: &str, variables: &HashMap<String, RowVariable>) -> String {
    let mut text = text.to_string();
    let mut variables: Vec<_> = variables.iter().collect();
    variables.sort_by_key(|(key, _)| std::cmp::Reverse(key.len()));
    for (key, var) in variables {
        text = text.replace(key, &var.name);
    }
    shown_indices(&text)
}

/// Whether a row of `f` (its own or a parameter's) still writes an effect
/// with type arguments: one the index expansion did not rename.
fn indexed_template(f: &FnDecl) -> bool {
    let unexpanded = |row: &[String]| row.iter().any(|e| e.contains('(') && !e.contains('@'));
    if f.effects.as_deref().is_some_and(unexpanded) {
        return true;
    }
    let mut found = false;
    for t in f.param_types.iter().flatten() {
        let mut t = t.clone();
        walk::term(&mut t, &mut |x| {
            if let TermKind::Pi {
                effects: Some(row), ..
            } = &*x.kind
                && unexpanded(row)
            {
                found = true;
            }
        });
    }
    found
}

/// Each indexed effect's instance (`types/indices.rs`, `res@Pos`) in `text`
/// as it is written, `res(Pos)`.
pub fn shown_indices(text: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars().peekable();
    let mut last = ' ';
    while let Some(c) = chars.next() {
        if c != '@' || !(last.is_alphanumeric() || last == '_') {
            out.push(c);
            last = c;
            continue;
        }
        out.push('(');
        let mut depth = 0usize;
        while let Some(&n) = chars.peek() {
            match n {
                '(' => depth += 1,
                ')' if depth == 0 => break,
                ')' => depth -= 1,
                // Arguments are written without a space between them; a
                // comma and a space end the instance.
                ',' if chars.clone().nth(1).is_some_and(|c| c == ' ') => break,
                ',' => {
                    out.push_str(", ");
                    chars.next();
                    continue;
                }
                n if n.is_alphanumeric() || n == '_' || n == ':' => {}
                _ => break,
            }
            out.push(n);
            chars.next();
        }
        out.push(')');
        last = ')';
    }
    out
}

impl<'a> Analysis<'a> {
    fn new(program: &'a Program) -> Self {
        let mut fns = HashMap::new();
        let mut datas = HashMap::new();
        let mut externs = HashSet::new();
        let mut operations = HashMap::new();
        let mut quants = HashMap::from([
            ("show".to_string(), Quant::Direct),
            ("Exceeded".to_string(), Quant::AtMostOne),
            ("Div".to_string(), Quant::Zero),
        ]);
        // The prelude's functions and effects, unless the program declares
        // the name; their rows are written and trusted.
        let lib: &'static Program = prelude();
        let mut owners = HashMap::new();
        let mut owner_sources = HashMap::new();
        let mut owner_order = Vec::new();
        let mut call_sites = HashSet::new();
        let mut call_sources = HashMap::new();
        let mut ambiguous_owners = HashSet::new();
        let mut ambiguous_calls = HashSet::new();
        let mut found = Vec::new();
        for source in [lib, program] {
            if std::ptr::eq(source, program) && std::ptr::eq(program, lib) && !owners.is_empty() {
                continue;
            }
            let mut register = |f: &FnDecl| {
                let source = std::ptr::from_ref(f) as usize;
                if let Some(owner) = owners.get(&source) {
                    ambiguous_owners.insert(*owner);
                    found.push(RowDiagnostic {
                        message: format!("ambiguous lexical occurrence of function `{}`", f.name),
                        span: f.span,
                    });
                } else {
                    let owner = RowOwner(fresh_identity());
                    owners.insert(source, owner);
                    owner_sources.insert(owner, source);
                    owner_order.push(owner);
                }
            };
            for stmt in &source.stmts {
                walk::values_stmt(stmt, &mut |node| {
                    if let walk::Node::Stmt(Stmt::Fn(f)) = node {
                        register(f);
                    }
                });
                if let Stmt::Extern { fns, .. } = stmt {
                    for f in fns {
                        register(f);
                    }
                }
            }
            for stmt in &source.stmts {
                walk::values_stmt(stmt, &mut |node| {
                    if let walk::Node::Term(t) = node
                        && matches!(&*t.kind, TermKind::App { .. } | TermKind::Perform { .. })
                    {
                        call_sources
                            .entry(t.id())
                            .or_insert(std::ptr::from_ref(t) as usize);
                    }
                    if let walk::Node::Term(t) = node
                        && matches!(&*t.kind, TermKind::App { .. } | TermKind::Perform { .. })
                        && !call_sites.insert(t.id())
                    {
                        ambiguous_calls.insert(t.id());
                        found.push(RowDiagnostic {
                            message: "ambiguous lexical occurrence of an effect-row call".into(),
                            span: t.span,
                        });
                    }
                });
            }
        }
        for stmts in [&lib.stmts, &program.stmts] {
            for s in stmts {
                match s {
                    Stmt::Fn(f) => {
                        fns.insert(f.name.as_str(), f);
                        externs.remove(f.name.as_str());
                    }
                    Stmt::Extern {
                        fns: declarations, ..
                    } => {
                        for f in declarations {
                            fns.insert(f.name.as_str(), f);
                            externs.insert(f.name.as_str());
                        }
                    }
                    Stmt::Struct(d) | Stmt::Enum(d) => {
                        datas.insert(d.name.as_str(), d);
                    }
                    Stmt::Effect(e) => {
                        operations.insert(e.name.as_str(), e);
                        let q = e.resume.as_deref().and_then(Quant::parse);
                        quants.insert(e.name.clone(), q.unwrap_or(Quant::AtMostOne));
                    }
                    _ => {}
                }
            }
        }
        // Named references include functions carried through fields and
        // returned closures. A cycle is conservatively divergent even when
        // the reference is not a syntactically direct call.
        let graph: HashMap<&str, HashSet<&str>> = fns
            .iter()
            .map(|(&name, f)| {
                let refs = crate::lin::free_vars(&f.body)
                    .into_iter()
                    .filter(|n| !f.params.contains(n))
                    .filter_map(|n| fns.get_key_value(n.as_str()).map(|(&key, _)| key))
                    .collect();
                (name, refs)
            })
            .collect();
        let recursive_refs = graph
            .keys()
            .copied()
            .filter(|start| {
                let mut seen = HashSet::new();
                let mut pending: Vec<_> = graph[start].iter().copied().collect();
                while let Some(next) = pending.pop() {
                    if next == *start {
                        return true;
                    }
                    if seen.insert(next) {
                        if let Some(refs) = graph.get(next) {
                            pending.extend(refs);
                        }
                    }
                }
                false
            })
            .collect::<HashSet<&str>>();
        let reaches = |from: &str, to: &str| {
            let mut seen = HashSet::new();
            let mut pending = vec![from];
            while let Some(next) = pending.pop() {
                if next == to {
                    return true;
                }
                if seen.insert(next)
                    && let Some(refs) = graph.get(next)
                {
                    pending.extend(refs);
                }
            }
            false
        };
        let structural = recursive_refs
            .iter()
            .copied()
            .filter(|&name| {
                graph[name].iter().all(|&g| g == name || !reaches(g, name))
                    && structural::decreases(fns[name])
            })
            .collect();
        Analysis {
            program,
            nominal_owners: None,
            nominal_owners_checked: false,
            javascript: false,
            fns,
            externs,
            datas,
            operations,
            expected_result: None,
            memo: HashMap::new(),
            in_progress: HashSet::new(),
            recursive_refs,
            structural,
            total: HashSet::new(),
            quants,
            calls: HashMap::new(),
            found,
            written: None,
            direct_vars: Vec::new(),
            inferring: Vec::new(),
            user_externs: program
                .stmts
                .iter()
                .filter_map(|s| match s {
                    Stmt::Extern { fns, .. } => Some(fns.iter().map(|f| f.name.as_str())),
                    _ => None,
                })
                .flatten()
                .collect(),
            owners,
            owner_sources,
            owner_order,
            declarations: HashMap::new(),
            scopes: HashMap::new(),
            generic_keys: HashMap::new(),
            scope: Vec::new(),
            owner: None,
            row_variables: HashMap::new(),
            call_owners: HashMap::new(),
            ambiguous_owners,
            ambiguous_calls,
            call_sources,
            constructions: HashMap::new(),
            constant_data: HashMap::new(),
            constant_values: HashMap::new(),
            term_rows: HashMap::new(),
            block_rows: HashMap::new(),
            continuations: HashMap::new(),
        }
    }

    /// Why `name` is not a value the program has: it is not a local, a
    /// function or a constructor. `None` when it is one of those.
    fn unresolved(&self, name: &str, locals: &Locals) -> Option<String> {
        if locals.iter().any(|(local, _)| local == name)
            || self.fns.contains_key(name)
            || self
                .datas
                .values()
                .any(|d| d.constructors.iter().any(|c| c.name == name))
        {
            return None;
        }
        Some(if KERNEL_NAMES.contains(&name) {
            format!(
                "`{name}` is the kernel's own; a program uses it inside a function of the proof language"
            )
        } else {
            format!(
                "`{name}` is not defined in the program (a declaration of the proof language is used inside a function of the proof language)"
            )
        })
    }

    fn with_types(mut self, types: &'a TypeReport) -> Self {
        if let Some(owners) = types.nominal_owners_for(self.program) {
            self.nominal_owners = Some(Cow::Borrowed(owners));
            self.nominal_owners_checked = true;
        }
        self
    }

    fn nominal_owner(&mut self, term: &SurfaceTerm) -> Option<String> {
        if !self.nominal_owners_checked {
            // Independent row checking does not require a type report. Only
            // unresolved constructor ownership asks for one, once per analysis.
            self.nominal_owners_checked = true;
            let types = crate::types::check_program(self.program);
            self.nominal_owners = types
                .nominal_owners_for(self.program)
                .map(|owners| Cow::Owned(owners.clone()));
        }
        self.nominal_owners.as_ref()?.get(&term.id()).cloned()
    }

    fn run(mut self, program: &'a Program) -> RowReport {
        let mut report = RowReport::default();
        let mut names: Vec<&str> = self
            .fns
            .keys()
            .copied()
            .filter(|n| {
                program
                    .stmts
                    .iter()
                    .any(|s| matches!(s, Stmt::Fn(f) if f.name == *n))
            })
            .collect();
        names.sort_by_key(|n| self.fns[n].span.start);
        for name in names {
            let f = self.fns[name];
            // A prelude function whose generic is an effect's index is kept
            // only as the source of its copies (`types/indices.rs`), which
            // are checked instead.
            if f.span.start >= crate::surface::PRELUDE_BASE && indexed_template(f) {
                continue;
            }
            let inferred = self.inferred_row(name);
            let allowed = f
                .effects
                .as_ref()
                .map(|w| self.scope_row(w, &self.scopes[&self.owner_of(f)]));
            // A row does not say which type arguments an effect is performed
            // with; an entry that writes them would be read as another effect.
            for written in f
                .effects
                .iter()
                .flatten()
                .filter(|e| e.contains('(') && !e.contains('@'))
            {
                let head = written.split('(').next().unwrap_or_default().trim();
                let hint = if matches!(head, "show" | "exceeded") {
                    format!("; write `∀ A. {head}(A)` for every instance")
                } else {
                    String::new()
                };
                self.diagnostic(
                    format!(
                        "the row of `{name}` writes type arguments ({written}); a row names \
                         effects without them{hint}"
                    ),
                    f.span,
                );
            }
            for effect in &inferred {
                if let Some(what) = effect.strip_prefix('?') {
                    self.diagnostic(unfollowed_in(what, name), f.span);
                } else if let Some(allowed) = &allowed
                    && !allowed.contains(effect)
                {
                    self.diagnostic(
                        format!(
                            "`{name}` may perform {effect} but its row is {{{}}}",
                            show(allowed.iter().map(|s| s.as_str())),
                        ),
                        f.span,
                    );
                }
            }
            report.functions.push((
                name.to_string(),
                display_row(&inferred, &self.row_variables),
            ));
        }
        let mut top_locals = Vec::new();
        for stmt in &program.stmts {
            if let Stmt::Extern { fns, .. } = stmt {
                for f in fns.iter().filter(|f| {
                    f.span.start < crate::surface::PRELUDE_BASE
                        && f.effects.as_ref().is_some_and(|e| !e.is_empty())
                }) {
                    report.errors.push(RowDiagnostic {
                        message: "an extern cannot perform effects; wrap it in a tauto function"
                            .into(),
                        span: f.span,
                    });
                }
            }
            let (row, span) = match stmt {
                Stmt::Let { value, .. } | Stmt::Var { value, .. } => {
                    (self.stmt_row(stmt, &mut top_locals), value.span)
                }
                Stmt::Expr(e) => (self.term_row(e, &mut top_locals), e.span),
                Stmt::Assign { value, .. } => (self.stmt_row(stmt, &mut top_locals), value.span),
                Stmt::While { condition, .. } => {
                    (self.stmt_row(stmt, &mut top_locals), condition.span)
                }
                _ => continue,
            };
            // The host answers `show`, `test`, `spawn` and the standard effects.
            for effect in row.iter() {
                if crate::host::HOST_EFFECTS.contains(&effect.as_str()) {
                    report.host_effects.insert(effect.clone());
                }
            }
            for effect in row.iter().filter(|e| {
                !matches!(e.as_str(), "Div" | "show" | "test" | "spawn")
                    && !crate::host::HOST_EFFECTS.contains(&e.as_str())
            }) {
                let message = match effect.strip_prefix('?') {
                    Some(what) => unfollowed(what),
                    None => format!("unhandled effect {effect} at the top level"),
                };
                let message = display_text(&message, &self.row_variables);
                report.errors.push(RowDiagnostic { message, span });
            }
        }
        // What an arm may perform is found while following it, and says more
        // than the unhandled effect it leaves.
        self.found.append(&mut report.errors);
        report.errors = self.found;
        // A class method left unexpanded (`Ord::compare`) is an applied
        // expression whose effects no row describes. The classes did not
        // expand because the program does not check: that is the error, and
        // what it hides is only its echo. So is a row that still writes type
        // arguments: the indices did not expand because the program does not
        // check (`types/indices.rs`).
        let unexpanded = report
            .errors
            .iter()
            .any(|e| e.message.to_string().contains("writes type arguments"));
        if unexpanded
            || report.errors.iter().any(|e| {
                e.message
                    .to_string()
                    .starts_with("cannot follow the effects")
            })
        {
            let found = if unexpanded {
                crate::types::check_program(program).errors
            } else {
                crate::types::expansion_errors(program)
            };
            if !found.is_empty() {
                report.errors = found
                    .into_iter()
                    .map(|e| RowDiagnostic {
                        message: format!("type error: {}", e.message),
                        span: e.span,
                    })
                    .collect();
            }
        }
        // A row that still writes type arguments (`fail(Text)`) did not
        // expand because the program does not check: that is the error, and
        // the rows it leaves unread only echo it.
        if report
            .errors
            .iter()
            .any(|e| e.span.start < crate::surface::PRELUDE_BASE)
        {
            let found = crate::types::index_expansion_errors(program);
            if !found.is_empty() {
                report.errors = found
                    .into_iter()
                    .map(|e| RowDiagnostic {
                        message: format!("type error: {}", e.message),
                        span: e.span,
                    })
                    .collect();
            }
        }
        report.calls = self.calls;
        report.quants = self.quants;
        report.call_owners = self.call_owners;
        report.row_variables = self.row_variables;
        report.owner_sources = self.owner_sources;
        report.ambiguous_owners = self.ambiguous_owners;
        report.ambiguous_calls = self.ambiguous_calls;
        report.call_sources = self.call_sources;
        report.declarations = self
            .owner_order
            .iter()
            .filter_map(|o| self.declarations.remove(o))
            .collect();
        report
    }

    fn owner_of(&self, f: &FnDecl) -> RowOwner {
        self.owners[&(std::ptr::from_ref(f) as usize)]
    }

    fn prepare_scope(&mut self, f: &FnDecl, parent: &[(String, String)]) -> Vec<(String, String)> {
        let owner = self.owner_of(f);
        if let Some(scope) = self.scopes.get(&owner) {
            return scope.clone();
        }
        let mut scope = parent.to_vec();
        let mut generics: Vec<_> = f
            .generics
            .iter()
            .cloned()
            .zip(f.bounds.iter().cloned().chain(std::iter::repeat(None)))
            .zip(f.rows.iter().copied().chain(std::iter::repeat(false)))
            .map(|((name, bound), declared)| (name, bound, declared))
            .collect();
        let mut free = BTreeSet::new();
        for ty in f.param_types.iter().flatten().chain(f.result.iter()) {
            values::free_row_variables(&value_type(ty), &mut free);
        }
        free.extend(
            f.effects
                .iter()
                .flatten()
                .filter_map(|e| e.strip_prefix('|').map(str::to_string)),
        );
        for var in free {
            let declared_here = generics.iter().any(|(name, _, row)| *name == var && *row);
            let declared_outside = parent
                .iter()
                .rev()
                .find(|(name, _)| *name == var)
                .is_some_and(|(_, key)| self.row_variables.get(key).is_some_and(|v| v.declared));
            if !declared_here && !declared_outside {
                self.diagnostic(
                    format!("the row variable `{var}` is not declared; write `<!{var}>`"),
                    f.span,
                );
            }
            if !generics.iter().any(|(name, _, _)| *name == var)
                && !parent.iter().any(|(name, _)| *name == var)
            {
                generics.push((var, None, false));
            }
        }
        let mut keys = Vec::new();
        for (name, bound, declared) in generics {
            let key = format!("@row:{}", fresh_identity());
            self.row_variables.insert(
                key.clone(),
                RowVariable {
                    name: name.clone(),
                    owner,
                    bound: bound.clone(),
                    declared,
                },
            );
            scope.push((name, key.clone()));
            keys.push((key, bound));
        }
        self.generic_keys.insert(owner, keys);
        self.scopes.insert(owner, scope.clone());
        scope
    }

    fn scope_row(&self, row: &[String], scope: &[(String, String)]) -> Row {
        row.iter()
            .map(|effect| {
                effect
                    .strip_prefix('|')
                    .and_then(|name| scope.iter().rev().find(|(n, _)| n == name))
                    .map(|(_, key)| format!("|{key}"))
                    .unwrap_or_else(|| effect.clone())
            })
            .collect()
    }

    fn scoped_type_in(&self, ty: Option<&SurfaceTerm>, scope: &[(String, String)]) -> Latent {
        let types = scope
            .iter()
            .map(|(n, key)| (n.clone(), Latent::Named(key.clone(), Vec::new())))
            .collect();
        let rows = scope
            .iter()
            .map(|(n, key)| (n.clone(), Row::from([format!("|{key}")])))
            .collect();
        values::substitute(&latent_of_type(ty), &types, &rows)
    }

    fn scoped_type(&self, ty: &SurfaceTerm) -> Latent {
        self.scoped_type_in(Some(ty), &self.scope)
    }

    fn signature(&self, f: &FnDecl, row: Row) -> Callable {
        let owner = self.owner_of(f);
        let scope = &self.scopes[&owner];
        let host = self.user_externs.contains(f.name.as_str())
            && self
                .fns
                .get(f.name.as_str())
                .is_some_and(|global| std::ptr::eq(*global, f));
        let result = self.scoped_type_in(f.result.as_ref(), scope);
        Callable {
            row,
            params: f
                .param_types
                .iter()
                .map(|ty| self.scoped_type_in(ty.as_ref(), scope))
                .collect(),
            mutable_params: f.borrows.iter().map(|b| *b == Some(true)).collect(),
            result: Box::new(if host {
                self.host_return(result)
            } else {
                result
            }),
            generics: self.generic_keys[&owner].clone(),
            host,
            row_written: f.effects.is_some(),
        }
    }

    fn record_declaration(&mut self, f: &FnDecl, inferred: Row) {
        let owner = self.owner_of(f);
        let row = f
            .effects
            .as_ref()
            .map(|w| self.scope_row(w, &self.scopes[&owner]))
            .unwrap_or_else(|| inferred.clone());
        self.declarations.insert(
            owner,
            DeclarationRows {
                name: f.name.clone(),
                body: f.body.id(),
                owner,
                row,
                inferred,
            },
        );
    }

    fn record_call(&mut self, t: &SurfaceTerm, row: Row) {
        if self
            .call_owners
            .get(&t.id())
            .is_some_and(|owner| *owner != self.owner)
        {
            self.ambiguous_calls.insert(t.id());
            self.diagnostic(
                "ambiguous lexical owner of an effect-row call".into(),
                t.span,
            );
        }
        self.calls.insert(t.id(), row);
        self.call_owners.insert(t.id(), self.owner);
    }

    fn record_construction(&mut self, t: &SurfaceTerm, signature: &Callable) {
        let Latent::Named(name, _) = &*signature.result else {
            return;
        };
        let fact = (self.owner, name.clone());
        if self
            .constructions
            .get(&t.id())
            .is_some_and(|previous| *previous != fact)
        {
            self.ambiguous_calls.insert(t.id());
            self.diagnostic(
                "ambiguous lexical owner of a constructor call".into(),
                t.span,
            );
        }
        if !self.ambiguous_calls.contains(&t.id()) {
            self.constructions.insert(t.id(), fact);
        }
    }

    /// The row callers see: the written one, else the inferred one.
    fn fn_row(&mut self, name: &'a str) -> Row {
        let f = self.fns[name];
        let scope = self.prepare_scope(f, &[]);
        match &f.effects {
            // The host's own code calls these to answer the effect in the
            // row; the call is the answer, not a request for it.
            Some(_) if self.externs.contains(name) && crate::host::is_host_primitive(f) => {
                Row::new()
            }
            Some(written) => self.scope_row(written, &scope),
            None if self.externs.contains(name) => {
                self.record_declaration(f, Row::new());
                Row::new()
            }
            None => self.inferred_row(name),
        }
    }

    /// What the body performs, whatever the written row says.
    fn inferred_row(&mut self, name: &'a str) -> Row {
        let f = self.fns[name];
        let scope = self.prepare_scope(f, &[]);
        if let Some(row) = self.memo.get(name) {
            return row.clone();
        }
        if !self.in_progress.insert(name) {
            return if self.total.contains(name) || self.structural.contains(name) {
                Row::new()
            } else {
                Row::from(["Div".to_string()])
            };
        }
        let mut locals: Locals = f
            .params
            .iter()
            .zip(&f.param_types)
            .map(|(n, t)| (n.clone(), self.scoped_type_in(t.as_ref(), &scope)))
            .collect();
        let direct_vars = f
            .generics
            .iter()
            .zip(f.bounds.iter().chain(std::iter::repeat(&None)))
            .filter(|(_, b)| b.as_deref() == Some("direct"))
            .map(|(g, _)| scope.iter().rev().find(|(n, _)| n == g).unwrap().1.clone())
            .collect();
        let outer_direct = std::mem::replace(&mut self.direct_vars, direct_vars);
        let outer_scope = std::mem::replace(&mut self.scope, scope);
        let outer_owner = self.owner.replace(self.owner_of(f));
        let result = f.result.as_ref().map(|ty| self.scoped_type(ty));
        let outer_result = std::mem::replace(&mut self.expected_result, result.clone());
        let mut row = self.term_row_as(&f.body, &mut locals, result.as_ref());
        if let Some(expected) = result {
            self.check_term(&f.body, &expected, &locals);
        }
        self.expected_result = outer_result;
        self.direct_vars = outer_direct;
        self.scope = outer_scope;
        self.owner = outer_owner;
        self.in_progress.remove(name);
        if !self.total.contains(name)
            && !self.structural.contains(name)
            && self.recursive_refs.contains(name)
        {
            row.insert("Div".into());
        }
        self.memo.insert(name, row.clone());
        self.record_declaration(f, row.clone());
        row
    }

    /// The value's callable signature, including its latent row.
    fn latent_of(&mut self, t: &SurfaceTerm, locals: &Locals) -> Latent {
        let value = self.value_of(t, locals, None);
        value.unborrowed().clone()
    }

    fn term_row(&mut self, t: &SurfaceTerm, locals: &mut Locals) -> Row {
        self.term_row_as(t, locals, None)
    }

    fn term_row_as(
        &mut self,
        t: &SurfaceTerm,
        locals: &mut Locals,
        expected: Option<&Latent>,
    ) -> Row {
        let outer = self.enter(t);
        let row = self.term_row_of(t, locals, expected);
        self.written = outer;
        row
    }

    /// Makes `t` the written term being followed, when it is one, and
    /// gives the one it replaces.
    fn enter(&mut self, t: &SurfaceTerm) -> Option<Span> {
        let outer = self.written;
        if !generated(t.span) {
            self.written = Some(t.span);
        }
        outer
    }

    fn term_row_of(
        &mut self,
        t: &SurfaceTerm,
        locals: &mut Locals,
        expected: Option<&Latent>,
    ) -> Row {
        let mut row = Row::new();
        match &*t.kind {
            TermKind::Perform { effect, args } => {
                let before = self.found.len();
                if let Some(signature) = self.operation_signature(effect) {
                    self.check_arguments(&signature, args, locals, t.span, None);
                }
                // A task's body that performs what only a handler around
                // the `spawn` answers: say where its handler goes.
                if effect == "spawn" {
                    for d in &mut self.found[before..] {
                        if d.message
                            .to_string()
                            .starts_with("a function value may perform")
                        {
                            d.message.push_str(
                                "; a task runs apart from the handlers around its `spawn`, \
                                 so its handler goes in the task's body: \
                                 `spawn(() => handler(f))`",
                            );
                        }
                    }
                }
                for a in args {
                    row.extend(self.term_row(a, locals));
                }
                // What a task or a test body asks of the host is in the row
                // of the `spawn` or `test` that starts it, so that a type
                // shows it.
                let body = match (effect.as_str(), args.as_slice()) {
                    ("spawn", [f]) | ("test", [_, f]) => Some(f),
                    _ => None,
                };
                if let Some(f) = body
                    && let Latent::Known(c) = self.latent_of(f, locals)
                {
                    for e in c.row.iter() {
                        // A task's waits hold up that task only: the host
                        // answers them where it runs the task.
                        if e == "wait" && effect == "spawn" {
                            continue;
                        }
                        if crate::host::HOST_EFFECTS.contains(&e.as_str()) {
                            row.insert(e.clone());
                        } else if self.set_bound(e).is_some() {
                            // `<h: Host>`: some of the host's effects, which
                            // the function's row names, so that a call
                            // shows them.
                            row.insert(e.clone());
                        }
                    }
                }
                let own = Row::from([effect_of_op(effect)]);
                self.record_call(t, own.clone());
                row.extend(own);
            }
            TermKind::Record { fields, .. } => {
                self.value_of(t, locals, expected);
                for (_, v) in fields {
                    row.extend(self.term_row(v, locals));
                }
            }
            TermKind::Borrow { term, .. } => {
                row.extend(self.term_row_as(term, locals, expected.map(Latent::unborrowed)));
            }
            TermKind::App {
                function,
                arguments,
            } => {
                let mut params = Vec::new();
                // A construction checks its arguments against the type the
                // context gives it. Checked again without that type, its
                // parameters would be read off the first argument alone.
                if let TermKind::Var(name) = &*function.kind
                    && !locals.iter().any(|(n, _)| n == name)
                    && !self.fns.contains_key(name.as_str())
                    && let Some(signature) = self.constructor_signature_at(t, name, expected)
                {
                    self.value_of(t, locals, expected);
                    params = self.construction_params(&signature, arguments, locals, expected);
                } else {
                    // Parameter contracts identify constructors in argument
                    // position before their execution rows are read.
                    self.check_call(function, arguments, locals, t.span, expected);
                    if let Latent::Known(f) = self.latent_of(function, locals) {
                        let (types, rows) =
                            self.call_substitution_as(&f, arguments, locals, expected);
                        params = f
                            .params
                            .iter()
                            .map(|p| substitute(p, &types, &rows))
                            .collect();
                    }
                }
                // The arguments' rows apart, so that `row` is first what
                // the call itself performs.
                let mut args = Row::new();
                for (i, a) in arguments.iter().enumerate() {
                    args.extend(self.term_row_as(a, locals, params.get(i)));
                }
                let evaluated = self.term_row(function, locals);
                match &*function.kind {
                    TermKind::Field { base, name }
                        if matches!(&*base.kind, TermKind::Var(n)
                            if matches!(locals.iter().rev().find(|(m, _)| m == n), Some((_, Latent::Info)))) =>
                    {
                        if name == "unbounded" {
                            row.insert("Div".into());
                        }
                    }
                    TermKind::Var(n)
                        if !locals.iter().any(|(m, _)| m == n)
                            && !self.fns.contains_key(n.as_str())
                            && (pure_builtin(n, arguments.len())
                                || (!self.ambiguous_calls.contains(&t.id())
                                    && self
                                        .constructions
                                        .get(&t.id())
                                        .is_some_and(|(owner, _)| *owner == self.owner))) => {}
                    _ => match self.latent_of(function, locals) {
                        Latent::Known(f) => {
                            row.extend(self.callable_row(&f, arguments, locals, t.span))
                        }
                        _ => {
                            row.insert(unchecked(&match &*function.kind {
                                TermKind::Var(n) => match self.unresolved(n, locals) {
                                    Some(why) => format!("!{why}"),
                                    None => format!("calling `{n}`"),
                                },
                                _ => match dotted(function) {
                                    Some(n) => format!("calling `{n}`"),
                                    None => "an applied expression".into(),
                                },
                            }));
                        }
                    },
                }
                self.record_call(t, row.clone());
                row.extend(args);
                row.extend(evaluated);
            }
            TermKind::Budget { limit, steps, body } => {
                row.extend(self.term_row(steps, locals));
                let mut inner = self.term_row(body, locals);
                // Only steps stop a body that does not: a memory budget
                // leaves `Div` in the row.
                if *limit == BudgetLimit::Steps {
                    inner.remove("Div");
                }
                row.extend(inner);
                row.insert("Exceeded".into());
            }
            TermKind::Handle { body, handlers } => {
                let raw = self.term_row(body, locals);
                let handled: BTreeSet<String> = handlers
                    .iter()
                    .filter_map(|h| match h {
                        Handler::Operation {
                            effect,
                            patterns,
                            guard: None,
                            ..
                        } if patterns.iter().all(irrefutable) => Some(effect_of_op(effect)),
                        _ => None,
                    })
                    .collect();
                row.extend(raw.iter().filter(|e| !handled.contains(*e)).cloned());
                let mut returned = Row::new();
                for h in handlers {
                    if let Handler::Return { pattern, body } = h {
                        let mark = locals.len();
                        bind_pattern(pattern, locals);
                        returned.extend(self.term_row(body, locals));
                        locals.truncate(mark);
                    }
                }
                row.extend(returned.iter().cloned());
                let value = self.handled_value(t, body, handlers, locals);
                // A first reading of each arm, with `k` performing nothing,
                // gives what the arm performs besides resuming.
                let found = self.found.len();
                let own: Vec<Row> = handlers
                    .iter()
                    .map(|h| match h {
                        Handler::Operation {
                            effect,
                            patterns,
                            cont,
                            guard,
                            body,
                            ..
                        } => self.arm_row(
                            effect,
                            patterns,
                            cont,
                            guard,
                            body,
                            Row::new(),
                            &value,
                            locals,
                        ),
                        Handler::Return { .. } => Row::new(),
                    })
                    .collect();
                self.found.truncate(found);
                for (i, h) in handlers.iter().enumerate() {
                    if let Handler::Operation { effect, .. } = h {
                        // `k` may be called after its arm has returned, so
                        // it performs what runs after the operation: the rest
                        // of the body under the reinstalled handler, the arms
                        // of the operations that rest performs, and the
                        // return arm.
                        let resumed = self.resumed_row(
                            body,
                            &effect_of_op(effect),
                            handlers,
                            &handled,
                            &own,
                            &returned,
                        );
                        self.continuations.insert((t.id(), i), resumed);
                    }
                }
                let value = self.handled_value(t, body, handlers, locals);
                for (i, h) in handlers.iter().enumerate() {
                    if let Handler::Operation {
                        effect,
                        patterns,
                        cont,
                        guard,
                        body: arm_body,
                        ..
                    } = h
                    {
                        let resumed = self.continuations[&(t.id(), i)].clone();
                        let arm = self.arm_row(
                            effect, patterns, cont, guard, arm_body, resumed, &value, locals,
                        );
                        // Resuming is not part of what a direct arm does.
                        if self.quants.get(&effect_of_op(effect)) == Some(&Quant::Direct) {
                            self.direct_arm(effect, &own[i], arm_body.span);
                        }
                        row.extend(arm);
                    }
                }
            }
            // Making a function performs nothing; its row is latent.
            TermKind::Lam { .. } => {}
            TermKind::Block(stmts) => {
                let mark = locals.len();
                let mut rows = Vec::with_capacity(stmts.len());
                for (i, s) in stmts.iter().enumerate() {
                    let r = if i + 1 == stmts.len()
                        && let Stmt::Expr(e) = s
                    {
                        self.term_row_as(e, locals, expected)
                    } else {
                        self.stmt_row(s, locals)
                    };
                    row.extend(r.iter().cloned());
                    rows.push(r);
                }
                self.block_rows.insert(t.id(), rows);
                locals.truncate(mark);
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                row.extend(self.term_row(condition, locals));
                row.extend(self.term_row_as(then, locals, expected));
                if let Some(o) = otherwise {
                    row.extend(self.term_row_as(o, locals, expected));
                }
            }
            TermKind::Field { base, .. } | TermKind::Ascribe { term: base, .. } => {
                row.extend(self.term_row(base, locals))
            }
            TermKind::Product(members) | TermKind::Tuple(members) => {
                for m in members {
                    row.extend(self.term_row(m, locals));
                }
            }
            TermKind::Tagged { term, .. } => row.extend(self.term_row_as(term, locals, expected)),
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                row.extend(self.term_row(scrutinee, locals));
                let value = self.value_of(scrutinee, locals, None);
                for arm in arms {
                    let mark = locals.len();
                    self.bind_value_pattern(&arm.pattern, &value, locals);
                    if let Some(g) = &arm.guard {
                        row.extend(self.term_row(g, locals));
                    }
                    row.extend(self.term_row_as(&arm.body, locals, expected));
                    locals.truncate(mark);
                }
            }
            _ => {}
        }
        self.term_rows.insert(t.id(), row.clone());
        row
    }

    #[allow(clippy::too_many_arguments)]
    fn arm_row(
        &mut self,
        effect: &str,
        patterns: &[Pattern],
        cont: &Option<String>,
        guard: &Option<SurfaceTerm>,
        body: &SurfaceTerm,
        resumed: Row,
        value: &Latent,
        locals: &mut Locals,
    ) -> Row {
        let mark = locals.len();
        for p in patterns {
            match p {
                Pattern::Bind(n) if effect == "exceeded" => locals.push((n.clone(), Latent::Info)),
                // A spawned body may diverge, but performs no operation on
                // its caller's handler stack: what it asks of the host is in
                // the row of its `spawn`.
                Pattern::Bind(n) if effect == "spawn" => locals.push((
                    n.clone(),
                    Latent::Known(Callable::simple(Row::from(["Div".into()]))),
                )),
                p => bind_pattern(p, locals),
            }
        }
        let mut continuation = Callable::simple(resumed);
        if let Some(operation) = self.operation_signature(effect) {
            continuation.params.push(*operation.result);
        }
        continuation.result = Box::new(value.clone());
        locals.extend(
            cont.iter()
                .map(|k| (k.clone(), Latent::Known(continuation.clone()))),
        );
        let mut arm = Row::new();
        if let Some(g) = guard {
            arm.extend(self.term_row(g, locals));
        }
        arm.extend(self.term_row(body, locals));
        locals.truncate(mark);
        arm
    }

    /// What the continuation of the `arm`th handler of `handle` performs.
    /// Before the handle's row is found, what the handle performs, if known.
    fn continuation_row(&self, handle: &SurfaceTerm, arm: usize) -> Row {
        self.continuations
            .get(&(handle.id(), arm))
            .or_else(|| self.term_rows.get(&handle.id()))
            .cloned()
            .unwrap_or_default()
    }

    /// What resuming after `op` in `body` performs: the rest of the body,
    /// then each operation that rest may perform, closed over the arms that
    /// resume it.
    fn resumed_row(
        &self,
        body: &SurfaceTerm,
        op: &str,
        handlers: &[Handler],
        handled: &BTreeSet<String>,
        own: &[Row],
        returned: &Row,
    ) -> Row {
        let mut rest = self.after(body, op).unwrap_or_default();
        let mut reached = BTreeSet::new();
        loop {
            let next: Vec<String> = handlers
                .iter()
                .filter_map(|h| match h {
                    Handler::Operation { effect, .. } => Some(effect_of_op(effect)),
                    Handler::Return { .. } => None,
                })
                .filter(|e| rest.contains(e) && !reached.contains(e))
                .collect();
            if next.is_empty() {
                break;
            }
            for e in next {
                if let Some(r) = self.after(body, &e) {
                    rest.extend(r);
                }
                reached.insert(e);
            }
        }
        let mut row: Row = rest.into_iter().filter(|e| !handled.contains(e)).collect();
        for (h, arm) in handlers.iter().zip(own) {
            if let Handler::Operation { effect, .. } = h
                && reached.contains(&effect_of_op(effect))
            {
                row.extend(arm.iter().cloned());
            }
        }
        row.extend(returned.iter().cloned());
        row
    }

    /// What `t` performs after it performs `op`, until `t` ends, read from
    /// the rows already found; `None` when `t` cannot perform `op`.
    fn after(&self, t: &SurfaceTerm, op: &str) -> Option<Row> {
        let whole = |t: &SurfaceTerm| self.term_rows.get(&t.id()).cloned().unwrap_or_default();
        match &*t.kind {
            TermKind::Perform { effect, .. } if effect_of_op(effect) == op => Some(Row::new()),
            TermKind::Block(stmts) => {
                let rows = self.block_rows.get(&t.id())?;
                let mut found: Option<Row> = None;
                for (i, s) in stmts.iter().enumerate() {
                    let r = match s {
                        Stmt::Let { value, .. }
                        | Stmt::Var { value, .. }
                        | Stmt::Assign { value, .. }
                        | Stmt::Expr(value)
                        | Stmt::Return(Some(value)) => self.after(value, op),
                        _ => rows.get(i).filter(|r| r.contains(op)).cloned(),
                    };
                    if let Some(mut r) = r {
                        for later in rows.iter().skip(i + 1) {
                            r.extend(later.iter().cloned());
                        }
                        found.get_or_insert_with(Row::new).extend(r);
                    }
                }
                found
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                let mut found = self.after(condition, op).map(|mut r| {
                    r.extend(whole(then));
                    if let Some(o) = otherwise {
                        r.extend(whole(o));
                    }
                    r
                });
                for branch in std::iter::once(then).chain(otherwise) {
                    if let Some(r) = self.after(branch, op) {
                        found.get_or_insert_with(Row::new).extend(r);
                    }
                }
                found
            }
            _ => Some(whole(t)).filter(|r| r.contains(op)),
        }
    }

    /// Checks callback effects against the host frame's capabilities. Known
    /// native callback effects must be direct or `Div`. JavaScript callbacks
    /// reject operations that may resume many times and open rows.
    fn extern_closures(&mut self, arguments: &[SurfaceTerm], locals: &Locals, span: Span) {
        for a in arguments {
            let Latent::Known(row) = self.latent_of(a, locals) else {
                continue;
            };
            if let Some(effect) = row.row.iter().find(|e| {
                if self.javascript {
                    self.quants.get(*e) == Some(&Quant::Many) || e.starts_with('|')
                } else {
                    !self.is_direct(e) && !e.starts_with('|') && *e != "Div"
                }
            }) {
                let message = if self.javascript {
                    format!(
                        "a callback through a JavaScript host frame cannot perform {effect}, which may resume more than once; keep reusable continuations in Nib"
                    )
                } else {
                    format!(
                        "a closure passed to an extern cannot perform {effect}, which may suspend"
                    )
                };
                if !self
                    .found
                    .iter()
                    .any(|d| d.message == message && d.span == span)
                {
                    self.diagnostic(message, span);
                }
            }
        }
    }

    /// Whether `effect` is a direct operation (or a row variable bounded
    /// `direct`, or one that cannot be followed, which is reported already).
    /// The effects a row variable bounded by a set (`<h: Host>`) stands for
    /// some of.
    pub(super) fn set_bound(&self, effect: &str) -> Option<Vec<String>> {
        let var = effect.strip_prefix('|')?;
        let bound = self.row_variables.get(var)?.bound.as_deref()?;
        crate::surface::effect_sets::set_of_bound(bound).map(|(_, set)| set)
    }

    /// Whether a row that permits `allowed` permits `effect`: it names the
    /// effect, or the effect is a row variable bounded by a set it names.
    pub(super) fn permits(&self, allowed: &Row, effect: &str) -> bool {
        allowed.contains(effect)
            || self
                .set_bound(effect)
                .is_some_and(|set| set.iter().all(|e| allowed.contains(e)))
    }

    fn is_direct(&self, effect: &str) -> bool {
        if let Some(var) = effect.strip_prefix('|') {
            if let Some(var) = self.row_variables.get(var) {
                return var.bound.as_deref() == Some("direct");
            }
            return self.direct_vars.iter().any(|v| v == var);
        }
        effect.starts_with('?') || self.quants.get(effect) == Some(&Quant::Direct)
    }

    /// The arm of a direct operation performs direct operations only.
    fn direct_arm(&mut self, op: &str, arm: &Row, span: Span) {
        for effect in arm {
            if self.is_direct(effect) {
                continue;
            }
            let message = format!(
                "the arm of {op} performs {}, which is not direct",
                effect.trim_start_matches('|')
            );
            if !self
                .found
                .iter()
                .any(|d| d.message == message && d.span == span)
            {
                self.diagnostic(message, span);
            }
        }
    }

    fn stmt_row(&mut self, s: &Stmt, locals: &mut Locals) -> Row {
        let mut row = Row::new();
        match s {
            Stmt::Fn(f) => {
                let callable = self.local_function(f, locals);
                locals.push((f.name.clone(), Latent::Known(callable)));
            }
            Stmt::Let {
                name, ty, value, ..
            }
            | Stmt::Var {
                name, ty, value, ..
            } => {
                let expected = ty.as_ref().map(|ty| self.scoped_type(ty));
                row.extend(self.term_row_as(value, locals, expected.as_ref()));
                let actual = self.value_of(value, locals, expected.as_ref());
                if let Some(expected) = &expected {
                    self.check_value(&actual, expected, value.span, 0);
                }
                // A mutable binding keeps its initial callable contract;
                // every assignment and mutable borrow must fit that contract.
                let latent = expected.unwrap_or(actual);
                locals.push((name.clone(), latent));
            }
            // A field's contract is its declared type, which the type
            // checker holds the value to.
            Stmt::Assign {
                place: Some(_),
                value,
                ..
            } => {
                row.extend(self.term_row(value, locals));
            }
            Stmt::Assign { name, value, .. } => {
                let expected = locals
                    .iter()
                    .rev()
                    .find(|(n, _)| n == name)
                    .map(|(_, v)| v.clone());
                row.extend(self.term_row_as(value, locals, expected.as_ref()));
                if let Some(expected) = expected {
                    self.check_term(value, &expected, locals);
                }
            }
            Stmt::Expr(e) => row.extend(self.term_row(e, locals)),
            Stmt::Return(Some(e)) => {
                let expected = self.expected_result.clone();
                row.extend(self.term_row_as(e, locals, expected.as_ref()));
                if let Some(expected) = expected {
                    self.check_term(e, &expected, locals);
                }
            }
            Stmt::While { condition, body } => {
                row.extend(self.term_row(condition, locals));
                row.extend(self.term_row(body, locals));
                row.insert("Div".into());
            }
            _ => {}
        }
        row
    }

    fn local_function(&mut self, f: &FnDecl, captures: &Locals) -> Callable {
        let scope = self.prepare_scope(f, &self.scope.clone());
        let owner = self.owner_of(f);
        let outer_scope = std::mem::replace(&mut self.scope, scope);
        let outer_owner = self.owner.replace(owner);
        let result = f.result.as_ref().map(|ty| self.scoped_type(ty));
        let outer_result = std::mem::replace(&mut self.expected_result, result.clone());
        let written = f.effects.as_ref().map(|w| self.scope_row(w, &self.scope));
        let mut inferred = Row::new();
        loop {
            // A self reference carries divergence through aliases and fields.
            // Local source declarations cannot inherit a top-level extraction
            // certificate just because they reuse its name.
            let mut recursive = written.clone().unwrap_or_else(|| inferred.clone());
            recursive.insert("Div".into());
            let signature = self.signature(f, recursive);
            let mut inner = captures.clone();
            inner.push((f.name.clone(), Latent::Known(signature.clone())));
            inner.extend(f.params.iter().cloned().zip(signature.params));
            let mut next = self.term_row_as(&f.body, &mut inner, result.as_ref());
            if let Some(expected) = &result {
                self.check_term(&f.body, expected, &inner);
            }
            next.extend(inferred.iter().cloned());
            if next == inferred {
                break;
            }
            inferred = next;
        }
        for effect in &inferred {
            if let Some(what) = effect.strip_prefix('?') {
                self.diagnostic(unfollowed_in(what, &f.name), f.span);
            } else if let Some(allowed) = &written
                && !allowed.contains(effect)
            {
                self.diagnostic(
                    format!(
                        "`{}` may perform {effect} but its row is {{{}}}",
                        f.name,
                        show(allowed.iter().map(String::as_str))
                    ),
                    f.span,
                );
            }
        }
        self.record_declaration(f, inferred.clone());
        let callable = self.signature(f, written.unwrap_or(inferred));
        self.expected_result = outer_result;
        self.scope = outer_scope;
        self.owner = outer_owner;
        callable
    }
}

fn latent_of_type(ty: Option<&SurfaceTerm>) -> Latent {
    ty.map(value_type).unwrap_or(Latent::Unknown)
}

use values::{substitute, value_type};

fn irrefutable(p: &Pattern) -> bool {
    matches!(p, Pattern::Wild | Pattern::Bind(_))
}

fn bind_pattern(p: &Pattern, locals: &mut Locals) {
    match p {
        Pattern::Bind(n) => locals.push((n.clone(), Latent::Unknown)),
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| bind_pattern(a, locals)),
        Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| bind_pattern(a, locals)),
        Pattern::Tuple(items) => items.iter().for_each(|a| bind_pattern(a, locals)),
        _ => {}
    }
}

fn dotted(t: &SurfaceTerm) -> Option<String> {
    match &*t.kind {
        TermKind::Var(n) => Some(n.clone()),
        TermKind::Field { base, name } => Some(format!("{}.{name}", dotted(base)?)),
        _ => None,
    }
}

fn generated(span: Span) -> bool {
    (crate::surface::GENERATED_BASE..crate::surface::PRELUDE_BASE).contains(&span.start)
}

fn show<'s>(items: impl Iterator<Item = &'s str>) -> String {
    items.collect::<Vec<_>>().join(", ")
}

fn pure_builtin(name: &str, arity: usize) -> bool {
    matches!(
        name,
        "+" | "-"
            | "*"
            | "/"
            | "=="
            | "!="
            | "<"
            | ">"
            | "<="
            | ">="
            | "&&"
            | "||"
            | "clone"
            | "div"
            | "mod"
    ) || (name == "Tuple" && arity == 0)
}

#[cfg(test)]
#[path = "rows/tests.rs"]
mod value_tests;
