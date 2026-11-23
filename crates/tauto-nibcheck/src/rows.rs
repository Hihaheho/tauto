//! Effect rows of executable code: which effects a function may perform.
//!
//! This follows the rules of `lean/Proto/Nib/Typing.lean` on the surface
//! AST, without deriving effects from erased value types: `perform` adds its effect, a call adds the
//! callee's row, `handle` removes the effects its arms answer *completely*
//! (an irrefutable, unguarded arm) and adds what the arms and the `return`
//! arm perform, `budget` swaps `div` for `exceeded`, and a `while` loop or a
//! recursive call adds `div`.
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

use crate::surface::Name;
use std::borrow::Cow;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use tauto_message::{Message, msg};

use tauto_parol::Span;

use crate::surface::walk;
use crate::surface::{
    BudgetLimit, DataDecl, EffectDecl, FnDecl, Handler, Pattern, Program, Stmt, SurfaceTerm,
    TermId, TermKind,
};
use crate::types::{Quant, TypeReport};

pub mod origins;
mod reach;
mod structural;
mod values;

pub use reach::{free_names_of, row_error_reached};

pub type Row = BTreeSet<Name>;

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
    source: Option<(usize, crate::surface::TermId, usize)>,
    pub name: Name,
    pub owner: RowOwner,
    pub bound: Option<crate::surface::GenericBound>,
    /// Declared a row variable, `<!e>`. A name written in a row (`e`) that is not declared is
    /// reported; it is not read as a row variable because of how it is used.
    pub declared: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclarationRows {
    pub name: Name,
    pub body: TermId,
    pub owner: RowOwner,
    /// The contract callers see: the written row, otherwise the inferred row.
    pub row: Row,
    pub inferred: Row,
}

/// The rows of a function value, nested as its type is: a parameter or the
/// result that is not a function has none.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RowSignature {
    pub row: Row,
    pub params: Vec<Option<RowSignature>>,
    pub result: Option<Box<RowSignature>>,
}

impl RowSignature {
    fn of_latent(l: &Latent) -> Option<Self> {
        match l.unborrowed() {
            Latent::Known(f) => Some(Self {
                row: f.row.clone(),
                params: f.params.iter().map(Self::of_latent).collect(),
                result: Self::of_latent(&f.result).map(Box::new),
            }),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RowDiagnostic {
    pub message: Message,
    pub span: Span,
    /// An effect a function performs that its written row leaves out: the
    /// edit that writes it into the row can be offered.
    pub missing: Option<MissingEffect>,
}

/// An effect to write into the row of a function, as a row names it.
#[derive(Debug, Clone, PartialEq)]
pub struct MissingEffect {
    pub effect: String,
    /// Where the result type of the function ends: its row is written after it.
    pub after: u32,
}

impl fmt::Display for RowDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (byte {})", self.message, self.span.start)
    }
}

#[derive(Debug, Default, Clone)]
pub struct RowReport {
    /// Every function's inferred row.
    pub functions: Vec<(Name, Row)>,
    pub errors: Vec<RowDiagnostic>,
    /// What each call and `perform` performs itself (a call: its callee's
    /// row, instantiated; not what its arguments perform), by the term's
    /// occurrence identity. `lin.rs` checks control-flow linearity against it.
    pub calls: HashMap<TermId, Row>,
    /// Each operation's resume quantity.
    pub quants: HashMap<Name, Quant>,
    pub declarations: Vec<DeclarationRows>,
    /// The standard effects (`std/builtin/os.taut`) that reach the top level
    /// unanswered: what the host answers, and so the permissions a run needs.
    pub host_effects: BTreeSet<String>,
    /// For each of `host_effects`, the functions it comes from
    /// ([`origins`]): what a run's permissions are granted to.
    pub host_origins: std::collections::BTreeMap<String, BTreeSet<origins::Origin>>,
    /// The functions with a row `!?` that call themselves or a later `!?` function: the row of
    /// each depends on a row not known yet, so none is found for them.
    pub row_hole_cycles: BTreeSet<Name>,
    /// Whether `wait` is among them: the top level is then a future the host
    /// runs.
    pub host_waits: bool,
    /// Whether the top level performs an entry (`main` or `test`): the
    /// program is then a module's entries, which `Entry::run` of the prelude
    /// runs.
    pub entries: bool,
    /// What each statement the top level runs performs, and where it is.
    pub top_rows: Vec<(Row, Span)>,
    pub call_owners: HashMap<TermId, Option<RowOwner>>,
    /// The latent row of each term whose value is a function, with the
    /// declaration whose row variables it is written in. A term followed
    /// more than once with different rows has none.
    pub values: HashMap<TermId, (Option<RowOwner>, Row)>,
    /// The latent signature of each term whose value is a function: its row,
    /// and those of its parameters and result that are functions. Value types
    /// erase rows; this is what a function type's rows are.
    pub signatures: HashMap<TermId, (Option<RowOwner>, RowSignature)>,
    pub row_variables: HashMap<Name, RowVariable>,
    // Addresses are lookup keys for the borrowed immutable AST only. They
    // never order declarations or appear in diagnostics or generated code.
    owner_sources: HashMap<RowOwner, usize>,
    ambiguous_owners: HashSet<RowOwner>,
    ambiguous_calls: HashSet<TermId>,
    call_sources: HashMap<TermId, usize>,
    /// The functions checked extraction showed total, and the profile the
    /// rows were found for: what [`check_rewrapped_rows`] judges the same
    /// program, wrapped, with.
    evidence: HashSet<Name>,
    pub(crate) target: Target,
}

impl RowReport {
    /// Whether checked extraction showed the function `name` total: its row
    /// leaves out the effects of the operators in it (`overflow`, `divzero`),
    /// so the body must not perform them.
    pub fn is_total(&self, name: &Name) -> bool {
        self.evidence.contains(name)
    }

    pub fn declaration_row(
        &self,
        name: &Name,
        body: TermId,
    ) -> Result<Option<&DeclarationRows>, Message> {
        let mut matches = self
            .declarations
            .iter()
            .filter(|d| d.name == *name && d.body == body);
        let first = matches.next();
        if matches.next().is_some()
            || first.is_some_and(|d| self.ambiguous_owners.contains(&d.owner))
        {
            return Err(msg!("rows-ambiguous-declaration", name = name.to_string()));
        }
        Ok(first)
    }

    /// Validate that row variables belong to this declaration, preserving their identities.
    /// A captured row cannot become a same-named quantified row in a backend.
    pub fn normalize_row(&self, row: &Row, owner: Option<RowOwner>) -> Result<Row, Message> {
        row.iter()
            .map(|effect| {
                if let Some(what) = effect.strip_prefix('?') {
                    return Err(display_message(unfollowed(what), &self.row_variables));
                }
                let Some(key) = effect.row_variable() else {
                    return Ok(effect.clone());
                };
                match self.row_variables.get(&key) {
                    Some(var) if Some(var.owner) == owner => Ok(effect.clone()),
                    Some(var) => Err(msg!(
                        "rows-captured-variable-needs-owner",
                        var = var.name.as_str()
                    )),
                    None if key.starts_with("@row:") => Err(msg!("rows-no-binder-identity")),
                    None => Err(msg!("rows-variable-no-owner", var = key.to_string())),
                }
            })
            .collect()
    }

    /// The latent row of the function value `t`, normalized, when row
    /// checking followed it to one.
    pub fn value_row(&self, t: TermId) -> Option<Row> {
        let (owner, row) = self.values.get(&t)?;
        self.normalize_row(row, *owner).ok()
    }

    /// The latent signature of the function value `t`, its rows normalized,
    /// when row checking followed it to one.
    pub fn value_signature(&self, t: TermId) -> Option<RowSignature> {
        let (owner, sig) = self.signatures.get(&t)?;
        fn norm(r: &RowReport, s: &RowSignature, owner: Option<RowOwner>) -> Option<RowSignature> {
            Some(RowSignature {
                row: r.normalize_row(&s.row, owner).ok()?,
                params: s
                    .params
                    .iter()
                    .map(|p| match p {
                        Some(p) => norm(r, p, owner).map(Some),
                        None => Some(None),
                    })
                    .collect::<Option<_>>()?,
                result: match &s.result {
                    Some(x) => Some(Box::new(norm(r, x, owner)?)),
                    None => None,
                },
            })
        }
        norm(self, sig, *owner)
    }

    /// The calls' rows, normalized; what fails says where the call is.
    pub fn normalized_calls(&self) -> Result<HashMap<TermId, Row>, (Message, Option<Span>)> {
        if let Some(id) = self
            .ambiguous_calls
            .iter()
            .min_by_key(|id| (id.span().start, id.span().end))
        {
            return Err((msg!("rows-ambiguous-call"), Some(id.span())));
        }
        let mut calls: Vec<_> = self.calls.iter().collect();
        calls.sort_by_key(|(id, row)| (id.span().start, id.span().end, self.display_row(row)));
        calls
            .into_iter()
            .map(|(id, row)| {
                let owner = self
                    .call_owners
                    .get(id)
                    .ok_or_else(|| (msg!("rows-call-no-owner"), Some(id.span())))?;
                let row = self
                    .normalize_row(row, *owner)
                    .map_err(|e| (e, Some(id.span())))?;
                Ok((*id, row))
            })
            .collect()
    }

    fn same_row(&self, a: &Row, other: &Self, b: &Row) -> bool {
        a.len() == b.len()
            && a.iter().all(|left| {
                b.iter().any(|right| {
                    if left == right {
                        return true;
                    }
                    let Some(l) = left
                        .row_variable()
                        .and_then(|key| self.row_variables.get(&key))
                    else {
                        return false;
                    };
                    let Some(r) = right
                        .row_variable()
                        .and_then(|key| other.row_variables.get(&key))
                    else {
                        return false;
                    };
                    // Independently checked raw syntax receives fresh local identities.
                    // Only the same borrowed binder occurrence establishes correspondence.
                    l.source.is_some()
                        && l.source == r.source
                        && l.bound == r.bound
                        && l.declared == r.declared
                })
            })
    }

    /// Keeps, for a call the prelude's report and this one read differently,
    /// the row this one read: a macro's program holds copies of the
    /// prelude's declarations, checked again where the macro runs.
    pub fn keep_own_calls(&mut self) {
        // Reachable row failures were already refused for the selected
        // entries (`refuse_row_errors` / `row_error_reached`). Unreached
        // errors are dropped so lowering does not see them again.
        self.errors.clear();
        self.ambiguous_calls.clear();
        self.ambiguous_owners.clear();
        let mut seen = HashSet::new();
        self.declarations
            .retain(|d| seen.insert((d.name.clone(), d.body)));
    }

    pub fn merge_prelude(&mut self, mut other: RowReport) {
        // Checking the same borrowed declaration twice allocates two report
        // owners, but its resolved generic binders retain their identities.
        // Align the owners before merging either calls or binder metadata.
        let owners: HashMap<_, _> = other
            .declarations
            .iter()
            .filter_map(|declaration| {
                let source = other.owner_sources.get(&declaration.owner)?;
                let existing = self.declarations.iter().find(|existing| {
                    self.owner_sources.get(&existing.owner) == Some(source)
                        && existing.name == declaration.name
                        && existing.body == declaration.body
                })?;
                Some((declaration.owner, existing.owner))
            })
            .collect();
        for declaration in &mut other.declarations {
            if let Some(owner) = owners.get(&declaration.owner) {
                declaration.owner = *owner;
            }
        }
        for owner in other.call_owners.values_mut().flatten() {
            if let Some(existing) = owners.get(owner) {
                *owner = *existing;
            }
        }
        for variable in other.row_variables.values_mut() {
            if let Some(owner) = owners.get(&variable.owner) {
                variable.owner = *owner;
            }
        }
        other.owner_sources = other
            .owner_sources
            .into_iter()
            .map(|(owner, source)| (owners.get(&owner).copied().unwrap_or(owner), source))
            .collect();
        other.ambiguous_owners = other
            .ambiguous_owners
            .into_iter()
            .map(|owner| owners.get(&owner).copied().unwrap_or(owner))
            .collect();
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
                        .is_some_and(|(a, b)| self.same_row(&a, &other, &b))
                    && self
                        .normalize_row(&d.inferred, Some(d.owner))
                        .ok()
                        .zip(
                            other
                                .normalize_row(&declaration.inferred, Some(declaration.owner))
                                .ok(),
                        )
                        .is_some_and(|(a, b)| self.same_row(&a, &other, &b))
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
                                .is_some_and(|(a, b)| self.same_row(&a, &other, &b))
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
        for (id, value) in other.signatures {
            if self.signatures.get(&id).is_some_and(|v| *v != value) {
                self.signatures.remove(&id);
            } else {
                self.signatures.insert(id, value);
            }
        }
        for (id, value) in other.values {
            if self.values.get(&id).is_some_and(|v| *v != value) {
                self.values.remove(&id);
            } else {
                self.values.insert(id, value);
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

    /// A row as a declaration writes it after `!`: `{Log, div} ∪ e`, the effects in a fixed order,
    /// the row variable last; `None` when the row holds an effect that could not be followed
    /// (`?…`), which no source writes, and the empty string for the empty row.
    pub fn written_row(&self, row: &Row) -> Option<String> {
        let mut literals = Vec::new();
        let mut variables = Vec::new();
        for effect in diagnostic_order(row) {
            if effect.starts_with('?') {
                return None;
            }
            let text = self.effect_name(&effect.display_in_row());
            if effect.row_variable().is_some() {
                variables.push(text);
            } else {
                literals.push(text);
            }
        }
        let mut parts = Vec::new();
        if !literals.is_empty() {
            parts.push(format!("{{{}}}", literals.join(", ")));
        }
        parts.extend(variables);
        Some(parts.join(" ∪ "))
    }

    /// The quantities an effect of a row may have: a declared one's own,
    /// any for a row variable (`<=1` and below when `bounded` says it is
    /// bounded so), none for an effect that cannot be followed (that is
    /// reported already).
    pub fn quants_of(&self, effect: &Name, bounded: &dyn Fn(&Name) -> bool) -> Vec<Quant> {
        if let Some(var) = effect.row_variable() {
            if let Some(var) = self.row_variables.get(&var) {
                return match var.bound.as_deref() {
                    Some("direct") => vec![Quant::Direct],
                    Some("<=1") => vec![Quant::Zero, Quant::AtMostOne, Quant::One],
                    _ => vec![Quant::Zero, Quant::AtMostOne, Quant::One, Quant::Many],
                };
            }
            return if bounded(&var) {
                vec![Quant::Zero, Quant::AtMostOne, Quant::One]
            } else {
                vec![Quant::Zero, Quant::AtMostOne, Quant::One, Quant::Many]
            };
        }
        if effect.starts_with('?') {
            return Vec::new();
        }
        // An index label resumes as its family's operation does: what it
        // holds runs elsewhere.
        if let Some((family, _)) = crate::types::indices::split_index_label(effect) {
            return vec![
                self.quants
                    .iter()
                    .find(|(k, _)| crate::types::indices::family_of(k) == family)
                    .map(|(_, q)| *q)
                    .unwrap_or(Quant::One),
            ];
        }
        vec![self.quants.get(effect).copied().unwrap_or(Quant::AtMostOne)]
    }
}

pub use tauto_nir::Target;

/// Check host callbacks against the JavaScript Promise boundary.
pub fn check_program_rows_javascript(program: &Program) -> RowReport {
    let mut analysis = Analysis::new(program);
    analysis.target = Target::JavaScript;
    analysis.run(program)
}

/// The rows of `wrapped`, the program `rows` were found for with its
/// top-level statements run under `Entry::run` (`host::wrap`). The wrapper changes no declaration's recursion, so the
/// extraction evidence `rows` were found with holds for `wrapped` too: a
/// function the kernel accepted as total stays without `div`.
pub fn check_rewrapped_rows(rows: &RowReport, wrapped: &Program) -> RowReport {
    let mut analysis = Analysis::new(wrapped);
    analysis.total.clone_from(&rows.evidence);
    analysis.target = rows.target;
    analysis.run(wrapped)
}

/// The rows of `copy`, a program made from the one `rows` were found for by
/// copying declarations (`copied_from` names the declaration each copy is
/// made from) and rewriting calls to reach the copies. A copy recurses as the
/// declaration it is made from does, so the extraction evidence `rows` were
/// found with holds for the copies of a function it shows total, and the
/// copy is judged with it.
pub fn check_copied_rows_with_types(
    rows: &RowReport,
    copied_from: &HashMap<Name, Name>,
    copy: &Program,
    types: &TypeReport,
) -> RowReport {
    let mut analysis = Analysis::new(copy).with_types(types);
    analysis.total.clone_from(&rows.evidence);
    analysis.total.extend(
        copied_from
            .iter()
            .filter(|(_, from)| rows.evidence.contains(*from))
            .map(|(copy, _)| copy.clone()),
    );
    analysis.target = rows.target;
    analysis.run(copy)
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
    analysis.target = Target::JavaScript;
    analysis.run(program)
}

/// Compiler-internal configuration: `total` must come from checked extraction,
/// not source annotations. Callers that read source use `check_program_rows`;
/// the file facade revalidates extraction evidence before using this entry point.
pub fn check_program_rows_trusted(
    program: &Program,
    total: &HashSet<Name>,
    target: Target,
) -> RowReport {
    let mut analysis = Analysis::new(program);
    analysis.total.clone_from(total);
    analysis.target = target;
    analysis.run(program)
}

/// The same checked-extraction boundary as [`check_program_rows_trusted`],
/// with an optional source-matched value report for nominal constructor owners.
pub fn check_program_rows_trusted_with_types(
    program: &Program,
    total: &HashSet<Name>,
    target: Target,
    types: &TypeReport,
) -> RowReport {
    let mut analysis = Analysis::new(program).with_types(types);
    analysis.total.clone_from(total);
    analysis.target = target;
    analysis.run(program)
}

/// The report as text, for `totes/nibcheck` to write the same: a line for
/// each function in the order of the report, each error in order, each call
/// sorted by its span and each quantity sorted by the effect's name.
pub fn dump_rows(report: &RowReport) -> String {
    let row = |r: &Row| format!("{{{}}}", show(report.display_row(r).iter()));
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
    Named(Name, Vec<Latent>),
    Record(Name, Vec<(String, Latent)>),
    Plain,
    Effects(Row),
    Borrow(Box<Latent>, bool),
    Unknown,
    /// A type parameter that a constructed value holds nothing of: `None`
    /// is an `Option(A)` for every `A`. Any contract agrees with it.
    Absent,
    /// The `info` of an `exceeded` arm: `info.more(m)` performs what `k`
    /// does, `info.unbounded()` that and `div`.
    Info,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Callable {
    row: Row,
    params: Vec<Latent>,
    mutable_params: Vec<bool>,
    result: Box<Latent>,
    generics: Vec<(Name, Option<crate::surface::GenericBound>)>,
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

type Locals = Vec<(Name, Latent)>;

struct Analysis<'a> {
    program: &'a Program,
    resolved: bool,
    nominal_owners: Option<Cow<'a, HashMap<TermId, Name>>>,
    nominal_owners_checked: bool,
    /// The value types, for the effect an operator performs; read once, when
    /// the first operator is met.
    operand_types: Option<Cow<'a, TypeReport>>,
    /// The checked type of each term, read once when a record's rows index an effect.
    term_types: Option<HashMap<TermId, crate::types::Ty>>,
    fns: HashMap<&'a Name, &'a FnDecl>,
    externs: HashSet<&'a Name>,
    datas: HashMap<&'a Name, &'a DataDecl>,
    structs: HashSet<&'a Name>,
    /// The constructors of `datas`, keyed by the names that select them.
    constructors: values::Constructors<'a>,
    /// The fields of each value `members` has unfolded. They depend only on
    /// the value and the declarations, which do not change during analysis.
    members: std::cell::RefCell<HashMap<Latent, Option<std::rc::Rc<[((Name, usize), Latent)]>>>>,
    operations: HashMap<&'a Name, &'a EffectDecl>,
    expected_result: Option<Latent>,
    memo: HashMap<&'a Name, Row>,
    in_progress: HashSet<&'a Name>,
    /// The functions being followed that the current body has read before
    /// their rows were known.
    leaned: HashSet<&'a Name>,
    /// The rows the last pass over a recursive group found for its members,
    /// which the next pass reads where it reaches a member being followed.
    seeds: HashMap<&'a Name, Row>,
    /// The members of the recursive groups being followed that this pass
    /// has already followed, with what each leaned on, in the order found.
    pass: Vec<(&'a Name, Row, HashSet<&'a Name>)>,
    recursive_refs: HashSet<&'a Name>,
    /// Recursive functions that call only themselves, on a strict part of
    /// a parameter: they end without a proof.
    structural: HashSet<&'a Name>,
    /// Exact declarations certified by the extraction facade.
    total: HashSet<Name>,
    /// Whether the body being followed belongs to a `total` declaration,
    /// whose arithmetic the extractor emits only behind its guards.
    in_total: bool,
    quants: HashMap<Name, Quant>,
    calls: HashMap<TermId, Row>,
    /// Errors found while following calls, once each.
    found: Vec<RowDiagnostic>,
    row_hole_cycles: BTreeSet<Name>,
    /// The innermost written term being followed. A diagnostic on a term
    /// the class expansion made is reported there: its own span is in no
    /// source.
    written: Option<Span>,
    /// The row variables of the function being followed that are bounded
    /// `direct`.
    direct_vars: Vec<Name>,
    /// The row variables of the calls whose arguments are being read, which
    /// a row the context gives may name before they are solved.
    inferring: Vec<Name>,
    /// The `extern` functions the program declares: their rows are empty.
    user_externs: HashSet<&'a Name>,
    target: Target,
    owners: HashMap<usize, RowOwner>,
    owner_sources: HashMap<RowOwner, usize>,
    owner_order: Vec<RowOwner>,
    declarations: HashMap<RowOwner, DeclarationRows>,
    scopes: HashMap<RowOwner, Vec<(Name, Name)>>,
    generic_keys: HashMap<RowOwner, Vec<(Name, Option<crate::surface::GenericBound>)>>,
    scope: Vec<(Name, Name)>,
    owner: Option<RowOwner>,
    row_variables: HashMap<Name, RowVariable>,
    call_owners: HashMap<TermId, Option<RowOwner>>,
    /// See [`RowReport::values`]; `None` where two followings disagree.
    values: HashMap<TermId, Option<(Option<RowOwner>, Row)>>,
    signatures: HashMap<TermId, Option<(Option<RowOwner>, RowSignature)>>,
    ambiguous_owners: HashSet<RowOwner>,
    ambiguous_calls: HashSet<TermId>,
    call_sources: HashMap<TermId, usize>,
    constructions: HashMap<TermId, (Option<RowOwner>, Name)>,
    /// Constructor applications whose arguments are themselves only
    /// constructors and literals: constant data, such as a long list.
    constant_data: HashMap<TermId, bool>,
    /// The value of each constant datum, per owner and expected type. A
    /// datum is visited again from each enclosing constructor, so without
    /// this a list of n items costs n² before the program runs.
    constant_values: HashMap<TermId, Vec<(Option<RowOwner>, Option<Latent>, Latent)>>,
    /// The value of each `λ`, by its locals and the type expected of it,
    /// while the same functions are being inferred. Reading a `λ` reads its
    /// body for its row and again for its value, and an argument `λ` is read
    /// again by the call that takes it: without this, `λ`s nested n deep cost
    /// 2ⁿ (a view of nested `λ`s took minutes).
    lambda_values: HashMap<(TermId, Option<RowOwner>, Option<Latent>, Locals), Latent>,
    /// The row last found for each term, and for each statement of a block.
    term_rows: HashMap<TermId, Row>,
    block_rows: HashMap<TermId, Vec<Row>>,
    /// What each operation arm's continuation performs, by handle and arm.
    continuations: HashMap<(TermId, usize), Row>,
}

/// The prelude's placement operations (`place`, `rc_place`): their arms only
/// answer a place, `k(e)`, so that a backend may pass the place as an
/// argument instead of suspending.
fn is_placement(op: &Name) -> bool {
    let spelled = op.as_str();
    let base = spelled.split('@').next().unwrap_or(spelled);
    let short = base.rsplit("::").next();
    ["place", "rc_place"].into_iter().any(|name| {
        short == Some(name)
            && (!op.is_resolved()
                || tauto_surface::bindings::library_reference(name)
                    .is_some_and(|l| l.as_str().split('@').next() == Some(base)))
    })
}

/// Whether an arm in `handled` removes the index label `e`: an arm of its
/// family for every instance does.
fn handles_label(handled: &BTreeSet<Name>, e: &Name) -> bool {
    crate::types::indices::split_index_label(e).is_some_and(|(family, _)| {
        handled
            .iter()
            .any(|h| !h.to_string().contains('@') && crate::types::indices::family_of(h) == family)
    })
}

/// The host's effect an index label (`spawn@^env`) holds, as the library
/// names it.
fn label_host_member(label: &Name) -> Option<Name> {
    let (_, member) = crate::types::indices::split_index_label(label)?;
    let short = member.split('@').next().unwrap_or(&member);
    let short = short.rsplit("::").next().unwrap_or(short);
    crate::host::HOST_EFFECTS
        .iter()
        .find(|h| **h == short)
        .map(|h| tauto_surface::bindings::library_name(h))
}

/// An effect the checker cannot follow, named by what it is: `?call:f`,
/// `?row-variable:e`, `?expression:` or, for a name the program does not
/// have, `?kernel:n` / `?undefined:n`.
/// The stand-in extraction writes for a match with no arms never runs: it is not a reason
/// for a function that calls it to say `div`.
fn is_extract_unreachable(name: &Name) -> bool {
    name.to_string().contains("extract_unreachable")
        || format!("{name:?}").contains("extract_unreachable")
}

fn unchecked(kind: &str, name: &str) -> Name {
    format!("?{kind}:{name}").into()
}

/// What an unchecked row says, from the tag `unchecked` wrote.
fn unfollowed(what: &str) -> Message {
    let (kind, name) = what.split_once(':').unwrap_or((what, ""));
    let name = name.to_string();
    match kind {
        "kernel" => msg!("rows-kernel-name", name = name),
        "undefined" => msg!("rows-undefined-name", name = name),
        "call" => msg!("rows-unfollowed-call", name = name),
        "row-variable" => msg!("rows-unfollowed-row-variable", name = name),
        _ => msg!("rows-unfollowed-expression"),
    }
}

fn unfollowed_in(what: &str, owner: &str) -> Message {
    let (kind, name) = what.split_once(':').unwrap_or((what, ""));
    match kind {
        // A name the program does not have is told as it is at every place that finds it,
        // inside a function or not: the span says where.
        "kernel" | "undefined" => unfollowed(what),
        "call" => msg!(
            "rows-unfollowed-call-in",
            name = name.to_string(),
            owner = owner.to_string()
        ),
        "row-variable" => msg!(
            "rows-unfollowed-row-variable-in",
            name = name.to_string(),
            owner = owner.to_string()
        ),
        _ => msg!("rows-unfollowed-expression-in", owner = owner.to_string()),
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

fn display_row(row: &Row, _variables: &HashMap<Name, RowVariable>) -> Row {
    row.clone()
}

fn display_text(text: &str, variables: &HashMap<Name, RowVariable>) -> String {
    let mut text = text.to_string();
    let mut variables: Vec<_> = variables.iter().collect();
    variables.sort_by_key(|(key, _)| std::cmp::Reverse(key.len()));
    for (key, var) in variables {
        text = text.replace(key.as_str(), var.name.as_str());
    }
    shown_indices(&text)
}

/// The message with the row-variable names of its text arguments written as
/// the source wrote them.
fn display_message(message: Message, variables: &HashMap<Name, RowVariable>) -> Message {
    use tauto_message::Value;
    Message {
        id: message.id,
        args: message
            .args
            .into_iter()
            .map(|(name, value)| {
                let value = match value {
                    Value::Text(t) => Value::Text(display_text(&t, variables)),
                    Value::Message(m) => Value::Message(Box::new(display_message(*m, variables))),
                    other => other,
                };
                (name, value)
            })
            .collect(),
    }
}

/// Whether a row of `f` (its own or a parameter's) still writes an effect
/// with type arguments: one the index expansion did not rename.
fn indexed_template(f: &FnDecl) -> bool {
    let unexpanded = |row: &[Name]| row.iter().any(|e| e.contains('(') && !e.contains('@'));
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
        // An index label, `spawn@^env`: the body's row it holds.
        if c == '@' && chars.peek() == Some(&'^') {
            chars.next();
            out.push_str("(() -> _ ! {");
            while let Some(&n) = chars.peek() {
                if !(n.is_alphanumeric() || n == '_' || n == ':') {
                    break;
                }
                out.push(n);
                chars.next();
            }
            out.push_str("})");
            last = ')';
            continue;
        }
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

/// The strongly connected component of each node of `graph`, by a number
/// (Tarjan's algorithm, without recursion): two nodes have the same number
/// exactly when each reaches the other.
fn components<'n>(graph: &HashMap<&'n Name, HashSet<&'n Name>>) -> HashMap<&'n Name, usize> {
    let mut index: HashMap<&Name, usize> = HashMap::new();
    let mut low: HashMap<&Name, usize> = HashMap::new();
    let mut on_stack: HashSet<&Name> = HashSet::new();
    let mut stack: Vec<&Name> = Vec::new();
    let mut out: HashMap<&Name, usize> = HashMap::new();
    let mut next = 0;
    let mut roots: Vec<&Name> = graph.keys().copied().collect();
    roots.sort();
    for root in roots {
        if index.contains_key(root) {
            continue;
        }
        // Each frame: a node and the edges of it still to follow.
        let edges = |n: &'n Name| -> Vec<&'n Name> {
            let mut e: Vec<&Name> = graph.get(n).into_iter().flatten().copied().collect();
            e.sort();
            e
        };
        let mut frames: Vec<(&Name, Vec<&Name>)> = Vec::new();
        index.insert(root, next);
        low.insert(root, next);
        next += 1;
        stack.push(root);
        on_stack.insert(root);
        frames.push((root, edges(root)));
        while let Some((node, pending)) = frames.last_mut() {
            let node = *node;
            if let Some(to) = pending.pop() {
                if !index.contains_key(to) {
                    index.insert(to, next);
                    low.insert(to, next);
                    next += 1;
                    stack.push(to);
                    on_stack.insert(to);
                    frames.push((to, edges(to)));
                } else if on_stack.contains(to) {
                    let l = low[node].min(index[to]);
                    low.insert(node, l);
                }
                continue;
            }
            frames.pop();
            if let Some((parent, _)) = frames.last() {
                let l = low[*parent].min(low[node]);
                low.insert(*parent, l);
            }
            if low[node] == index[node] {
                let id = out.len();
                while let Some(m) = stack.pop() {
                    on_stack.remove(m);
                    out.insert(m, id);
                    if m == node {
                        break;
                    }
                }
            }
        }
    }
    out
}

impl<'a> Analysis<'a> {
    /// `div` and the operators' effects as `intrinsic` names them, however
    /// a row or a handler spells them.
    fn operator_effect_name(&self, effect: &Name) -> Option<Name> {
        ["div", "overflow", "divzero"]
            .into_iter()
            .find(|name| tauto_surface::bindings::is_library_effect(effect, name))
            .map(|name| self.intrinsic(name))
    }

    fn operator_name(&self, effect: Name) -> Name {
        self.operator_effect_name(&effect).unwrap_or(effect)
    }

    fn intrinsic(&self, name: &str) -> Name {
        if self.resolved {
            tauto_surface::bindings::library_effect_name(name)
        } else {
            Name::from(name)
        }
    }

    fn new(program: &'a Program) -> Self {
        let mut fns = HashMap::new();
        let mut datas = HashMap::new();
        let mut structs = HashSet::new();
        let mut externs = HashSet::new();
        let mut operations = HashMap::new();
        // The prelude's functions and effects, unless the program declares
        // the name; their rows are written and trusted.
        let lib: &'static Program = crate::types::prelude_for(program);
        let resolved = tauto_surface::bindings::declared_names(&lib.stmts)
            .iter()
            .any(|n| n.is_resolved());
        let intrinsic = |name: &str| {
            if resolved {
                tauto_surface::bindings::library_effect_name(name)
            } else {
                Name::from(name)
            }
        };
        let mut quants = HashMap::from([
            (intrinsic("exceeded"), Quant::AtMostOne),
            (intrinsic("budget"), Quant::One),
            (intrinsic("budget_memory"), Quant::One),
            (intrinsic("div"), Quant::Zero),
        ]);
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
                        message: msg!("rows-ambiguous-function", name = f.name.to_string()),
                        span: f.span,
                        missing: None,
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
                            message: msg!("rows-ambiguous-call"),
                            span: t.span,
                            missing: None,
                        });
                    }
                });
            }
        }
        for stmts in [&lib.stmts, &program.stmts] {
            for s in stmts {
                match s {
                    Stmt::Fn(f) => {
                        fns.insert(&f.name, f);
                        externs.remove(&f.name);
                    }
                    Stmt::Extern {
                        fns: declarations,
                        instances,
                        types,
                        structs,
                        enums,
                        ..
                    } => {
                        let replaceable = tauto_surface::surface::extern_is_replaceable(
                            declarations,
                            instances,
                            types,
                            structs,
                            enums,
                        );
                        for f in declarations {
                            fns.insert(&f.name, f);
                            // Bodyful replaceable members get ordinary row
                            // inference; only required host signatures stay
                            // as empty-row externs.
                            if !replaceable || !tauto_surface::surface::extern_fn_has_body(f) {
                                externs.insert(&f.name);
                            }
                        }
                    }
                    Stmt::Struct(d) | Stmt::Enum(d) => {
                        datas.insert(&d.name, d);
                        if matches!(s, Stmt::Struct(_)) {
                            structs.insert(&d.name);
                        } else {
                            structs.remove(&d.name);
                        }
                    }
                    Stmt::Effect(e) => {
                        operations.insert(&e.name, e);
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
        let graph: HashMap<&Name, HashSet<&Name>> = fns
            .iter()
            .map(|(&name, f)| {
                let refs = crate::lin::free_vars(&f.body)
                    .into_iter()
                    .filter(|n| !f.params.contains(n))
                    .filter_map(|n| fns.get_key_value(&n).map(|(&key, _)| key))
                    .collect();
                (name, refs)
            })
            .collect();
        // A function written `!?` has no row yet: it is an error, in the order of the functions.
        // One that calls itself or a later `!?` function would take its row from a row that is not
        // known yet: no row is found for it.
        let mut holes: Vec<(&Name, &HashSet<&Name>)> = graph
            .iter()
            .filter(|(name, _)| fns[**name].row_hole.is_some())
            .map(|(name, refs)| (*name, refs))
            .collect();
        holes.sort_by_key(|(name, _)| fns[*name].span.start);
        let mut row_hole_cycles = BTreeSet::new();
        for (name, refs) in holes {
            let f = fns[name];
            found.push(RowDiagnostic {
                message: msg!("rows-row-hole", name = f.name.to_string()),
                span: f.row_hole.unwrap_or(f.span),
                missing: None,
            });
            if refs.iter().any(|g| {
                let g = fns[*g];
                g.row_hole.is_some() && (std::ptr::eq(g, f) || g.span.start > f.span.start)
            }) {
                row_hole_cycles.insert(f.name.clone());
            }
        }
        // The groups of functions that reach one another, each found once:
        // a function is recursive when its group has another function in it,
        // or when it names itself.
        let component = components(&graph);
        let mut groups: HashMap<usize, Vec<&Name>> = HashMap::new();
        for &name in fns.keys() {
            groups.entry(component[name]).or_default().push(name);
        }
        let recursive_refs = graph
            .iter()
            .filter(|(name, refs)| groups[&component[*name]].len() > 1 || refs.contains(*name))
            .map(|(name, _)| *name)
            .collect::<HashSet<&Name>>();
        let structural = recursive_refs
            .iter()
            .copied()
            .filter(|&name| {
                // The functions that call one another with `name`: itself
                // alone, or a group of mutually recursive ones.
                let group: Vec<&FnDecl> =
                    groups[&component[name]].iter().map(|m| fns[*m]).collect();
                structural::decreases(&group)
            })
            .collect();
        Analysis {
            program,
            resolved,
            nominal_owners: None,
            nominal_owners_checked: false,
            operand_types: None,
            term_types: None,
            target: Target::Rust,
            fns,
            externs,
            constructors: values::Constructors::new(&datas, &structs),
            members: Default::default(),
            datas,
            structs,
            operations,
            expected_result: None,
            memo: HashMap::new(),
            in_progress: HashSet::new(),
            leaned: HashSet::new(),
            seeds: HashMap::new(),
            pass: Vec::new(),
            recursive_refs,
            structural,
            total: HashSet::new(),
            in_total: false,
            quants,
            calls: HashMap::new(),
            found,
            row_hole_cycles,
            written: None,
            direct_vars: Vec::new(),
            inferring: Vec::new(),
            user_externs: program
                .stmts
                .iter()
                .filter_map(|s| match s {
                    Stmt::Extern { fns, .. } => Some(
                        fns.iter()
                            .filter(|f| !tauto_surface::surface::extern_fn_has_body(f))
                            .map(|f| &f.name),
                    ),
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
            values: HashMap::new(),
            signatures: HashMap::new(),
            ambiguous_owners,
            ambiguous_calls,
            call_sources,
            constructions: HashMap::new(),
            constant_data: HashMap::new(),
            constant_values: HashMap::new(),
            lambda_values: HashMap::new(),
            term_rows: HashMap::new(),
            block_rows: HashMap::new(),
            continuations: HashMap::new(),
        }
    }

    /// Why `name` is not a value the program has: it is not a local, a
    /// function or a constructor. `None` when it is one of those.
    fn unresolved(&self, name: &Name, locals: &Locals) -> Option<Message> {
        self.unresolved_tag(name, locals)
            .map(|(kind, name)| unfollowed(&format!("{kind}:{name}")))
    }

    /// The tag of `unchecked` for a name that is not a value the program has.
    fn unresolved_tag(&self, name: &Name, locals: &Locals) -> Option<(&'static str, Name)> {
        if locals.iter().any(|(local, _)| local == name)
            || self.fns.contains_key(name)
            || self.structs.contains(name)
            || self.constructors.names_any(name)
        {
            return None;
        }
        Some((
            if KERNEL_NAMES.contains(&name.as_str()) {
                "kernel"
            } else {
                "undefined"
            },
            name.clone(),
        ))
    }

    fn with_types(mut self, types: &'a TypeReport) -> Self {
        self.operand_types = Some(Cow::Borrowed(types));
        if let Some(owners) = types.nominal_owners_for(self.program) {
            self.nominal_owners = Some(Cow::Borrowed(owners));
            self.nominal_owners_checked = true;
        }
        self
    }

    /// The effect the operator `op` at `term` performs when its result does not exist:
    /// `overflow` for a fixed-width `+`, `-` or `*` whose result does not fit,
    /// `uhost_add`, `uhost_sub` and `uhost_mul` for a `uhost`, `divzero` for a
    /// `Float` divided by zero and for `div` and `mod` of integers. Unbounded
    /// `nat` arithmetic does not perform `overflow` (Succ elimination extracts
    /// as `n - 1` on `nat`).
    fn operator_effect(
        &mut self,
        term: &SurfaceTerm,
        op: &str,
        arguments: &[SurfaceTerm],
    ) -> Option<Name> {
        // The kernel checked a `total` declaration, and its extraction
        // writes `-` only after the guard that keeps it in range.
        if self.in_total {
            return None;
        }
        if self.operand_types.is_none() {
            self.operand_types = Some(Cow::Owned(crate::types::check_program(self.program)));
        }
        let types = self.operand_types.as_ref()?;
        let width = types.widths.get(&term.id()).copied();
        // Numerals whose result fits, as `0 - 1` for `-1`: nothing to fail.
        if let Some(w) = width
            && w != crate::types::Width::Host
            && let Some(n) = literal_result(op, arguments)
            && w.fits(n)
        {
            return None;
        }
        let effect = match (op, types.widths.get(&term.id())) {
            // An integer divided by a divisor that may be zero; a nonzero
            // literal divisor cannot fail.
            ("div" | "mod", _) => {
                if matches!(arguments.get(1).map(|a| &*a.kind), Some(TermKind::Nat(n)) if n.parse::<i128>().is_ok_and(|n| n != 0))
                {
                    return None;
                }
                "divzero"
            }
            // The arithmetic of `uhost` is the host's to answer
            // (`uhost_add` of `std/builtin/os.taut`); a handler may take it.
            ("+", Some(crate::types::Width::Host)) => "uhost_add",
            ("-", Some(crate::types::Width::Host)) => "uhost_sub",
            ("*", Some(crate::types::Width::Host)) => "uhost_mul",
            ("+" | "-" | "*", Some(w)) if *w != crate::types::Width::Nat => "overflow",
            ("/", _)
                if matches!(
                    types.terms.get(&term.id()),
                    Some(crate::types::Ty::Float | crate::types::Ty::Float32)
                ) =>
            {
                "divzero"
            }
            _ => return None,
        };
        Some(self.intrinsic(effect))
    }

    fn nominal_owner(&mut self, term: &SurfaceTerm) -> Option<Name> {
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
        let mut report = RowReport {
            evidence: self.total.clone(),
            target: self.target,
            row_hole_cycles: self.row_hole_cycles.clone(),
            ..RowReport::default()
        };
        let mut names: Vec<&Name> = self
            .fns
            .keys()
            .copied()
            .filter(|n| {
                program.stmts.iter().any(|s| match s {
                    Stmt::Fn(f) => f.name == **n,
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
                        fns.iter().any(|f| f.name == **n)
                    }
                    _ => false,
                })
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
            let allowed = self
                .written_of(f)
                .map(|w| self.scope_row(&w, &self.scopes[&self.owner_of(f)]));
            // A row does not say which type arguments an effect is performed
            // with; an entry that writes them would be read as another effect.
            // A function is not an effect: that its name is in a row is what
            // is said, below, not how it writes its arguments.
            let with_arguments: Vec<_> = f
                .effects
                .iter()
                .flatten()
                .filter(|e| e.contains('(') && !e.contains('@'))
                .filter(|e| !self.names_function(e))
                .collect();
            for written in with_arguments {
                let head = written.split('(').next().unwrap_or_default().trim();
                let message = if head == "exceeded" {
                    msg!(
                        "rows-writes-type-arguments-instances",
                        name = name.to_string(),
                        written = written.to_string(),
                        head = head.to_string()
                    )
                } else {
                    msg!(
                        "rows-writes-type-arguments",
                        name = name.to_string(),
                        written = written.to_string()
                    )
                };
                self.diagnostic(message, f.span);
            }
            // An entry that names no declared effect is a misspelling or a
            // missing import, not an unused effect.
            // The rows written in the signature's types (a callback's
            // `() -> A ! {…}`) are rows too, and name only effects.
            let mut written_rows: Vec<Name> = f.effects.iter().flatten().cloned().collect();
            for t in f.param_types.iter().flatten().chain(f.result.iter()) {
                let mut t = t.clone();
                walk::term(&mut t, &mut |x| match &*x.kind {
                    TermKind::Pi {
                        effects: Some(row), ..
                    }
                    | TermKind::Row(row) => written_rows.extend(row.iter().cloned()),
                    _ => {}
                });
            }
            for written in &written_rows {
                if let Some(effect) = self.undefined_effect(written) {
                    let message = if self.names_function(written) {
                        msg!(
                            "rows-function-in-row",
                            name = name.to_string(),
                            effect = effect
                        )
                    } else {
                        msg!(
                            "rows-undefined-effect",
                            name = name.to_string(),
                            effect = effect
                        )
                    };
                    self.diagnostic(message, f.span);
                }
            }
            for effect in diagnostic_order(&inferred) {
                if let Some(what) = effect.strip_prefix('?') {
                    self.diagnostic(unfollowed_in(what, name), f.span);
                } else if let Some(allowed) = &allowed
                    && !allowed.contains(effect)
                    && !self.permits_index_label(allowed, effect)
                {
                    self.diagnostic_missing(
                        msg!(
                            "rows-may-perform",
                            name = name.to_string(),
                            effect = effect.display_in_row(),
                            row = show(allowed.iter())
                        ),
                        f.span,
                        missing_effect(f, effect),
                    );
                }
            }
            report
                .functions
                .push((name.clone(), display_row(&inferred, &self.row_variables)));
        }
        let mut top_locals = Vec::new();
        let mut top_rows = Vec::new();
        for stmt in &program.stmts {
            if let Stmt::Extern {
                fns,
                instances,
                types,
                structs,
                enums,
                ..
            } = stmt
            {
                // Replaceable bodies are ordinary definitions; only required
                // host signatures are limited to `{wait}` in a written row.
                if tauto_surface::surface::extern_is_replaceable(
                    fns, instances, types, structs, enums,
                ) {
                    continue;
                }
                for f in fns.iter().filter(|f| {
                    f.effects.as_ref().is_some_and(|row| {
                        // A call may wait on the host (a JavaScript
                        // Promise, a Rust Future); nothing else.
                        row.iter()
                            .any(|e| !tauto_surface::bindings::is_library(e, "wait"))
                    })
                }) {
                    report.errors.push(RowDiagnostic {
                        message: msg!("rows-extern-effects"),
                        span: f.span,
                        missing: None,
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
            for effect in row.iter() {
                if tauto_surface::bindings::is_library(effect, "main")
                    || tauto_surface::bindings::is_library(effect, "test")
                {
                    report.entries = true;
                }
            }
            top_rows.push((row.clone(), span));
            // The host answers `show`, the entries, `spawn`, the standard effects, and
            // `overflow` and `divzero` of the operators, by stopping the run.
            for effect in row.iter() {
                // What a task left at the top asks of the host.
                if let Some(member) = label_host_member(effect) {
                    report.host_effects.insert(member.to_string());
                    if tauto_surface::bindings::is_library(&member, "wait") {
                        report.host_waits = true;
                    }
                    continue;
                }
                if crate::host::HOST_EFFECTS
                    .iter()
                    .any(|name| tauto_surface::bindings::is_library(effect, name))
                {
                    report.host_effects.insert(effect.to_string());
                    if tauto_surface::bindings::is_library(effect, "wait") {
                        report.host_waits = true;
                    }
                }
            }
            for effect in row.iter().filter(|e| {
                label_host_member(e).is_none()
                // What the host answers in any body by stopping or waiting.
                && !crate::types::indices::split_index_label(e).is_some_and(|(_, m)| {
                    ["div", "overflow", "divzero", "wait"].contains(&m.as_str())
                })
                    && ![
                        "div", "budget", "budget_memory", "test", "main", "spawn", "overflow",
                        "divzero",
                    ]
                    .iter()
                    .any(|name| tauto_surface::bindings::is_library_effect(e, name))
                    && !crate::host::HOST_EFFECTS
                        .iter()
                        .any(|name| tauto_surface::bindings::is_library(e, name))
            }) {
                let message = match effect.strip_prefix('?') {
                    Some(what) => unfollowed(what),
                    None => msg!("rows-unhandled-top-level", effect = effect.to_string()),
                };
                let message = display_message(message, &self.row_variables);
                report.errors.push(RowDiagnostic {
                    message,
                    span,
                    missing: None,
                });
            }
        }
        // A module's top level only says which entries it has: it is
        // evaluated before any body is called, and again to call them, so it
        // asks nothing of the host but `div`.
        report.top_rows = top_rows.clone();
        if report.entries {
            for (row, span) in &top_rows {
                for effect in row.iter().filter(|e| {
                    ![
                        "div",
                        "budget",
                        "budget_memory",
                        "overflow",
                        "divzero",
                        "test",
                        "main",
                    ]
                    .iter()
                    .any(|name| tauto_surface::bindings::is_library_effect(e, name))
                        && !e.starts_with('?')
                        && !crate::types::indices::split_index_label(e)
                            .is_some_and(|(family, _)| family == "main" || family == "test")
                }) {
                    report.errors.push(RowDiagnostic {
                        message: display_message(
                            msg!("rows-entry-top-level", effect = effect.to_string()),
                            &self.row_variables,
                        ),
                        span: *span,
                        missing: None,
                    });
                }
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
            .any(|e| e.message.id.starts_with("rows-writes-type-arguments"));
        // A clean report takes the type errors (including replaceable-`extern`
        // validation from `Checker::run`), so `--rows` refuses the same blocks
        // as `--types`. A report with errors of its own keeps them, as the
        // rows found them, unless they only echo a failed expansion: an
        // unknown callee stays "cannot follow", not a type error that hides
        // what the rows could not read.
        let found = if report.errors.is_empty() || unexpanded {
            crate::types::check_program(program).errors
        } else {
            crate::types::expansion_errors(program)
        };
        if !found.is_empty() {
            report.errors = found
                .into_iter()
                .map(|e| RowDiagnostic {
                    message: msg!("rows-type-error", message = e.message.clone()),
                    span: e.span,
                    missing: None,
                })
                .collect();
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
                        message: msg!("rows-type-error", message = e.message.clone()),
                        span: e.span,
                        missing: None,
                    })
                    .collect();
            }
        }
        report.calls = self.calls;
        report.quants = self.quants;
        report.call_owners = self.call_owners;
        report.values = self
            .values
            .into_iter()
            .filter_map(|(id, v)| Some((id, v?)))
            .collect();
        report.signatures = self
            .signatures
            .into_iter()
            .filter_map(|(id, v)| Some((id, v?)))
            .collect();
        report.row_variables = self.row_variables;
        report.owner_sources = self.owner_sources;
        report.ambiguous_owners = self.ambiguous_owners;
        report.ambiguous_calls = self.ambiguous_calls;
        report.call_sources = self.call_sources;
        let top = report.top_rows.first().map(|(_, s)| *s).unwrap_or_default();
        report.host_origins = origins::host_origins(program, &report, top);
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

    fn prepare_scope(&mut self, f: &FnDecl, parent: &[(Name, Name)]) -> Vec<(Name, Name)> {
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
        free.extend(f.effects.iter().flatten().filter_map(Name::row_variable));
        for var in free {
            let declared_here = generics.iter().any(|(name, _, row)| *name == var && *row);
            let declared_outside = parent
                .iter()
                .rev()
                .find(|(name, _)| *name == var)
                .is_some_and(|(_, key)| self.row_variables.get(&key).is_some_and(|v| v.declared));
            if !declared_here && !declared_outside {
                self.diagnostic(
                    msg!("rows-undeclared-row-variable", var = var.to_string()),
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
        for (index, (name, bound, declared)) in generics.into_iter().enumerate() {
            let key = if name.is_resolved() {
                name.clone()
            } else {
                Name::Local(tauto_surface::identity::LocalRef::fresh(name.to_string()))
            };
            self.row_variables.insert(
                key.clone(),
                RowVariable {
                    source: (!name.is_resolved()).then_some((
                        std::ptr::from_ref(f) as usize,
                        f.body.id(),
                        index,
                    )),
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

    /// The effect a written row entry names when no effect of that name is
    /// declared: the resolver gives such a name a reserved identity, so only
    /// the declarations tell it from an effect.
    fn undefined_effect(&self, entry: &Name) -> Option<String> {
        // The effect of divergence is made by the binding phase and is declared
        // in no source, so no table below holds it.
        if tauto_surface::bindings::is_divergence(entry) {
            return None;
        }
        if entry.row_variable().is_some()
            || crate::types::indices::split_index_label(entry).is_some()
        {
            return None;
        }
        let head: Name = match entry {
            Name::Global(_) => entry.clone(),
            Name::Effect(use_) => use_.effect().clone().into(),
            // A program read as written (the differential's oracle) keeps the
            // names as spelled.
            Name::Spelled(text) => {
                if text.starts_with(['|', '?', '∀']) || text.contains('@') {
                    return None;
                }
                let head = text.split('(').next().unwrap_or_default().trim();
                let name = Name::from(head);
                let declared = head.is_empty()
                    || self.quants.contains_key(&name)
                    || self.operations.contains_key(&name)
                    // The library's own effect (`div`) is declared under its
                    // resolved name, while the entry is spelled.
                    || tauto_surface::bindings::library_reference(head).is_some_and(|r| {
                        let r = Name::from(r);
                        self.quants.contains_key(&r) || self.operations.contains_key(&r)
                    })
                    || crate::host::HOST_EFFECTS
                        .iter()
                        .chain(["test", "spawn", "exceeded"].iter())
                        .any(|host| *host == head);
                return (!declared).then(|| entry.to_string());
            }
            _ => return None,
        };
        let mut origin = head.as_global()?;
        while let Some(next) = origin.origin() {
            origin = next;
        }
        let head = Name::Global(origin.clone());
        let declared = self.quants.contains_key(&head)
            || self.operations.contains_key(&head)
            || self
                .operations
                .keys()
                .any(|k| k.as_global() == Some(origin))
            || crate::host::HOST_EFFECTS
                .iter()
                .chain(["test", "spawn", "exceeded"].iter())
                .any(|name| tauto_surface::bindings::is_library(&head, name));
        (!declared).then(|| entry.to_string())
    }

    /// Whether a row entry names a function: a function is called, not
    /// performed, so it is no effect however the name resolves.
    fn names_function(&self, entry: &Name) -> bool {
        self.fns.contains_key(entry)
            || match entry {
                Name::Effect(use_) => {
                    let head: Name = use_.effect().clone().into();
                    self.fns.contains_key(&head)
                }
                _ => false,
            }
    }

    fn scope_row(&self, row: &[Name], scope: &[(Name, Name)]) -> Row {
        row.iter()
            .map(|effect| {
                // An index label is read by its spelling, whatever the
                // resolver made of it.
                if crate::types::indices::split_index_label(effect).is_some() {
                    return Name::from(effect.to_string());
                }
                if let Some(name) = self.operator_effect_name(effect) {
                    return name;
                }
                effect
                    .row_variable()
                    .and_then(|name| scope.iter().rev().find(|(n, _)| *n == name))
                    .map(|(_, key)| key.in_row())
                    .unwrap_or_else(|| effect.clone())
            })
            .collect()
    }

    fn scoped_type_in(&self, ty: Option<&SurfaceTerm>, scope: &[(Name, Name)]) -> Latent {
        let types = scope
            .iter()
            .map(|(n, key)| (n.clone(), Latent::Named(key.clone(), Vec::new())))
            .collect();
        let rows = scope
            .iter()
            .map(|(n, key)| (n.clone(), Row::from([key.in_row()])))
            .collect();
        values::substitute(&latent_of_type(ty), &types, &rows)
    }

    fn scoped_type(&self, ty: &SurfaceTerm) -> Latent {
        self.scoped_type_in(Some(ty), &self.scope)
    }

    fn signature(&self, f: &FnDecl, row: Row) -> Callable {
        let owner = self.owner_of(f);
        let scope = &self.scopes[&owner];
        let host = self.user_externs.contains(&f.name)
            && self
                .fns
                .get(&f.name)
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
            row_written: self.written_of(f).is_some(),
        }
    }

    fn record_declaration(&mut self, f: &FnDecl, inferred: Row) {
        let owner = self.owner_of(f);
        let row = self
            .written_of(f)
            .map(|w| self.scope_row(&w, &self.scopes[&owner]))
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
            self.diagnostic(msg!("rows-ambiguous-call-owner"), t.span);
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
            self.diagnostic(msg!("rows-ambiguous-constructor-owner"), t.span);
        }
        if !self.ambiguous_calls.contains(&t.id()) {
            self.constructions.insert(t.id(), fact);
        }
    }

    /// The row written on `f`. A `fn` with a body and no row written is `! {}`;
    /// only `!?` (a row not written yet) and an `extern` have none.
    fn written_of(&self, f: &FnDecl) -> Option<Vec<Name>> {
        match &f.effects {
            Some(w) => Some(w.clone()),
            // The helpers extraction writes (`TautoErased…`, `extract_…`) are the compiler's
            // own text, not a program's: they keep the row their body performs.
            None if f.name.to_string().starts_with("Tauto")
                || f.name.to_string().starts_with("extract_") =>
            {
                None
            }
            None if f.row_hole.is_none() && !self.externs.contains(&f.name) => Some(Vec::new()),
            None => None,
        }
    }

    /// The row callers see: the written one, else the inferred one.
    fn fn_row(&mut self, name: &'a Name) -> Row {
        let f = self.fns[name];
        let scope = self.prepare_scope(f, &[]);
        if is_extract_unreachable(name) {
            return Row::new();
        }
        match self.written_of(f) {
            Some(written) => self.scope_row(&written, &scope),
            None if self.externs.contains(name) => {
                self.record_declaration(f, Row::new());
                Row::new()
            }
            None => self.inferred_row(name),
        }
    }

    /// What the body performs, whatever the written row says.
    fn inferred_row(&mut self, name: &'a Name) -> Row {
        let f = self.fns[name];
        let scope = self.prepare_scope(f, &[]);
        if let Some(row) = self.memo.get(name) {
            return row.clone();
        }
        // What a `λ` is worth depends on the functions being inferred.
        self.lambda_values.clear();
        if let Some((_, row, leaned)) = self.pass.iter().find(|(n, _, _)| *n == name) {
            let (row, leaned) = (row.clone(), leaned.clone());
            self.leaned.extend(leaned);
            return row;
        }
        if self.in_progress.contains(name) {
            // Its row is not known yet: the last pass's, else only `div`.
            self.leaned.insert(name);
            let mut row = self.seeds.get(name).cloned().unwrap_or_default();
            if !self.total.contains(name)
                && !self.structural.contains(name)
                && !is_extract_unreachable(name)
            {
                row.insert(self.intrinsic("div"));
            }
            return row;
        }
        // A body that reads a function still being followed is in a
        // recursive group, whose rows are found together: each pass reads the
        // rows the last one found where it reaches a member being followed,
        // until a pass finds them again. Only then are they kept in `memo`; a
        // row found from a guess would miss what the guessed member performs.
        let outer_leaned = std::mem::take(&mut self.leaned);
        let start = self.pass.len();
        loop {
            let row = self.follow_body(name, f, scope.clone());
            let mut leaned = std::mem::take(&mut self.leaned);
            let reentered = leaned.remove(name);
            if !leaned.is_empty() {
                // A member of a group whose head is further out.
                self.pass.push((name, row.clone(), leaned.clone()));
                self.leaned = outer_leaned;
                self.leaned.extend(leaned);
                return row;
            }
            let members: Vec<_> = self.pass.drain(start..).collect();
            let settled = (!reentered && members.is_empty())
                || (self.seeds.get(name) == Some(&row)
                    && members.iter().all(|(n, r, _)| self.seeds.get(n) == Some(r)));
            if settled {
                for (n, r, _) in members {
                    self.seeds.remove(n);
                    self.memo.insert(n, r);
                }
                self.seeds.remove(name);
                self.memo.insert(name, row.clone());
                self.leaned = outer_leaned;
                return row;
            }
            for (n, r, _) in members {
                self.seeds.insert(n, r);
            }
            self.seeds.insert(name, row);
        }
    }

    /// Follows the body of `name` once.
    fn follow_body(&mut self, name: &'a Name, f: &'a FnDecl, scope: Vec<(Name, Name)>) -> Row {
        self.lambda_values.clear();
        self.in_progress.insert(name);
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
        let outer_total = std::mem::replace(&mut self.in_total, self.total.contains(name));
        let outer_scope = std::mem::replace(&mut self.scope, scope);
        let outer_owner = self.owner.replace(self.owner_of(f));
        let result = f.result.as_ref().map(|ty| self.scoped_type(ty));
        let outer_result = std::mem::replace(&mut self.expected_result, result.clone());
        let row = self.term_row_as(&f.body, &mut locals, result.as_ref());
        // A row read from a type spells the operators' effects as written.
        let mut row: Row = row.into_iter().map(|e| self.operator_name(e)).collect();
        if let Some(expected) = result {
            self.check_term(&f.body, &expected, &locals);
        }
        self.expected_result = outer_result;
        self.direct_vars = outer_direct;
        self.in_total = outer_total;
        self.scope = outer_scope;
        self.owner = outer_owner;
        self.in_progress.remove(name);
        self.lambda_values.clear();
        if self.total.contains(name) {
            // The kernel checked the declaration total: a `div` its body
            // reaches comes only from the erased calling convention, whose
            // function values are its own total code.
            row.remove(&self.intrinsic("div"));
        } else if !self.structural.contains(name)
            && !is_extract_unreachable(name)
            && self.recursive_refs.contains(name)
        {
            row.insert(self.intrinsic("div"));
        }
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
            TermKind::App { .. } if let Some(members) = t.product_value_members() => {
                for m in members {
                    row.extend(self.term_row(m, locals));
                }
            }
            TermKind::Perform { effect, args } => {
                let before = self.found.len();
                if let Some(signature) = self.operation_signature(effect) {
                    self.check_arguments(&signature, args, locals, t.span, None);
                }
                // A task's body that performs what only a handler around
                // the `spawn` answers: say where its handler goes.
                if tauto_surface::bindings::is_library(&effect, "spawn") {
                    for d in &mut self.found[before..] {
                        if d.message.id == "rows-value-performs" {
                            d.message.id = "rows-value-performs-spawn".into();
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
                    ("spawn", [f]) | ("test", [_, f]) | ("main", [f]) => Some(f),
                    _ => None,
                };
                // An entry's body runs when a command calls it, under the
                // host: what it asks of the host is what the run needs, and is
                // not performed where the entry is.
                let entry = tauto_surface::bindings::is_library(effect, "test")
                    || tauto_surface::bindings::is_library(effect, "main");
                if let Some(f) = body
                    && let Latent::Known(c) = self.latent_of(f, locals)
                {
                    for e in c.row.iter() {
                        // The indices of a task's own tasks fold into its index.
                        // An entry's index includes the permissions its tasks need.
                        if let Some(member) = label_host_member(e) {
                            row.insert(crate::types::indices::index_label(effect, &member));
                            continue;
                        }
                        if entry {
                            if crate::host::HOST_EFFECTS
                                .iter()
                                .any(|name| tauto_surface::bindings::is_library(e, name))
                            {
                                row.insert(crate::types::indices::index_label(effect, e));
                            }
                            continue;
                        }
                        // A task's waits hold up that task only: the host
                        // answers them where it runs the task.
                        if tauto_surface::bindings::is_library(&e, "wait")
                            && tauto_surface::bindings::is_library(&effect, "spawn")
                        {
                            continue;
                        }
                        if crate::host::HOST_EFFECTS
                            .iter()
                            .any(|name| tauto_surface::bindings::is_library(e, name))
                        {
                            // The body's row is the label's index: no handler
                            // around the `spawn` answers it, since the body
                            // runs apart from them.
                            row.insert(crate::types::indices::index_label(effect, e));
                        } else if self.set_bound(e).is_some() {
                            // `<h: Host>`: some of the host's effects, which
                            // the function's row names, so that a call
                            // shows them.
                            row.insert(e.clone());
                        }
                    }
                }
                let own = Row::from([effect.clone()]);
                self.record_call(t, own.clone());
                row.extend(own);
            }
            TermKind::Record { fields, .. } => {
                self.value_of(t, locals, expected);
                // Each field is followed against the type the context gives
                // it, as a constructor's arguments are: a call there whose row
                // argument the context writes out is checked against it.
                let given = expected.and_then(|e| self.fields(e)).unwrap_or_default();
                for (name, v) in fields {
                    let field = given
                        .iter()
                        .find(|(n, _)| n == name)
                        .map(|(_, l)| l.clone());
                    row.extend(self.term_row_as(v, locals, field.as_ref()));
                }
            }
            TermKind::Borrow { term, .. } => {
                row.extend(self.term_row_as(term, locals, expected.map(Latent::unborrowed)));
            }
            TermKind::App {
                function,
                arguments,
            } => {
                // `f(<A: T>, x)`: the named type arguments are no argument.
                let arguments = crate::types::split_implicits(arguments).1;
                let mut params = Vec::new();
                // A construction checks its arguments against the type the
                // context gives it. Checked again without that type, its
                // parameters would be read off the first argument alone.
                if let TermKind::Var(name) = &*function.kind
                    && !locals.iter().any(|(n, _)| n == name)
                    && !self.fns.contains_key(&name)
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
                if let TermKind::Var(name) = &*function.kind
                    && !locals.iter().any(|(n, _)| n == name)
                    && !self.fns.contains_key(name)
                    && matches!(name.as_str(), "+" | "-" | "*" | "/" | "div" | "mod")
                    && let Some(effect) = self.operator_effect(t, name.as_str(), arguments)
                {
                    row.insert(effect);
                }
                match &*function.kind {
                    TermKind::Field { base, name }
                        if matches!(&*base.kind, TermKind::Var(n)
                            if matches!(locals.iter().rev().find(|(m, _)| m == n), Some((_, Latent::Info)))) =>
                    {
                        if name == "unbounded" {
                            row.insert(self.intrinsic("div"));
                        }
                    }
                    TermKind::Var(n)
                        if !locals.iter().any(|(m, _)| m == n)
                            && !self.fns.contains_key(&n)
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
                            row.insert(match &*function.kind {
                                TermKind::Var(n) => match self.unresolved_tag(n, locals) {
                                    Some((kind, name)) => unchecked(kind, &name),
                                    None => unchecked("call", n),
                                },
                                _ => match dotted(function) {
                                    Some(n) => unchecked("call", &n),
                                    None => unchecked("expression", ""),
                                },
                            });
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
                // leaves `div` in the row.
                if *limit == BudgetLimit::Steps {
                    inner.remove(&self.intrinsic("div"));
                }
                row.extend(inner);
                row.insert(self.intrinsic("exceeded"));
                // The host counts: the same body may stop at another place
                // on another backend, so running a budget is an effect, its
                // operation's.
                row.insert(self.intrinsic(limit.operation()));
            }
            TermKind::Handle { body, handlers } => {
                let raw = self.term_row(body, locals);
                let handled: BTreeSet<Name> = handlers
                    .iter()
                    .filter_map(|h| match h {
                        Handler::Operation {
                            effect,
                            patterns,
                            guard: None,
                            ..
                        } if patterns.iter().all(irrefutable) => {
                            Some(self.operator_name(effect.clone()))
                        }
                        _ => None,
                    })
                    .collect();
                // An index label is another label than its members: only an
                // arm of its family removes it. An arm of one instance
                // (`spawn<i64>(f)`) answers only the performs of that
                // instance, while the label holds the merged index of all of
                // them: it leaves the label, and the host is still asked for
                // what it holds (rule 3).
                row.extend(
                    raw.iter()
                        .filter(|e| !handles_label(&handled, e) && !handled.contains(*e))
                        .cloned(),
                );
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
                // An arm of `place` or `rc_place` only says where the value goes: its
                // body is `k(e)`, and `e` performs nothing.
                for (h, arm_own) in handlers.iter().zip(&own) {
                    if let Handler::Operation {
                        effect,
                        cont,
                        body: arm_body,
                        ..
                    } = h
                        && is_placement(effect)
                    {
                        let shaped = matches!(&*arm_body.kind, TermKind::App { function, arguments }
                            if arguments.len() == 1
                                && matches!(&*function.kind, TermKind::Var(n) if Some(n) == cont.as_ref()));
                        if !shaped || !arm_own.is_empty() {
                            self.found.push(RowDiagnostic {
                                message: msg!(
                                    "rows-placement-arm-answers-only",
                                    op = effect
                                        .as_str()
                                        .split('@')
                                        .next()
                                        .unwrap_or("")
                                        .rsplit("::")
                                        .next()
                                        .unwrap_or("")
                                        .to_string()
                                ),
                                span: arm_body.span,
                                missing: None,
                            });
                        }
                    }
                }
                for (i, h) in handlers.iter().enumerate() {
                    if let Handler::Operation { effect, .. } = h {
                        // `k` may be called after its arm has returned, so
                        // it performs what runs after the operation: the rest
                        // of the body under the reinstalled handler, the arms
                        // of the operations that rest performs, and the
                        // return arm.
                        let resumed = self.resumed_row(
                            body,
                            &effect.clone(),
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
                        if self.quants.get(&effect.clone()) == Some(&Quant::Direct) {
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
        effect: &Name,
        patterns: &[Pattern],
        cont: &Option<Name>,
        guard: &Option<SurfaceTerm>,
        body: &SurfaceTerm,
        resumed: Row,
        value: &Latent,
        locals: &mut Locals,
    ) -> Row {
        let mark = locals.len();
        let operation = self.operation_signature(effect);
        for (i, p) in patterns.iter().enumerate() {
            match p {
                Pattern::Bind { name: n, .. }
                    if tauto_surface::bindings::is_library(&effect, "exceeded") =>
                {
                    locals.push((n.clone(), Latent::Info))
                }
                // A spawned body may diverge, but performs no operation on
                // its caller's handler stack: what it asks of the host is in
                // the row of its `spawn`.
                Pattern::Bind { name: n, .. }
                    if tauto_surface::bindings::is_library(&effect, "spawn") =>
                {
                    locals.push((
                        n.clone(),
                        Latent::Known(Callable::simple(Row::from([self.intrinsic("div")]))),
                    ))
                }
                // An argument is what the operation's parameter type says
                // it is: a function it takes performs the row of that type.
                Pattern::Bind { name: n, .. } => locals.push((
                    n.clone(),
                    operation
                        .as_ref()
                        .and_then(|o| o.params.get(i).cloned())
                        .unwrap_or(Latent::Unknown),
                )),
                p => bind_pattern(p, locals),
            }
        }
        let mut continuation = Callable::simple(resumed);
        if let Some(operation) = operation {
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
        op: &Name,
        handlers: &[Handler],
        handled: &BTreeSet<Name>,
        own: &[Row],
        returned: &Row,
    ) -> Row {
        let mut rest = self.after(body, op).unwrap_or_default();
        let mut reached = BTreeSet::new();
        loop {
            let next: Vec<Name> = handlers
                .iter()
                .filter_map(|h| match h {
                    Handler::Operation { effect, .. } => Some(effect.clone()),
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
        let mut row: Row = rest
            .into_iter()
            .filter(|e| !handles_label(handled, e) && !handled.contains(e))
            .collect();
        for (h, arm) in handlers.iter().zip(own) {
            if let Handler::Operation { effect, .. } = h
                && reached.contains(&effect.clone())
            {
                row.extend(arm.iter().cloned());
            }
        }
        row.extend(returned.iter().cloned());
        row
    }

    /// What `t` performs after it performs `op`, until `t` ends, read from
    /// the rows already found; `None` when `t` cannot perform `op`.
    fn after(&self, t: &SurfaceTerm, op: &Name) -> Option<Row> {
        let whole = |t: &SurfaceTerm| self.term_rows.get(&t.id()).cloned().unwrap_or_default();
        match &*t.kind {
            TermKind::Perform { effect, .. } if *effect == *op => Some(Row::new()),
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
    /// native callback effects must be direct or `div`. JavaScript callbacks
    /// reject operations that may resume many times and open rows.
    fn extern_closures(&mut self, arguments: &[SurfaceTerm], locals: &Locals, span: Span) {
        for a in arguments {
            let Latent::Known(row) = self.latent_of(a, locals) else {
                continue;
            };
            if let Some(effect) = row.row.iter().find(|e| {
                if self.target.promise_callbacks() {
                    self.quants.get(*e) == Some(&Quant::Many) || e.row_variable().is_some()
                } else {
                    !self.is_direct(e)
                        && !e.row_variable().is_some()
                        && !tauto_surface::bindings::is_divergence(e)
                        && !tauto_surface::bindings::is_library(e, "budget")
                        && !tauto_surface::bindings::is_library(e, "budget_memory")
                }
            }) {
                let message = if self.target.promise_callbacks() {
                    msg!("rows-js-callback-effect", effect = effect.to_string())
                } else {
                    msg!("rows-extern-closure-effect", effect = effect.to_string())
                };
                let message = display_message(message, &self.row_variables);
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
    pub(super) fn set_bound(&self, effect: &Name) -> Option<Vec<Name>> {
        let var = effect.row_variable()?;
        let bound = self.row_variables.get(&var)?.bound.as_ref()?;
        bound.effect_set().map(|(_, set)| set.to_vec())
    }

    /// Whether a row that permits `allowed` permits `effect`: it names the
    /// effect, or the effect is a row variable bounded by a set it names.
    pub(super) fn permits(&self, allowed: &Row, effect: &Name) -> bool {
        allowed.contains(effect)
            || self.permits_index_label(allowed, effect)
            || self
                .set_bound(effect)
                .is_some_and(|set| set.iter().all(|e| allowed.contains(e)))
    }

    /// Whether a row naming a family's own label for every instance
    /// (`spawn`, as the library's `Host` has it) and the effect an index
    /// label holds (`spawn@^div` holds `div`) permits that label: a body
    /// that calls a function which spawns, inside a body the host runs.
    /// The label is the host's to answer, and what it holds is a
    /// host effect the row names.
    fn permits_index_label(&self, allowed: &Row, effect: &Name) -> bool {
        let Some((family, member)) = crate::types::indices::split_index_label(effect) else {
            return false;
        };
        let short = member.split('@').next().unwrap_or(&member);
        let short = short.rsplit("::").next().unwrap_or(short);
        if !allowed
            .iter()
            .any(|a| !a.to_string().contains('@') && crate::types::indices::family_of(a) == family)
        {
            return false;
        }
        // `spawn@^e` for a row variable `<!e: Host>`: it holds some of the
        // host's effects, which the row names. The label names the variable as
        // written, so the variables of that name are told apart by where they are
        // declared. If the function being followed declares one, that one is meant,
        // and its bound must be a set the row covers. Otherwise it comes from a
        // callee's row, and some variable of that name must be bounded by such a set.
        let covered = |v: &Name| {
            self.set_bound(v)
                .is_some_and(|set| set.iter().all(|e| allowed.contains(e)))
        };
        let named: Vec<&Name> = self
            .row_variables
            .keys()
            .filter(|v| v.to_string().split('#').next() == Some(member.as_str()))
            .collect();
        let own: Vec<&Name> = named
            .iter()
            .copied()
            .filter(|v| Some(&self.row_variables[*v].owner) == self.owner.as_ref())
            .collect();
        if !own.is_empty() {
            return own.into_iter().all(covered);
        }
        if named.iter().copied().any(covered) {
            return true;
        }
        allowed
            .iter()
            .any(|a| tauto_surface::bindings::is_library_effect(a, short))
    }

    fn is_direct(&self, effect: &Name) -> bool {
        if let Some(var) = effect.row_variable() {
            if let Some(var) = self.row_variables.get(&var) {
                return var.bound.as_deref() == Some("direct");
            }
            return self.direct_vars.iter().any(|v| v == &var);
        }
        effect.starts_with('?') || self.quants.get(effect) == Some(&Quant::Direct)
    }

    /// The arm of a direct operation performs direct operations only.
    fn direct_arm(&mut self, op: &Name, arm: &Row, span: Span) {
        for effect in arm {
            if self.is_direct(effect) {
                continue;
            }
            let message = display_message(
                msg!(
                    "rows-arm-not-direct",
                    op = op.to_string(),
                    effect = effect.trim_start_matches('|').to_string()
                ),
                &self.row_variables,
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
                row.insert(self.intrinsic("div"));
            }
            // `lower_fors` / `lower_loops` expand them where the program is read.
            Stmt::For { .. } | Stmt::Loop { .. } | Stmt::Break(_) | Stmt::Continue => {}
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
        let written = f
            .effects
            .clone()
            .or_else(|| f.row_hole.is_none().then(Vec::new))
            .map(|w| self.scope_row(&w, &self.scope));
        let mut inferred = Row::new();
        loop {
            // A self reference carries divergence through aliases and fields.
            // Local source declarations cannot inherit a top-level extraction
            // certificate just because they reuse its name.
            let mut recursive = written.clone().unwrap_or_else(|| inferred.clone());
            recursive.insert(self.intrinsic("div"));
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
        for effect in diagnostic_order(&inferred) {
            if let Some(what) = effect.strip_prefix('?') {
                self.diagnostic(unfollowed_in(what, &f.name), f.span);
            } else if let Some(allowed) = &written
                && !allowed.contains(effect)
                && !self.permits_index_label(allowed, effect)
            {
                self.diagnostic_missing(
                    msg!(
                        "rows-may-perform",
                        name = f.name.to_string(),
                        effect = effect.display_in_row(),
                        row = show(allowed.iter())
                    ),
                    f.span,
                    missing_effect(f, effect),
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

/// The value of an operator applied to numerals only: `-a`, `a + b`,
/// `a - b`, `a * b`.
fn literal_result(op: &str, arguments: &[SurfaceTerm]) -> Option<i128> {
    let values: Option<Vec<i128>> = arguments
        .iter()
        .map(|a| match &*a.kind {
            TermKind::Nat(n) => n.parse::<i128>().ok(),
            _ => None,
        })
        .collect();
    match (op, values?.as_slice()) {
        ("-", [a]) => Some(-a),
        ("-", [a, b]) => Some(a - b),
        ("+", [a, b]) => a.checked_add(*b),
        ("*", [a, b]) => a.checked_mul(*b),
        _ => None,
    }
}

fn latent_of_type(ty: Option<&SurfaceTerm>) -> Latent {
    ty.map(value_type).unwrap_or(Latent::Unknown)
}

use values::{substitute, value_type};

fn irrefutable(p: &Pattern) -> bool {
    matches!(p, Pattern::Wild | Pattern::Bind { .. })
}

fn bind_pattern(p: &Pattern, locals: &mut Locals) {
    match p {
        Pattern::Ctor { .. } if let Some(items) = p.product_members() => {
            items.iter().for_each(|a| bind_pattern(a, locals))
        }
        Pattern::Bind { name: n, .. } => locals.push((n.clone(), Latent::Unknown)),
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| bind_pattern(a, locals)),
        Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| bind_pattern(a, locals)),
        _ => {}
    }
}

fn dotted(t: &SurfaceTerm) -> Option<String> {
    match &*t.kind {
        TermKind::Var(n) => Some(n.to_string()),
        TermKind::Field { base, name } => Some(format!("{}.{name}", dotted(base)?)),
        _ => None,
    }
}

fn generated(span: Span) -> bool {
    (crate::surface::GENERATED_BASE..crate::surface::PRELUDE_BASE).contains(&span.start)
}

// Presentation order must not depend on when declaration IDs were allocated.
fn diagnostic_order(row: &Row) -> Vec<&Name> {
    let mut effects: Vec<_> = row.iter().collect();
    effects.sort_by_key(|effect| effect.display_in_row());
    effects
}

/// The effect `f` performs and its written row leaves out, to write into the row: a row
/// variable of a callee is not one, nor is a function whose result type is not written.
fn missing_effect(f: &FnDecl, effect: &Name) -> Option<MissingEffect> {
    if effect.as_local().is_some() || effect.starts_with('?') {
        return None;
    }
    let result = f.result.as_ref()?;
    Some(MissingEffect {
        effect: effect.display_in_row(),
        after: result.span.end,
    })
}

fn show<'s>(items: impl Iterator<Item = &'s Name>) -> String {
    let mut names = items.map(Name::display_in_row).collect::<Vec<_>>();
    names.sort();
    names.join(", ")
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
    )
}

#[cfg(test)]
#[path = "rows/tests.rs"]
mod value_tests;
