//! The kernel's named side: declarations over the shared [`SurfaceTerm`],
//! elaborated (matches, implicit arguments, classes, holes) into the terms
//! the core kernel (`core.rs`) checks. Sorts are `Prop`, `Type` (= `Type0`),
//! `Type1`, …, cumulative. A theorem's proof term is checked against its
//! statement; the axioms it relies on are tracked. The terms stay named
//! here; typing, reduction and convertibility (beta, delta, literal
//! arithmetic, iota, eta, proof irrelevance) are asked of the core, which
//! also checks every declaration before it is added. A theorem whose proof
//! was checked before is taken from the proof cache (`check/cache.rs`, keyed
//! by the checker's source, the proof text and the interfaces of what it
//! names): its statement is checked, its proof is not checked again.
//! `TAUTO_CACHE=off` checks everything.

use crate::surface::Name;
use std::collections::{BTreeSet, HashMap, HashSet};

use tauto_parol::Span;

use level::Level;

use crate::surface::{
    DataDecl, FnDecl, InductiveDecl, Program, Stmt, SurfaceTerm, TermKind, TheoremDecl,
};

type T = SurfaceTerm;
type SubstMemo = HashMap<(usize, crate::surface::TermId, u32, u32), (T, Option<T>)>;

mod cache;
mod classes;
mod core;
#[cfg(feature = "selfhost")]
pub use core::selfhost;
use core::{Ask, Failed, Failure, Met, Typed};
mod deq;
mod derivation;
pub use derivation::{Derivation, InferenceRule, ProofInspector, ProofReduction};
#[cfg(test)]
mod differential;
mod effects;
mod implicit;
mod incremental;
mod inductive;
mod level;
mod macro_checker;
mod matching;
pub use macro_checker::KernelChecker;
mod mutable;
mod nested;
mod noconf;
mod opaque;
mod order;
mod resumes;
mod roles;
pub use roles::checked_entries;
mod steps;
mod sugar;
mod universe;
mod wf;

pub use incremental::{Checker, Declared, chain_state, fingerprint};
pub use roles::{
    ApplicationSite, BoundaryType, Checked, CtorSite, Family, FieldSite, Role, Signature,
};
pub use sugar::{Records, guard_chain, record_sugar};

const PRELUDE: &str = include_str!("prelude.taut");
/// The decisions and division of numbers the core computes on numerals
/// (`Core::numeric`); read after the shared data, since it uses `Pair`.
const PRELUDE_NAT: &str = include_str!("prelude_nat.taut");
/// What a generated decidable equality uses (`check/deq.rs`), read after
/// `prelude_nat.taut`.
const PRELUDE_DEQ: &str = include_str!("prelude_deq.taut");

/// The data of the library prelude (`std/prelude/Std.taut`) that the
/// proofs see too, as families.
const SHARED_WITH_PRELUDE: &[&str] = &["Option", "List", "Pair", "Ordering", "Result"];

/// What proofs may use without declaring it: `prelude.taut`; the `enum`s
/// and `struct`s `Option`, `List`, `Pair`, `Ordering` and `Result` of the library prelude,
/// read as inductive families (a positional field is `_0`, `_1`, …, and a
/// struct's one constructor is [`struct_constructor`]); `prelude_nat.taut`;
/// `prelude_deq.taut`;
/// and the whole of
/// `std/prelude/Ord.taut`, the class `Ord` with the instances whose laws
/// the kernel proves. Each is declared once, and programs read the same
/// declarations. Every declaration here is checked by both kernels and
/// none is an axiom but [`QUOT_SOUND`] ([`declare_prelude`]).
/// An error of reading the prelude file `path` read at `base`, named by its
/// file, line and column rather than by the byte of its span.
fn prelude_error(base: u32, path: &'static str, text: &'static str) -> impl Fn(String) -> String {
    move |e| {
        format!(
            "prelude: {}",
            crate::nibstd::locate_error(e, base, &[(path, text)])
        )
    }
}

/// The order in which [`Kernel::declare`] checks the statements of one
/// program: the positions in `stmts`, each declaration moved just before the
/// first statement that uses it when it is written after it. A checker that
/// takes the statements one at a time ([`Checker`]) takes them in this order,
/// so that it decides what checking them together decides.
pub fn checking_order(stmts: &[Stmt]) -> Vec<usize> {
    let mut lowered = stmts.to_vec();
    for s in &mut lowered {
        tauto_surface::surface::qualify::lower_tuples(s, "Pair");
    }
    order::dependency_positions(&lowered)
}

pub fn kernel_prelude() -> Result<Program, String> {
    let mut program = crate::surface::parse_program_unresolved_at(PRELUDE, 0).map_err(
        prelude_error(0, "crates/tauto-kernel/src/prelude.taut", PRELUDE),
    )?;
    let library = crate::surface::parse_program_as_written(crate::nibstd::STD)
        .map_err(prelude_error(0, "std/prelude/Std.taut", crate::nibstd::STD))?;
    for stmt in &library.stmts {
        match stmt {
            Stmt::Enum(d) if SHARED_WITH_PRELUDE.contains(&d.name.as_str()) => {
                program
                    .stmts
                    .push(Stmt::Inductive(family_of_data(d, false)));
            }
            Stmt::Struct(d) if SHARED_WITH_PRELUDE.contains(&d.name.as_str()) => {
                program.stmts.push(Stmt::Inductive(family_of_data(d, true)));
            }
            _ => {}
        }
    }
    let nat = crate::surface::parse_program_unresolved_at(
        PRELUDE_NAT,
        crate::surface::PRELUDE_BASE + (1 << 29),
    )
    .map_err(prelude_error(
        crate::surface::PRELUDE_BASE + (1 << 29),
        "crates/tauto-kernel/src/prelude_nat.taut",
        PRELUDE_NAT,
    ))?;
    program.stmts.extend(nat.stmts);
    let deq = crate::surface::parse_program_unresolved_at(
        PRELUDE_DEQ,
        crate::surface::PRELUDE_BASE + (1 << 28),
    )
    .map_err(prelude_error(
        crate::surface::PRELUDE_BASE + (1 << 28),
        "crates/tauto-kernel/src/prelude_deq.taut",
        PRELUDE_DEQ,
    ))?;
    program.stmts.extend(deq.stmts);
    let ord = crate::surface::parse_program_unresolved_at(
        crate::nibstd::ORD,
        crate::surface::PRELUDE_BASE,
    )
    .map_err(prelude_error(
        crate::surface::PRELUDE_BASE,
        "std/prelude/Ord.taut",
        crate::nibstd::ORD,
    ))?;
    program.stmts.extend(ord.stmts);
    // Read as a program's files are: `#(a, b)`, `A × B` and the names of the prelude.
    tauto_surface::surface::qualify::lower_prelude_sugar(&mut program.stmts);
    // The modules of the files are one set: a file uses the names of the others.
    let (stmts, errors) = crate::surface::modules::resolve(std::mem::take(&mut program.stmts));
    program.stmts = stmts;
    program.errors.extend(errors);
    Ok(program)
}

/// The constructor a `struct` of the library prelude has as a family: a
/// program writes it as `S { f: e, … }` and matches it as `S { f: p, … }`.
pub use tauto_surface::inductive_data::struct_constructor;

/// The prelude's one axiom: related values have the same class in the
/// quotient. Every declaration that uses it lists it among its axioms.
pub const QUOT_SOUND: &str = "Quot::sound";

/// Makes `kernel`, a new one, the kernel with its prelude declared: the
/// names the prelude declared, or what went wrong. Every declaration must
/// check, and none may be an axiom other than [`QUOT_SOUND`] or incomplete,
/// so that nothing else the proofs may use is trusted. The prelude is checked once in a thread, and each
/// kernel starts from a copy of that one.
pub fn declare_prelude(kernel: &mut Kernel) -> Result<Vec<Name>, String> {
    type Declared = Result<(Kernel, Vec<Name>), String>;
    thread_local! {
        static DECLARED: std::cell::OnceCell<Declared> = const { std::cell::OnceCell::new() };
    }
    let (declared, names) = DECLARED.with(|cell| cell.get_or_init(declare_prelude_once).clone())?;
    *kernel = declared;
    Ok(names)
}

fn declare_prelude_once() -> Result<(Kernel, Vec<Name>), String> {
    let mut kernel = Kernel::new();
    let prelude = kernel_prelude()?;
    let mut names = Vec::new();
    for entry in kernel.declare(&prelude, true) {
        match entry.verdict {
            Verdict::Checked { axioms } if axioms.is_empty() => names.push(entry.name),
            Verdict::Checked { axioms }
                if tauto_surface::bindings::is_library(&entry.name, QUOT_SOUND)
                    && axioms.len() == 1
                    && tauto_surface::bindings::is_library(&axioms[0], QUOT_SOUND) =>
            {
                names.push(entry.name)
            }
            Verdict::Failed(d) => return Err(format!("prelude: {}: {d}", entry.name)),
            other => return Err(format!("prelude: {}: {other:?}", entry.name)),
        }
    }
    Ok((kernel, names))
}

/// A program's `enum` or `struct` (`is_struct`) read as the inductive family
/// of the same shape: the proofs see its constructors, and the functions over
/// it are checked by the kernel. It makes no decidable equality, which is
/// made only where it is written.
pub fn program_family(d: &DataDecl, is_struct: bool) -> InductiveDecl {
    tauto_surface::inductive_data::family(d, is_struct)
}

fn family_of_data(d: &DataDecl, is_struct: bool) -> InductiveDecl {
    // The data the prelude shares have a decidable equality.
    InductiveDecl {
        vis: Default::default(),
        generates: crate::surface::Generates {
            items: Kernel::decidable_list(&d.name),
            written: true,
            at: d.span,
            breaks: true,
        },
        ..tauto_surface::inductive_data::family(d, is_struct)
    }
}

pub use crate::surface::Fix;
use tauto_message::{Message, Value, msg};
pub use tauto_surface::diagnostic::{Diagnostic, Entry, HoleGoal, Mismatch, Verdict};

fn err<X>(message: impl Into<Message>, span: Span) -> Result<X, Diagnostic> {
    Err(Diagnostic::new(message, Some(span)))
}

/// Whether `m` is one of the messages `ids`, or holds one: what a search of
/// its text for theirs would find, in any language.
fn says(m: &Message, ids: &[&str]) -> bool {
    ids.contains(&m.id.as_ref())
        || m.args
            .iter()
            .any(|(_, v)| matches!(v, Value::Message(inner) if says(inner, ids)))
}

const NOT_DEFINED: &[&str] = &[
    "kernel-not-defined",
    "kernel-not-defined-hint",
    "kernel-not-defined-yet",
    "kernel-not-defined-struct",
    "kernel-float-not-defined",
    "kernel-integer-division",
    "kernel-core-not-defined",
    "kernel-implicit-not-defined",
];

const TYPE_MISMATCH: &[&str] = &["kernel-mismatch", "kernel-core-type-mismatch"];

const USES_FAILED: &[&str] = &["kernel-uses-failed", "kernel-uses-failed-then"];

/// The messages that start by saying a term is not one of the kernel's.
const NOT_KERNEL_TERM: &[&str] = &[
    "kernel-not-kernel-term",
    "kernel-not-kernel-term-match",
    "kernel-not-kernel-term-text",
    "kernel-not-kernel-term-kind",
    "kernel-if-no-else",
];

#[derive(Clone)]
struct Global {
    ty: T,
    /// A definition unfolds; theorems and axioms do not.
    value: Option<T>,
    axioms: BTreeSet<Name>,
    /// How many leading parameters a call may leave out.
    implicit: usize,
    /// How many parameters the declaration lists, when it is not the depth
    /// of its type (a function returning a function).
    params: Option<usize>,
    /// The declaration did not check; its statement is kept for the
    /// messages of later proofs, which fail if they use it.
    failed: bool,
    /// The declaration has a hole (or uses one that has): its statement is
    /// usable, but whatever uses it is incomplete too.
    incomplete: bool,
}

type Ctx = Vec<(Name, T)>;

#[derive(Clone)]
struct FileLimit {
    file: String,
    limit: std::time::Duration,
    deadline: crate::clock::Instant,
}

#[derive(Clone)]
pub struct Kernel {
    resolver: tauto_surface::resolve::Resolver,
    globals: HashMap<Name, Global>,
    /// Functions skipped as not terms of the kernel: a function that uses one
    /// is skipped too, not failed.
    skipped: HashSet<Name>,
    /// The names declared by `fn` without effects: one without parameters
    /// of its own is called with `()`, never named bare.
    fns: HashSet<Name>,
    inds: HashMap<Name, inductive::Ind>,
    /// Constructor name → (family, index).
    ctors: HashMap<Name, (Name, usize)>,
    /// Eliminator name → family.
    recs: HashMap<Name, Name>,
    fresh: usize,
    /// Binders of the arrow types a match in a type is written under
    /// ([`Self::elaborate_type`]). A match does not generalize over one its
    /// arms do not use.
    arrow_binders: Vec<Name>,
    /// Unknowns of the call being elaborated (`?n`), with their solutions.
    metas: HashMap<Name, Option<T>>,
    /// The declaration being checked, for the message on a bad recursion.
    current: Option<Name>,
    /// Inside a field taken out of a value: the value is matched as the `Pair` a product
    /// is unfolded to, which is no `#(…)` written where a `Pair` is.
    projecting: usize,
    /// Names the program declares that the kernel may not have yet: why a
    /// use of one is not defined (declared further on, or a `struct`).
    ahead: HashMap<Name, Ahead>,
    /// The functions being defined by a `match`, with their types: a
    /// `match` on a call of one of them can be typed before the call becomes
    /// an induction hypothesis.
    defining: Vec<(Name, T)>,
    /// How many leading parameters of each function being defined are implicit.
    defining_implicit: Vec<(Name, usize)>,
    /// A recursion on parts deeper than the fields, while its arms are read.
    deep: Option<matching::DeepScope>,
    /// The matched variables of the arms being elaborated, each with the
    /// constructor it is in its arm, outermost first: a type written on a λ's
    /// parameter there reads the matched value as that constructor.
    matched: Vec<(Name, T)>,
    /// The independent re-check of every accepted declaration.
    core: core::Core,
    holes: Vec<HoleGoal>,
    /// The `let`s around each hole, outermost first, by the hole's name and place: the
    /// name and the value it was replaced with (`expand_lets`). The hole's
    /// context shows them as variables.
    hole_lets: HashMap<(String, Span), Vec<(Name, T)>>,
    /// Proofs checked before (`check/cache.rs`); none unless checking files.
    cache: Option<cache::Cache>,
    /// The terms the bodies elaborated to, by declaration, when asked for
    /// (`record_elaborated`).
    elaborated: Option<Vec<(Name, T)>>,
    derivations: Option<Vec<(Name, Derivation)>>,
    derivation_names: HashSet<Name>,
    /// What a syntax macro's output was written as, by the span of its root node.
    shown: HashMap<u32, String>,
    /// The decidable equalities of the types declared so far are generated
    /// (`check/deq.rs`).
    deq_started: bool,
    /// For each `opaque fn f`, by the name of its equation `f::eq`: `f`, sealed
    /// once the equation is checked (`check/opaque.rs`).
    seal_after: HashMap<Name, Name>,
    /// The inductives that list their decidable equality (`=> fn T::beq, …`), and, for one that
    /// could not be made, why.
    deq_listed: HashMap<Name, crate::surface::Generates>,
    deq_why: HashMap<Name, Message>,
    /// The declarations generated for a decidable equality, by the family that lists them, as
    /// they checked: extraction writes them after the family, as if they were in its file.
    pub derived: Vec<(Name, Vec<crate::surface::Stmt>)>,
    /// Whether to note the constructors that patterns' short names are read as
    /// (`record_ctor_sites`), and what was noted.
    record_sites: bool,
    ctor_sites: Vec<CtorSite>,
    field_sites: Vec<FieldSite>,
    ctor_site_origins: HashMap<crate::surface::TermId, Vec<crate::surface::TermId>>,
    application_sites: Vec<ApplicationSite>,
    application_heads: HashMap<crate::surface::TermId, Name>,
    /// The classes and instances of the proof language (`check/classes.rs`).
    classes: classes::Registry,
    source_classes: classes::Registry,
    /// Source declarations and their checked dictionary expansion.
    class_expansions: Vec<(Stmt, Vec<Stmt>)>,
    /// The level-polymorphic declarations and the instances made of them
    /// (`check/universe.rs`).
    templates: HashMap<Name, universe::Template>,
    level_instances: HashSet<Name>,
    level_depth: usize,
    /// How long one declaration may take (`Kernel::set_timeout`).
    timeout: Option<std::time::Duration>,
    /// The file being declared, and when its time is up (`Kernel::set_file_limit`).
    file_limit: Option<FileLimit>,
    /// Theorems with proofs are declared by their statements only
    /// (`declare_prefix`).
    statement_only: bool,
    /// How many steps of reduction one declaration may take
    /// (`Kernel::set_step_limit`).
    step_limit: Option<u64>,
    /// The declarations given their own limit on the steps (`Kernel::set_budget`).
    budgets: HashMap<Name, u64>,
    /// Why nothing more is checked: a declaration ran out of time.
    gave_up: Option<Message>,
    from_cache: bool,
    timings: Vec<Timing>,
    /// The effects and the functions with effects read in proofs
    /// (`check/effects.rs`).
    effects: effects::Effects,
}

#[derive(Debug, Clone)]
pub struct Timing {
    pub name: Name,
    pub elapsed: std::time::Duration,
    /// Steps of weak head reduction.
    pub steps: u64,
    /// The names unfolded most, with how often.
    pub top: Vec<(String, u64)>,
    /// The proof was checked before and taken from the cache
    /// (`check/cache.rs`); only its statement was checked now.
    pub cached: bool,
}

/// The name a statement declares, when it declares one.
/// `d`, found in a declaration that uses `n`, which did not check: the
/// failure of `n` comes first, since `d` may only follow from it.
fn after_failed(n: &str, mut d: Diagnostic) -> Diagnostic {
    d.message = msg!("kernel-uses-failed-then", name = n, message = d.message);
    d
}

/// Why a name the program declares is not defined where it is used.
#[derive(Clone)]
enum Ahead {
    Later,
    Struct,
    /// Checked earlier, but failed before its statement was known.
    Failed,
    /// Checked earlier, but left out of proofs, with why.
    Skipped(Message),
}

fn declared_name(stmt: &Stmt) -> Option<Name> {
    match stmt {
        Stmt::Theorem(t) | Stmt::Def(t) => Some(t.name.clone()),
        Stmt::Fn(f) => Some(f.name.clone()),
        Stmt::Inductive(i) => Some(i.name.clone()),
        Stmt::Let { name, .. } => Some(name.clone()),
        _ => None,
    }
}

/// What the kernel says of `decl` after `prefix`, the statements before it
/// (macro expansion checks a declaration without a typed macro's call, and
/// again with what the macro made).
/// The kernel after the prelude and `prefix`. Macro expansion asks it of the
/// declarations before each typed macro call, and each ask's prefix is mostly
/// an earlier one's with declarations after it, so the kernels of the last few
/// prefixes are kept and only the new declarations are declared into a copy of
/// the longest kept one that the prefix starts with. More than one is kept
/// because consecutive asks need not extend each other: the declaration a
/// macro reads is asked after the declarations before it, and the lemmas the
/// macro makes are then placed before that declaration; and a declaration
/// written after one that uses it moves ahead of it in the order below.
/// A kept kernel also serves a prefix that has more declarations among its own
/// (those a later declaration moved ahead of), as long as none of the kept
/// declarations failed. Theorems are declared by their statements, and the
/// limits of the check (`Kernel::set_timeout`, `Kernel::set_file_limit`) apply
/// to each declaration; one that runs out of time is an error.
/// They are declared in the order a whole file's check reads them
/// (`order::dependency_order`), so a declaration that uses one written after
/// it in the prefix checks here as it does there.
fn declare_prefix(prefix: &[Stmt]) -> Result<Kernel, String> {
    const KEPT: usize = 8;
    let ordered = order::dependency_order(prefix);
    let prefix = &ordered[..];
    thread_local! {
        /// The statements declared, in the order declared, the kernel after
        /// them, and whether none of them failed. Most recently used last.
        static KEPT_KERNELS: std::cell::RefCell<Vec<(Vec<Stmt>, Kernel, bool)>> =
            const { std::cell::RefCell::new(Vec::new()) };
    }
    /// Which statements of `prefix` are the kept ones `kept`, when `kept` are
    /// some of them in the same order, and whether every statement of `prefix`
    /// before the last of them is one of them.
    fn contained(kept: &[Stmt], prefix: &[Stmt]) -> Option<(Vec<bool>, bool)> {
        let mut taken = vec![false; prefix.len()];
        let mut next = 0;
        for (i, stmt) in prefix.iter().enumerate() {
            if next < kept.len() && kept[next] == *stmt {
                taken[i] = true;
                next += 1;
            }
        }
        if next < kept.len() {
            return None;
        }
        let last = taken.iter().rposition(|t| *t).map_or(0, |i| i + 1);
        let initial = taken[..last].iter().all(|t| *t);
        Some((taken, initial))
    }
    // A kept kernel serves when its statements are some of `prefix` in the
    // same order, and either they are an initial segment of it or none of them
    // failed: a statement that failed might have used one that `prefix` places
    // before it, and one that did not fail used only what was declared.
    let last = KEPT_KERNELS.with(|cell| {
        let mut kept = cell.borrow_mut();
        let mut best: Option<(usize, Vec<bool>)> = None;
        for (i, (stmts, _, clean)) in kept.iter().enumerate() {
            if stmts.len() > prefix.len() {
                continue;
            }
            let Some((taken, initial)) = contained(stmts, prefix) else {
                continue;
            };
            if !(initial || *clean) {
                continue;
            }
            if best
                .as_ref()
                .is_none_or(|(b, _)| kept[*b].0.len() < stmts.len())
            {
                best = Some((i, taken));
            }
        }
        let (at, taken) = best?;
        let entry = kept.remove(at);
        let found = (entry.0.clone(), entry.1.clone(), entry.2, taken);
        kept.push(entry);
        Some(found)
    });
    let (mut declared, mut kernel, mut clean, taken) = match last {
        Some((declared, kernel, clean, taken)) => (declared, kernel, clean, Some(taken)),
        None => {
            let mut kernel = Kernel::new();
            declare_prelude(&mut kernel)?;
            (Vec::new(), kernel, true, None)
        }
    };
    let kept_already = taken.as_ref().is_some_and(|t| t.iter().all(|x| *x));
    let (timeout, file_limit) = PREFIX_LIMITS.with(|l| l.borrow().clone());
    kernel.timeout = timeout;
    kernel.file_limit = file_limit;
    kernel.gave_up = None;
    // The theorems of a prefix are declared by their statements: whatever
    // uses them reads the statement, and the proofs are checked where the
    // theorems are, in the check of the whole file.
    kernel.statement_only = true;
    for (i, stmt) in prefix.iter().enumerate() {
        if taken.as_ref().is_some_and(|t| t[i]) {
            continue;
        }
        let entries = kernel.declare(
            &Program {
                stmts: vec![stmt.clone()],
                errors: Vec::new(),
            },
            false,
        );
        if kernel.gave_up.is_some() {
            let message = entries
                .iter()
                .find_map(|e| match &e.verdict {
                    Verdict::Failed(d) => Some(d.message.to_string()),
                    _ => None,
                })
                .or_else(|| kernel.gave_up.as_ref().map(|m| m.to_string()))
                .unwrap_or_default();
            return Err(message);
        }
        if entries
            .iter()
            .any(|e| matches!(e.verdict, Verdict::Failed(_)))
        {
            clean = false;
        }
        declared.push(stmt.clone());
    }
    kernel.statement_only = false;
    if !kept_already {
        KEPT_KERNELS.with(|cell| {
            let mut kept = cell.borrow_mut();
            if kept.len() == KEPT {
                kept.remove(0);
            }
            kept.push((declared, kernel.clone(), clean));
        });
    }
    Ok(kernel)
}

thread_local! {
    /// The limits of the declarations of a prefix, as the kernel of the check
    /// in this thread has them (`Kernel::set_timeout`, `Kernel::set_file_limit`).
    static PREFIX_LIMITS: std::cell::RefCell<(Option<std::time::Duration>, Option<FileLimit>)> =
        const { std::cell::RefCell::new((None, None)) };
}

/// The declarations of `later` that `decl` uses (`order::used_later`).
pub fn used_later(decl: &Stmt, later: &[Stmt]) -> Vec<Stmt> {
    order::used_later(decl, later)
}

pub fn check_in(prefix: &[Stmt], decl: &Stmt) -> Result<Vec<Entry>, String> {
    let mut kernel = declare_prefix(prefix)?;
    let one = Program {
        stmts: vec![decl.clone()],
        errors: Vec::new(),
    };
    Ok(kernel.declare(&one, false))
}

/// The kernel after the prelude and `prefix`, kept to check several versions
/// of one declaration (a step of a proof is checked a few times while it is
/// expanded); each check starts from the same state.
pub struct Prefixed(Kernel);

impl Prefixed {
    pub fn new(prefix: &[Stmt]) -> Result<Self, String> {
        Ok(Prefixed(declare_prefix(prefix)?))
    }

    /// What the kernel says of `decl`, the last entry when it makes several.
    pub fn verdict(&self, decl: &Stmt) -> Option<Verdict> {
        let mut kernel = self.0.clone();
        kernel
            .declare(
                &Program {
                    stmts: vec![decl.clone()],
                    errors: Vec::new(),
                },
                false,
            )
            .into_iter()
            .last()
            .map(|e| e.verdict)
    }
}

/// The variables a declaration's parameters bring, and the type an expression
/// of its body has there (macro expansion shows both to a typed macro).
pub fn goal_of(
    prefix: &[Stmt],
    decl: &TheoremDecl,
    term: &SurfaceTerm,
) -> Result<(Vec<(Name, SurfaceTerm)>, SurfaceTerm), String> {
    let mut kernel = declare_prefix(prefix)?;
    let rendered = |d: Diagnostic| d.message.to_string();
    let mut declaration = [Stmt::Theorem(decl.clone())];
    kernel.resolver.statements(&mut declaration);
    let Stmt::Theorem(decl) = &declaration[0] else {
        unreachable!()
    };
    let (ctx, _) = kernel
        .shaped_signature(&decl.params, &decl.ty)
        .map_err(rendered)?;
    let mut term = term.clone();
    let names = ctx.iter().map(|(name, _)| name.clone()).collect::<Vec<_>>();
    kernel.resolver.term_in_context(&mut term, &names);
    let shaped = kernel.shape(&term).map_err(rendered)?;
    let elaborated = kernel.elab(&ctx, &shaped, None).map_err(rendered)?;
    let ty = kernel.infer(&ctx, &elaborated).map_err(rendered)?;
    Ok((ctx, ty))
}

/// `term` read with the constants `kernel` has, in normal form, and its type:
/// what `tauto eval` shows. The value is only shown; a proof that needs it
/// states it as a `Refl` theorem, which the kernel checks.
pub fn eval_term(
    kernel: &mut Kernel,
    term: &SurfaceTerm,
) -> Result<(SurfaceTerm, SurfaceTerm), String> {
    let ctx: Ctx = Vec::new();
    let rendered = |d: Diagnostic| d.message.to_string();
    // `Nat::add(30, 4)` names the function as it would in the file.
    let mut term = crate::surface::modules::resolve_term_against(
        term,
        kernel.globals.keys().map(|k| k.as_str()),
    );
    kernel.resolver.term_in_context(&mut term, &[]);
    let shaped = kernel.shape(&term).map_err(rendered)?;
    let elaborated = kernel.elab(&ctx, &shaped, None).map_err(rendered)?;
    let ty = kernel.infer(&ctx, &elaborated).map_err(rendered)?;
    let value = kernel.core.nf_in(&ctx, &elaborated);
    Ok((kernel.without_implicit(&value), ty))
}

impl Kernel {
    /// Whether `g` names a function without parameters of its own, which is
    /// called with `()` and never named bare. Names with `@` are the
    /// checker's own (an instance's record), never written.
    pub(crate) fn nullary_fn(&self, ctx: &Ctx, g: &Name) -> bool {
        !is_local(ctx, g)
            && !g.contains('@')
            && self.fns.contains(g)
            && self
                .globals
                .get(g)
                .is_some_and(|x| x.params == Some(x.implicit))
    }

    /// `t` with each function without parameters called with `()`, as it is
    /// written: the kernel reads `f()` as the constant `f`, and what it
    /// hands back to a macro is read again as written.
    fn calls_written(&self, t: &T) -> T {
        self.calls_written_in(&Vec::new(), t)
    }

    /// `calls_written` under the locals `ctx`, which keep their names.
    pub(crate) fn calls_written_in(&self, ctx: &Ctx, t: &T) -> T {
        fn go(k: &Kernel, ctx: &Ctx, t: &mut T) {
            match &*t.kind {
                TermKind::Var(g) if k.nullary_fn(ctx, g) => {
                    *t = t.with_kind(
                        TermKind::App {
                            function: Box::new(t.clone()),
                            arguments: Vec::new(),
                        },
                        t.span,
                    );
                }
                TermKind::App { function, .. } if matches!(&*function.kind, TermKind::Var(_)) => {
                    if let TermKind::App { arguments, .. } = std::sync::Arc::make_mut(&mut t.kind) {
                        arguments.iter_mut().for_each(|a| go(k, ctx, a));
                    }
                }
                _ => crate::surface::walk::children(t, &mut |c| go(k, ctx, c)),
            }
        }
        let mut t = t.clone();
        go(self, ctx, &mut t);
        t
    }

    /// `t` with each `Eq(T, a, b)` written `a = b`, as a goal is shown and
    /// written back: reading `a = b` again finds `T` from its sides.
    pub fn eqs_written(t: &T) -> T {
        fn go(t: &mut T) {
            if let TermKind::App {
                function,
                arguments,
            } = &*t.kind
                && matches!(&*function.kind, TermKind::Var(eq) if tauto_surface::bindings::is_library(&eq, "Eq"))
                && arguments.len() == 3
            {
                let mut sides = arguments[1..].to_vec();
                sides.iter_mut().for_each(go);
                let written = T::app(&tauto_surface::bindings::library_name("="), sides, t.span);
                *t = t.with_kind((*written.kind).clone(), t.span);
                return;
            }
            crate::surface::walk::children(t, &mut go);
        }
        let mut t = t.clone();
        go(&mut t);
        t
    }

    /// `t` with the arguments a call may leave out left out, as it is written.
    fn without_implicit(&self, t: &T) -> T {
        let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        else {
            return t.clone();
        };
        let skip = match &*function.kind {
            TermKind::Var(f) => self.globals.get(f).map_or(0, |g| g.implicit),
            _ => 0,
        };
        let arguments: Vec<T> = arguments
            .iter()
            .skip(skip.min(arguments.len()))
            .map(|a| self.without_implicit(a))
            .collect();
        let function = self.without_implicit(function);
        if arguments.is_empty() {
            return function;
        }
        t.with_kind(
            TermKind::App {
                function: Box::new(function),
                arguments,
            },
            t.span,
        )
    }
}

/// The kernel over the declarations before one and the variables of a context:
/// what the `elab_*` operations of a typed macro ask of it. It reads; nothing
/// it does is kept.
pub struct Elaborator {
    kernel: Kernel,
    ctx: Ctx,
}

impl Elaborator {
    pub fn new(prefix: &[Stmt], context: &[(Name, SurfaceTerm)]) -> Result<Self, String> {
        let mut kernel = declare_prefix(prefix)?;
        let mut ctx: Ctx = Vec::new();
        for (n, d) in context {
            let mut d = d.clone();
            kernel.resolver.term_in_context(
                &mut d,
                &ctx.iter().map(|(name, _)| name.clone()).collect::<Vec<_>>(),
            );
            let d = kernel.shape(&d).map_err(|e| e.message.to_string())?;
            let d = kernel
                .elab(&ctx, &d, None)
                .map_err(|e| e.message.to_string())?;
            ctx.push((n.clone(), d));
        }
        Ok(Elaborator { kernel, ctx })
    }

    /// The term with its implicit arguments written out, and its type.
    pub fn infer(&mut self, t: &SurfaceTerm) -> Result<(SurfaceTerm, SurfaceTerm), String> {
        let mut t = t.clone();
        self.kernel.resolver.term_in_context(
            &mut t,
            &self
                .ctx
                .iter()
                .map(|(name, _)| name.clone())
                .collect::<Vec<_>>(),
        );
        let shaped = self.kernel.shape(&t).map_err(|e| e.message.to_string())?;
        let e = self
            .kernel
            .elab(&self.ctx, &shaped, None)
            .map_err(|e| e.message.to_string())?;
        let ty = self
            .kernel
            .infer(&self.ctx, &e)
            .map_err(|e| e.message.to_string())?;
        Ok((
            self.kernel.calls_written(&e),
            self.kernel.calls_written(&ty),
        ))
    }

    pub fn check(&mut self, t: &SurfaceTerm, ty: &SurfaceTerm) -> Result<SurfaceTerm, String> {
        let (ty, _) = self.infer(ty)?;
        let mut t = t.clone();
        self.kernel.resolver.term_in_context(
            &mut t,
            &self
                .ctx
                .iter()
                .map(|(name, _)| name.clone())
                .collect::<Vec<_>>(),
        );
        let shaped = self.kernel.shape(&t).map_err(|e| e.message.to_string())?;
        let e = self
            .kernel
            .elab(&self.ctx, &shaped, Some(&ty))
            .map_err(|e| e.message.to_string())?;
        let found = self
            .kernel
            .infer(&self.ctx, &e)
            .map_err(|e| e.message.to_string())?;
        if !self.kernel.conv(&self.ctx, &found, &ty) {
            return Err(self.kernel.mismatch(&self.ctx, &ty, &found).to_string());
        }
        Ok(self.kernel.calls_written(&e))
    }

    pub fn defeq(&mut self, a: &SurfaceTerm, b: &SurfaceTerm) -> Result<bool, String> {
        let (a, _) = self.infer(a)?;
        let (b, _) = self.infer(b)?;
        Ok(self.kernel.conv(&self.ctx, &a, &b))
    }

    pub fn whnf(&mut self, t: &SurfaceTerm) -> Result<SurfaceTerm, String> {
        let (e, _) = self.infer(t)?;
        let e = self.kernel.whnf(&self.ctx, &e);
        Ok(self.kernel.calls_written(&e))
    }

    /// The type of a declaration before the one in hand, or of a variable of
    /// the context.
    pub fn type_of(&self, name: &Name) -> Option<SurfaceTerm> {
        if let Some((_, t)) = self.ctx.iter().rev().find(|(n, _)| n == name) {
            return Some(self.kernel.calls_written(t));
        }
        self.kernel
            .globals
            .get(name)
            .map(|g| self.kernel.calls_written(&g.ty))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FileEntry {
    pub file: std::path::PathBuf,
    pub entry: Entry,
}

/// One run of a macro, as `check --json` reports it.
#[derive(Clone)]
pub struct ExpansionInfo {
    pub id: u32,
    pub macro_name: String,
    pub kind: &'static str,
    pub parent: Option<u32>,
    pub at: Option<(std::path::PathBuf, usize, usize)>,
    pub steps: u64,
    pub captures: Vec<String>,
}

/// A constant the kernel knows after checking a file: what a proof may use.
#[derive(Debug, Clone)]
pub struct LibEntry {
    pub name: Name,
    /// `theorem`, `axiom`, `def`, `inductive`, `constructor` or `eliminator`.
    pub kind: &'static str,
    pub ty: SurfaceTerm,
    /// How many leading parameters a call may leave out.
    pub implicit: usize,
    /// `ok`, `incomplete` or `failed`.
    pub state: &'static str,
    /// For an `inductive`, its constructors in the order declared.
    pub inductive: Option<IndInfo>,
}

/// What a `match` on a value of an inductive family needs.
#[derive(Debug, Clone)]
pub struct IndInfo {
    pub params: usize,
    pub indices: usize,
    pub ctors: Vec<CtorInfo>,
}

#[derive(Debug, Clone)]
pub struct CtorInfo {
    pub name: Name,
    /// The fields a pattern names: the arguments after the generics.
    pub fields: Vec<(Name, SurfaceTerm)>,
    /// Which of `fields` are of the family being defined (a call of the
    /// theorem on one is its induction hypothesis).
    pub recursive: Vec<usize>,
}

impl Kernel {
    /// The constants in scope, sorted by name.
    pub fn library(&self) -> Vec<LibEntry> {
        let mut out: Vec<LibEntry> = self
            .globals
            .iter()
            .map(|(name, g)| {
                let kind = if self.inds.contains_key(name) {
                    "inductive"
                } else if self.ctors.contains_key(name) {
                    "constructor"
                } else if self.recs.contains_key(name) {
                    "eliminator"
                } else if g.value.is_some() {
                    "def"
                } else if g.axioms.contains(name) {
                    "axiom"
                } else {
                    "theorem"
                };
                LibEntry {
                    name: name.clone(),
                    kind,
                    ty: g.ty.clone(),
                    implicit: g.implicit,
                    state: if g.failed {
                        "failed"
                    } else if g.incomplete {
                        "incomplete"
                    } else {
                        "ok"
                    },
                    inductive: self.inds.get(name).map(|ind| IndInfo {
                        params: ind.params.len(),
                        indices: ind.indices,
                        ctors: ind
                            .ctors
                            .iter()
                            .map(|c| CtorInfo {
                                name: c.name.clone(),
                                fields: c.args[c.implicit.min(c.args.len())..].to_vec(),
                                recursive: c
                                    .recs
                                    .iter()
                                    .filter(|r| r.arg >= c.implicit)
                                    .map(|r| r.arg - c.implicit)
                                    .collect(),
                            })
                            .collect(),
                    }),
                }
            })
            .collect();
        out.sort_by(|a, b| {
            a.name
                .as_str()
                .cmp(b.name.as_str())
                .then_with(|| a.name.cmp(&b.name))
        });
        out
    }
}

impl Kernel {
    /// Records the final core check of each body, including incomplete proofs.
    /// Cached proofs cannot provide a derivation.
    pub fn record_derivations(&mut self, names: &[Name]) {
        self.derivations = Some(Vec::new());
        self.derivation_names = names.iter().cloned().collect();
    }

    pub fn derivations(&self) -> &[(Name, Derivation)] {
        self.derivations.as_deref().unwrap_or_default()
    }

    /// Keeps the term each body elaborates to, for `elaborated`. A proof
    /// taken from the cache is not elaborated, so do not use both.
    pub fn record_elaborated(&mut self) {
        self.elaborated = Some(Vec::new());
    }

    /// The terms the bodies elaborated to, in order, since
    /// `record_elaborated`.
    pub fn elaborated(&self) -> &[(Name, SurfaceTerm)] {
        self.elaborated.as_deref().unwrap_or_default()
    }

    /// Notes, for each pattern in the arms of the declarations checked from now on, the
    /// constructor its short name was read as (`Checked::ctor_sites`). Extraction
    /// writes that constructor; the checker's own typing is not repeated. Also records
    /// the implicit slots of source applications (`Checked::application_sites`).
    /// A cached declaration keeps both kinds of notes with its terms.
    pub fn record_ctor_sites(&mut self) {
        self.record_sites = true;
    }

    pub fn use_cache(&mut self) {
        self.cache = cache::Cache::from_env();
    }

    /// Gives up on a declaration whose check takes longer than `limit`: it is
    /// rejected, and the declarations after it are not checked.
    pub fn set_timeout(&mut self, limit: Option<std::time::Duration>) {
        self.timeout = limit;
        PREFIX_LIMITS.with(|l| l.borrow_mut().0 = limit);
    }

    /// Gives up on the declarations of one file that take longer than `limit`
    /// together, counted from now: the declaration in hand is rejected and
    /// nothing after it is checked. `file` names the file in the message;
    /// `None` lifts the limit.
    pub fn set_file_limit(&mut self, file: Option<(&str, std::time::Duration)>) {
        self.file_limit = file.map(|(file, limit)| FileLimit {
            file: file.to_string(),
            limit,
            deadline: crate::clock::Instant::now() + limit,
        });
        PREFIX_LIMITS.with(|l| l.borrow_mut().1 = self.file_limit.clone());
    }

    /// Gives up on a declaration whose check takes more than `limit` steps of
    /// reduction (`None`: no limit): it is rejected, and the declarations
    /// after it are not checked. The count is the same on every machine.
    pub fn set_step_limit(&mut self, limit: Option<u64>) {
        self.step_limit = limit;
    }

    /// Lets the declaration `name` take `steps` steps of reduction in place of
    /// the limit of [`Kernel::set_step_limit`].
    pub fn set_budget(&mut self, name: &Name, steps: u64) {
        self.budgets.insert(name.clone(), steps);
    }

    pub fn timings(&self) -> &[Timing] {
        &self.timings
    }

    pub fn show_syntax(&mut self, shown: HashMap<u32, String>) {
        self.shown = shown;
    }

    pub fn new() -> Self {
        let mut k = Kernel {
            resolver: tauto_surface::resolve::Resolver::new(
                tauto_surface::bindings::library_bindings(),
            ),
            globals: HashMap::new(),
            skipped: HashSet::new(),
            fns: HashSet::new(),
            inds: HashMap::new(),
            ctors: HashMap::new(),
            recs: HashMap::new(),
            fresh: 0,
            arrow_binders: Vec::new(),
            metas: HashMap::new(),
            current: None,
            projecting: 0,
            ahead: HashMap::new(),
            defining: Vec::new(),
            defining_implicit: Vec::new(),
            deep: None,
            matched: Vec::new(),
            core: core::Core::new(),
            holes: Vec::new(),
            hole_lets: HashMap::new(),
            cache: None,
            elaborated: None,
            derivations: None,
            derivation_names: HashSet::new(),
            shown: HashMap::new(),
            deq_started: false,
            seal_after: HashMap::new(),
            deq_listed: HashMap::new(),
            deq_why: HashMap::new(),
            derived: Vec::new(),
            record_sites: false,
            ctor_sites: Vec::new(),
            field_sites: Vec::new(),
            ctor_site_origins: HashMap::new(),
            application_sites: Vec::new(),
            application_heads: HashMap::new(),
            classes: Default::default(),
            source_classes: Default::default(),
            class_expansions: Vec::new(),
            templates: HashMap::new(),
            level_instances: Default::default(),
            level_depth: 0,
            timeout: None,
            file_limit: None,
            statement_only: false,
            step_limit: Some(core::DEFAULT_STEP_LIMIT),
            budgets: HashMap::new(),
            gave_up: None,
            from_cache: false,
            timings: Vec::new(),
            effects: Default::default(),
        };
        let sp = Span::new(0, 0);
        let nat = T::var(
            &Name::from(tauto_surface::identity::DeclRef::primitive("Nat").unwrap()),
            sp,
        );
        let binary = pi("_", nat.clone(), pi("_", nat.clone(), nat));
        for op in ["+", "*", "-"] {
            k.globals.insert(
                tauto_surface::identity::DeclRef::primitive(op)
                    .unwrap()
                    .into(),
                Global {
                    ty: binary.clone(),
                    value: None,
                    axioms: BTreeSet::new(),
                    implicit: 0,
                    params: None,
                    failed: false,
                    incomplete: false,
                },
            );
        }
        k
    }

    /// Checks ordinary declarations, retaining every explicit axiom in the verdict.
    /// The builtin privilege used while installing the prelude stays internal.
    pub fn binding_session(&self) -> tauto_surface::resolve::Resolver {
        self.resolver.clone()
    }

    pub fn resolve_statements(&mut self, statements: &mut [Stmt]) {
        self.resolver.statements(statements);
    }

    /// A source environment can name an already allocated declaration.
    /// This neither accepts that declaration nor rewrites resolved terms.
    pub fn source_alias(&mut self, spelling: &str, reference: &tauto_surface::identity::DeclRef) {
        self.resolver.source_alias(spelling, reference);
    }

    pub fn resolve_declaration(&mut self, name: &Name) -> Name {
        self.resolver.global(name)
    }

    pub fn declare_program(&mut self, program: &Program) -> Vec<Entry> {
        self.declare(program, false)
    }

    pub(crate) fn declare(&mut self, program: &Program, builtin: bool) -> Vec<Entry> {
        let mut entries = Vec::new();
        // `#(a, b)` is the prelude's `Pair` here: the kernel has no product of its own.
        let mut lowered = program.stmts.clone();
        for s in &mut lowered {
            tauto_surface::surface::qualify::lower_tuples(s, "Pair");
        }
        if builtin {
            tauto_surface::resolve::Resolver::new(
                tauto_surface::bindings::library_definition_bindings(),
            )
            .statements(&mut lowered);
        } else {
            self.resolver.statements(&mut lowered);
        }
        if self.record_sites {
            for statement in &mut lowered {
                crate::surface::walk::stmt(statement, &mut |term| {
                    if let TermKind::App { function, .. } = &*term.kind
                        && let TermKind::Var(name) = &*function.kind
                    {
                        self.application_heads
                            .entry(term.id())
                            .or_insert_with(|| name.clone());
                    }
                });
            }
        }
        let stmts = order::dependency_order(&lowered);
        self.classes = self.source_classes.clone();
        let stmts = self.class_pass(&stmts, &mut entries);
        let stmts = self.opaque_pass(&stmts, &mut entries);
        let stmts = self.wf_pass(&stmts, &mut entries);
        let stmts = self.level_pass(&stmts, &mut entries);
        // Held to their effects' `resume` before `effect_pass` reads each
        // `handle` as a fold, which no longer shows how often `k` is called.
        let mut overused = HashMap::new();
        for stmt in &stmts {
            if let Stmt::Effect(e) = stmt {
                self.effects
                    .resumes
                    .insert(e.name.clone(), e.resume.clone());
            }
        }
        for stmt in &stmts {
            if let Some(name) = declared_name(stmt)
                && let Some(found) = resumes::overused(stmt, &self.effects.resumes)
            {
                overused.insert(name, found);
            }
        }
        let mut stmts = self.effect_pass(&stmts);
        if builtin {
            tauto_surface::resolve::Resolver::new(
                tauto_surface::bindings::library_definition_bindings(),
            )
            .statements(&mut stmts);
        }
        self.resolver.statements(&mut stmts);
        self.classes.resolve(&mut self.resolver);
        self.source_classes = self.classes.clone();
        for stmt in &stmts {
            match stmt {
                // Still a `struct` or `enum`: it could not be the `inductive`
                // it says it is (`tauto_surface::inductive_data`).
                Stmt::Struct(d) | Stmt::Enum(d)
                    if d.kind.as_deref() == Some(tauto_surface::inductive_data::KIND) =>
                {
                    let problems =
                        tauto_surface::inductive_data::problems(d, matches!(stmt, Stmt::Struct(_)));
                    if let Some((why, at)) = problems.into_iter().next() {
                        entries.push(Entry {
                            name: d.name.clone(),
                            verdict: Verdict::Failed(Diagnostic::new(why, Some(at))),
                        });
                    }
                    self.ahead.insert(d.name.clone(), Ahead::Failed);
                }
                Stmt::Struct(d) | Stmt::Enum(d) => {
                    self.ahead.insert(d.name.clone(), Ahead::Struct);
                }
                _ => {
                    if let Some(name) = declared_name(stmt) {
                        self.ahead.entry(name).or_insert(Ahead::Later);
                    }
                }
            }
        }
        // A declaration the passes above rejected is not checked again, and a
        // use of it is told that it did not check.
        for e in &entries {
            if let Verdict::Failed(_) = e.verdict {
                self.ahead.insert(e.name.clone(), Ahead::Failed);
            }
        }
        for stmt in &stmts {
            if let Some(why) = &self.gave_up {
                if let Some(name) = declared_name(stmt) {
                    entries.push(Entry {
                        name,
                        verdict: Verdict::Skipped(why.clone()),
                    });
                }
                continue;
            }
            if let Some(limit) = &self.file_limit
                && crate::clock::Instant::now() >= limit.deadline
            {
                // The time of the file is up before this declaration starts.
                let message = msg!(
                    "kernel-file-time-limit",
                    file = limit.file.as_str(),
                    seconds = limit.limit.as_secs_f64().to_string()
                );
                if let Some(name) = declared_name(stmt) {
                    self.gave_up = Some(msg!("kernel-ran-out-of-time", name = (&name).to_string()));
                    entries.push(Entry {
                        verdict: Verdict::Failed(Diagnostic::new(message, None)),
                        name,
                    });
                }
                continue;
            }
            if let Some(name) = declared_name(stmt)
                && let Some((message, span)) = overused.remove(&name)
            {
                if let Some(a) = self.ahead.get_mut(&name) {
                    *a = Ahead::Failed;
                }
                entries.push(Entry {
                    name,
                    verdict: Verdict::Failed(Diagnostic::new(message, Some(span))),
                });
                continue;
            }
            let before = entries.len();
            let started = crate::clock::Instant::now();
            // `budget N` written on the declaration, then one given by `set_budget`.
            let written = match stmt {
                Stmt::Theorem(t) | Stmt::Def(t) => t.budget,
                Stmt::Fn(f) => f.budget,
                _ => None,
            };
            let limit = match written
                .or_else(|| declared_name(stmt).and_then(|n| self.budgets.get(&n).copied()))
            {
                Some(steps) => Some(steps),
                None => self.step_limit,
            };
            let declaration_deadline = self.timeout.map(|limit| started + limit);
            // The time of the file is up first when its deadline is the earlier.
            let by_file = match (&self.file_limit, declaration_deadline) {
                (Some(f), Some(d)) => f.deadline <= d,
                (Some(_), None) => true,
                _ => false,
            };
            let deadline = match (&self.file_limit, declaration_deadline) {
                (Some(f), Some(d)) => Some(f.deadline.min(d)),
                (Some(f), None) => Some(f.deadline),
                (None, d) => d,
            };
            self.core.start_budget(limit, deadline);
            self.from_cache = false;
            if let Some(name) = self.template_of(stmt) {
                self.check_template(&name, builtin, &mut entries);
            } else if let Some(name) = declared_name(stmt)
                && let Some(owner) = self.instance_of(&name)
                && matches!(self.ahead.get(&owner), Some(Ahead::Failed))
            {
                // An instance of a template that does not check for every
                // level is not used, even where it would check.
                entries.push(Entry {
                    verdict: Verdict::Failed(Diagnostic::new(
                        msg!("kernel-uses-failed", name = owner.to_string()),
                        None,
                    )),
                    name,
                });
            } else {
                self.declare_one(stmt, builtin, &mut entries);
            }
            self.other_undefined_uses(stmt, &mut entries[before..]);
            for e in &entries[before..] {
                let Some(a) = self.ahead.get_mut(&e.name) else {
                    continue;
                };
                match &e.verdict {
                    Verdict::Failed(_) => *a = Ahead::Failed,
                    // Not in the kernel: a use of it is told why, not that it
                    // comes later.
                    Verdict::Skipped(why) if !self.globals.contains_key(&e.name) => {
                        *a = Ahead::Skipped(why.clone())
                    }
                    _ => {}
                }
            }
            let spent = self.core.end_budget();
            let elapsed = started.elapsed();
            if spent.out {
                // Reduction stopped short, so what was decided cannot be trusted:
                // the declaration is rejected and nothing after it is checked.
                let limit = self.timeout.unwrap_or_default().as_secs_f64();
                let limit = limit.to_string();
                let top: Vec<String> = spent
                    .top
                    .iter()
                    .map(|(n, k)| msg!("kernel-unfolded-times", name = n, count = *k).to_string())
                    .collect();
                let message = if spent.out_of_steps {
                    let steps = spent.steps.saturating_sub(1).to_string();
                    match &spent.reached_in {
                        Some(name) => msg!(
                            "kernel-out-of-steps-in",
                            steps = steps,
                            name = name,
                            top = top.join(", ")
                        ),
                        None => msg!("kernel-out-of-steps", steps = steps),
                    }
                } else if let Some(f) = self.file_limit.as_ref().filter(|_| by_file) {
                    msg!(
                        "kernel-file-time-limit",
                        file = f.file.as_str(),
                        seconds = f.limit.as_secs_f64().to_string()
                    )
                } else if spent.top.is_empty() {
                    msg!("kernel-gave-up", seconds = limit)
                } else {
                    msg!(
                        "kernel-gave-up-unfolded",
                        seconds = limit,
                        top = top.join(", ")
                    )
                };
                for e in &mut entries[before..] {
                    e.verdict = Verdict::Failed(Diagnostic::new(message.clone(), None));
                }
                if let Some(e) = entries.get(before) {
                    self.gave_up = Some(msg!("kernel-ran-out-of-time", name = e.name.to_string()));
                }
            }
            if let Some(op) = &spent.past_u128 {
                // A failure there may be the number left as it is: say so, where
                // the comparison that needed it was.
                for e in &mut entries[before..] {
                    if let Verdict::Failed(d) = &mut e.verdict {
                        d.message = msg!(
                            "kernel-past-u128",
                            message = d.message.clone(),
                            op = op.as_str()
                        );
                    }
                }
            }
            if let Some(e) = entries.get(before) {
                self.timings.push(Timing {
                    name: e.name.clone(),
                    elapsed,
                    steps: spent.steps,
                    top: spent.top,
                    cached: self.from_cache,
                });
            }
        }
        entries.extend(self.decidable_unmet());
        entries
    }

    fn declare_one(&mut self, stmt: &Stmt, builtin: bool, entries: &mut Vec<Entry>) {
        // The equation of an `opaque fn` is checked with the function
        // unfolding; after it, the function no longer unfolds.
        if let Stmt::Theorem(t) = stmt
            && let Some(f) = self.seal_after.remove(&t.name)
        {
            self.declare_one(stmt, builtin, entries);
            self.seal(&f);
            return;
        }
        let mut prepared = stmt.clone();
        if let Err(d) = self.prepare_recursors(&mut prepared) {
            entries.push(Entry {
                name: "recursor".into(),
                verdict: Verdict::Failed(d),
            });
            return;
        }
        let stmt = match self.mutable_sugar(&prepared) {
            Ok(stmt) => {
                let (stmt, labels) = self.program_sugar_labels(&stmt);
                if let Err(d) = self.declare_labels(&labels) {
                    entries.push(Entry {
                        name: "label".into(),
                        verdict: Verdict::Failed(d),
                    });
                    return;
                }
                stmt
            }
            Err((name, d)) => {
                // A function whose `handle`s are not read in proofs is run,
                // not read with its `var`s as states.
                let verdict = match self.effects.skipped.get(&name) {
                    Some(why) => {
                        Verdict::Skipped(msg!("kernel-handle-not-read", why = why.clone()))
                    }
                    None => Verdict::Failed(d),
                };
                entries.push(Entry { name, verdict });
                return;
            }
        };
        let stmt = &stmt;
        if let Stmt::Mutual { items, span } = stmt {
            entries.extend(self.mutual(items, *span));
            return;
        }
        let declared = match stmt {
            Stmt::Theorem(t) | Stmt::Def(t) => Some(&t.name),
            Stmt::Fn(f) => Some(&f.name),
            Stmt::Inductive(i) => Some(&i.name),
            Stmt::Let { name, .. } => Some(name),
            _ => None,
        };
        if let Some(name) = declared
            && is_reserved(name)
        {
            entries.push(Entry {
                name: name.clone(),
                verdict: Verdict::Failed(Diagnostic::new(
                    msg!("kernel-reserved", name = name.to_string()),
                    None,
                )),
            });
            return;
        }
        if let Some(name) = declared
            && self.globals.contains_key(name)
        {
            entries.push(Entry {
                name: name.clone(),
                verdict: Verdict::Failed(Diagnostic::new(
                    msg!("kernel-already-defined", name = name.to_string()),
                    None,
                )),
            });
            return;
        }
        if let Stmt::Inductive(i) = stmt
            && let Some(entry) = self.decidable_note(i)
        {
            entries.push(entry);
        }
        let (name, verdict) = match stmt {
            Stmt::Theorem(t) => (t.name.clone(), self.theorem(t, builtin)),
            Stmt::Def(t) => (t.name.clone(), self.definition(t)),
            Stmt::Fn(f) => (f.name.clone(), self.function(f)),
            Stmt::Inductive(i) => (i.name.clone(), self.inductive(i)),
            Stmt::Let { name, value, .. } => (name.clone(), self.constant(name, value)),
            _ => return,
        };
        let verdict = self.classes.explain(verdict);
        let verdict = self.effect_verdict(&name, verdict);
        // An effect whose types are not the kernel's is simply not read in
        // proofs; the functions that perform it say so.
        if self.effects.generated.contains(&name) && matches!(verdict, Verdict::Skipped(_)) {
            return;
        }
        // A theorem is opaque: its proof never unfolds. Nothing could
        // have unfolded it before it was declared, so no cache is stale.
        if matches!(stmt, Stmt::Theorem(_)) && matches!(verdict, Verdict::Checked { .. }) {
            self.core.seal_fresh(&name);
        }
        let checked_inductive =
            matches!(stmt, Stmt::Inductive(_)) && matches!(verdict, Verdict::Checked { .. });
        entries.push(Entry {
            name: name.clone(),
            verdict,
        });
        if checked_inductive && self.deq_started && self.deq_listed.contains_key(&name) {
            self.decidable_equality(&name);
        }
        self.decidable_pending();
    }

    fn theorem(&mut self, t: &TheoremDecl, builtin: bool) -> Verdict {
        if self.statement_only && !builtin && t.body.is_some() {
            return self.theorem_checked_before(t, BTreeSet::new());
        }
        let key = if builtin || t.body.is_none() {
            None
        } else {
            self.proof_key(t)
        };
        // The cache keeps the globals the proof names, not their axioms: a
        // global's interface is its statement, so one that became an axiom
        // (or stopped being one) leaves the key as it was, and its axioms
        // are taken as they are now.
        if let Some(key) = &key
            && let Some(uses) = self.cache.as_ref().and_then(|c| c.get(key))
            && let Some(axioms) = self.axioms_of(&uses)
        {
            self.from_cache = true;
            return self.theorem_checked_before(t, axioms);
        }
        let (verdict, term) = self.theorem_term(t, builtin);
        if let (Some(key), Verdict::Checked { .. }, Some(term), Some(cache)) =
            (&key, &verdict, &term, &self.cache)
            && !self.core.budget_out()
        {
            let mut uses = BTreeSet::new();
            self.collect_globals(term, &mut uses);
            cache.put(key, &uses);
        }
        verdict
    }

    /// The axioms the globals `uses` rely on now, or none when one of them is
    /// no longer a global.
    fn axioms_of(&self, uses: &BTreeSet<Name>) -> Option<BTreeSet<Name>> {
        let mut axioms = BTreeSet::new();
        for n in uses {
            axioms.extend(self.globals.get(n)?.axioms.iter().cloned());
        }
        Some(axioms)
    }

    /// A theorem whose proof checked before (`check/cache.rs`): its statement
    /// is checked, by both checkers, and its proof taken as it was.
    fn theorem_checked_before(&mut self, t: &TheoremDecl, axioms: BTreeSet<Name>) -> Verdict {
        let statement = (|| {
            let statement = self.telescope(&t.params, &t.ty)?;
            let statement = self.shape_type(&statement, &[])?;
            let statement = self.elab(&Vec::new(), &statement, None)?;
            self.expect_type(&Vec::new(), &statement)?;
            Ok::<_, Diagnostic>(statement)
        })();
        let statement = match statement {
            Ok(s) => s,
            Err(d) => return Verdict::Failed(d),
        };
        if let Err(m) = self.core.add_decl(&t.name, &statement, None, false) {
            self.add_failed(&t.name, statement);
            self.set_implicit(&t.name, t.implicit);
            self.set_params(&t.name, t.params.len());
            return Verdict::Failed(core_rejects(&t.name, m, t.span));
        }
        self.add(&t.name, statement, None, axioms.clone());
        self.set_implicit(&t.name, t.implicit);
        self.set_params(&t.name, t.params.len());
        Verdict::Checked {
            axioms: axioms.into_iter().collect(),
        }
    }

    /// Checks a theorem (or the body of a definition or function) and adds
    /// it; the term that was checked is returned, so that a definition
    /// unfolds to exactly that term.
    fn theorem_term(&mut self, t: &TheoremDecl, builtin: bool) -> (Verdict, Option<T>) {
        let out = self.theorem_term_from(t, builtin, None);
        if let (Some(record), Some(term)) = (&mut self.elaborated, &out.1) {
            record.push((t.name.clone(), term.clone()));
        }
        out
    }

    /// `theorem_term`, with the term the body elaborated to before
    /// (`check/cache.rs`) when there is one: it is not elaborated again, and
    /// the core takes it as checked, checking only the statement.
    fn theorem_term_from(
        &mut self,
        t: &TheoremDecl,
        builtin: bool,
        before: Option<T>,
    ) -> (Verdict, Option<T>) {
        if let Some(d) = self.reserved(&t.name, t.span) {
            return (Verdict::Failed(d), None);
        }
        self.holes.clear();
        let result = (|| {
            let statement = self.telescope(&t.params, &t.ty)?;
            let statement = self.shape_type(&statement, &[])?;
            let statement = self.elab(&Vec::new(), &statement, None)?;
            self.expect_type(&Vec::new(), &statement)?;
            Ok::<_, Diagnostic>(statement)
        })();
        let statement = match result {
            Ok(s) => s,
            Err(d) => {
                // A declaration that did not check is the cause, not the
                // error its stand-in type makes here.
                let d = match self.uses_failed(&t.ty) {
                    Some(n) => after_failed(&n, d),
                    None => d,
                };
                return (Verdict::Failed(d), None);
            }
        };
        let mut axioms = BTreeSet::new();
        let mut checked = None;
        // The body is one this checker checked before (`check/cache.rs`).
        let mut cached = false;
        match &t.body {
            None => {
                if !builtin || tauto_surface::bindings::is_library(&t.name, QUOT_SOUND) {
                    axioms.insert(t.name.clone());
                }
            }
            Some(body) => {
                self.current = Some(t.name.clone());
                let proof = (|| {
                    if let Some(lam) = before {
                        cached = true;
                        return Ok(lam);
                    }
                    let body = &self.expand_lets(body)?;
                    let (shaped, result) = self.shaped_signature(&t.params, &t.ty)?;
                    let body = &match &t.decreasing_by {
                        Some(y) => self.structural_on(&shaped, body, y)?,
                        None => body.clone(),
                    };
                    let mut compiled =
                        self.compile_match(Some(&t.name), t.implicit, &shaped, &result, body)?;
                    if compiled.is_none()
                        && (matching::has_match(body) || matching::has_written_match(body))
                    {
                        compiled = Some(self.elaborate_at(body, &shaped, Some(&result))?);
                    }
                    let body = compiled.as_ref().unwrap_or(body);
                    let lam = self.lambda_of(&t.params, body)?;
                    let lam = self.shape(&lam)?;
                    let lam = self.elab(&Vec::new(), &lam, Some(&statement))?;
                    self.check_body(&t.name, &lam, &statement)?;
                    Ok::<_, Diagnostic>(lam)
                })();
                self.current = None;
                let proof = match proof {
                    Ok(lam) => match self.uses_failed(&lam) {
                        Some(n) => err(msg!("kernel-uses-failed", name = (n).to_string()), t.span),
                        None => Ok(lam),
                    },
                    // The same when the proof does not check: what it says is
                    // about the stand-in, not the declaration that failed.
                    Err(d) => match self
                        .uses_failed(&statement)
                        .or_else(|| self.uses_failed(body))
                    {
                        Some(n) => Err(after_failed(&n, d)),
                        None => Err(d),
                    },
                };
                match proof {
                    Ok(lam) => {
                        self.collect_axioms(&lam, &mut axioms);
                        checked = Some(lam);
                    }
                    Err(d) => {
                        // Keep the statement for the messages of later proofs.
                        self.add_failed(&t.name, statement);
                        self.set_implicit(&t.name, t.implicit);
                        self.set_params(&t.name, t.params.len());
                        return (Verdict::Failed(d), None);
                    }
                }
            }
        }
        if let Some(n) = self.uses_failed(&statement) {
            self.add_failed(&t.name, statement);
            self.set_implicit(&t.name, t.implicit);
            self.set_params(&t.name, t.params.len());
            return (
                Verdict::Failed(Diagnostic::new(
                    msg!("kernel-uses-failed", name = (n).to_string()),
                    Some(t.span),
                )),
                None,
            );
        }
        let mut uses = self.uses_incomplete(&statement);
        if let Some(lam) = &checked {
            for n in self.uses_incomplete(lam) {
                if !uses.contains(&n) {
                    uses.push(n);
                }
            }
        }
        let mut holes = std::mem::take(&mut self.holes);
        for h in &mut holes {
            h.statement = Some(statement.clone());
            h.params = t.params.iter().map(|(n, _)| n.clone()).collect();
        }
        if !holes.is_empty() || !uses.is_empty() {
            self.add_incomplete(&t.name, statement);
            self.set_implicit(&t.name, t.implicit);
            self.set_params(&t.name, t.params.len());
            return (Verdict::Incomplete { holes, uses }, None);
        }
        let added = if cached {
            self.core
                .add_decl_checked_before(&t.name, &statement, checked.as_ref(), false)
        } else {
            self.core
                .add_decl(&t.name, &statement, checked.as_ref(), false)
        };
        if let Err(m) = added {
            self.add_failed(&t.name, statement);
            self.set_implicit(&t.name, t.implicit);
            self.set_params(&t.name, t.params.len());
            return (Verdict::Failed(core_rejects(&t.name, m, t.span)), None);
        }
        self.add(&t.name, statement, None, axioms.clone());
        self.set_implicit(&t.name, t.implicit);
        self.set_params(&t.name, t.params.len());
        (
            Verdict::Checked {
                axioms: axioms.into_iter().collect(),
            },
            checked,
        )
    }

    fn check_body(&mut self, name: &Name, lam: &T, statement: &T) -> Result<(), Diagnostic> {
        if !self.derivation_names.contains(name) {
            return self.check(&Vec::new(), lam, statement);
        }
        let globals = &self.globals;
        let declared = |n: &Name| globals.get(n).map(|g| g.ty.clone());
        let typed = self
            .core
            .derivation_in(&Vec::new(), lam, statement, &declared, &[name])
            .map_err(|f| self.diagnose(&Vec::new(), lam, *f))?;
        for m in &typed.holes {
            self.met_hole(&Vec::new(), m)?;
        }
        if let Some(tree) = typed.derivation {
            self.derivations
                .as_mut()
                .unwrap()
                .push((name.clone(), tree));
        }
        Ok(())
    }

    /// A sort's name, or `_`, cannot name a declaration.
    fn reserved(&self, name: &str, span: Span) -> Option<Diagnostic> {
        is_reserved(name).then(|| Diagnostic::new(msg!("kernel-reserved", name = name), Some(span)))
    }

    fn set_params(&mut self, name: &Name, n: usize) {
        if let Some(g) = self.globals.get_mut(name) {
            g.params = Some(n);
        }
    }

    fn set_implicit(&mut self, name: &Name, n: usize) {
        if let Some(g) = self.globals.get_mut(name) {
            g.implicit = n;
        }
    }

    /// `mutual { … }`: a group of families, or of functions.
    fn mutual(&mut self, items: &[Stmt], span: Span) -> Vec<Entry> {
        let name_of = |s: &Stmt| match s {
            Stmt::Inductive(i) => i.name.clone(),
            Stmt::Fn(f) => f.name.clone(),
            Stmt::Theorem(t) => t.name.clone(),
            _ => crate::surface::Name::Spelled(String::new()),
        };
        let fail = |items: &[Stmt], message: Message| -> Vec<Entry> {
            items
                .iter()
                .map(|s| Entry {
                    name: name_of(s),
                    verdict: Verdict::Failed(Diagnostic::new(message.clone(), Some(span))),
                })
                .collect()
        };
        if items.is_empty() {
            return vec![Entry {
                name: "mutual".into(),
                verdict: Verdict::Failed(Diagnostic::new(msg!("kernel-mutual-empty"), Some(span))),
            }];
        }
        for s in items {
            let n = name_of(s);
            if self.globals.contains_key(&n) {
                return fail(
                    items,
                    msg!("kernel-already-defined", name = (&n).to_string()),
                );
            }
            if is_reserved(&n) {
                return fail(items, msg!("kernel-reserved", name = (&n).to_string()));
            }
        }
        if items.iter().all(|s| matches!(s, Stmt::Inductive(_))) {
            let decls: Vec<&crate::surface::InductiveDecl> = items
                .iter()
                .filter_map(|s| match s {
                    Stmt::Inductive(i) => Some(i),
                    _ => None,
                })
                .collect();
            let verdict = self.inductive_group(&decls);
            if let Some(d) = decls.iter().find(|d| d.generates.written) {
                return fail(
                    items,
                    msg!("kernel-mutual-decidable", name = (&d.name).to_string()),
                );
            }
            return decls
                .iter()
                .map(|d| Entry {
                    name: d.name.clone(),
                    verdict: verdict.clone(),
                })
                .collect();
        }
        if let Some(entries) = self.shared_steps(items, span) {
            return entries;
        }
        if items
            .iter()
            .all(|s| matches!(s, Stmt::Fn(_) | Stmt::Theorem(_)))
        {
            return match self.inline_plain(items) {
                Ok(None) => self.function_group(items, span),
                Ok(Some((before, matched, plain))) => {
                    let mut entries = Vec::new();
                    for f in before {
                        self.declare_one(&Stmt::Fn(f), false, &mut entries);
                    }
                    entries.extend(self.function_group(&matched, span));
                    for f in plain {
                        self.declare_one(&Stmt::Fn(f), false, &mut entries);
                    }
                    entries
                }
                Err(message) => fail(items, message),
            };
        }
        fail(items, msg!("kernel-mutual-mixed"))
    }

    /// A `mutual` block's functions whose body is not a `match` (a function
    /// that calls the others). Those that reach a `match` of the block are
    /// written out at each of their calls in the block's `match`es; those that
    /// do not are ordinary functions. The result: the ordinary ones, declared
    /// before the block; the block that is left; and the written-out ones,
    /// declared after it. `None` when every body is a `match`, or none is.
    fn inline_plain(
        &mut self,
        items: &[Stmt],
    ) -> Result<Option<(Vec<FnDecl>, Vec<Stmt>, Vec<FnDecl>)>, Message> {
        // A function is by `match` only when it matches on one of its own
        // parameters; a `match` on another term (such as the one an `if`
        // stands for) is a plain body like any other.
        let by_match = |f: &FnDecl| match &*f.body.kind {
            TermKind::Match { scrutinee, .. } => matches!(
                &*scrutinee.kind,
                TermKind::Var(x) if f.params.contains(x)
            ),
            _ => false,
        };
        let is_plain = |s: &Stmt| matches!(s, Stmt::Fn(f) if !by_match(f));
        let plain: Vec<FnDecl> = items
            .iter()
            .filter_map(|s| match s {
                Stmt::Fn(f) if is_plain(s) => Some(f.clone()),
                _ => None,
            })
            .collect();
        if plain.is_empty() || plain.len() == items.len() {
            return Ok(None);
        }
        // Only a function that reaches a `match` of the block needs writing
        // out: its calls hide a recursive call whose argument the `match`
        // has to see. The others are ordinary functions of their own.
        let group: Vec<Name> = items
            .iter()
            .filter(|s| !is_plain(s))
            .filter_map(|s| match s {
                Stmt::Fn(f) => Some(f.name.clone()),
                Stmt::Theorem(t) => Some(t.name.clone()),
                _ => None,
            })
            .collect();
        let mut reaches: Vec<bool> = plain
            .iter()
            .map(|f| group.iter().any(|g| names_anywhere(&f.body, g)))
            .collect();
        loop {
            let next: Vec<bool> = (0..plain.len())
                .map(|i| {
                    reaches[i]
                        || (0..plain.len())
                            .any(|j| reaches[j] && names_anywhere(&plain[i].body, &plain[j].name))
                })
                .collect();
            if next == reaches {
                break;
            }
            reaches = next;
        }
        let mut before: Vec<FnDecl> = Vec::new();
        let mut kept: Vec<FnDecl> = Vec::new();
        for (f, r) in plain.into_iter().zip(&reaches) {
            if *r {
                kept.push(f);
            } else {
                before.push(f);
            }
        }
        // Each ordinary one after the ordinary ones it calls.
        let mut ordered: Vec<FnDecl> = Vec::new();
        while ordered.len() < before.len() {
            let len = ordered.len();
            for f in &before {
                if !ordered.iter().any(|o| o.name == f.name)
                    && before.iter().all(|g| {
                        g.name == f.name
                            || !names_anywhere(&f.body, &g.name)
                            || ordered.iter().any(|o| o.name == g.name)
                    })
                {
                    ordered.push(f.clone());
                }
            }
            if ordered.len() == len {
                // A cycle among them: the first left reaches itself.
                let f = before
                    .iter()
                    .find(|f| !ordered.iter().any(|o| o.name == f.name));
                return Err(msg!(
                    "kernel-mutual-plain-cycle",
                    name = (&f.expect("one is left").name).to_string()
                ));
            }
        }
        let before = ordered;
        let plain = kept;
        if plain.is_empty() {
            let rest = items.iter().filter(|s| !is_plain(s)).cloned().collect();
            return Ok(Some((before, rest, Vec::new())));
        }
        if let Some(f) = plain.iter().find(|f| !f.generics.is_empty()) {
            return Err(msg!(
                "kernel-mutual-plain-generics",
                name = (&f.name).to_string()
            ));
        }
        let names: Vec<Name> = plain.iter().map(|f| f.name.clone()).collect();
        // The plain functions' calls among themselves have no cycle: a
        // recursion goes through a `match`, and writing out the calls ends.
        let calls: Vec<Vec<usize>> = plain
            .iter()
            .map(|f| {
                (0..plain.len())
                    .filter(|&j| mentions(&f.body, &names[j]))
                    .collect()
            })
            .collect();
        fn cycle(at: usize, calls: &[Vec<usize>], path: &mut Vec<usize>) -> Option<usize> {
            if path.contains(&at) {
                return Some(at);
            }
            path.push(at);
            let found = calls[at].iter().find_map(|&j| cycle(j, calls, path));
            path.pop();
            found
        }
        for i in 0..plain.len() {
            if let Some(j) = cycle(i, &calls, &mut Vec::new()) {
                return Err(msg!(
                    "kernel-mutual-plain-cycle",
                    name = (&names[j]).to_string()
                ));
            }
        }
        self.written_out_size(items, &plain, &calls)?;
        let bodies: Vec<T> = plain.iter().map(|f| f.body.clone()).collect();
        let mut matched = Vec::new();
        for s in items {
            match s {
                Stmt::Fn(_) if is_plain(s) => {}
                Stmt::Fn(f) => {
                    let (body, _) = self.write_out_calls(&f.body, &plain, &bodies);
                    if let Some(n) = names.iter().find(|n| mentions(&body, n)) {
                        return Err(msg!(
                            "kernel-mutual-plain-partial",
                            name = (n).to_string(),
                            user = (&f.name).to_string()
                        ));
                    }
                    let mut f = f.clone();
                    f.body = body;
                    matched.push(Stmt::Fn(f));
                }
                other => matched.push(other.clone()),
            }
        }
        // Each is declared after the ones it calls.
        let mut order: Vec<usize> = Vec::new();
        while order.len() < plain.len() {
            for i in 0..plain.len() {
                if !order.contains(&i) && calls[i].iter().all(|j| *j == i || order.contains(j)) {
                    order.push(i);
                }
            }
        }
        let plain = order.into_iter().map(|i| plain[i].clone()).collect();
        Ok(Some((before, matched, plain)))
    }

    /// Fails when writing out the calls of `plain` would make the block's
    /// bodies more than `WRITTEN_OUT_GROWTH` times as large as written: the
    /// copies multiply when a written-out function calls another more than
    /// once. `calls[i]` are the functions of `plain` that `plain[i]` calls.
    fn written_out_size(
        &self,
        items: &[Stmt],
        plain: &[FnDecl],
        calls: &[Vec<usize>],
    ) -> Result<(), Message> {
        // The number of nodes of `t`, and how often it calls each of `plain`.
        let count = |t: &T| -> (u128, Vec<u128>) {
            let mut t = t.clone();
            let mut size = 0u128;
            let mut direct = vec![0u128; plain.len()];
            crate::surface::walk::term(&mut t, &mut |u| {
                size += 1;
                if let TermKind::App {
                    function,
                    arguments,
                } = &*u.kind
                    && let TermKind::Var(g) = &*function.kind
                    && let Some(i) = plain
                        .iter()
                        .position(|f| &f.name == g && f.params.len() == arguments.len())
                {
                    direct[i] += 1;
                }
            });
            (size, direct)
        };
        let counted: Vec<(u128, Vec<u128>)> = plain.iter().map(|f| count(&f.body)).collect();
        // Written out: each function's size and the copies of each other
        // function in it, callees first (the calls have no cycle).
        let mut size: Vec<Option<u128>> = vec![None; plain.len()];
        let mut copies: Vec<Vec<u128>> = vec![vec![0; plain.len()]; plain.len()];
        while size.iter().any(Option::is_none) {
            for i in 0..plain.len() {
                if size[i].is_some() || calls[i].iter().any(|&j| j != i && size[j].is_none()) {
                    continue;
                }
                let (own, direct) = &counted[i];
                let mut total = *own;
                let mut c = direct.clone();
                for j in 0..plain.len() {
                    if direct[j] > 0 && j != i {
                        total =
                            total.saturating_add(direct[j].saturating_mul(size[j].unwrap_or(0)));
                        for k in 0..plain.len() {
                            c[k] = c[k].saturating_add(direct[j].saturating_mul(copies[j][k]));
                        }
                    }
                }
                size[i] = Some(total);
                copies[i] = c;
            }
        }
        let mut written = 0u128;
        let mut out = 0u128;
        let mut most = vec![0u128; plain.len()];
        for f in plain {
            written = written.saturating_add(count(&f.body).0);
        }
        for s in items {
            let Stmt::Fn(f) = s else { continue };
            if plain.iter().any(|p| p.name == f.name) {
                continue;
            }
            let (own, direct) = count(&f.body);
            written = written.saturating_add(own);
            out = out.saturating_add(own);
            for j in 0..plain.len() {
                out = out.saturating_add(direct[j].saturating_mul(size[j].unwrap_or(0)));
                most[j] = most[j].saturating_add(direct[j]);
                for k in 0..plain.len() {
                    most[k] = most[k].saturating_add(direct[j].saturating_mul(copies[j][k]));
                }
            }
        }
        if out <= written.saturating_mul(WRITTEN_OUT_GROWTH) {
            return Ok(());
        }
        let (j, times) = most
            .iter()
            .enumerate()
            .max_by_key(|(_, n)| **n)
            .expect("a function is written out");
        Err(msg!(
            "kernel-mutual-plain-too-large",
            name = (&plain[j].name).to_string(),
            times = times.to_string(),
            growth = (out / written.max(1)).to_string()
        ))
    }

    /// `t` with each call `f(a, …)` of a function of `plain` given all its
    /// arguments replaced by `f`'s body (from `bodies`) with the arguments
    /// for the parameters; and whether anything was replaced.
    fn write_out_calls(&mut self, t: &T, plain: &[FnDecl], bodies: &[T]) -> (T, bool) {
        let mut t = t.clone();
        let mut changed = false;
        // A body that is itself a call is written out in turn; the calls have
        // no cycle (`inline_plain`).
        crate::surface::walk::term(&mut t, &mut |u| loop {
            let TermKind::App {
                function,
                arguments,
            } = &*u.kind
            else {
                return;
            };
            let TermKind::Var(g) = &*function.kind else {
                return;
            };
            let Some(i) = plain
                .iter()
                .position(|f| &f.name == g && f.params.len() == arguments.len())
            else {
                return;
            };
            // Through fresh names, so an argument that mentions another
            // parameter is not replaced again.
            let fresh: Vec<Name> = plain[i].params.iter().map(|p| self.fresh_name(p)).collect();
            let mut b = bodies[i].clone();
            for (p, x) in plain[i].params.iter().zip(&fresh) {
                b = self.subst(&b, p, &T::new(TermKind::Var(x.clone()), u.span));
            }
            for (x, a) in fresh.iter().zip(arguments) {
                b = self.subst(&b, x, a);
            }
            *u = b;
            changed = true;
        });
        (t, changed)
    }

    /// The functions (or theorems) of a `mutual` block, each defined by a
    /// `match`; their calls to each other become eliminator recursion.
    fn function_group(&mut self, items: &[Stmt], span: Span) -> Vec<Entry> {
        // (name, params, result, body)
        type Decl = (Name, usize, Vec<(Name, T)>, T, T);
        let mut decls: Vec<Decl> = Vec::new();
        for s in items {
            match s {
                Stmt::Fn(f) => {
                    let Some(result) = &f.result else {
                        return self.group_fail(items, span, msg!("kernel-mutual-result-type"));
                    };
                    let mut params = generic_params(f);
                    for (n, t) in f.params.iter().zip(&f.param_types) {
                        let Some(t) = t else {
                            return self.group_fail(items, span, msg!("kernel-mutual-param-typed"));
                        };
                        params.push((n.clone(), t.clone()));
                    }
                    if f.effects.as_ref().is_some_and(|e| !e.is_empty()) {
                        return self.group_fail(items, span, msg!("kernel-mutual-no-effects"));
                    }
                    decls.push((
                        f.name.clone(),
                        f.generics.len(),
                        params,
                        result.clone(),
                        f.body.clone(),
                    ));
                }
                Stmt::Theorem(t) => {
                    let Some(body) = &t.body else {
                        return self.group_fail(items, span, msg!("kernel-mutual-theorem-proof"));
                    };
                    decls.push((
                        t.name.clone(),
                        t.implicit,
                        t.params.clone(),
                        t.ty.clone(),
                        body.clone(),
                    ));
                }
                _ => unreachable!(),
            }
        }
        // A mutual call instantiates the common implicit telescope by position.
        // Keep value parameters separate, while sharing the group's type binders.
        let common: Vec<Name> = decls
            .first()
            .map(|decl| {
                decl.2
                    .iter()
                    .take(decl.1)
                    .map(|(name, _)| name.clone())
                    .collect()
            })
            .unwrap_or_default();
        for (_, implicit, params, result, body) in &mut decls {
            let substitutions: HashMap<_, _> = params
                .iter()
                .take(*implicit)
                .zip(&common)
                .map(|((name, _), common)| (name.clone(), common.clone()))
                .collect();
            let mut replace = |name: &mut Name| {
                if let Some(common) = substitutions.get(name) {
                    *name = common.clone();
                }
            };
            for (name, ty) in params {
                replace(name);
                crate::surface::references::term(ty, &mut replace);
            }
            crate::surface::references::term(result, &mut replace);
            crate::surface::references::term(body, &mut replace);
        }
        let names: Vec<Name> = decls.iter().map(|d| d.0.clone()).collect();
        let key = self.key(items, &names);
        let base = self
            .record_sites
            .then(|| cache::place_base(&format!("{items:?}")));
        let mark = self.ctor_sites.len();
        let app_mark = self.application_sites.len();
        let field_mark = self.field_sites.len();
        let mut cached_sites = None;
        let mut cached_apps = None;
        let mut cached_fields = None;
        let before = key.as_ref().and_then(|k| {
            let cache = self.cache.as_ref()?;
            let terms = cache.get_terms(k, span)?;
            if let Some(base) = base {
                cached_sites = Some(cache.get_sites(k, base)?);
                cached_apps = Some(cache.get_applications(k, base)?);
                cached_fields = Some(cache.get_fields(k, base)?);
            }
            (terms.len() == decls.len()).then_some(terms)
        });
        let mut hit = before.is_some();
        let mut before = before;
        let mut build = || {
            let before = before.take();
            let mut statements = Vec::new();
            let mut shaped = Vec::new();
            for (_, _, params, result, _) in &decls {
                let statement = self.telescope(params, result)?;
                let statement = self.shape_type(&statement, &[])?;
                let statement = self.elab(&Vec::new(), &statement, None)?;
                self.expect_type(&Vec::new(), &statement)?;
                statements.push(statement);
                shaped.push(self.shaped_signature(params, result)?);
            }
            // Checked before by this checker (`check/cache.rs`): the core
            // takes it as checked, as a theorem's proof is.
            if let Some(lams) = before {
                for (st, lam) in statements.iter().zip(&lams) {
                    if let Some(n) = self.uses_failed(lam).or_else(|| self.uses_failed(st)) {
                        return err(msg!("kernel-uses-failed", name = (n).to_string()), span);
                    }
                }
                for ((name, ..), (st, lam)) in decls.iter().zip(statements.iter().zip(&lams)) {
                    if let Err(m) = self.core.add_decl_checked_before(name, st, Some(lam), true) {
                        for (other, ..) in &decls {
                            self.core.forget(other);
                        }
                        return Err(core_rejects(name, m, span));
                    }
                }
                return Ok::<_, Diagnostic>((statements, lams));
            }
            // `let`s in the bodies unfold as in a single function's body.
            let bodies = decls
                .iter()
                .map(|d| self.expand_lets(&d.4))
                .collect::<Result<Vec<_>, _>>()?;
            let specs: Vec<matching::FnSpec> = decls
                .iter()
                .zip(&bodies)
                .zip(&shaped)
                .map(
                    |(((name, implicit, _, _, _), body), (params, result))| matching::FnSpec {
                        name: Some(name),
                        implicit: *implicit,
                        params: params.clone(),
                        result: result.clone(),
                        body,
                    },
                )
                .collect();
            let compiled = self.compile_group(&specs)?;
            let mut lams = Vec::new();
            for (((name, _, params, _, _), c), statement) in
                decls.iter().zip(&compiled).zip(&statements)
            {
                let lam = self.lambda_of(params, c)?;
                let lam = self.shape(&lam)?;
                let lam = self.elab(&Vec::new(), &lam, Some(statement))?;
                self.check_body(name, &lam, statement)?;
                if !self.holes.is_empty() {
                    return err(msg!("kernel-mutual-hole"), span);
                }
                if let Some(n) = self
                    .uses_failed(&lam)
                    .or_else(|| self.uses_failed(statement))
                {
                    return err(msg!("kernel-uses-failed", name = (n).to_string()), span);
                }
                lams.push(lam);
            }
            for ((name, ..), (st, lam)) in decls.iter().zip(statements.iter().zip(&lams)) {
                if let Err(m) = self.core.add_decl(name, st, Some(lam), true) {
                    return Err(core_rejects(name, m, span));
                }
            }
            Ok::<_, Diagnostic>((statements, lams))
        };
        let mut built = build();
        if hit && built.is_err() {
            // What the cache held does not check: it is elaborated again.
            hit = false;
            built = build();
        }
        match built {
            Err(d) => {
                // A declaration that did not check is the cause, not the
                // error its stand-in type makes here.
                let d = match decls.iter().find_map(|(_, _, params, result, body)| {
                    params
                        .iter()
                        .find_map(|(_, t)| self.uses_failed(t))
                        .or_else(|| self.uses_failed(result))
                        .or_else(|| self.uses_failed(body))
                }) {
                    Some(n) if !says(&d.message, USES_FAILED) => after_failed(&n, d),
                    _ => d,
                };
                // Keep the statements for the messages of later proofs, read
                // as a single theorem's is (its generics given), so that a
                // later use meets the statement written.
                for (name, implicit, params, result, _) in &decls {
                    let st = self.telescope(params, result).and_then(|t| {
                        let t = self.shape_type(&t, &[])?;
                        self.elab(&Vec::new(), &t, None)
                    });
                    let st =
                        st.or_else(|_| self.telescope(params, result).and_then(|t| self.shape(&t)));
                    if let Ok(st) = st {
                        self.add_failed(name, st);
                        self.set_implicit(name, *implicit);
                        self.set_params(name, params.len());
                    }
                }
                items
                    .iter()
                    .map(|s| Entry {
                        name: match s {
                            Stmt::Fn(f) => f.name.clone(),
                            Stmt::Theorem(t) => t.name.clone(),
                            _ => crate::surface::Name::Spelled(String::new()),
                        },
                        verdict: Verdict::Failed(d.clone()),
                    })
                    .collect()
            }
            Ok((statements, lams)) => {
                if let (Some(key), Some(cache), false) = (&key, &self.cache, hit)
                    && !self.core.budget_out()
                {
                    cache.put_terms(key, &lams.iter().collect::<Vec<_>>());
                    if let Some(base) = base {
                        cache.put_sites(key, &self.ctor_sites[mark..], base);
                        cache.put_applications(key, &self.application_sites[app_mark..], base);
                        cache.put_fields(key, &self.field_sites[field_mark..], base);
                    }
                }
                if hit && let Some(sites) = cached_sites {
                    self.ctor_sites.extend(sites);
                    self.application_sites
                        .extend(cached_apps.unwrap_or_default());
                    self.field_sites.extend(cached_fields.unwrap_or_default());
                }
                let mut out = Vec::new();
                for ((name, implicit, params, ..), (st, lam)) in
                    decls.iter().zip(statements.into_iter().zip(lams))
                {
                    let mut axioms = BTreeSet::new();
                    self.collect_axioms(&lam, &mut axioms);
                    self.add(name, st, Some(lam), axioms.clone());
                    // Like a single function's: callers outside the group
                    // leave the generics out.
                    self.set_implicit(name, *implicit);
                    self.set_params(name, params.len());
                    out.push(Entry {
                        name: name.clone(),
                        verdict: Verdict::Checked {
                            axioms: axioms.into_iter().collect(),
                        },
                    });
                }
                out
            }
        }
    }

    fn group_fail(&self, items: &[Stmt], span: Span, message: Message) -> Vec<Entry> {
        items
            .iter()
            .map(|s| Entry {
                name: match s {
                    Stmt::Fn(f) => f.name.clone(),
                    Stmt::Theorem(t) => t.name.clone(),
                    _ => crate::surface::Name::Spelled(String::new()),
                },
                verdict: Verdict::Failed(Diagnostic::new(message.clone(), Some(span))),
            })
            .collect()
    }

    /// `def`: a transparent definition whose body is a type; it unfolds to
    /// the term that was checked.
    fn definition(&mut self, t: &TheoremDecl) -> Verdict {
        let (verdict, checked) = self.theorem_term(t, false);
        // A body that is a `match` or a block stays opaque. A field
        // (`x.f`) or a dotted eliminator (`T::rec`) is read before the
        // kernel sees it, so it does not make the body opaque.
        let plain = t.body.as_ref().is_some_and(|b| {
            let mut b = b.clone();
            fields_as_names(&mut b);
            self.lambda_of(&t.params, &b)
                .and_then(|l| self.shape(&l))
                .is_ok()
        });
        if let Some(lam) = checked
            && plain
            && self.core.set_value(&t.name, &lam).is_ok()
            && let Some(g) = self.globals.get_mut(&t.name)
        {
            g.value = Some(lam);
        }
        verdict
    }

    fn function(&mut self, f: &FnDecl) -> Verdict {
        // A function with effects is read as a function of the kernel
        // (`check/effects.rs`), and its bare name is that function's value.
        if !self.effects.fns.contains_key(&f.name) {
            self.fns.insert(f.name.clone());
        }
        let mut verdict = self.function_term(f);
        if let Verdict::Failed(_) = &verdict {
            let mut uses = None;
            crate::surface::walk::term(&mut f.body.clone(), &mut |term| {
                if let TermKind::Var(name) = &*term.kind
                    && uses.is_none()
                    && (self.skipped.contains(name)
                        || matches!(self.ahead.get(name), Some(Ahead::Skipped(_))))
                {
                    uses = Some(name.to_string());
                }
            });
            if let Some(n) = uses {
                verdict = Verdict::Skipped(msg!("kernel-uses-skipped", name = n));
            }
        }
        if let Verdict::Skipped(_) = verdict {
            self.skipped.insert(f.name.clone());
        }
        verdict
    }

    fn function_term(&mut self, f: &FnDecl) -> Verdict {
        if f.effects.as_ref().is_some_and(|e| !e.is_empty()) {
            // A function with effects is a term of the proof language only as
            // `check/effects.rs` reads it.
            let why = self
                .effects
                .skipped
                .get(&f.name)
                .cloned()
                .unwrap_or_else(|| Message::text(""));
            return Verdict::Skipped(msg!("kernel-has-effects", why = why));
        }
        // The kernel reads a function type without its row, so calling such a
        // parameter would be read as pure. Only `check/effects.rs` reads one
        // with its effects; otherwise the function is executable code, and
        // its row is checked as written.
        if !self.effects.handling.contains(&f.name)
            && let Some(p) = f
                .params
                .iter()
                .zip(&f.param_types)
                .map(|(n, t)| (n, t.as_ref()))
                .chain(
                    f.generics
                        .iter()
                        .zip(&f.generic_types)
                        .map(|(n, t)| (n, Some(t))),
                )
                .chain(std::iter::once((&f.name, f.result.as_ref())))
                .find_map(|(n, t)| t.filter(|t| has_effect_row(t)).map(|_| n))
        {
            return Verdict::Skipped(if *p == f.name {
                msg!("kernel-result-effect-row")
            } else {
                msg!("kernel-param-effect-row", name = (p).to_string())
            });
        }
        let Some(result) = &f.result else {
            return Verdict::Skipped(msg!("kernel-no-result-type"));
        };
        let mut params = generic_params(f);
        for (n, t) in f.params.iter().zip(&f.param_types) {
            match t {
                Some(t) => params.push((n.clone(), t.clone())),
                None => return Verdict::Skipped(msg!("kernel-untyped-param")),
            }
        }
        let decl = TheoremDecl {
            budget: None,
            vis: Default::default(),
            name: f.name.clone(),
            implicit: f.generics.len(),
            params,
            ty: result.clone(),
            body: Some(f.body.clone()),
            decreasing_by: f.decreasing_by.clone().filter(|y| names_param(f, y)),
            span: f.body.span,
        };
        // A value that nothing uses is not executable code: it is never run
        // and its type is never checked, so a body with one is refused
        // rather than skipped, once the signature is the kernel's.
        let mut refused = None;
        let body = match self.expand_lets(&f.body) {
            Ok(b) => b,
            Err(d) => {
                if never_checked(&d) {
                    refused = Some(d);
                }
                f.body.clone()
            }
        };
        if refused.is_none() && !matching::has_match(&body) && self.shape(&body).is_err() {
            return Verdict::Skipped(msg!("kernel-body-executable"));
        }
        // A type only executable code has (the syntax types of a macro, say).
        let signature = self
            .telescope(&decl.params, &decl.ty)
            .and_then(|t| self.shape(&t))
            .and_then(|t| self.elab(&Vec::new(), &t, None))
            .and_then(|t| self.expect_type(&Vec::new(), &t));
        if let Err(d) = signature
            && says(&d.message, NOT_DEFINED)
        {
            return Verdict::Skipped(msg!("kernel-type-not-kernel"));
        }
        if let Some(d) = refused {
            return Verdict::Failed(d);
        }
        let key = self.key(&[Stmt::Fn(f.clone())], &[f.name.clone()]);
        let base = self
            .record_sites
            .then(|| cache::place_base(&format!("{f:?}")));
        let mark = self.ctor_sites.len();
        let app_mark = self.application_sites.len();
        let field_mark = self.field_sites.len();
        let mut cached_sites = None;
        let mut cached_apps = None;
        let mut cached_fields = None;
        let before = key.as_ref().and_then(|k| {
            let cache = self.cache.as_ref()?;
            let mut terms = cache.get_terms(k, f.body.span)?;
            if let Some(base) = base {
                cached_sites = Some(cache.get_sites(k, base)?);
                cached_apps = Some(cache.get_applications(k, base)?);
                cached_fields = Some(cache.get_fields(k, base)?);
            }
            (terms.len() == 1).then(|| terms.pop()).flatten()
        });
        let mut hit = before.is_some();
        let (mut verdict, mut checked) = self.theorem_term_from(&decl, false, before);
        if hit && checked.is_none() {
            // What the cache held does not check: it is elaborated again.
            hit = false;
            self.globals.remove(&f.name);
            (verdict, checked) = self.theorem_term(&decl, false);
        }
        if let (Some(key), Some(lam), Some(cache), false) = (&key, &checked, &self.cache, hit)
            && !self.core.budget_out()
        {
            cache.put_terms(key, &[lam]);
            if let Some(base) = base {
                cache.put_sites(key, &self.ctor_sites[mark..], base);
                cache.put_applications(key, &self.application_sites[app_mark..], base);
                cache.put_fields(key, &self.field_sites[field_mark..], base);
            }
        }
        if hit
            && checked.is_some()
            && let Some(sites) = cached_sites
        {
            self.ctor_sites.extend(sites);
            self.application_sites
                .extend(cached_apps.unwrap_or_default());
            self.field_sites.extend(cached_fields.unwrap_or_default());
        }
        if let Some(lam) = checked
            && self.core.set_value(&f.name, &lam).is_ok()
            && let Some(g) = self.globals.get_mut(&f.name)
        {
            g.value = Some(lam);
        }
        verdict
    }

    fn constant(&mut self, name: &Name, value: &T) -> Verdict {
        if let Some(d) = self.reserved(name, value.span) {
            return Verdict::Failed(d);
        }
        let result = self.shape(value).and_then(|v| {
            let ty = self.infer(&Vec::new(), &v)?;
            if let Some(n) = self.uses_failed(&v) {
                return err(msg!("kernel-uses-failed", name = (n).to_string()), v.span);
            }
            if let Err(m) = self.core.add_constant(name, &v) {
                return Err(core_rejects(name, m, v.span));
            }
            Ok((v, ty))
        });
        match result {
            Ok((v, ty)) => {
                let mut axioms = BTreeSet::new();
                self.collect_axioms(&v, &mut axioms);
                self.add(name, ty, Some(v), axioms.clone());
                Verdict::Checked {
                    axioms: axioms.into_iter().collect(),
                }
            }
            Err(d) => match NOT_KERNEL_TERM.contains(&d.message.id.as_ref()) {
                true => Verdict::Skipped(d.message),
                false => Verdict::Failed(d),
            },
        }
    }

    fn add(&mut self, name: &Name, ty: T, value: Option<T>, axioms: BTreeSet<Name>) {
        self.globals.insert(
            name.into(),
            Global {
                ty,
                value,
                axioms,
                implicit: 0,
                params: None,
                failed: false,
                incomplete: false,
            },
        );
    }

    /// Keeps the statement of a declaration with a hole, marked so that a
    /// later declaration using it is incomplete too.
    fn add_incomplete(&mut self, name: &Name, ty: T) {
        self.add(name, ty, None, BTreeSet::new());
        if let Some(g) = self.globals.get_mut(name) {
            g.incomplete = true;
        }
    }

    /// The incomplete declarations `t` mentions, in the order met.
    fn uses_incomplete(&self, t: &T) -> Vec<Name> {
        let mut found = Vec::new();
        visit_vars(t, &mut |n| {
            if self.globals.get(n).is_some_and(|g| g.incomplete) && !found.iter().any(|f| f == n) {
                found.push(n.clone());
            }
        });
        found
    }

    /// Keeps the statement of a declaration that did not check, marked so
    /// that a later declaration using it fails too.
    fn add_failed(&mut self, name: &Name, ty: T) {
        self.add(name, ty, None, BTreeSet::new());
        if let Some(g) = self.globals.get_mut(name) {
            g.failed = true;
        }
    }

    /// A declaration that did not check and that `t` mentions.
    fn uses_failed(&self, t: &T) -> Option<Name> {
        let mut found = None;
        visit_vars(t, &mut |n| {
            if found.is_none() && self.globals.get(n).is_some_and(|g| g.failed) {
                found = Some(n.clone());
            }
        });
        found
    }

    fn collect_axioms(&self, t: &T, out: &mut BTreeSet<Name>) {
        let mut uses = BTreeSet::new();
        self.collect_globals(t, &mut uses);
        for n in uses {
            out.extend(self.globals[&n].axioms.iter().cloned());
        }
    }

    /// The globals `t` names, where `collect_axioms` looks for them.
    fn collect_globals(&self, t: &T, out: &mut BTreeSet<Name>) {
        match &*t.kind {
            TermKind::Var(n) => {
                if self.globals.contains_key(n) {
                    out.insert(n.clone());
                }
            }
            TermKind::App { .. } => {
                t.for_each_in_applications(|part| self.collect_globals(part, out))
            }
            TermKind::Pi { params, result, .. } => {
                for (_, d) in params {
                    self.collect_globals(d, out);
                }
                self.collect_globals(result, out);
            }
            TermKind::Lam { body, .. } => self.collect_globals(body, out),
            _ => {}
        }
    }

    /// `(x: A, y: B) -> T` as nested `Pi`.
    fn telescope(&mut self, params: &[(Name, T)], result: &T) -> Result<T, Diagnostic> {
        let (params, result) = self.elaborate_signature(params, result)?;
        let mut acc = result;
        for (n, d) in params.into_iter().rev() {
            acc = pi(&n, d, acc);
        }
        Ok(acc)
    }

    /// `params` and `result` with the `match`es and field projections
    /// (`p.fst`) written in them compiled, each against the parameters
    /// before it, as in a body: the kernel gets the same eliminator.
    fn elaborate_signature(
        &mut self,
        params: &[(Name, T)],
        result: &T,
    ) -> Result<(Vec<(Name, T)>, T), Diagnostic> {
        if !params.iter().any(|(_, d)| has_match_in_type(d)) && !has_match_in_type(result) {
            return Ok((params.to_vec(), result.clone()));
        }
        let mut ctx: Ctx = Vec::new();
        let mut out = Vec::new();
        for (n, d) in params {
            let d = self.elaborate_type(d, &ctx)?;
            ctx.push((n.clone(), self.kernel_type(&ctx, &d)?));
            out.push((n.clone(), d));
        }
        let result = self.elaborate_type(result, &ctx)?;
        Ok((out, result))
    }

    /// A type, through its `∀`s, with its matches compiled
    /// ([`Self::elaborate_signature`]).
    fn elaborate_type(&mut self, t: &T, ctx: &[(Name, T)]) -> Result<T, Diagnostic> {
        match &*t.kind {
            TermKind::Pi {
                params,
                result,
                effects,
            } if has_match_in_type(t) => {
                let mut inner = ctx.to_vec();
                let mut out = Vec::new();
                for (n, d) in params {
                    let d = self.elaborate_type(d, &inner)?;
                    // An unnamed binder still enters the context the
                    // match is compiled in, so it gets a name nothing
                    // written can mean; `_` is not a variable.
                    let name = match n {
                        Some(n) if n.spelling() != Some("_") => n.clone(),
                        _ => self.fresh_name("arg"),
                    };
                    inner.push((name.clone(), self.kernel_type(&inner, &d)?));
                    out.push((Some(name), d));
                }
                let mark = self.arrow_binders.len();
                self.arrow_binders
                    .extend(inner[ctx.len()..].iter().map(|(n, _)| n.clone()));
                let result = self.elaborate_type(result, &inner);
                self.arrow_binders.truncate(mark);
                Ok(T::new(
                    TermKind::Pi {
                        params: out,
                        result: Box::new(result?),
                        effects: effects.clone(),
                    },
                    t.span,
                ))
            }
            _ if has_match_in_type(t) => self.elaborate(t, ctx),
            _ => Ok(t.clone()),
        }
    }

    /// `d` as the kernel reads it under `ctx`.
    fn kernel_type(&mut self, ctx: &[(Name, T)], d: &T) -> Result<T, Diagnostic> {
        let mut typing: Ctx = self.defining.clone();
        typing.extend(ctx.iter().cloned());
        let d = self.shape(d)?;
        self.elab(&typing, &d, None)
    }

    /// The parameters and the result type, shaped and with their implicit
    /// arguments written out.
    fn shaped_signature(
        &mut self,
        params: &[(Name, T)],
        result: &T,
    ) -> Result<(Vec<(Name, T)>, T), Diagnostic> {
        let (params, result) = self.elaborate_signature(params, result)?;
        let (params, result) = (&params, &result);
        let mut ctx: Ctx = Vec::new();
        for (n, d) in params {
            let d = self.shape_type(d, &ctx)?;
            let d = self.elab(&ctx, &d, None)?;
            ctx.push((n.clone(), d));
        }
        let result = self.shape_type(result, &ctx)?;
        let result = self.elab(&ctx, &result, None)?;
        Ok((ctx, result))
    }

    /// `shape` for a type, compiling a `match` or `a == b` written in it against the
    /// parameters in `ctx`.
    pub(super) fn shape_type(&mut self, t: &T, ctx: &[(Name, T)]) -> Result<T, Diagnostic> {
        match matching::has_written_match(t) || matching::has_equality(t) {
            true => self.elaborate(t, ctx),
            false => self.shape(t),
        }
    }

    fn lambda_of(&self, params: &[(Name, T)], body: &T) -> Result<T, Diagnostic> {
        let mut acc = body.clone();
        for (n, _) in params.iter().rev() {
            acc = lam(n, acc);
        }
        Ok(acc)
    }

    /// Curries multi-parameter binders and rejects syntax the kernel does
    /// not read.
    fn shape(&self, t: &T) -> Result<T, Diagnostic> {
        let sp = t.span;
        Ok(match &*t.kind {
            TermKind::Var(_) | TermKind::Nat(_) | TermKind::Bool(_) | TermKind::Hole(_) => {
                t.clone()
            }
            // In a loop along the last arguments (`map_applications`).
            TermKind::App { .. } => t.map_applications(false, |a| self.shape(a))?,
            TermKind::Pi { params, result, .. } => {
                let mut acc = self.shape(result)?;
                for (n, d) in params.iter().rev() {
                    let name = n.clone().unwrap_or_else(|| "_".into());
                    acc = pi(&name, self.shape(d)?, acc);
                    acc.span = sp;
                }
                acc
            }
            TermKind::Lam {
                params,
                body,
                types,
            } => {
                let mut acc = self.shape(body)?;
                for (i, n) in params.iter().enumerate().rev() {
                    // The written type stays on the λ until `elab` meets the
                    // type it is given, and holds it to that.
                    let ty = match types.get(i) {
                        Some(Some(ty)) => vec![Some(self.shape(ty)?)],
                        _ => Vec::new(),
                    };
                    acc = T::new(
                        TermKind::Lam {
                            params: vec![n.clone()],
                            body: Box::new(acc),
                            types: ty,
                        },
                        sp,
                    );
                }
                acc
            }
            // `∃ x: D. P` is the prelude's `Exists(D, x => P)`.
            TermKind::Exists {
                binder,
                domain,
                body,
            } => T::new(
                TermKind::App {
                    function: Box::new(T::var(
                        &tauto_surface::bindings::library_name("Exists"),
                        sp,
                    )),
                    arguments: vec![
                        self.shape(domain)?,
                        T::new(
                            TermKind::Lam {
                                params: vec![binder.clone()],
                                body: Box::new(self.shape(body)?),
                                types: vec![Some(self.shape(domain)?)],
                            },
                            sp,
                        ),
                    ],
                },
                sp,
            ),
            // `f(<x: v>, h)`: the implicit arguments named, which the
            // elaborator places by the generics' names.
            TermKind::Record { name, fields, base: None }
                if name.spelling() == Some(tauto_surface::IMPLICITS) =>
            {
                T::new(
                    TermKind::Record {
                        name: name.clone(),
                        fields: fields
                            .iter()
                            .map(|(f, v)| Ok((f.clone(), self.shape(v)?)))
                            .collect::<Result<_, Diagnostic>>()?,
                        base: None,
                    },
                    sp,
                )
            }
            TermKind::Match { .. } => {
                return err(msg!("kernel-not-kernel-term-match"), sp);
            }
            TermKind::Text(_)
                if !self
                    .inds
                    .contains_key(&tauto_surface::bindings::library_name("Text")) =>
            {
                return err(msg!("kernel-not-kernel-term-text"), sp);
            }
            // What the surface reader refused (`a = b = c`) says why.
            TermKind::Other(what) if what.starts_with('`') => {
                return err(Message::text(what.clone()), sp);
            }
            other => {
                return err(
                    msg!("kernel-not-kernel-term-kind", kind = kind_name(other)),
                    sp,
                );
            }
        })
    }

    /// Unfolds `{ let x: T = e … value }` in a proof term: every `x` becomes
    /// `the(T, e)`, which the kernel types as `T` only if `e : T`. The kernel
    /// sees no `let`; the annotation is checked where it is written.
    fn expand_lets(&mut self, t: &T) -> Result<T, Diagnostic> {
        let sp = t.span;
        let expanded = match &*t.kind {
            TermKind::Block(stmts) => {
                let Some((Stmt::Expr(last), lets)) = stmts.split_last() else {
                    return err(msg!("kernel-block-value"), sp);
                };
                let mut body = self.expand_lets(last)?;
                for stmt in lets.iter().rev() {
                    let Stmt::Let {
                        name,
                        ty,
                        value,
                        borrow: false,
                        ..
                    } = stmt
                    else {
                        // A value nothing uses would never have its type checked.
                        if let Stmt::Expr(discarded) = stmt {
                            return err(msg!("kernel-statement-discarded"), discarded.span);
                        }
                        return err(msg!("kernel-block-lets"), sp);
                    };
                    let value = self.expand_lets(value)?;
                    let vsp = value.span;
                    // Without a type, the value stands for the name as it is.
                    let annotated = match ty {
                        Some(ty) => T::new(
                            TermKind::App {
                                function: Box::new(T::var(
                                    &tauto_surface::bindings::library_name("the"),
                                    vsp,
                                )),
                                arguments: vec![self.expand_lets(ty)?, value],
                            },
                            vsp,
                        ),
                        None => value,
                    };
                    // The holes in the body see the name in their context.
                    for hole in holes_in(&body) {
                        self.hole_lets
                            .entry(hole)
                            .or_default()
                            .insert(0, (name.clone(), annotated.clone()));
                    }
                    let next = self.subst(&body, name, &annotated);
                    // A body with a hole may still use the name: the hole is written later.
                    if next == body && !has_hole(&body) {
                        // An unused `let` would never have its type checked.
                        return err(msg!("kernel-let-unused", name = (name).to_string()), vsp);
                    }
                    body = next;
                }
                body
            }
            // In a loop along the last arguments (`map_applications`).
            TermKind::App { .. } => t.map_applications(true, |a| self.expand_lets(a))?,
            TermKind::Lam {
                params,
                body,
                types,
                ..
            } => T::new(
                TermKind::Lam {
                    params: params.clone(),
                    body: Box::new(self.expand_lets(body)?),
                    types: types
                        .iter()
                        .map(|ty| ty.as_ref().map(|ty| self.expand_lets(ty)).transpose())
                        .collect::<Result<_, _>>()?,
                },
                sp,
            ),
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } => T::new(
                TermKind::Match {
                    binder: binder.clone(),
                    scrutinee: scrutinee.clone(),
                    result: match result {
                        Some(r) => Some(Box::new(self.expand_lets(r)?)),
                        None => None,
                    },
                    arms: arms
                        .iter()
                        .map(|a| {
                            Ok(crate::surface::MatchArm {
                                goal: a.goal.clone(),
                                pattern: a.pattern.clone(),
                                guard: a.guard.clone(),
                                body: self.expand_lets(&a.body)?,
                            })
                        })
                        .collect::<Result<_, Diagnostic>>()?,
                },
                sp,
            ),
            _ => t.clone(),
        };
        self.retain_ctor_site_origin(t, &expanded);
        Ok(expanded)
    }

    // ---- names and substitution ----------------------------------------

    fn fresh_name(&mut self, base: impl Into<Name>) -> Name {
        self.fresh += 1;
        let base = base.into();
        let display = base.trim_end_matches(|c: char| c == '\'' || c.is_ascii_digit());
        let display = format!("{display}'{}", self.fresh);
        match base {
            Name::Local(reference) => reference.freshened(display).into(),
            _ => tauto_surface::identity::LocalRef::fresh(display).into(),
        }
    }

    fn subst(&mut self, t: &T, x: &Name, v: &T) -> T {
        let names = FreeNames::of(v);
        self.subst_in(t, x, v, &names, &mut HashMap::new())
            .unwrap_or_else(|| t.clone())
    }

    /// `t` with `v` for `x`, or `None` when `t` does not change: an unchanged
    /// part is shared with `t`, not copied. `names` are the free names of `v`,
    /// which a binder would capture.
    fn subst_in(
        &mut self,
        t: &T,
        x: &Name,
        v: &T,
        names: &FreeNames,
        memo: &mut SubstMemo,
    ) -> Option<T> {
        let key = (
            std::sync::Arc::as_ptr(&t.kind) as usize,
            t.id(),
            t.span.start,
            t.span.end,
        );
        if let Some((_, result)) = memo.get(&key) {
            return result.clone();
        }
        let result = self.subst_node(t, x, v, names, memo);
        // Retaining the input prevents pointer reuse by temporary binder bodies.
        memo.insert(key, (t.clone(), result.clone()));
        result
    }

    fn subst_node(
        &mut self,
        t: &T,
        x: &Name,
        v: &T,
        names: &FreeNames,
        memo: &mut SubstMemo,
    ) -> Option<T> {
        let sp = t.span;
        let replaced = match &*t.kind {
            TermKind::Var(n) if n == x => {
                if self.record_sites {
                    self.ctor_site_origins
                        .entry(v.id())
                        .or_insert_with(|| vec![v.id()]);
                }
                Some(v.clone())
            }
            TermKind::App {
                function,
                arguments,
            } => {
                let f = self.subst_in(function, x, v, names, memo);
                let args: Vec<Option<T>> = arguments
                    .iter()
                    .map(|a| self.subst_in(a, x, v, names, memo))
                    .collect();
                if f.is_none() && args.iter().all(Option::is_none) {
                    return None;
                }
                let out = T::new(
                    TermKind::App {
                        function: Box::new(f.unwrap_or_else(|| (**function).clone())),
                        arguments: args
                            .into_iter()
                            .zip(arguments)
                            .map(|(new, old)| new.unwrap_or_else(|| old.clone()))
                            .collect(),
                    },
                    sp,
                );
                // A call the source wrote stays one after the substitution.
                Some(if t.is_written_call() { out.written_call() } else { out })
            }
            TermKind::Pi {
                params,
                result,
                effects,
            } => {
                let (n, d) = &params[0];
                let plain = params.len() == 1 && n.is_some() && effects.is_none();
                let name = n.clone().unwrap_or_else(|| "_".into());
                // `(a: A, b: B) -> R` is `(a: A) -> (b: B) -> R`: the rest of
                // the parameters are under the first one's binder.
                let rest = (params.len() > 1).then(|| {
                    T::new(
                        TermKind::Pi {
                            params: params[1..].to_vec(),
                            result: result.clone(),
                            effects: effects.clone(),
                        },
                        sp,
                    )
                });
                let result = rest.as_ref().unwrap_or(&**result);
                let d2 = self.subst_in(d, x, v, names, memo);
                let r2 = self.under_binder(&name, result, x, v, names, memo);
                if plain && d2.is_none() && r2.is_none() {
                    return None;
                }
                let (name, r2) = match r2 {
                    Some(r) => r,
                    None => (name, result.clone()),
                };
                let mut out = pi(&name, d2.unwrap_or_else(|| d.clone()), r2);
                out.span = sp;
                Some(out)
            }
            TermKind::Lam {
                params,
                body,
                types,
            } => {
                // `(a, b) => e` is `a => b => e`: the rest of the parameters
                // (and the types written on them) are under the first one's
                // binder.
                let rest = (params.len() > 1).then(|| {
                    T::new(
                        TermKind::Lam {
                            params: params[1..].to_vec(),
                            body: body.clone(),
                            types: types.get(1..).unwrap_or_default().to_vec(),
                        },
                        sp,
                    )
                });
                let body = rest.as_ref().unwrap_or(&**body);
                // The type written on the first parameter is outside its
                // binder, so it is substituted too: a λ whose body does not
                // mention `x` is still changed when its written type does,
                // or the type would be checked against a renamed context.
                let written = match types.first() {
                    Some(Some(ty)) => Some(self.subst_in(ty, x, v, names, memo)),
                    _ => None,
                };
                let under = self.under_binder(&params[0], body, x, v, names, memo);
                if under.is_none() && !matches!(written, Some(Some(_))) && params.len() == 1 {
                    return None;
                }
                let (name, body) = under.unwrap_or_else(|| (params[0].clone(), body.clone()));
                let written = match (written, types.first()) {
                    (Some(new), Some(Some(old))) => vec![Some(new.unwrap_or_else(|| old.clone()))],
                    _ => Vec::new(),
                };
                Some(T::new(
                    TermKind::Lam {
                        params: vec![name],
                        body: Box::new(body),
                        types: written,
                    },
                    sp,
                ))
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } => {
                let arms: Vec<(bool, crate::surface::MatchArm)> = arms
                    .iter()
                    .map(|arm| {
                        // A bare name in a pattern is a constructor when one
                        // is declared under it (`None`), and binds nothing.
                        let mut bound = Vec::new();
                        pattern_binders(&arm.pattern, &mut bound);
                        bound.retain(|b| !self.ctors.contains_key(b));
                        if bound.iter().chain(binder).any(|b| b == x)
                            || binder.as_ref().is_some_and(|b| names.contains(b))
                        {
                            // Shadowed, or the match's own binder captures:
                            // leave the arm alone.
                            return (false, arm.clone());
                        }
                        // A binder of the arm that would capture a free name
                        // of `v` is renamed in the arm first.
                        let original = arm;
                        let mut arm = arm.clone();
                        for b in bound.iter().filter(|b| names.contains(b)) {
                            let b2 = self.fresh_name(b);
                            let to = T::var(&b2, arm.body.span);
                            rename_pattern_binder(&mut arm.pattern, b, &b2);
                            arm.body = self.subst(&arm.body, b, &to);
                            arm.guard = arm.guard.map(|g| self.subst(&g, b, &to));
                            arm.goal = arm.goal.map(|g| self.subst(&g, b, &to));
                        }
                        let arm = &arm;
                        let goal = arm
                            .goal
                            .as_ref()
                            .map(|g| self.subst_in(g, x, v, names, memo));
                        let guard = arm
                            .guard
                            .as_ref()
                            .map(|g| self.subst_in(g, x, v, names, memo));
                        let body = self.subst_in(&arm.body, x, v, names, memo);
                        let changed = goal.as_ref().is_some_and(Option::is_some)
                            || guard.as_ref().is_some_and(Option::is_some)
                            || body.is_some();
                        if !changed {
                            return (false, original.clone());
                        }
                        (
                            changed,
                            crate::surface::MatchArm {
                                goal: match (&arm.goal, goal) {
                                    (_, Some(Some(g))) => Some(g),
                                    (g, _) => g.clone(),
                                },
                                pattern: arm.pattern.clone(),
                                guard: match (&arm.guard, guard) {
                                    (_, Some(Some(g))) => Some(g),
                                    (g, _) => g.clone(),
                                },
                                body: body.unwrap_or_else(|| arm.body.clone()),
                            },
                        )
                    })
                    .collect();
                let scrutinee2 = self.subst_in(scrutinee, x, v, names, memo);
                let result2 = result.as_ref().map(|r| self.subst_in(r, x, v, names, memo));
                if scrutinee2.is_none()
                    && !result2.as_ref().is_some_and(Option::is_some)
                    && arms.iter().all(|(changed, _)| !changed)
                {
                    return None;
                }
                Some(T::new(
                    TermKind::Match {
                        binder: binder.clone(),
                        scrutinee: Box::new(scrutinee2.unwrap_or_else(|| (**scrutinee).clone())),
                        result: match (result, result2) {
                            (_, Some(Some(r))) => Some(Box::new(r)),
                            (r, _) => r.clone(),
                        },
                        arms: arms.into_iter().map(|(_, arm)| arm).collect(),
                    },
                    sp,
                ))
            }
            TermKind::Field { base, name } => {
                let b = self.subst_in(base, x, v, names, memo)?;
                Some(T::new(
                    TermKind::Field {
                        base: Box::new(b),
                        name: name.clone(),
                    },
                    sp,
                ))
            }
            // A type ascription `(e: T)` binds nothing: both the term and the
            // type are read, so a name used only there is still used.
            TermKind::Ascribe { term, ty } => {
                let t2 = self.subst_in(term, x, v, names, memo);
                let ty2 = self.subst_in(ty, x, v, names, memo);
                if t2.is_none() && ty2.is_none() {
                    return None;
                }
                Some(T::new(
                    TermKind::Ascribe {
                        term: Box::new(t2.unwrap_or_else(|| (**term).clone())),
                        ty: Box::new(ty2.unwrap_or_else(|| (**ty).clone())),
                    },
                    sp,
                ))
            }
            // The implicit arguments written by name (`f(<x: v>)`) are
            // terms of the call.
            TermKind::Record {
                name,
                fields,
                base: None,
            } if name.spelling() == Some(tauto_surface::IMPLICITS) => {
                let new: Vec<Option<T>> = fields
                    .iter()
                    .map(|(_, value)| self.subst_in(value, x, v, names, memo))
                    .collect();
                if new.iter().all(Option::is_none) {
                    return None;
                }
                Some(T::new(
                    TermKind::Record {
                        name: name.clone(),
                        fields: fields
                            .iter()
                            .zip(new)
                            .map(|((f, old), new)| (f.clone(), new.unwrap_or_else(|| old.clone())))
                            .collect(),
                        base: None,
                    },
                    sp,
                ))
            }
            _ => None,
        };
        if let Some(replaced) = &replaced {
            self.retain_ctor_site_origin(t, replaced);
        }
        replaced
    }

    fn retain_ctor_site_origin(&mut self, original: &T, transformed: &T) {
        if !self.record_sites || original.id() == transformed.id() {
            return;
        }
        let origins = self
            .ctor_site_origins
            .get(&original.id())
            .cloned()
            .unwrap_or_else(|| vec![original.id()]);
        let recorded = self.ctor_site_origins.entry(transformed.id()).or_default();
        for origin in origins {
            if !recorded.contains(&origin) {
                recorded.push(origin);
            }
        }
    }

    /// Substitutes below a binder `n`, renaming it when it would capture;
    /// `None` when nothing changes.
    fn under_binder(
        &mut self,
        n: &Name,
        body: &T,
        x: &Name,
        v: &T,
        names: &FreeNames,
        memo: &mut SubstMemo,
    ) -> Option<(Name, T)> {
        if n == x {
            return None;
        }
        if names.contains(n) {
            let n2 = self.fresh_name(n);
            let renamed = self.subst(body, n, &T::var(&n2, body.span));
            let body = self
                .subst_in(&renamed, x, v, names, memo)
                .unwrap_or(renamed);
            Some((n2, body))
        } else {
            Some((n.clone(), self.subst_in(body, x, v, names, memo)?))
        }
    }

    /// The name a binder `n` over `body` is entered under. Contexts are
    /// lists of names, so a binder that reuses the name of a variable in
    /// `ctx`, of a global, or of a free name of `outer` would make those
    /// mean the bound variable inside; it is renamed (and `body` with it).
    pub(super) fn enter_binder(
        &mut self,
        ctx: &Ctx,
        n: &Name,
        body: &T,
        outer: &[&T],
    ) -> (Name, T) {
        if n.spelling() == Some("_") {
            // `_` binds nothing, so it is entered under a name of its own.
            return (self.fresh_name("_"), body.clone());
        }
        let clashes = n.spelling() != Some("_")
            && (is_local(ctx, n)
                || self.globals.contains_key(n)
                || self.current.as_deref() == Some(n)
                || outer.iter().any(|t| occurs(t, n)));
        if !clashes {
            return (n.clone(), body.clone());
        }
        let n2 = self.fresh_name(n);
        let body = self.subst(body, n, &T::var(&n2, body.span));
        (n2, body)
    }

    /// `fun x => body` checked against `Pi (name: domain) result`: the name
    /// `x` is entered under, with `body` renamed to match.
    pub(super) fn enter_lam(
        &mut self,
        ctx: &Ctx,
        x: &Name,
        body: &T,
        name: &Name,
        domain: &T,
        result: &T,
    ) -> (Name, T) {
        if name == x {
            self.enter_binder(ctx, x, body, &[domain])
        } else {
            self.enter_binder(ctx, x, body, &[domain, result])
        }
    }

    /// `t` in weak head normal form, as the core reduces it.
    /// `t` in weak head normal form, stopping at a product `Prod(A, B)`: the checker tells a
    /// product from a `Pair` written by its name, and only the core sees the `Pair` a product
    /// is ([`Kernel::whnf_pair`] unfolds it).
    fn whnf(&mut self, ctx: &Ctx, t: &T) -> T {
        if self.product_parts(t).is_some() {
            return t.clone();
        }
        let b = self.core.beta_in(ctx, t);
        if self.product_parts(&b).is_some() {
            return b;
        }
        self.core.whnf_in(ctx, t)
    }

    /// `t` in weak head normal form, a product unfolded to its `Pair`.
    fn whnf_pair(&mut self, ctx: &Ctx, t: &T) -> T {
        self.core.whnf_in(ctx, t)
    }

    /// The innermost pair of subterms (in weak head normal form) that make `a`
    /// and `b` differ, or `None` where they are not comparable part by part.
    fn difference(&mut self, ctx: &Ctx, a: &T, b: &T) -> Option<(T, T)> {
        self.core.difference_in(ctx, a, b)
    }

    /// `t` computed as far as it goes into its arguments, so that a value is
    /// shown as the tree of constructors it is and not as a half-unfolded
    /// recursor. Binders are left as they are, and the work is bounded.
    fn computed(&mut self, ctx: &Ctx, t: &T) -> T {
        // A term on a variable in scope does not compute to a tree of
        // constructors, only a few steps of it may say it shorter. Reducing
        // each of its parts as far as the fuel goes unfolds a name whose
        // value computes deep (`pow2(n + 4000)`) at every part again.
        let open = free_vars(t).iter().any(|n| ctx.iter().any(|(m, _)| m == n));
        let mut fuel = if open {
            OPEN_COMPUTED_FUEL
        } else {
            COMPUTED_FUEL
        };
        let c = self.computed_with(ctx, t, &mut fuel);
        // A name that has not been unfolded can say more than its body. A
        // value computed to the end, a tree of constructors, is what the
        // name is, however its constructors are spelled (`main::Seq::Nil`).
        if self.is_constructed(&c) || describe(&c).len() <= describe(t).len() {
            c
        } else {
            t.clone()
        }
    }

    /// Whether `t` is a tree of constructors (and types and numerals) only,
    /// with nothing left to compute.
    fn is_constructed(&self, t: &T) -> bool {
        let named = |n: &Name| {
            self.inds.contains_key(n)
                || self
                    .inds
                    .values()
                    .any(|i| i.ctors.iter().any(|c| c.name == *n))
        };
        match &*t.kind {
            TermKind::Nat(_) => true,
            TermKind::Var(n) => named(n),
            TermKind::App {
                function,
                arguments,
            } => {
                matches!(&*function.kind, TermKind::Var(n) if named(n))
                    && arguments.iter().all(|a| self.is_constructed(a))
            }
            _ => false,
        }
    }

    fn computed_with(&mut self, ctx: &Ctx, t: &T, fuel: &mut usize) -> T {
        if *fuel == 0 {
            return t.clone();
        }
        *fuel -= 1;
        let t = self.core.whnf_shown(ctx, t);
        if let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        {
            let arguments = arguments
                .iter()
                .map(|x| self.computed_with(ctx, x, fuel))
                .collect();
            return T::new(
                TermKind::App {
                    function: function.clone(),
                    arguments,
                },
                t.span,
            );
        }
        t
    }

    /// `type mismatch: expected …, found …`, then the innermost parts that differ.
    fn mismatch(&mut self, ctx: &Ctx, expected: &T, found: &T) -> Message {
        let (e, a) = (self.whnf(ctx, expected), self.whnf(ctx, found));
        let mut message = msg!(
            "kernel-mismatch",
            expected = shorten(&describe(&e)),
            found = shorten(&describe(&a))
        );
        let line = |message: Message, line: Message| {
            msg!("kernel-mismatch-line", message = message, line = line)
        };
        if let Some((de, da)) = self.difference(ctx, &e, &a) {
            let (de, da) = (self.computed(ctx, &de), self.computed(ctx, &da));
            let (de, da) = (shorten(&describe(&de)), shorten(&describe(&da)));
            if de != shorten(&describe(&e)) || da != shorten(&describe(&a)) {
                message = line(
                    message,
                    msg!("kernel-mismatch-differing", expected = de, found = da),
                );
            }
        }
        if let Some((side, value, call)) = self.collapsed(ctx, &e, &a) {
            let side = match side {
                "expected" => msg!("kernel-side-expected"),
                _ => msg!("kernel-side-found"),
            };
            message = line(
                message,
                msg!(
                    "kernel-mismatch-computed",
                    side = side,
                    value = shorten(&describe(&value)),
                    call = shorten(&describe(&call))
                ),
            );
        }
        for (what, t) in [
            ("kernel-mismatch-expected-written", expected),
            ("kernel-mismatch-found-written", found),
        ] {
            if let Some(written) = self.shown.get(&t.span.start) {
                message = line(message, msg!(what, written = written));
            }
        }
        message
    }

    /// Where `e` and `a` first differ, the call on one side that computes to
    /// what is shown there, with its arguments computed: `is_ok(bc(xs, ys))`
    /// shown as `false` loses why it is `false`, and `is_ok(bad(2, 4))` says it.
    /// Only the arguments are computed, so the call itself is kept; nothing is
    /// said when that tells no more than the call as written.
    fn collapsed(&mut self, ctx: &Ctx, e: &T, a: &T) -> Option<(&'static str, T, T)> {
        let (mut e, mut a) = (e.clone(), a.clone());
        loop {
            let next = match (&*e.kind, &*a.kind) {
                (
                    TermKind::App {
                        function: fe,
                        arguments: xe,
                    },
                    TermKind::App {
                        function: fa,
                        arguments: xa,
                    },
                ) if xe.len() == xa.len() && describe(fe) == describe(fa) => {
                    let i = (0..xe.len()).find(|&i| !self.conv(ctx, &xe[i], &xa[i]))?;
                    (xe[i].clone(), xa[i].clone())
                }
                _ => break,
            };
            (e, a) = next;
        }
        for (side, t) in [("found", &a), ("expected", &e)] {
            let TermKind::App {
                function,
                arguments,
            } = &*t.kind
            else {
                continue;
            };
            let value = self.computed(ctx, t);
            if describe(&value) == describe(t) {
                continue;
            }
            let arguments: Vec<T> = arguments.iter().map(|x| self.computed(ctx, x)).collect();
            let call = T::new(
                TermKind::App {
                    function: function.clone(),
                    arguments,
                },
                t.span,
            );
            if describe(&call) != describe(t) && describe(&call) != describe(&value) {
                return Some((side, value, call));
            }
        }
        None
    }

    /// Whether `a` and `b` are convertible, as the core decides it.
    fn conv(&mut self, ctx: &Ctx, a: &T, b: &T) -> bool {
        self.core.conv_in(ctx, a, b)
    }

    /// Whether a term of `a` is one of `b` (the sorts are cumulative).
    fn subtype(&mut self, ctx: &Ctx, a: &T, b: &T) -> bool {
        self.core.subtype_in(ctx, a, b)
    }

    // Terms are typed by the core (`Core::type_in`). What is here is the
    // named checker's reading of its answer: the holes met, and a diagnostic
    // at the part that does not type.

    fn infer(&mut self, ctx: &Ctx, t: &T) -> Result<T, Diagnostic> {
        let typed = self.ask_core(ctx, t, Ask::Infer)?;
        Ok(typed.ty.expect("an inferred type"))
    }

    /// `t` typed by the core, the holes it met recorded.
    fn ask_core(&mut self, ctx: &Ctx, t: &T, ask: Ask<'_>) -> Result<Typed, Diagnostic> {
        kernel_binders(t)?;
        let current = self.current.clone();
        let avoid: Vec<&str> = current.as_deref().into_iter().collect();
        let globals = &self.globals;
        let declared = |n: &Name| globals.get(n).map(|g| g.ty.clone());
        match self.core.type_in(ctx, t, ask, &declared, &avoid) {
            Ok(typed) => {
                for m in &typed.holes {
                    self.met_hole(ctx, m)?;
                }
                Ok(typed)
            }
            Err(f) => Err(self.diagnose(ctx, t, *f)),
        }
    }

    /// A hole met, recorded with its goal. The same place checked again (a
    /// `match` that generalizes the arguments after the matched one is
    /// elaborated twice) is the same hole, the latest check being the one
    /// that stood.
    fn met_hole(&mut self, ctx: &Ctx, m: &Met) -> Result<(), Diagnostic> {
        let TermKind::Hole(name) = &*m.hole.kind else {
            unreachable!("a hole is met")
        };
        let again = self.holes.iter().position(|h| &h.name == name);
        if let Some(at) = again
            && self.holes[at].span != m.hole.span
        {
            return err(msg!("kernel-hole-twice", name = name), m.hole.span);
        }
        let goal = self.beta(&m.goal);
        let mut context: Vec<(Name, T)> = ctx
            .iter()
            .chain(&m.bound)
            .map(|(n, t)| (n.clone(), self.beta(t)))
            .collect();
        // The `let`s around the hole, typed where the hole is. A value that
        // does not type is reported where the `let` is checked, not here.
        // An inner value may name an outer `let`, which is in `at` by then.
        let lets = self
            .hole_lets
            .get(&(name.clone(), m.hole.span))
            .cloned()
            .unwrap_or_default();
        let mut at: Ctx = ctx.iter().chain(&m.bound).cloned().collect();
        for (n, value) in lets {
            if context.iter().any(|(c, _)| c == &n) {
                continue;
            }
            // Typing the value meets the holes in it again, this one among
            // them, out of their places: what they record there is put back.
            let holes = self.holes.clone();
            let ty = self
                .shape(&value)
                .and_then(|v| self.elab(&at, &v, None))
                .and_then(|v| self.infer(&at, &v))
                // A value that only types inside the declaration (a call of
                // the declaration itself, which is its induction hypothesis
                // there) still has the type it is written with.
                .or_else(|e| match Self::written_type(&value) {
                    Some(ty) => self.shape(ty).and_then(|t| self.elab(&at, &t, None)),
                    None => Err(e),
                });
            self.holes = holes;
            if let Ok(ty) = ty {
                let ty = self.beta(&ty);
                at.push((n.clone(), ty.clone()));
                context.push((n, ty));
            }
        }
        let (goal, context) = self.tidy_hole(goal, context);
        // A step's macro compares the goal with the one written.
        let goal = Self::eqs_written(&self.calls_written(&goal));
        let context = context
            .into_iter()
            .map(|(n, t)| {
                let t = Self::eqs_written(&self.calls_written(&t));
                (n, t)
            })
            .collect();
        let found = HoleGoal {
            name: name.clone(),
            span: m.hole.span,
            goal,
            context,
            statement: None,
            params: Vec::new(),
        };
        match again {
            Some(at) => self.holes[at] = found,
            None => self.holes.push(found),
        }
        Ok(())
    }

    /// `T` of a `let` value written `the(T, v)`, the form a `let` with a
    /// type takes.
    fn written_type(value: &T) -> Option<&T> {
        match &*value.kind {
            TermKind::App {
                function,
                arguments,
            } if arguments.len() == 2
                && matches!(&*function.kind, TermKind::Var(n)
                    if tauto_surface::bindings::is_library(n, "the")) =>
            {
                Some(&arguments[0])
            }
            _ => None,
        }
    }

    /// A declaration that failed at a use of a name that is not defined is
    /// told of every other such use in it too (`Diagnostic::also`). The
    /// resolver has already bound each local name, so a name that is still a
    /// global one, that the core cannot read and that no declaration of the
    /// program has, is not defined wherever it is written: that is decided
    /// without a type, and nothing is checked past the failure.
    fn other_undefined_uses(&self, stmt: &Stmt, entries: &mut [Entry]) {
        fn undefined(m: &Message) -> bool {
            match m.get("message") {
                Some(Value::Message(inner)) => undefined(inner),
                _ => matches!(
                    m.id.as_ref(),
                    "kernel-not-defined" | "kernel-not-defined-hint"
                ),
            }
        }
        for e in entries {
            let Verdict::Failed(d) = &mut e.verdict else {
                continue;
            };
            if !undefined(&d.message) {
                continue;
            }
            let mut uses: Vec<(Span, Name)> = Vec::new();
            crate::surface::walk::stmt(&mut stmt.clone(), &mut |t| {
                let TermKind::Var(n) = &*t.kind else {
                    return;
                };
                // A name of the language (a sort, a primitive, a declaration
                // of the library) is read by the checker in its own way.
                let Name::Global(r) = n else {
                    return;
                };
                if r.sort().is_some()
                    || tauto_surface::identity::DeclRef::primitive(r.display()).as_ref() == Some(r)
                    || tauto_surface::bindings::library_reference(r.display()).as_ref() == Some(n)
                    || self.current.as_ref() == Some(n)
                    || self.globals.contains_key(n)
                    || self.ahead.contains_key(n)
                    || self.core.read(t).is_ok()
                {
                    return;
                }
                uses.push((t.span, n.clone()));
            });
            uses.sort_by_key(|(s, _)| (s.start, s.end));
            uses.dedup_by_key(|(s, _)| (s.start, s.end));
            for (span, n) in uses {
                if d.span == Some(span) {
                    continue;
                }
                let m = self.unread_name(&n);
                if undefined(&m) {
                    d.also.push(Diagnostic::new(m, Some(span)));
                }
            }
        }
    }

    /// What a name the core could not read is: the message of a use of it.
    fn unread_name(&self, n: &Name) -> Message {
        match self.ahead.get(n) {
            _ if self.globals.contains_key(n) => {
                msg!("kernel-not-defined", name = (n).to_string())
            }
            Some(Ahead::Later) => {
                msg!("kernel-not-defined-yet", name = (n).to_string())
            }
            Some(Ahead::Failed) => msg!("kernel-uses-failed", name = (n).to_string()),
            Some(Ahead::Struct) => {
                msg!("kernel-not-defined-struct", name = (n).to_string())
            }
            Some(Ahead::Skipped(why)) => {
                msg!(
                    "kernel-uses-skipped-why",
                    name = (n).to_string(),
                    why = why.clone()
                )
            }
            // A constructor renamed to another case convention
            // (`drain_free` to `DrainFree`) is named; the old
            // name is not kept as a second one.
            None => match self.respelled_ctor(n) {
                Some(hint) => msg!(
                    "kernel-not-defined-hint",
                    name = (n).to_string(),
                    hint = hint
                ),
                None => msg!("kernel-not-defined", name = (n).to_string()),
            },
        }
    }

    /// The constructor `name` is in another case convention, when exactly
    /// one is: its full name, or a qualified one whose last part matches.
    fn respelled_ctor(&self, name: &str) -> Option<String> {
        let mut names: Vec<&str> = self.ctors.keys().map(Name::as_str).collect();
        names.sort_unstable();
        if let Some(c) = tauto_surface::suggest::respelled(name, names.iter().copied()) {
            return Some(c.to_string());
        }
        let short: Vec<&str> = names
            .iter()
            .map(|c| c.rsplit_once("::").map_or(*c, |(_, s)| s))
            .collect();
        let hit = tauto_surface::suggest::respelled(name, short.iter().copied())?;
        let full: Vec<&&str> = names
            .iter()
            .filter(|c| c.rsplit_once("::").map_or(**c, |(_, s)| s) == hit)
            .collect();
        match full.as_slice() {
            [_] => Some(hit.to_string()),
            _ => None,
        }
    }

    /// Why `t` does not type, at the part the core stopped at.
    fn diagnose(&mut self, ctx: &Ctx, t: &T, f: Failure) -> Diagnostic {
        let (node, k) = locate(t, &f.at);
        let part = applied(node, k);
        let sp = part.span;
        let mut inner = ctx.clone();
        inner.extend(f.bound);
        let fail = |m: Message, sp| Diagnostic::new(m, Some(sp));
        match f.why {
            Failed::Unread(u) => {
                let m = match &*u.kind {
                    TermKind::Var(n) if n.spelling() == Some("_") => {
                        msg!("kernel-underscore-not-value")
                    }
                    TermKind::Var(n) if tauto_surface::bindings::is_library(&n, "Float") => {
                        msg!("kernel-float-not-defined")
                    }
                    TermKind::Var(n) if tauto_surface::bindings::is_library(&n, "/") => {
                        msg!("kernel-integer-division")
                    }
                    TermKind::Var(n) if tauto_surface::bindings::is_library(&n, "#()") => {
                        msg!("kernel-unit-value-as-type")
                    }
                    TermKind::Var(n) if self.current.as_ref() == Some(n) => {
                        msg!("kernel-calls-itself", name = (n).to_string())
                    }
                    TermKind::Var(n) => self.unread_name(n),
                    TermKind::Hole(name) => msg!("kernel-hole-type-unknown", name = name),
                    TermKind::Other(what) if what.starts_with('`') => Message::text(what.clone()),
                    _ => msg!("kernel-not-kernel-term"),
                };
                fail(m, u.span)
            }
            Failed::Said(m) => fail(
                match m {
                    "kernel-core-cannot-infer-function" => msg!("kernel-cannot-infer-function"),
                    "kernel-core-cannot-type-applied" => msg!("kernel-cannot-type-applied"),
                    m => msg!(m),
                },
                sp,
            ),
            Failed::NotFunction => {
                let TermKind::App {
                    function,
                    arguments,
                } = &*node.kind
                else {
                    return fail(msg!("kernel-core-not-function"), sp);
                };
                fail(
                    msg!("kernel-too-many-arguments", name = describe(function)),
                    arguments[k - 1].span,
                )
            }
            Failed::NoPi(e) => {
                let e = self.whnf(&inner, &e);
                fail(msg!("kernel-function-given", expected = describe(&e)), sp)
            }
            Failed::NotType => fail(msg!("kernel-not-a-type", term = describe(&part)), sp),
            Failed::Mismatch { expected, found } => self
                .blame_argument(&inner, &part, &expected)
                .unwrap_or_else(|| self.mismatch_diag(&inner, &expected, &found, sp)),
        }
    }

    /// A variable the checker renamed to generalize a `match` (`m'25`, when `m`
    /// is the argument that came after the matched one) is shown under its
    /// own name, the stale `m` dropped, if nothing mentions `m` any more.
    fn tidy_hole(&mut self, mut goal: T, mut context: Vec<(Name, T)>) -> (T, Vec<(Name, T)>) {
        let mut i = 0;
        while i < context.len() {
            let name = context[i].0.clone();
            let base = match &name {
                Name::Local(reference) => reference.origin().cloned().map(Name::Local),
                _ => None,
            };
            let old = base
                .as_ref()
                .and_then(|b| context[..i].iter().position(|(n, _)| n == b));
            if let (Some(base), Some(old)) = (base, old) {
                let mentioned = occurs(&goal, &base)
                    || context
                        .iter()
                        .enumerate()
                        .any(|(j, (_, t))| j != old && occurs(t, &base));
                if !mentioned {
                    let v = T::var(&base, goal.span);
                    goal = self.subst(&goal, &name, &v);
                    for (_, t) in context.iter_mut().skip(i + 1) {
                        *t = self.subst(t, &name, &v);
                    }
                    context[i].0 = base;
                    context.remove(old);
                    continue;
                }
            }
            i += 1;
        }
        (goal, context)
    }

    /// `t` with its applied functions applied (`(x => B)(a)` is `B[a/x]`),
    /// and nothing else unfolded: a goal as it reads, not as it computes.
    fn beta(&mut self, t: &T) -> T {
        match &*t.kind {
            TermKind::App {
                function,
                arguments,
            } => {
                let function = self.beta(function);
                let arguments: Vec<T> = arguments.iter().map(|a| self.beta(a)).collect();
                if let TermKind::Lam { params, body, .. } = &*function.kind
                    && let Some((first, rest)) = arguments.split_first()
                {
                    let applied = self.subst(body, &params[0], first);
                    let applied = if rest.is_empty() {
                        applied
                    } else {
                        T::new(
                            TermKind::App {
                                function: Box::new(applied),
                                arguments: rest.to_vec(),
                            },
                            t.span,
                        )
                    };
                    return self.beta(&applied);
                }
                T::new(
                    TermKind::App {
                        function: Box::new(function),
                        arguments,
                    },
                    t.span,
                )
            }
            TermKind::Pi {
                params,
                result,
                effects,
            } => {
                let params = params
                    .iter()
                    .map(|(n, d)| (n.clone(), self.beta(d)))
                    .collect();
                T::new(
                    TermKind::Pi {
                        params,
                        result: Box::new(self.beta(result)),
                        effects: effects.clone(),
                    },
                    t.span,
                )
            }
            TermKind::Lam {
                params,
                body,
                types,
                ..
            } => T::new(
                TermKind::Lam {
                    params: params.clone(),
                    body: Box::new(self.beta(body)),
                    types: types.clone(),
                },
                t.span,
            ),
            _ => t.clone(),
        }
    }

    fn expect_type(&mut self, ctx: &Ctx, t: &T) -> Result<Sort, Diagnostic> {
        let typed = self.ask_core(ctx, t, Ask::Sort)?;
        Ok(typed.sort.expect("a sort"))
    }

    fn check(&mut self, ctx: &Ctx, t: &T, expected: &T) -> Result<(), Diagnostic> {
        self.ask_core(ctx, t, Ask::Check(expected)).map(|_| ())
    }

    fn mismatch_diag(&mut self, ctx: &Ctx, expected: &T, found: &T, span: Span) -> Diagnostic {
        let message = self.mismatch(ctx, expected, found);
        let (e, f) = (self.whnf(ctx, expected), self.whnf(ctx, found));
        let differing = self
            .difference(ctx, &e, &f)
            .filter(|(de, da)| describe(de) != describe(&e) || describe(da) != describe(&f));
        // Where the found part is written, if it was written inside `span`.
        let differing_span = differing.as_ref().and_then(|(_, da)| {
            let sp = da.span;
            (sp.start < sp.end && sp.start >= span.start && sp.end <= span.end).then_some(sp)
        });
        Diagnostic {
            message: message.into(),
            span: Some(span),
            detail: Some(Box::new(Mismatch {
                expected: expected.clone(),
                found: found.clone(),
                differing,
                differing_span,
                argument: None,
            })),
            fix: None,
            also: Vec::new(),
        }
    }

    /// A call `g(a₁, …)` whose result is not the expected type: when the
    /// expected type, matched against the result of `g`, says what each
    /// argument had to be, the first argument that is not that is the one to
    /// point at, instead of the whole call. Only the message changes; the
    /// call was rejected either way.
    fn blame_argument(&mut self, ctx: &Ctx, t: &T, expected: &T) -> Option<Diagnostic> {
        let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        else {
            return None;
        };
        let TermKind::Var(g) = &*function.kind else {
            return None;
        };
        let (mut ty, k) = {
            let global = self.globals.get(g)?;
            (global.ty.clone(), global.implicit)
        };
        if is_local(ctx, g) || k == 0 || arguments.len() < k {
            return None;
        }
        let mut metas = Vec::new();
        for _ in 0..k {
            let TermKind::Pi { params, result, .. } = (*ty.kind).clone() else {
                break;
            };
            let name = params[0].0.clone().unwrap_or_else(|| "_".into());
            let m = self.fresh_name("?");
            self.metas.insert(m.clone(), None);
            ty = self.subst(&result, &name, &T::var(&m, t.span));
            metas.push(m);
        }
        let blamed = (|| {
            let mut asks = Vec::new();
            for arg in &arguments[k..] {
                let whnf = self.whnf(ctx, &ty);
                let TermKind::Pi { params, result, .. } = &*whnf.kind else {
                    return None;
                };
                let name = params[0].0.clone().unwrap_or_else(|| "_".into());
                asks.push((arg.clone(), params[0].1.clone()));
                ty = self.subst(result, &name, arg);
            }
            if !self.unify(ctx, &ty, expected) {
                return None;
            }
            for (i, (arg, dom)) in asks.iter().enumerate() {
                let dom = self.resolve(dom);
                if dom_has_meta(&dom) {
                    continue;
                }
                let Ok(actual) = self.infer(ctx, arg) else {
                    continue;
                };
                if !self.subtype(ctx, &actual, &dom) {
                    let mut d = self.mismatch_diag(ctx, &dom, &actual, arg.span);
                    d.message = format!(
                        "{}\n  argument {} of `{g}`, which the expected type `{}` of the call fixes",
                        d.message,
                        i + 1,
                        describe(expected)
                    )
                    .into();
                    if let Some(m) = d.detail.as_mut() {
                        m.argument = Some((g.clone(), i));
                    }
                    return Some(d);
                }
            }
            None
        })();
        for m in &metas {
            self.metas.remove(m);
        }
        blamed
    }
}

fn dom_has_meta(t: &T) -> bool {
    free_vars(t).iter().any(|v| v.starts_with('?'))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Sort {
    Prop,
    Type(Level),
}

impl Sort {
    /// `Type` (0), `Type1`, …
    fn ty(n: u32) -> Sort {
        Sort::Type(Level::konst(n))
    }

    fn next(&self) -> Option<Sort> {
        match self {
            Sort::Prop => Some(Sort::ty(0)),
            Sort::Type(l) => l.succ().map(Sort::Type),
        }
    }

    /// Cumulativity: `Prop` is below every `Type`, and `Type(l)` below
    /// `Type(m)` when `l ≤ m` whatever the level variables are.
    fn le(&self, other: &Sort) -> bool {
        match (self, other) {
            (Sort::Prop, _) => true,
            (Sort::Type(_), Sort::Prop) => false,
            (Sort::Type(a), Sort::Type(b)) => a.le(b),
        }
    }

    /// The sort of `(x: A) -> B` for `A` in `self` and `B` in `codomain`:
    /// `Prop` when `B` is one, else the larger of the two.
    fn pi(&self, codomain: &Sort) -> Sort {
        match (self, codomain) {
            (_, Sort::Prop) => Sort::Prop,
            (Sort::Prop, other) => other.clone(),
            (Sort::Type(a), Sort::Type(b)) => Sort::Type(a.join(b)),
        }
    }
}

fn sort_named<N: ?Sized>(name: &N) -> Option<Sort>
where
    for<'a> Name: From<&'a N>,
{
    match Name::from(name).sort_symbol()? {
        tauto_surface::identity::SortSymbol::Proposition => Some(Sort::Prop),
        tauto_surface::identity::SortSymbol::Type(level) => Some(Sort::ty(level)),
    }
}

fn sort_of(t: &T) -> Option<Sort> {
    match &*t.kind {
        TermKind::Var(n) => sort_named(n),
        // `Type(u + 1)`: a sort whose level has variables.
        TermKind::App {
            function,
            arguments,
        } if matches!(&*function.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(&n, "Type"))
            && arguments.len() == 1 =>
        {
            level_of(&arguments[0]).map(Sort::Type)
        }
        _ => None,
    }
}

/// The level a term writes: a number, a variable, `l + n`, `max(l, m)`.
fn level_of(t: &T) -> Option<Level> {
    match &*t.kind {
        TermKind::Nat(n) => n.parse().ok().map(Level::konst),
        TermKind::Var(v) if !is_reserved(v) => Some(Level::var(v)),
        TermKind::App {
            function,
            arguments,
        } => match (&*function.kind, arguments.as_slice()) {
            (TermKind::Var(op), [a, b]) if tauto_surface::bindings::is_library(&op, "+") => {
                let TermKind::Nat(k) = &*b.kind else {
                    return None;
                };
                level_of(a)?.plus(k.parse().ok()?)
            }
            (TermKind::Var(op), [a, b]) if tauto_surface::bindings::is_library(&op, "max") => {
                Some(level_of(a)?.join(&level_of(b)?))
            }
            _ => None,
        },
        _ => None,
    }
}

fn level_term(level: &Level, span: Span) -> T {
    let nat = |n: u32| T::new(TermKind::Nat(n.to_string()), span);
    let mut parts: Vec<T> = Vec::new();
    if level.as_const().is_some() || level.variables().next().is_none() {
        return nat(level.as_const().unwrap_or(0));
    }
    if let Some(c) = level.constant_floor() {
        parts.push(nat(c));
    }
    for (v, k) in level.terms() {
        let var = T::var(v, span);
        parts.push(if k == 0 {
            var
        } else {
            T::new(
                TermKind::App {
                    function: Box::new(T::var(&tauto_surface::bindings::library_name("+"), span)),
                    arguments: vec![var, nat(k)],
                },
                span,
            )
        });
    }
    let mut it = parts.into_iter();
    let first = it.next().expect("a level with a variable has a part");
    it.fold(first, |acc, p| {
        T::new(
            TermKind::App {
                function: Box::new(T::var(&tauto_surface::bindings::library_name("max"), span)),
                arguments: vec![acc, p],
            },
            span,
        )
    })
}

fn sort_term(s: &Sort, span: Span) -> T {
    match s {
        Sort::Prop => T::var(&tauto_surface::bindings::library_name("Prop"), span),
        Sort::Type(l) => match l.as_const() {
            Some(0) => T::var(&tauto_surface::bindings::library_name("Type"), span),
            Some(n) => T::var(&format!("Type{n}"), span),
            None => T::new(
                TermKind::App {
                    function: Box::new(T::var(
                        &tauto_surface::bindings::library_name("Type"),
                        span,
                    )),
                    arguments: vec![level_term(l, span)],
                },
                span,
            ),
        },
    }
}

/// A `match`, an `if`, a field projection or `a == b` in a type, also under `∀` and `∃`:
/// a type reads them as a body does.
fn has_match_in_type(t: &T) -> bool {
    match &*t.kind {
        TermKind::Match { .. }
        | TermKind::If { .. }
        | TermKind::Field { .. }
        | TermKind::Ascribe { .. } => true,
        TermKind::App {
            function,
            arguments,
        } if arguments.len() == 2
            && matches!(&*function.kind, TermKind::Var(op) if tauto_surface::bindings::is_library(&op, "==") || tauto_surface::bindings::is_library(&op, "!=")) =>
        {
            true
        }
        TermKind::Pi { params, result, .. } => {
            params.iter().any(|(_, d)| has_match_in_type(d)) || has_match_in_type(result)
        }
        TermKind::App {
            function,
            arguments,
        } => has_match_in_type(function) || arguments.iter().any(has_match_in_type),
        TermKind::Lam { body, .. } => has_match_in_type(body),
        TermKind::Exists { domain, body, .. } => {
            has_match_in_type(domain) || has_match_in_type(body)
        }
        _ => false,
    }
}

fn pi(name: impl Into<Name>, domain: T, result: T) -> T {
    let span = result.span;
    T::new(
        TermKind::Pi {
            params: vec![(Some(name.into()), domain)],
            result: Box::new(result),
            effects: None,
        },
        span,
    )
}

fn lam(name: impl Into<Name>, body: T) -> T {
    let span = body.span;
    T::new(
        TermKind::Lam {
            params: vec![name.into()],
            body: Box::new(body),
            types: Vec::new(),
        },
        span,
    )
}

/// The names a pattern binds, in the order met.
fn pattern_binders(p: &crate::surface::Pattern, out: &mut Vec<Name>) {
    use crate::surface::Pattern;
    match p {
        Pattern::Bind(n) => out.push(n.clone()),
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| pattern_binders(a, out)),
        Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| pattern_binders(a, out)),
        Pattern::Tuple(items) => items.iter().for_each(|a| pattern_binders(a, out)),
        _ => {}
    }
}

/// `p` with its binder `from` named `to`.
fn rename_pattern_binder(p: &mut crate::surface::Pattern, from: &Name, to: &Name) {
    use crate::surface::Pattern;
    match p {
        Pattern::Bind(n) if n == from => *n = to.clone(),
        Pattern::Ctor { args, .. } => args
            .iter_mut()
            .for_each(|a| rename_pattern_binder(a, from, to)),
        Pattern::Record { fields, .. } => fields
            .iter_mut()
            .for_each(|(_, a)| rename_pattern_binder(a, from, to)),
        Pattern::Tuple(items) => items
            .iter_mut()
            .for_each(|a| rename_pattern_binder(a, from, to)),
        _ => {}
    }
}

/// The typed generic telescope of a function as its leading implicit parameters.
fn generic_params(f: &FnDecl) -> Vec<(Name, T)> {
    f.generic_parameters()
}

fn core_rejects(name: &str, m: Message, span: Span) -> Diagnostic {
    Diagnostic::new(
        msg!("kernel-core-rejects", name = name, message = m),
        Some(span),
    )
}

/// The kernel reads curried binders only (`shape` makes them so).
/// What the core reads of a term is what the kernel's binders are: each
/// binds one name, and none is named as a sort.
fn kernel_binders(t: &T) -> Result<(), Diagnostic> {
    let sort = |n: &str, sp| {
        if sort_named(n).is_some() {
            return err(msg!("kernel-sort-names-variable", name = n), sp);
        }
        Ok(())
    };
    match &*t.kind {
        TermKind::Pi { params, result, .. } => {
            let [(n, d)] = params.as_slice() else {
                return err(msg!("kernel-binder-one-name"), t.span);
            };
            if let Some(n) = n {
                sort(n, t.span)?;
            }
            kernel_binders(d)?;
            kernel_binders(result)
        }
        TermKind::Lam { params, body, .. } => {
            let [n] = params.as_slice() else {
                return err(msg!("kernel-binder-one-name"), t.span);
            };
            sort(n, t.span)?;
            kernel_binders(body)
        }
        TermKind::App { .. } => t.try_applications(|part, _| kernel_binders(part)),
        _ => Ok(()),
    }
}

/// The subterm of `t` at the path `at` of a [`Failure`]: a term, and how
/// many of its arguments are applied when it is an application (an
/// application is read one argument at a time).
fn locate<'a>(t: &'a T, at: &[u8]) -> (&'a T, usize) {
    let all = |t: &T| match &*t.kind {
        TermKind::App { arguments, .. } => arguments.len(),
        _ => 0,
    };
    let (mut t, mut k) = (t, all(t));
    for step in at {
        match (&*t.kind, step) {
            (TermKind::App { function, .. }, 0) => {
                k -= 1;
                if k == 0 {
                    t = function;
                    k = all(t);
                }
            }
            (TermKind::App { arguments, .. }, _) => {
                t = &arguments[k - 1];
                k = all(t);
            }
            (TermKind::Pi { params, .. }, 0) => {
                t = &params[0].1;
                k = all(t);
            }
            (TermKind::Pi { result, .. }, _) => {
                t = result;
                k = all(t);
            }
            (TermKind::Lam { body, .. }, _) => {
                t = body;
                k = all(t);
            }
            _ => break,
        }
    }
    (t, k)
}

/// `t` with only its first `k` arguments, when it is an application.
fn applied(t: &T, k: usize) -> T {
    match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } if k < arguments.len() => T::new(
            TermKind::App {
                function: function.clone(),
                arguments: arguments[..k].to_vec(),
            },
            Span {
                end: arguments[k - 1].span.end,
                ..t.span
            },
        ),
        _ => t.clone(),
    }
}

/// Names that never stand for a declaration or a variable: the sorts, and
/// `_`, which binds nothing.
fn is_reserved(name: &str) -> bool {
    if name == "recursor" {
        return true;
    }
    name == "_" || sort_named(name).is_some()
}

/// The names `t` mentions that it does not bind, in the order met.
pub fn free_vars(t: &T) -> Vec<Name> {
    let mut out: Vec<Name> = Vec::new();
    visit_vars(t, &mut |n| {
        if !out.iter().any(|o| o == n) {
            out.push(n.clone());
        }
    });
    out
}

fn visit_vars(t: &T, f: &mut impl FnMut(&Name)) {
    fn go(t: &T, bound: &mut Vec<Name>, f: &mut impl FnMut(&Name)) {
        match &*t.kind {
            TermKind::Var(n) if !bound.contains(n) => f(n),
            TermKind::App { .. } => t.for_each_in_applications(|part| go(part, bound, f)),
            TermKind::Pi { params, result, .. } => {
                let depth = bound.len();
                for (n, d) in params {
                    go(d, bound, f);
                    bound.push(n.clone().unwrap_or_else(|| "_".into()));
                }
                go(result, bound, f);
                bound.truncate(depth);
            }
            TermKind::Lam { params, body, .. } => {
                let depth = bound.len();
                bound.extend(params.iter().cloned());
                go(body, bound, f);
                bound.truncate(depth);
            }
            // A product type (`SynIdent × SynExpr`), a union and a labelled
            // member mention the types they are made of.
            TermKind::Product(items) | TermKind::Union(items) | TermKind::Tuple(items) => {
                items.iter().for_each(|i| go(i, bound, f))
            }
            TermKind::Tagged { term, .. } => go(term, bound, f),
            _ => {}
        }
    }
    go(t, &mut Vec::new(), f)
}

fn is_op(name: &str) -> bool {
    matches!(name, "+" | "*" | "-")
}

fn is_local(ctx: &Ctx, name: &Name) -> bool {
    ctx.iter().any(|(n, _)| n == name)
}

/// The names `occurs` finds in `t`: its free variables, as far as it looks.
/// The free names of a term, collected the first time a binder asks
/// whether it would capture one. A substitution that meets no binder (an
/// argument put into a long chain of applications) does not walk the value.
struct FreeNames<'a> {
    of: &'a T,
    names: std::cell::OnceCell<HashSet<Name>>,
}

impl<'a> FreeNames<'a> {
    fn of(of: &'a T) -> Self {
        FreeNames {
            of,
            names: std::cell::OnceCell::new(),
        }
    }

    fn contains(&self, n: &Name) -> bool {
        self.names
            .get_or_init(|| {
                let mut names = HashSet::new();
                free_names(self.of, &mut Vec::new(), &mut names);
                names
            })
            .contains(n)
    }
}

fn free_names(t: &T, bound: &mut Vec<Name>, out: &mut HashSet<Name>) {
    match &*t.kind {
        TermKind::Var(n) => {
            if !bound.iter().any(|b| b == n) {
                out.insert(n.clone());
            }
        }
        TermKind::App {
            function,
            arguments,
        } => {
            free_names(function, bound, out);
            for a in arguments {
                free_names(a, bound, out);
            }
        }
        TermKind::Pi { params, result, .. } => {
            let depth = bound.len();
            for (name, domain) in params {
                free_names(domain, bound, out);
                if let Some(name) = name {
                    bound.push(name.clone());
                }
            }
            free_names(result, bound, out);
            bound.truncate(depth);
        }
        TermKind::Lam { params, body, .. } => {
            let depth = bound.len();
            bound.extend(params.iter().cloned());
            free_names(body, bound, out);
            bound.truncate(depth);
        }
        TermKind::Field { base, .. } => free_names(base, bound, out),
        TermKind::Ascribe { term, ty } => {
            free_names(term, bound, out);
            free_names(ty, bound, out);
        }
        _ => {}
    }
}

/// Every `x.f` in `t` replaced by a name, for asking whether the rest of `t`
/// is syntax the kernel reads.
fn fields_as_names(t: &mut T) {
    if let TermKind::Field { .. } = &*t.kind {
        *t = T::var("_", t.span);
        return;
    }
    crate::surface::walk::children(t, &mut fields_as_names);
}

fn occurs(t: &T, x: &Name) -> bool {
    match &*t.kind {
        TermKind::Var(n) => n == x,
        TermKind::App {
            function,
            arguments,
        } => occurs(function, x) || arguments.iter().any(|a| occurs(a, x)),
        TermKind::Pi { params, result, .. } => {
            for (name, domain) in params {
                if occurs(domain, x) {
                    return true;
                }
                if name.as_deref() == Some(x) {
                    return false;
                }
            }
            occurs(result, x)
        }
        TermKind::Lam { params, body, .. } => {
            !params.iter().any(|name| name == x) && occurs(body, x)
        }
        TermKind::Field { base, .. } => occurs(base, x),
        TermKind::Ascribe { term, ty } => occurs(term, x) || occurs(ty, x),
        _ => false,
    }
}

fn kind_name(kind: &TermKind) -> &'static str {
    match kind {
        TermKind::Text(_) => "text",
        // A literal is read only once `std/Float.taut` is imported (`sugar.rs`).
        TermKind::Float(_) => {
            "a Float literal (a Float literal is read as a kernel term only after `Float` is \
             declared, and only when it is finite; add `import std::Float`)"
        }
        TermKind::Exists { .. } => "∃",
        TermKind::Union(_) => "union",
        TermKind::Tagged { .. } => "tagged term",
        TermKind::If { .. } => "if",
        TermKind::Field { .. } => "field",
        TermKind::Block(_) => "block",
        TermKind::Perform { .. } => "perform",
        TermKind::Handle { .. } => "handle",
        TermKind::Budget { .. } => "budget",
        TermKind::Match { .. } => "match",
        TermKind::Record { .. } => "record",
        TermKind::Tuple(_) => "tuple",
        _ => "this syntax",
    }
}

/// The longest diagnostic term shown in full.
const SHOWN_LIMIT: usize = 300;

fn shorten(s: &str) -> String {
    let n = s.chars().count();
    if n <= SHOWN_LIMIT {
        return s.to_string();
    }
    let head: String = s.chars().take(SHOWN_LIMIT).collect();
    format!("{head}… ({} more characters)", n - SHOWN_LIMIT)
}

/// `t` as a message shows it. A name the checker made up when it renamed a
/// binder (`b'2396`, never one a program can write) is shown without its
/// counter, as `b'`, with one more `'` for each other made-up `b` in `t`.
pub fn describe(t: &T) -> String {
    describe_in(t, &mut ShownNames::default(), 0)
}

#[derive(Default)]
struct ShownNames {
    names: HashMap<Name, String>,
    counts: HashMap<String, usize>,
}

/// How tightly an operator `describe` shows binds: a larger number binds
/// tighter, in the same order as the parser: `*` before `+` and `-`.
fn op_precedence(op: &str) -> u8 {
    match op {
        "*" => 2,
        _ => 1,
    }
}

/// `t` described where it must bind at least as tightly as `outer`: an
/// operator that binds looser, or a `∀`, `->` or `=>` under an operator or
/// in front of `(…)`, is put in parentheses. Operators group to the left,
/// so `a + (b + c)` keeps its parentheses and `(a + b) + c` loses them.
fn describe_in(t: &T, shown: &mut ShownNames, outer: u8) -> String {
    let name = |n: &Name, shown: &mut ShownNames| -> String {
        let Some((base, counter)) = n.split_once('\'') else {
            return n.to_string();
        };
        if base.is_empty() || counter.is_empty() || !counter.bytes().all(|b| b.is_ascii_digit()) {
            return n.to_string();
        }
        if let Some(s) = shown.names.get(n) {
            return s.clone();
        }
        let count = shown.counts.entry(base.to_string()).or_default();
        *count += 1;
        let s = format!("{base}{}", "'".repeat(*count));
        shown.names.insert(n.clone(), s.clone());
        s
    };
    let paren = |yes: bool, s: String| if yes { format!("({s})") } else { s };
    match &*t.kind {
        TermKind::Var(n) => name(n, shown),
        TermKind::Nat(n) => n.clone(),
        TermKind::Hole(n) => format!("?{n}"),
        TermKind::Bool(b) => b.to_string(),
        TermKind::App {
            function,
            arguments,
        } => match &*function.kind {
            // `Eq(T, a, b)` is written `a = b`, which binds looser than any operator.
            TermKind::Var(eq)
                if tauto_surface::bindings::is_library(&eq, "Eq") && arguments.len() == 3 =>
            {
                let a = describe_in(&arguments[1], shown, 1);
                let b = describe_in(&arguments[2], shown, 1);
                paren(outer > 0, format!("{a} = {b}"))
            }
            TermKind::Var(op) if is_op(op) && arguments.len() == 2 => {
                let prec = op_precedence(op);
                let a = describe_in(&arguments[0], shown, prec);
                let b = describe_in(&arguments[1], shown, prec + 1);
                paren(outer > prec, format!("{a} {op} {b}"))
            }
            // `a = b` as a program writes it (`eqs_written`), looser than
            // every other operator.
            TermKind::Var(eq)
                if tauto_surface::bindings::is_library(&eq, "=") && arguments.len() == 2 =>
            {
                let a = describe_in(&arguments[0], shown, 1);
                let b = describe_in(&arguments[1], shown, 1);
                paren(outer > 0, format!("{a} = {b}"))
            }
            _ => {
                let f = describe_in(function, shown, u8::MAX);
                let args: Vec<String> =
                    arguments.iter().map(|a| describe_in(a, shown, 0)).collect();
                format!("{f}({})", args.join(", "))
            }
        },
        TermKind::Pi { params, result, .. } => {
            let s = match &params[0].0 {
                // `(P) -> False` as a program writes it, `¬P`.
                n if !n
                    .as_ref()
                    .is_some_and(|n| n.spelling() != Some("_") && occurs(result, n))
                    && matches!(&*result.kind, TermKind::Var(f) if tauto_surface::bindings::is_library(&f, "False")) =>
                {
                    format!("¬{}", describe_in(&params[0].1, shown, 3))
                }
                Some(n) if n.spelling() != Some("_") && occurs(result, n) => {
                    let n = name(n, shown);
                    let domain = describe_in(&params[0].1, shown, 0);
                    format!("∀ {n}: {domain}. {}", describe_in(result, shown, 0))
                }
                _ => {
                    let domain = describe_in(&params[0].1, shown, 0);
                    format!("({domain}) -> {}", describe_in(result, shown, 0))
                }
            };
            paren(outer > 0, s)
        }
        TermKind::Lam { params, body, .. } => {
            let x = name(&params[0], shown);
            paren(outer > 0, format!("{x} => {}", describe_in(body, shown, 0)))
        }
        _ => "…".into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::check;

    #[test]
    fn generated_names_are_distinguished_by_identity_when_described() {
        let span = Span::new(0, 1);
        let first = Name::from(tauto_surface::identity::LocalRef::fresh("x'1"));
        let second = Name::from(tauto_surface::identity::LocalRef::fresh("x'1"));
        let other = Name::from(tauto_surface::identity::LocalRef::fresh("y'2"));
        let term = T::new(
            TermKind::App {
                function: Box::new(T::var("f", span)),
                arguments: vec![
                    T::var(&first, span),
                    T::var(&other, span),
                    T::var(&second, span),
                    T::var(&first, span),
                ],
            },
            span,
        );
        assert_eq!(describe(&term), "f(x', y', x'', x')");
    }

    #[test]
    fn substitution_preserves_shared_nodes_and_shadowed_binders() {
        let span = Span::new(1, 2);
        let x: Name = tauto_surface::identity::LocalRef::fresh("x").into();
        let y: Name = tauto_surface::identity::LocalRef::fresh("y").into();
        let f: Name = tauto_surface::identity::DeclRef::fresh("f").into();
        let app = |arguments: Vec<T>| {
            T::new(
                TermKind::App {
                    function: Box::new(T::var(&f, span)),
                    arguments,
                },
                span,
            )
        };
        let shared = app(vec![T::var(&x, span)]);
        let bound = lam(&x, shared.clone());
        let mut other_position = shared.clone();
        other_position.span = Span::new(3, 4);
        let input = app(vec![shared.clone(), shared, bound.clone(), other_position]);
        let output = Kernel::new().subst(&input, &x, &T::var(&y, span));
        let TermKind::App { arguments, .. } = &*output.kind else {
            panic!("application")
        };
        assert!(std::sync::Arc::ptr_eq(
            &arguments[0].kind,
            &arguments[1].kind
        ));
        assert!(std::sync::Arc::ptr_eq(&arguments[2].kind, &bound.kind));
        assert_eq!(arguments[0].span, span);
        assert_eq!(arguments[3].span, Span::new(3, 4));
        assert_eq!(free_vars(&arguments[0]), vec![f, y]);
    }

    fn named_pi(params: &[(&str, &str)], result: T) -> T {
        T::new(
            TermKind::Pi {
                params: params
                    .iter()
                    .map(|(name, domain)| {
                        (
                            (!name.is_empty()).then(|| (*name).into()),
                            T::var(*domain, Default::default()),
                        )
                    })
                    .collect(),
                result: Box::new(result),
                effects: None,
            },
            Default::default(),
        )
    }

    fn named_lambda(params: &[&str], body: T) -> T {
        T::new(
            TermKind::Lam {
                params: params.iter().map(|name| (*name).into()).collect(),
                body: Box::new(body),
                types: Vec::new(),
            },
            Default::default(),
        )
    }

    #[test]
    fn free_vars_sees_the_members_of_a_product() {
        let v = |n: &str| T::var(n, Default::default());
        let tagged = T::new(
            TermKind::Tagged {
                tag: "renamed".into(),
                term: Box::new(v("SynExpr")),
            },
            Default::default(),
        );
        let product = T::new(
            TermKind::Product(vec![v("SynIdent"), tagged]),
            Default::default(),
        );
        let ty = T::app("List", vec![product], Default::default());
        assert_eq!(
            free_vars(&ty),
            ["List", "SynIdent", "SynExpr"].map(Name::from)
        );
    }

    #[test]
    fn describe_keeps_the_parentheses_operators_need() {
        let v = |n: &str| T::var(n, Default::default());
        let op = |o: &str, a: T, b: T| T::app(o, vec![a, b], Default::default());
        let cases = [
            (op("+", v("a"), op("+", v("b"), v("c"))), "a + (b + c)"),
            (op("+", op("+", v("a"), v("b")), v("c")), "a + b + c"),
            (op("-", v("a"), op("-", v("b"), v("c"))), "a - (b - c)"),
            (op("*", op("+", v("a"), v("b")), v("c")), "(a + b) * c"),
            (op("+", v("a"), op("*", v("b"), v("c"))), "a + b * c"),
            (op("*", v("a"), op("*", v("b"), v("c"))), "a * (b * c)"),
            (
                T::app("f", vec![op("+", v("a"), v("b"))], Default::default()),
                "f(a + b)",
            ),
            (
                T::app(
                    "Eq",
                    vec![v("Nat"), op("+", v("a"), v("b")), v("c")],
                    Default::default(),
                ),
                "a + b = c",
            ),
            (
                op(
                    "+",
                    v("a"),
                    T::app("Eq", vec![v("Nat"), v("b"), v("c")], Default::default()),
                ),
                "a + (b = c)",
            ),
        ];
        for (term, shown) in cases {
            assert_eq!(describe(&term), shown);
        }
    }

    #[test]
    fn named_binder_traversal_empty_binders_keep_free_names() {
        let value = T::var("outside", Default::default());
        for term in [named_pi(&[], value.clone()), named_lambda(&[], value)] {
            let mut bound = vec!["existing".into()];
            let mut names = HashSet::new();
            free_names(&term, &mut bound, &mut names);
            assert_eq!(names, HashSet::from(["outside".into()]));
            assert_eq!(bound, [Name::from("existing")]);
            assert!(occurs(&term, &Name::from("outside")));
            assert!(!occurs(&term, &Name::from("existing")));
        }
    }

    #[test]
    fn named_binder_traversal_dependent_domains_are_sequential() {
        let term = named_pi(
            &[("A", "Type"), ("value", "A"), ("", "Outside")],
            T::app(
                "Result",
                vec![
                    T::var("A", Default::default()),
                    T::var("value", Default::default()),
                ],
                Default::default(),
            ),
        );
        let mut bound = vec!["existing".into()];
        let mut names = HashSet::new();
        free_names(&term, &mut bound, &mut names);
        assert_eq!(
            names,
            HashSet::from(["Type".into(), "Outside".into(), "Result".into()])
        );
        assert_eq!(bound, [Name::from("existing")]);
        for name in ["Type", "Outside", "Result"] {
            assert!(occurs(&term, &Name::from(name)), "{name}");
        }
        for name in ["A", "value", "existing"] {
            assert!(!occurs(&term, &Name::from(name)), "{name}");
        }
        let own_domain = named_pi(&[("A", "A")], T::var("A", Default::default()));
        assert!(occurs(&own_domain, &Name::from("A")));
    }

    #[test]
    fn named_binder_traversal_lambda_shadowing_restores_outer_scope() {
        let term = named_lambda(
            &["first", "second", "existing"],
            named_pi(
                &[("first", "Outside")],
                T::var("second", Default::default()),
            ),
        );
        let mut bound = vec!["existing".into()];
        let mut names = HashSet::new();
        free_names(&term, &mut bound, &mut names);
        assert_eq!(names, HashSet::from(["Outside".into()]));
        assert_eq!(bound, [Name::from("existing")]);
        assert!(occurs(&term, &Name::from("Outside")));
        for name in ["first", "second", "existing"] {
            assert!(!occurs(&term, &Name::from(name)), "{name}");
        }
    }

    #[test]
    fn hole_context_retains_the_supplied_local_reference() {
        let span = Default::default();
        let parameter: Name = tauto_surface::identity::LocalRef::fresh("P").into();
        let proposition: Name = tauto_surface::identity::DeclRef::of_sort(
            tauto_surface::identity::SortSymbol::Proposition,
        )
        .into();
        let declaration = Stmt::Theorem(TheoremDecl {
            name: tauto_surface::identity::DeclRef::fresh("pending").into(),
            params: vec![(parameter.clone(), T::var(&proposition, span))],
            implicit: 0,
            ty: T::var(&parameter, span),
            body: Some(T::new(TermKind::Hole("proof".into()), span)),
            span,
            budget: None,
            vis: Default::default(),
            decreasing_by: None,
        });
        for _ in 0..2 {
            let entries = Kernel::new().declare_program(&Program {
                stmts: vec![declaration.clone()],
                errors: Vec::new(),
            });
            let Verdict::Incomplete { holes, .. } = &entries.last().unwrap().verdict else {
                panic!("{entries:?}");
            };
            assert_eq!(holes[0].context[0].0, parameter);
            assert!(matches!(&*holes[0].goal.kind, TermKind::Var(name) if name == &parameter));
        }
    }

    fn verdict(source: &str, name: &str) -> Verdict {
        check(source)
            .unwrap()
            .into_iter()
            .find(|e| e.name.as_str() == name)
            .unwrap()
            .verdict
    }

    #[test]
    fn overflowing_level_expressions_are_not_sorts() {
        let span = Span { start: 0, end: 0 };
        let nat = |n: &str| T::new(TermKind::Nat(n.into()), span);
        let plus = |a: T, n: &str| {
            T::new(
                TermKind::App {
                    function: Box::new(T::var("+", span)),
                    arguments: vec![a, nat(n)],
                },
                span,
            )
        };
        assert!(level_of(&plus(nat("4294967295"), "1")).is_none());
        assert!(level_of(&plus(plus(T::var("u", span), "4294967295"), "1")).is_none());
    }

    #[test]
    fn mismatch_shows_the_differing_part_computed() {
        let source = "inductive Seq(A: Type): Type {
  Nil: Seq(A)
  Cons(h: A, t: Seq(A)): Seq(A)
}
fn pad(n: Nat): Seq(Nat) { Nat::rec(k => Seq(Nat), Nil(Nat), k => ih => Cons(Nat, 0, ih), n) }
theorem t(): Cons(Nat, 1, pad(2)) = Cons(Nat, 1, Nil(Nat)) { Refl(Seq(Nat), Cons(Nat, 1, pad(2))) }";
        match verdict(source, "t") {
            Verdict::Failed(d) => {
                assert!(
                    d.message
                        .to_string()
                        .contains("found `Seq::Cons(Nat, 0, Seq::Cons(Nat, 0, Seq::Nil(Nat)))`"),
                    "{d}"
                );
                assert!(
                    !d.message
                        .to_string()
                        .contains("differing part: expected `Nil(Nat)`, found `Nat::rec"),
                    "{d}"
                );
            }
            other => panic!("expected a failure, got {other:?}"),
        }
    }

    #[test]
    fn the_kernel_prelude_is_checked_and_assumes_only_quot_sound() {
        let mut kernel = Kernel::new();
        let names = declare_prelude(&mut kernel).unwrap();
        for name in [
            "Pair",
            "Quot::lift",
            QUOT_SOUND,
            "Ord",
            "Ord::laws@List",
            "Ord::laws@Option",
            "Ord::laws@Pair",
        ] {
            assert!(
                names.iter().any(|n| n.as_str() == name),
                "{name}: {names:?}"
            );
        }
    }

    /// `step` uses its argument twice, and each use goes through the whole
    /// sequence: without sharing, `grow(k)` would be reduced 2^k times.
    #[test]
    fn an_argument_used_twice_is_reduced_once() {
        // How many steps the kernel takes is its own business, so the source is here.
        let src = r#"inductive Seq: Type {
  Stop: Seq
  More(n: Nat, rest: Seq): Seq
}
fn r#copy(s: Seq): Seq {
  ⊢ Seq from match s {
    Stop => Stop
    More(n, rest) => More(n, r#copy(rest))
  }
}
fn longer(s: Seq): Nat {
  ⊢ Nat from match s {
    Stop => 0
    More(n, rest) => Succ(longer(rest))
  }
}
fn keep(k: Nat, s: Seq): Seq {
  (⊢ (Seq) -> Seq from match k {
    Zero => (t: Seq) => r#copy(t)
    Succ(j) => (t: Seq) => t
  })(s)
}
fn step(s: Seq): Seq {
  keep(longer(s), s)
}
fn grow(k: Nat): Seq {
  ⊢ Seq from match k {
    Zero => More(1, More(2, More(3, Stop)))
    Succ(j) => step(grow(j))
  }
}
theorem t(): grow(16) = More(1, More(2, More(3, Stop))) { Refl }"#;
        let program = parse_program(src).unwrap();
        let mut kernel = Kernel::new();
        declare_prelude(&mut kernel).unwrap();
        let entries = kernel.declare(&program, false);
        let t = entries.iter().find(|e| e.name.as_str() == "t").unwrap();
        assert!(
            matches!(t.verdict, Verdict::Checked { .. }),
            "{:?}",
            t.verdict
        );
        let steps = kernel
            .timings()
            .iter()
            .find(|t| t.name.as_str() == "t")
            .unwrap()
            .steps;
        assert!(steps < 100_000, "{steps} steps");
    }

    #[test]
    fn a_text_literal_without_text_names_the_missing_import() {
        let src = "theorem t(): Eq(Nat, 0, 0) { the(Nat, \"a\") }";
        match verdict(src, "t") {
            Verdict::Failed(d) => {
                assert!(d.message.to_string().contains("import std::Text"), "{d}")
            }
            Verdict::Skipped(why) => assert!(why.to_string().contains("import std::Text"), "{why}"),
            other => panic!("{other:?}"),
        }
    }

    // Each of these would prove `False` with no axiom if a name could stand
    // for two things.
}

/// A source read as one file of a program is, for the unit tests: the
/// prelude's sugar (`a = b`, `#(a, b)`) lowered, and a name the prelude or
/// another type also declares (a constructor `Mk`, as `BelowPair` has)
/// given its full name (`main.Counter.Mk`). Constructors are named by their
/// type; the kernel takes each name as one declaration.
#[cfg(test)]
pub(crate) fn parse_program(source: &str) -> Result<Program, String> {
    let mut program = crate::surface::parse_program_as_written(source)?;
    tauto_surface::surface::qualify::lower_prelude_sugar(&mut program.stmts);
    let mut files = [std::mem::take(&mut program.stmts)];
    if let Some((name, _)) =
        tauto_surface::surface::qualify::files(&mut files, &["main".into()], None).first()
    {
        return Err(format!("`{name}` is ambiguous"));
    }
    let [stmts] = files;
    program.stmts = stmts;
    Ok(program)
}

// Unit tests use declarations without macro expansion or file imports. The
// source-reading integration tests remain in the facade crate.
#[cfg(test)]
fn check(source: &str) -> Result<Vec<Entry>, String> {
    tauto_messages::install();
    let program = parse_program(source)?;
    let mut kernel = Kernel::new();
    declare_prelude(&mut kernel)?;
    Ok(kernel.declare(&program, false))
}

/// Whether `decreasing_by y` names a parameter of `f`: its recursion is
/// structural on it, not well-founded.
pub(crate) fn names_param(f: &FnDecl, y: &T) -> bool {
    matches!(&*y.kind, TermKind::Var(v) if f.params.contains(v))
}

/// Whether `t` has a hole `?h` in it.
fn has_hole(t: &T) -> bool {
    let mut found = false;
    let mut t = t.clone();
    crate::surface::walk::term(&mut t, &mut |s| {
        found |= matches!(&*s.kind, TermKind::Hole(_))
    });
    found
}

/// The names of the holes `?h` in `t`.
fn holes_in(t: &T) -> Vec<(String, Span)> {
    let mut found = Vec::new();
    let mut t = t.clone();
    crate::surface::walk::term(&mut t, &mut |s| {
        if let TermKind::Hole(h) = &*s.kind {
            found.push((h.clone(), s.span));
        }
    });
    found
}

/// Whether `expand_lets` refused a block for a value that nothing uses (an
/// unused `let`, a discarded statement), whose type would never be checked.
fn never_checked(d: &Diagnostic) -> bool {
    says(&d.message, &["kernel-statement-discarded", "kernel-let-unused"])
}

/// Whether `n` is written anywhere in `t`, under any binder and inside any
/// construct. It may say yes for a name a binder shadows, never no for one
/// that is there.
fn names_anywhere(t: &T, n: &Name) -> bool {
    let mut t = t.clone();
    let mut found = false;
    crate::surface::walk::term(&mut t, &mut |u| {
        if matches!(&*u.kind, TermKind::Var(x) if x == n) {
            found = true;
        }
    });
    found
}

fn mentions(t: &T, n: &Name) -> bool {
    let mut names = HashSet::new();
    free_names(t, &mut Vec::new(), &mut names);
    names.contains(n)
}

fn expand_numeral(t: T) -> T {
    let TermKind::Nat(n) = &*t.kind else {
        return t;
    };
    let span = t.span;
    match n.parse::<u128>() {
        Ok(0) => T::var(&tauto_surface::bindings::library_name("Zero"), span),
        Ok(k) => T::new(
            TermKind::App {
                function: Box::new(T::var(&tauto_surface::bindings::library_name("Succ"), span)),
                arguments: vec![T::new(TermKind::Nat((k - 1).to_string()), span)],
            },
            span,
        ),
        Err(_) => t,
    }
}

/// How many times as large a `mutual` block's bodies may grow when the calls
/// of its functions not defined by a `match` are written out.
const WRITTEN_OUT_GROWTH: u128 = 64;

/// How many subterms a mismatch computes before it shows the rest as written.
const COMPUTED_FUEL: usize = 2000;
const OPEN_COMPUTED_FUEL: usize = 8;

/// Whether `t` holds a function type with a row that is not empty.
fn has_effect_row(t: &T) -> bool {
    let mut found = false;
    crate::surface::walk::term(&mut t.clone(), &mut |t| {
        if let TermKind::Pi {
            effects: Some(row), ..
        } = &*t.kind
            && !row.is_empty()
        {
            found = true;
        }
    });
    found
}
