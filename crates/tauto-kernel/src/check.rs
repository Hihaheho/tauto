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

use std::collections::{BTreeSet, HashMap, HashSet};

use tauto_parol::Span;

use level::Level;

use crate::surface::{
    DataDecl, FnDecl, InductiveDecl, Program, Stmt, SurfaceTerm, TermKind, TheoremDecl,
};

type T = SurfaceTerm;

mod cache;
mod classes;
mod core;
#[cfg(feature = "selfhost")]
pub use core::selfhost;
use core::{Ask, Failed, Failure, Met, Typed};
mod deq;
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
pub use roles::{Checked, Family, Role, Signature};
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
pub fn declare_prelude(kernel: &mut Kernel) -> Result<Vec<String>, String> {
    type Declared = Result<(Kernel, Vec<String>), String>;
    thread_local! {
        static DECLARED: std::cell::OnceCell<Declared> = const { std::cell::OnceCell::new() };
    }
    let (declared, names) = DECLARED.with(|cell| cell.get_or_init(declare_prelude_once).clone())?;
    *kernel = declared;
    Ok(names)
}

fn declare_prelude_once() -> Result<(Kernel, Vec<String>), String> {
    let mut kernel = Kernel::new();
    let prelude = kernel_prelude()?;
    let mut names = Vec::new();
    for entry in kernel.declare(&prelude, true) {
        match entry.verdict {
            Verdict::Checked { axioms } if axioms.is_empty() => names.push(entry.name),
            Verdict::Checked { axioms } if entry.name == QUOT_SOUND && axioms == [QUOT_SOUND] => {
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

/// The messages that say a name is not defined.
const NOT_DEFINED: &[&str] = &[
    "kernel-not-defined",
    "kernel-not-defined-hint",
    "kernel-not-defined-yet",
    "kernel-not-defined-struct",
    "kernel-float-not-defined",
    "kernel-integer-division",
    "kernel-unit-value-as-type",
    "kernel-core-not-defined",
    "kernel-implicit-not-defined",
];

/// The messages that say two types do not match.
const TYPE_MISMATCH: &[&str] = &["kernel-mismatch", "kernel-core-type-mismatch"];

/// The messages that say a name used did not check.
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
    axioms: BTreeSet<String>,
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

type Ctx = Vec<(String, T)>;

#[derive(Clone)]
pub struct Kernel {
    globals: HashMap<String, Global>,
    /// Functions skipped as not terms of the kernel: a function that uses one
    /// is skipped too, not failed.
    skipped: HashSet<String>,
    /// The names declared by `fn` without effects: one without parameters
    /// of its own is called with `()`, never named bare.
    fns: HashSet<String>,
    inds: HashMap<String, inductive::Ind>,
    /// Constructor name → (family, index).
    ctors: HashMap<String, (String, usize)>,
    /// Eliminator name → family.
    recs: HashMap<String, String>,
    fresh: usize,
    /// Binders of the arrow types a match in a type is written under
    /// ([`Self::elaborate_type`]). A match does not generalize over one its
    /// arms do not use.
    arrow_binders: Vec<String>,
    /// Unknowns of the call being elaborated (`?n`), with their solutions.
    metas: HashMap<String, Option<T>>,
    /// The declaration being checked, for the message on a bad recursion.
    current: Option<String>,
    /// Inside a field taken out of a value: the value is matched as the `Pair` a product
    /// is unfolded to, which is no `#(…)` written where a `Pair` is.
    projecting: usize,
    /// Names the program declares that the kernel may not have yet: why a
    /// use of one is not defined (declared further on, or a `struct`).
    ahead: HashMap<String, Ahead>,
    /// The functions being defined by a `match`, with their types: a
    /// `match` on a call of one of them can be typed before the call becomes
    /// an induction hypothesis.
    defining: Vec<(String, T)>,
    /// How many leading parameters of each function being defined are implicit.
    defining_implicit: Vec<(String, usize)>,
    /// A recursion on parts deeper than the fields, while its arms are read.
    deep: Option<matching::DeepScope>,
    /// The matched variables of the arms being elaborated, each with the
    /// constructor it is in its arm, outermost first: a type written on a λ's
    /// parameter there reads the matched value as that constructor.
    matched: Vec<(String, T)>,
    /// The independent re-check of every accepted declaration.
    core: core::Core,
    /// The holes met while checking the declaration in hand.
    holes: Vec<HoleGoal>,
    /// Proofs checked before (`check/cache.rs`); none unless checking files.
    cache: Option<cache::Cache>,
    /// The terms the bodies elaborated to, by declaration, when asked for
    /// (`record_elaborated`).
    elaborated: Option<Vec<(String, T)>>,
    /// What a syntax macro's output was written as, by the span of its root node.
    shown: HashMap<u32, String>,
    /// The decidable equalities of the types declared so far are generated
    /// (`check/deq.rs`).
    deq_started: bool,
    /// For each `opaque fn f`, by the name of its equation `f::eq`: `f`, sealed
    /// once the equation is checked (`check/opaque.rs`).
    seal_after: HashMap<String, String>,
    /// The inductives that list their decidable equality (`=> fn T::beq, …`), and, for one that
    /// could not be made, why.
    deq_listed: HashMap<String, crate::surface::Generates>,
    deq_why: HashMap<String, Message>,
    /// The declarations generated for a decidable equality, by the family that lists them, as
    /// they checked: extraction writes them after the family, as if they were in its file.
    pub derived: Vec<(String, Vec<crate::surface::Stmt>)>,
    /// The classes and instances of the proof language (`check/classes.rs`).
    classes: classes::Registry,
    /// The level-polymorphic declarations and the instances made of them
    /// (`check/universe.rs`).
    templates: HashMap<String, universe::Template>,
    level_instances: HashSet<String>,
    level_depth: usize,
    /// How long one declaration may take (`Kernel::set_timeout`).
    timeout: Option<std::time::Duration>,
    /// How many steps of reduction one declaration may take
    /// (`Kernel::set_step_limit`).
    step_limit: Option<u64>,
    /// The declarations given their own limit on the steps (`Kernel::set_budget`).
    budgets: HashMap<String, u64>,
    /// Why nothing more is checked: a declaration ran out of time.
    gave_up: Option<String>,
    /// Whether the declaration in hand took its proof from the cache.
    from_cache: bool,
    /// The time each declaration took, in order.
    timings: Vec<Timing>,
    /// The effects and the functions with effects read in proofs
    /// (`check/effects.rs`).
    effects: effects::Effects,
}

/// How long a declaration took to check, and the reduction it did.
#[derive(Debug, Clone)]
pub struct Timing {
    pub name: String,
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
    Skipped(String),
}

fn declared_name(stmt: &Stmt) -> Option<String> {
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
/// The declarations are declared one at a time whether a kernel is kept or
/// not, so the kernel (its fresh names included) is the same either way.
/// They are declared in the order a whole file's check reads them
/// (`order::dependency_order`), so a declaration that uses one written after
/// it in the prefix checks here as it does there.
fn declare_prefix(prefix: &[Stmt]) -> Result<Kernel, String> {
    /// How many kernels are kept.
    const KEPT: usize = 8;
    let ordered = order::dependency_order(prefix);
    let prefix = &ordered[..];
    thread_local! {
        /// Most recently used last.
        static KEPT_KERNELS: std::cell::RefCell<Vec<(Vec<Stmt>, Kernel)>> =
            const { std::cell::RefCell::new(Vec::new()) };
    }
    let last = KEPT_KERNELS.with(|cell| {
        let mut kept = cell.borrow_mut();
        let at = kept
            .iter()
            .enumerate()
            .filter(|(_, (stmts, _))| {
                stmts.len() <= prefix.len() && stmts[..] == prefix[..stmts.len()]
            })
            .max_by_key(|(_, (stmts, _))| stmts.len())
            .map(|(i, _)| i)?;
        let entry = kept.remove(at);
        let found = (entry.0.len(), entry.1.clone());
        kept.push(entry);
        Some(found)
    });
    let kept_already = last
        .as_ref()
        .is_some_and(|(known, _)| *known == prefix.len());
    let (known, mut kernel) = match last {
        Some(last) => last,
        None => {
            let mut kernel = Kernel::new();
            declare_prelude(&mut kernel)?;
            (0, kernel)
        }
    };
    for stmt in &prefix[known..] {
        kernel.declare(
            &Program {
                stmts: vec![stmt.clone()],
                errors: Vec::new(),
            },
            false,
        );
    }
    if !kept_already {
        KEPT_KERNELS.with(|cell| {
            let mut kept = cell.borrow_mut();
            if kept.len() == KEPT {
                kept.remove(0);
            }
            kept.push((prefix.to_vec(), kernel.clone()));
        });
    }
    Ok(kernel)
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
) -> Result<(Vec<(String, SurfaceTerm)>, SurfaceTerm), String> {
    let mut kernel = declare_prefix(prefix)?;
    let rendered = |d: Diagnostic| d.message.to_string();
    let (ctx, _) = kernel
        .shaped_signature(&decl.params, &decl.ty)
        .map_err(rendered)?;
    let shaped = kernel.shape(term).map_err(rendered)?;
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
    let term = crate::surface::modules::resolve_term_against(
        term,
        kernel.globals.keys().map(|k| k.as_str()),
    );
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
    pub(crate) fn nullary_fn(&self, ctx: &Ctx, g: &str) -> bool {
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
    pub(crate) fn eqs_written(t: &T) -> T {
        fn go(t: &mut T) {
            if let TermKind::App {
                function,
                arguments,
            } = &*t.kind
                && matches!(&*function.kind, TermKind::Var(eq) if eq == "Eq")
                && arguments.len() == 3
            {
                let mut sides = arguments[1..].to_vec();
                sides.iter_mut().for_each(go);
                *t = T::app("=", sides, t.span);
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
    pub fn new(prefix: &[Stmt], context: &[(String, SurfaceTerm)]) -> Result<Self, String> {
        let mut kernel = declare_prefix(prefix)?;
        let mut ctx: Ctx = Vec::new();
        for (n, d) in context {
            let d = kernel.shape(d).map_err(|e| e.message.to_string())?;
            let d = kernel
                .elab(&ctx, &d, None)
                .map_err(|e| e.message.to_string())?;
            ctx.push((n.clone(), d));
        }
        Ok(Elaborator { kernel, ctx })
    }

    /// The term with its implicit arguments written out, and its type.
    pub fn infer(&mut self, t: &SurfaceTerm) -> Result<(SurfaceTerm, SurfaceTerm), String> {
        let shaped = self.kernel.shape(t).map_err(|e| e.message.to_string())?;
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

    /// The term checked against a type.
    pub fn check(&mut self, t: &SurfaceTerm, ty: &SurfaceTerm) -> Result<SurfaceTerm, String> {
        let (ty, _) = self.infer(ty)?;
        let shaped = self.kernel.shape(t).map_err(|e| e.message.to_string())?;
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

    /// Whether the two terms are definitionally equal.
    pub fn defeq(&mut self, a: &SurfaceTerm, b: &SurfaceTerm) -> Result<bool, String> {
        let (a, _) = self.infer(a)?;
        let (b, _) = self.infer(b)?;
        Ok(self.kernel.conv(&self.ctx, &a, &b))
    }

    /// The term reduced to weak head normal form.
    pub fn whnf(&mut self, t: &SurfaceTerm) -> Result<SurfaceTerm, String> {
        let (e, _) = self.infer(t)?;
        let e = self.kernel.whnf(&self.ctx, &e);
        Ok(self.kernel.calls_written(&e))
    }

    /// The type of a declaration before the one in hand, or of a variable of
    /// the context.
    pub fn type_of(&self, name: &str) -> Option<SurfaceTerm> {
        if let Some((_, t)) = self.ctx.iter().rev().find(|(n, _)| n == name) {
            return Some(self.kernel.calls_written(t));
        }
        self.kernel
            .globals
            .get(name)
            .map(|g| self.kernel.calls_written(&g.ty))
    }
}

/// An entry and the file it came from.
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
    /// Where the call was written.
    pub at: Option<(std::path::PathBuf, usize, usize)>,
    pub steps: u64,
    pub captures: Vec<String>,
}

/// A constant the kernel knows after checking a file: what a proof may use.
#[derive(Debug, Clone)]
pub struct LibEntry {
    pub name: String,
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
    pub name: String,
    /// The fields a pattern names: the arguments after the generics.
    pub fields: Vec<(String, SurfaceTerm)>,
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
        out.sort_by(|a, b| a.name.cmp(&b.name));
        out
    }
}

impl Kernel {
    /// Keeps the term each body elaborates to, for `elaborated`. A proof
    /// taken from the cache is not elaborated, so do not use both.
    pub fn record_elaborated(&mut self) {
        self.elaborated = Some(Vec::new());
    }

    /// The terms the bodies elaborated to, in order, since
    /// `record_elaborated`.
    pub fn elaborated(&self) -> &[(String, SurfaceTerm)] {
        self.elaborated.as_deref().unwrap_or_default()
    }

    pub fn use_cache(&mut self) {
        self.cache = cache::Cache::from_env();
    }

    /// Gives up on a declaration whose check takes longer than `limit`: it is
    /// rejected, and the declarations after it are not checked.
    pub fn set_timeout(&mut self, limit: Option<std::time::Duration>) {
        self.timeout = limit;
    }

    /// Gives up on a declaration whose check takes more than `limit` steps of
    /// reduction (`None`: no limit): it is rejected, and the declarations
    /// after it are not checked. The count is the same on every machine.
    pub fn set_step_limit(&mut self, limit: Option<u64>) {
        self.step_limit = limit;
    }

    /// Lets the declaration `name` take `steps` steps of reduction in place of
    /// the limit of [`Kernel::set_step_limit`].
    pub fn set_budget(&mut self, name: &str, steps: u64) {
        self.budgets.insert(name.to_string(), steps);
    }

    /// The time each declaration checked so far took, in order.
    pub fn timings(&self) -> &[Timing] {
        &self.timings
    }

    pub fn show_syntax(&mut self, shown: HashMap<u32, String>) {
        self.shown = shown;
    }

    pub fn new() -> Self {
        let mut k = Kernel {
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
            cache: None,
            elaborated: None,
            shown: HashMap::new(),
            deq_started: false,
            seal_after: HashMap::new(),
            deq_listed: HashMap::new(),
            deq_why: HashMap::new(),
            derived: Vec::new(),
            classes: Default::default(),
            templates: HashMap::new(),
            level_instances: Default::default(),
            level_depth: 0,
            timeout: None,
            step_limit: Some(core::DEFAULT_STEP_LIMIT),
            budgets: HashMap::new(),
            gave_up: None,
            from_cache: false,
            timings: Vec::new(),
            effects: Default::default(),
        };
        let sp = Span::new(0, 0);
        let nat = T::var("Nat", sp);
        let binary = pi("_", nat.clone(), pi("_", nat.clone(), nat));
        for op in ["+", "*", "-"] {
            k.globals.insert(
                op.into(),
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
        let stmts = order::dependency_order(&lowered);
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
        let stmts = self.effect_pass(&stmts);
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
            self.core
                .start_budget(limit, self.timeout.map(|limit| started + limit));
            self.from_cache = false;
            if let Some(name) = self.template_of(stmt) {
                self.check_template(&name, builtin, &mut entries);
            } else if let Some(name) = declared_name(stmt)
                && let Some(owner) = self.instance_of(&name)
                && matches!(self.ahead.get(owner), Some(Ahead::Failed))
            {
                // An instance of a template that does not check for every
                // level is not used, even where it would check.
                entries.push(Entry {
                    verdict: Verdict::Failed(Diagnostic::new(
                        msg!("kernel-uses-failed", name = owner),
                        None,
                    )),
                    name,
                });
            } else {
                self.declare_one(stmt, builtin, &mut entries);
            }
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
                    self.gave_up = Some(msg!("kernel-ran-out-of-time", name = &e.name).to_string());
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

    /// Checks one statement of [`Kernel::declare`], adding its entries.
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
                    Some(why) => Verdict::Skipped(
                        msg!("kernel-handle-not-read", why = why.clone()).to_string(),
                    ),
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
            Stmt::Theorem(t) | Stmt::Def(t) => Some(t.name.as_str()),
            Stmt::Fn(f) => Some(f.name.as_str()),
            Stmt::Inductive(i) => Some(i.name.as_str()),
            Stmt::Let { name, .. } => Some(name.as_str()),
            _ => None,
        };
        if let Some(name) = declared
            && is_reserved(name)
        {
            entries.push(Entry {
                name: name.to_string(),
                verdict: Verdict::Failed(Diagnostic::new(
                    msg!("kernel-reserved", name = name),
                    None,
                )),
            });
            return;
        }
        if let Some(name) = declared
            && self.globals.contains_key(name)
        {
            entries.push(Entry {
                name: name.to_string(),
                verdict: Verdict::Failed(Diagnostic::new(
                    msg!("kernel-already-defined", name = name),
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
    fn axioms_of(&self, uses: &BTreeSet<String>) -> Option<BTreeSet<String>> {
        let mut axioms = BTreeSet::new();
        for n in uses {
            axioms.extend(self.globals.get(n)?.axioms.iter().cloned());
        }
        Some(axioms)
    }

    /// A theorem whose proof checked before (`check/cache.rs`): its statement
    /// is checked, by both checkers, and its proof taken as it was.
    fn theorem_checked_before(&mut self, t: &TheoremDecl, axioms: BTreeSet<String>) -> Verdict {
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
    /// only the core checks it.
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
        match &t.body {
            None => {
                if !builtin || t.name == QUOT_SOUND {
                    axioms.insert(t.name.clone());
                }
            }
            Some(body) => {
                self.current = Some(t.name.clone());
                let proof = (|| {
                    if let Some(lam) = before {
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
                    self.check(&Vec::new(), &lam, &statement)?;
                    Ok::<_, Diagnostic>(lam)
                })();
                self.current = None;
                let proof = match proof {
                    Ok(lam) => match self.uses_failed(&lam) {
                        Some(n) => err(msg!("kernel-uses-failed", name = n), t.span),
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
                    msg!("kernel-uses-failed", name = n),
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
        if let Err(m) = self
            .core
            .add_decl(&t.name, &statement, checked.as_ref(), false)
        {
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

    /// A sort's name, or `_`, cannot name a declaration.
    fn reserved(&self, name: &str, span: Span) -> Option<Diagnostic> {
        is_reserved(name).then(|| Diagnostic::new(msg!("kernel-reserved", name = name), Some(span)))
    }

    fn set_params(&mut self, name: &str, n: usize) {
        if let Some(g) = self.globals.get_mut(name) {
            g.params = Some(n);
        }
    }

    fn set_implicit(&mut self, name: &str, n: usize) {
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
            _ => String::new(),
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
                return fail(items, msg!("kernel-already-defined", name = &n));
            }
            if is_reserved(&n) {
                return fail(items, msg!("kernel-reserved", name = &n));
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
                return fail(items, msg!("kernel-mutual-decidable", name = &d.name));
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
                Ok(Some((matched, plain))) => {
                    let mut entries = self.function_group(&matched, span);
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
    /// that calls the others), written out at each call of the block's
    /// `match`es: the block that is left, and those functions, which are
    /// declared after it. `None` when every body is a `match`, or none is.
    fn inline_plain(
        &mut self,
        items: &[Stmt],
    ) -> Result<Option<(Vec<Stmt>, Vec<FnDecl>)>, Message> {
        let is_plain =
            |s: &Stmt| matches!(s, Stmt::Fn(f) if !matches!(&*f.body.kind, TermKind::Match { .. }));
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
        if let Some(f) = plain.iter().find(|f| !f.generics.is_empty()) {
            return Err(msg!("kernel-mutual-plain-generics", name = &f.name));
        }
        let names: Vec<String> = plain.iter().map(|f| f.name.clone()).collect();
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
                return Err(msg!("kernel-mutual-plain-cycle", name = &names[j]));
            }
        }
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
                            name = n,
                            user = &f.name
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
        Ok(Some((matched, plain)))
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
            let fresh: Vec<String> = plain[i].params.iter().map(|p| self.fresh_name(p)).collect();
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
        type Decl = (String, usize, Vec<(String, T)>, T, T);
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
        let names: Vec<&str> = decls.iter().map(|d| d.0.as_str()).collect();
        let key = self.key(&format!("{items:?}"), &names);
        let before = key.as_ref().and_then(|k| {
            let terms = self.cache.as_ref()?.get_terms(k, span)?;
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
            // Elaborated before (`check/cache.rs`): only the core checks it.
            if let Some(lams) = before {
                for (st, lam) in statements.iter().zip(&lams) {
                    if let Some(n) = self.uses_failed(lam).or_else(|| self.uses_failed(st)) {
                        return err(msg!("kernel-uses-failed", name = n), span);
                    }
                }
                for ((name, ..), (st, lam)) in decls.iter().zip(statements.iter().zip(&lams)) {
                    if let Err(m) = self.core.add_decl(name, st, Some(lam), true) {
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
                        name: Some(name.as_str()),
                        implicit: *implicit,
                        params: params.clone(),
                        result: result.clone(),
                        body,
                    },
                )
                .collect();
            let compiled = self.compile_group(&specs)?;
            let mut lams = Vec::new();
            for (((_, _, params, _, _), c), statement) in
                decls.iter().zip(&compiled).zip(&statements)
            {
                let lam = self.lambda_of(params, c)?;
                let lam = self.shape(&lam)?;
                let lam = self.elab(&Vec::new(), &lam, Some(statement))?;
                self.check(&Vec::new(), &lam, statement)?;
                if !self.holes.is_empty() {
                    return err(msg!("kernel-mutual-hole"), span);
                }
                if let Some(n) = self
                    .uses_failed(&lam)
                    .or_else(|| self.uses_failed(statement))
                {
                    return err(msg!("kernel-uses-failed", name = n), span);
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
                            _ => String::new(),
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
                    _ => String::new(),
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
        if let Some(d) = value_generic(f) {
            self.skipped.insert(f.name.clone());
            return Verdict::Failed(d);
        }
        // A function with effects is read as a function of the kernel
        // (`check/effects.rs`), and its bare name is that function's value.
        if !self.effects.fns.contains_key(&f.name) {
            self.fns.insert(f.name.clone());
        }
        let mut verdict = self.function_term(f);
        if let Verdict::Failed(d) = &verdict {
            // A name the failure is about (`n` is not defined yet, uses `n`,
            // which did not check), or one the body reads.
            let text = d.message.to_string();
            let mut uses = text
                .split('`')
                .skip(1)
                .step_by(2)
                .find(|n| self.skipped.contains(*n))
                .map(str::to_string);
            visit_vars(&f.body, &mut |n| {
                if uses.is_none() && self.skipped.contains(n) {
                    uses = Some(n.to_string());
                }
            });
            if let Some(n) = uses {
                verdict = Verdict::Skipped(msg!("kernel-uses-skipped", name = n).to_string());
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
            return Verdict::Skipped(msg!("kernel-has-effects", why = why).to_string());
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
                .chain(std::iter::once((&f.name, &f.result)))
                .find_map(|(n, t)| t.as_ref().filter(|t| has_effect_row(t)).map(|_| n))
        {
            return Verdict::Skipped(if *p == f.name {
                msg!("kernel-result-effect-row").to_string()
            } else {
                msg!("kernel-param-effect-row", name = p).to_string()
            });
        }
        let Some(result) = &f.result else {
            return Verdict::Skipped(msg!("kernel-no-result-type").to_string());
        };
        let mut params = generic_params(f);
        for (n, t) in f.params.iter().zip(&f.param_types) {
            match t {
                Some(t) => params.push((n.clone(), t.clone())),
                None => return Verdict::Skipped(msg!("kernel-untyped-param").to_string()),
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
        let body = match self.expand_lets(&f.body) {
            Ok(b) => b,
            Err(_) => f.body.clone(),
        };
        if !matching::has_match(&body) && self.shape(&body).is_err() {
            return Verdict::Skipped(msg!("kernel-body-executable").to_string());
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
            return Verdict::Skipped(msg!("kernel-type-not-kernel").to_string());
        }
        let key = self.key(&format!("{f:?}"), &[f.name.as_str()]);
        let before = key.as_ref().and_then(|k| {
            let mut terms = self.cache.as_ref()?.get_terms(k, f.body.span)?;
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
        }
        if let Some(lam) = checked
            && self.core.set_value(&f.name, &lam).is_ok()
            && let Some(g) = self.globals.get_mut(&f.name)
        {
            g.value = Some(lam);
        }
        verdict
    }

    fn constant(&mut self, name: &str, value: &T) -> Verdict {
        if let Some(d) = self.reserved(name, value.span) {
            return Verdict::Failed(d);
        }
        let result = self.shape(value).and_then(|v| {
            let ty = self.infer(&Vec::new(), &v)?;
            if let Some(n) = self.uses_failed(&v) {
                return err(msg!("kernel-uses-failed", name = n), v.span);
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
                true => Verdict::Skipped(d.message.to_string()),
                false => Verdict::Failed(d),
            },
        }
    }

    fn add(&mut self, name: &str, ty: T, value: Option<T>, axioms: BTreeSet<String>) {
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
    fn add_incomplete(&mut self, name: &str, ty: T) {
        self.add(name, ty, None, BTreeSet::new());
        if let Some(g) = self.globals.get_mut(name) {
            g.incomplete = true;
        }
    }

    /// The incomplete declarations `t` mentions, in the order met.
    fn uses_incomplete(&self, t: &T) -> Vec<String> {
        let mut found = Vec::new();
        visit_vars(t, &mut |n| {
            if self.globals.get(n).is_some_and(|g| g.incomplete) && !found.iter().any(|f| f == n) {
                found.push(n.to_string());
            }
        });
        found
    }

    /// Keeps the statement of a declaration that did not check, marked so
    /// that a later declaration using it fails too.
    fn add_failed(&mut self, name: &str, ty: T) {
        self.add(name, ty, None, BTreeSet::new());
        if let Some(g) = self.globals.get_mut(name) {
            g.failed = true;
        }
    }

    /// A declaration that did not check and that `t` mentions.
    fn uses_failed(&self, t: &T) -> Option<String> {
        let mut found = None;
        visit_vars(t, &mut |n| {
            if found.is_none() && self.globals.get(n).is_some_and(|g| g.failed) {
                found = Some(n.to_string());
            }
        });
        found
    }

    fn collect_axioms(&self, t: &T, out: &mut BTreeSet<String>) {
        let mut uses = BTreeSet::new();
        self.collect_globals(t, &mut uses);
        for n in uses {
            out.extend(self.globals[&n].axioms.iter().cloned());
        }
    }

    /// The globals `t` names, where `collect_axioms` looks for them.
    fn collect_globals(&self, t: &T, out: &mut BTreeSet<String>) {
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

    // ---- shapes ---------------------------------------------------------

    /// `(x: A, y: B) -> T` as nested `Pi`.
    fn telescope(&mut self, params: &[(String, T)], result: &T) -> Result<T, Diagnostic> {
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
        params: &[(String, T)],
        result: &T,
    ) -> Result<(Vec<(String, T)>, T), Diagnostic> {
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
    fn elaborate_type(&mut self, t: &T, ctx: &[(String, T)]) -> Result<T, Diagnostic> {
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
                        Some(n) if n != "_" => n.clone(),
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
    fn kernel_type(&mut self, ctx: &[(String, T)], d: &T) -> Result<T, Diagnostic> {
        let mut typing: Ctx = self.defining.clone();
        typing.extend(ctx.iter().cloned());
        let d = self.shape(d)?;
        self.elab(&typing, &d, None)
    }

    /// The parameters and the result type, shaped and with their implicit
    /// arguments written out.
    fn shaped_signature(
        &mut self,
        params: &[(String, T)],
        result: &T,
    ) -> Result<(Vec<(String, T)>, T), Diagnostic> {
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
    pub(super) fn shape_type(&mut self, t: &T, ctx: &[(String, T)]) -> Result<T, Diagnostic> {
        match matching::has_written_match(t) || matching::has_equality(t) {
            true => self.elaborate(t, ctx),
            false => self.shape(t),
        }
    }

    fn lambda_of(&self, params: &[(String, T)], body: &T) -> Result<T, Diagnostic> {
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
                    function: Box::new(T::var("Exists", sp)),
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
            TermKind::Match { .. } => {
                return err(msg!("kernel-not-kernel-term-match"), sp);
            }
            TermKind::Text(_) if !self.inds.contains_key("Text") => {
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
        Ok(match &*t.kind {
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
                        return err(msg!("kernel-block-lets"), sp);
                    };
                    let value = self.expand_lets(value)?;
                    let vsp = value.span;
                    // Without a type, the value stands for the name as it is.
                    let annotated = match ty {
                        Some(ty) => T::new(
                            TermKind::App {
                                function: Box::new(T::var("the", vsp)),
                                arguments: vec![self.expand_lets(ty)?, value],
                            },
                            vsp,
                        ),
                        None => value,
                    };
                    let next = self.subst(&body, name, &annotated);
                    if next == body {
                        // An unused `let` would never have its type checked.
                        return err(msg!("kernel-let-unused", name = name), vsp);
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
        })
    }

    // ---- names and substitution ----------------------------------------

    fn fresh_name(&mut self, base: &str) -> String {
        self.fresh += 1;
        let base = base.trim_end_matches(|c: char| c == '\'' || c.is_ascii_digit());
        format!("{base}'{}", self.fresh)
    }

    fn subst(&mut self, t: &T, x: &str, v: &T) -> T {
        let names = FreeNames::of(v);
        self.subst_in(t, x, v, &names).unwrap_or_else(|| t.clone())
    }

    /// `t` with `v` for `x`, or `None` when `t` does not change: an unchanged
    /// part is shared with `t`, not copied. `names` are the free names of `v`,
    /// which a binder would capture.
    fn subst_in(&mut self, t: &T, x: &str, v: &T, names: &FreeNames) -> Option<T> {
        let sp = t.span;
        match &*t.kind {
            TermKind::Var(n) if n == x => Some(v.clone()),
            TermKind::App {
                function,
                arguments,
            } => {
                let f = self.subst_in(function, x, v, names);
                let args: Vec<Option<T>> = arguments
                    .iter()
                    .map(|a| self.subst_in(a, x, v, names))
                    .collect();
                if f.is_none() && args.iter().all(Option::is_none) {
                    return None;
                }
                Some(T::new(
                    TermKind::App {
                        function: Box::new(f.unwrap_or_else(|| (**function).clone())),
                        arguments: args
                            .into_iter()
                            .zip(arguments)
                            .map(|(new, old)| new.unwrap_or_else(|| old.clone()))
                            .collect(),
                    },
                    sp,
                ))
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
                let d2 = self.subst_in(d, x, v, names);
                let r2 = self.under_binder(&name, result, x, v, names);
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
                    Some(Some(ty)) => Some(self.subst_in(ty, x, v, names)),
                    _ => None,
                };
                let under = self.under_binder(&params[0], body, x, v, names);
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
                        for b in bound.iter().filter(|b| names.contains(b.as_str())) {
                            let b2 = self.fresh_name(b);
                            let to = T::var(&b2, arm.body.span);
                            rename_pattern_binder(&mut arm.pattern, b, &b2);
                            arm.body = self.subst(&arm.body, b, &to);
                            arm.guard = arm.guard.map(|g| self.subst(&g, b, &to));
                            arm.goal = arm.goal.map(|g| self.subst(&g, b, &to));
                        }
                        let arm = &arm;
                        let goal = arm.goal.as_ref().map(|g| self.subst_in(g, x, v, names));
                        let guard = arm.guard.as_ref().map(|g| self.subst_in(g, x, v, names));
                        let body = self.subst_in(&arm.body, x, v, names);
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
                let scrutinee2 = self.subst_in(scrutinee, x, v, names);
                let result2 = result.as_ref().map(|r| self.subst_in(r, x, v, names));
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
                let b = self.subst_in(base, x, v, names)?;
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
                let t2 = self.subst_in(term, x, v, names);
                let ty2 = self.subst_in(ty, x, v, names);
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
            _ => None,
        }
    }

    /// Substitutes below a binder `n`, renaming it when it would capture;
    /// `None` when nothing changes.
    fn under_binder(
        &mut self,
        n: &str,
        body: &T,
        x: &str,
        v: &T,
        names: &FreeNames,
    ) -> Option<(String, T)> {
        if n == x {
            return None;
        }
        if names.contains(n) {
            let n2 = self.fresh_name(n);
            let renamed = self.subst(body, n, &T::var(&n2, body.span));
            let body = self.subst_in(&renamed, x, v, names).unwrap_or(renamed);
            Some((n2, body))
        } else {
            Some((n.to_string(), self.subst_in(body, x, v, names)?))
        }
    }

    /// The name a binder `n` over `body` is entered under. Contexts are
    /// lists of names, so a binder that reuses the name of a variable in
    /// `ctx`, of a global, or of a free name of `outer` would make those
    /// mean the bound variable inside; it is renamed (and `body` with it).
    pub(super) fn enter_binder(
        &mut self,
        ctx: &Ctx,
        n: &str,
        body: &T,
        outer: &[&T],
    ) -> (String, T) {
        if n == "_" {
            // `_` binds nothing, so it is entered under a name of its own.
            return (self.fresh_name("_"), body.clone());
        }
        let clashes = n != "_"
            && (is_local(ctx, n)
                || self.globals.contains_key(n)
                || self.current.as_deref() == Some(n)
                || outer.iter().any(|t| occurs(t, n)));
        if !clashes {
            return (n.to_string(), body.clone());
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
        x: &str,
        body: &T,
        name: &str,
        domain: &T,
        result: &T,
    ) -> (String, T) {
        if name == x {
            self.enter_binder(ctx, x, body, &[domain])
        } else {
            self.enter_binder(ctx, x, body, &[domain, result])
        }
    }

    // ---- reduction and conversion --------------------------------------

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
        let named = |n: &str| {
            self.inds.contains_key(n)
                || self
                    .inds
                    .values()
                    .any(|i| i.ctors.iter().any(|c| c.name == n))
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

    // ---- typing ---------------------------------------------------------

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
        let declared = |n: &str| globals.get(n).map(|g| g.ty.clone());
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
        let context: Vec<(String, T)> = ctx
            .iter()
            .chain(&m.bound)
            .map(|(n, t)| (n.clone(), self.beta(t)))
            .collect();
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

    /// The constructor `name` is in another case convention, when exactly
    /// one is: its full name, or a qualified one whose last part matches.
    fn respelled_ctor(&self, name: &str) -> Option<String> {
        let mut names: Vec<&str> = self.ctors.keys().map(String::as_str).collect();
        names.sort_unstable();
        if let Some(c) = tauto_surface::suggest::respelled(name, names.iter().copied()) {
            return Some(c.to_string());
        }
        let short: Vec<&str> = names
            .iter()
            .map(|c| c.rsplit_once('.').map_or(*c, |(_, s)| s))
            .collect();
        let hit = tauto_surface::suggest::respelled(name, short.iter().copied())?;
        let full: Vec<&&str> = names
            .iter()
            .filter(|c| c.rsplit_once('.').map_or(**c, |(_, s)| s) == hit)
            .collect();
        match full.as_slice() {
            [one] => Some(one.to_string()),
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
                    TermKind::Var(n) if n == "_" => msg!("kernel-underscore-not-value"),
                    TermKind::Var(n) if n == "Float" => msg!("kernel-float-not-defined"),
                    TermKind::Var(n) if n == "/" => msg!("kernel-integer-division"),
                    TermKind::Var(n) if n == "#()" => msg!("kernel-unit-value-as-type"),
                    TermKind::Var(n) if self.current.as_deref() == Some(n.as_str()) => {
                        msg!("kernel-calls-itself", name = n)
                    }
                    TermKind::Var(n) => match self.ahead.get(n.as_str()) {
                        _ if self.globals.contains_key(n.as_str()) => {
                            msg!("kernel-not-defined", name = n)
                        }
                        Some(Ahead::Later) => msg!("kernel-not-defined-yet", name = n),
                        Some(Ahead::Failed) => msg!("kernel-uses-failed", name = n),
                        Some(Ahead::Struct) => msg!("kernel-not-defined-struct", name = n),
                        Some(Ahead::Skipped(why)) => {
                            msg!("kernel-uses-skipped-why", name = n, why = why.clone())
                        }
                        // A constructor renamed to another case convention
                        // (`drain_free` to `DrainFree`) is named; the old
                        // name is not kept as a second one.
                        None => match self.respelled_ctor(n) {
                            Some(hint) => msg!("kernel-not-defined-hint", name = n, hint = hint),
                            None => msg!("kernel-not-defined", name = n),
                        },
                    },
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
    fn tidy_hole(&mut self, mut goal: T, mut context: Vec<(String, T)>) -> (T, Vec<(String, T)>) {
        let mut i = 0;
        while i < context.len() {
            let name = context[i].0.clone();
            let base = name.split_once('\'').and_then(|(b, n)| {
                (!b.is_empty() && !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
                    .then(|| b.to_string())
            });
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

    /// `t` is a type; which sort it lives in.
    fn expect_type(&mut self, ctx: &Ctx, t: &T) -> Result<Sort, Diagnostic> {
        let typed = self.ask_core(ctx, t, Ask::Sort)?;
        Ok(typed.sort.expect("a sort"))
    }

    fn check(&mut self, ctx: &Ctx, t: &T, expected: &T) -> Result<(), Diagnostic> {
        self.ask_core(ctx, t, Ask::Check(expected)).map(|_| ())
    }

    /// The mismatch of `found` with `expected` at `span`, with its parts.
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
            let global = self.globals.get(g.as_str())?;
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

// ---- helpers ----------------------------------------------------------

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

    /// The sort of this sort.
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

fn sort_named(name: &str) -> Option<Sort> {
    if name == "Prop" {
        return Some(Sort::Prop);
    }
    let rest = name.strip_prefix("Type")?;
    if rest.is_empty() {
        Some(Sort::ty(0))
    } else {
        rest.parse().ok().map(Sort::ty)
    }
}

fn sort_of(t: &T) -> Option<Sort> {
    match &*t.kind {
        TermKind::Var(n) => sort_named(n),
        // `Type(u + 1)`: a sort whose level has variables.
        TermKind::App {
            function,
            arguments,
        } if matches!(&*function.kind, TermKind::Var(n) if n == "Type") && arguments.len() == 1 => {
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
            (TermKind::Var(op), [a, b]) if op == "+" => {
                let TermKind::Nat(k) = &*b.kind else {
                    return None;
                };
                level_of(a)?.plus(k.parse().ok()?)
            }
            (TermKind::Var(op), [a, b]) if op == "max" => Some(level_of(a)?.join(&level_of(b)?)),
            _ => None,
        },
        _ => None,
    }
}

/// `level` written as a term.
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
                    function: Box::new(T::var("+", span)),
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
                function: Box::new(T::var("max", span)),
                arguments: vec![acc, p],
            },
            span,
        )
    })
}

fn sort_term(s: &Sort, span: Span) -> T {
    match s {
        Sort::Prop => T::var("Prop", span),
        Sort::Type(l) => match l.as_const() {
            Some(0) => T::var("Type", span),
            Some(n) => T::var(&format!("Type{n}"), span),
            None => T::new(
                TermKind::App {
                    function: Box::new(T::var("Type", span)),
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
            && matches!(&*function.kind, TermKind::Var(op) if op == "==" || op == "!=") =>
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

fn pi(name: &str, domain: T, result: T) -> T {
    let span = result.span;
    T::new(
        TermKind::Pi {
            params: vec![(Some(name.to_string()), domain)],
            result: Box::new(result),
            effects: None,
        },
        span,
    )
}

fn lam(name: &str, body: T) -> T {
    let span = body.span;
    T::new(
        TermKind::Lam {
            params: vec![name.to_string()],
            body: Box::new(body),
            types: Vec::new(),
        },
        span,
    )
}

/// The names a pattern binds, in the order met.
fn pattern_binders(p: &crate::surface::Pattern, out: &mut Vec<String>) {
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
fn rename_pattern_binder(p: &mut crate::surface::Pattern, from: &str, to: &str) {
    use crate::surface::Pattern;
    match p {
        Pattern::Bind(n) if n == from => *n = to.to_string(),
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

/// The generics `<A, B>` of a function as its leading parameters, each a
/// `Type`; like a theorem's, they are implicit.
fn generic_params(f: &FnDecl) -> Vec<(String, T)> {
    let sp = f.body.span;
    f.generics
        .iter()
        .map(|g| (g.clone(), T::var("Type", sp)))
        .collect()
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
pub fn free_vars(t: &T) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    visit_vars(t, &mut |n| {
        if !out.iter().any(|o| o == n) {
            out.push(n.to_string());
        }
    });
    out
}

fn visit_vars(t: &T, f: &mut impl FnMut(&str)) {
    fn go(t: &T, bound: &mut Vec<String>, f: &mut impl FnMut(&str)) {
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

fn is_local(ctx: &Ctx, name: &str) -> bool {
    ctx.iter().any(|(n, _)| n == name)
}

/// The names `occurs` finds in `t`: its free variables, as far as it looks.
/// The free names of a term, collected the first time a binder asks
/// whether it would capture one. A substitution that meets no binder (an
/// argument put into a long chain of applications) does not walk the value.
struct FreeNames<'a> {
    of: &'a T,
    names: std::cell::OnceCell<HashSet<String>>,
}

impl<'a> FreeNames<'a> {
    fn of(of: &'a T) -> Self {
        FreeNames {
            of,
            names: std::cell::OnceCell::new(),
        }
    }

    fn contains(&self, n: &str) -> bool {
        self.names
            .get_or_init(|| {
                let mut names = HashSet::new();
                free_names(self.of, &mut Vec::new(), &mut names);
                names
            })
            .contains(n)
    }
}

fn free_names(t: &T, bound: &mut Vec<String>, out: &mut HashSet<String>) {
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

fn occurs(t: &T, x: &str) -> bool {
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

/// The longest term a mismatch shows in full.
const SHOWN_LIMIT: usize = 300;

/// `s` cut to `SHOWN_LIMIT` characters, saying how much was left out.
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
    let mut shown = HashMap::new();
    describe_in(t, &mut shown, 0)
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
fn describe_in(t: &T, shown: &mut HashMap<String, String>, outer: u8) -> String {
    let name = |n: &str, shown: &mut HashMap<String, String>| -> String {
        let Some((base, counter)) = n.split_once('\'') else {
            return n.to_string();
        };
        if base.is_empty() || counter.is_empty() || !counter.bytes().all(|b| b.is_ascii_digit()) {
            return n.to_string();
        }
        if let Some(s) = shown.get(n) {
            return s.clone();
        }
        let mut s = format!("{base}'");
        while shown.values().any(|v| *v == s) {
            s.push('\'');
        }
        shown.insert(n.to_string(), s.clone());
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
            TermKind::Var(eq) if eq == "Eq" && arguments.len() == 3 => {
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
            // `Eq(T, a, b)` as a program writes it, `a = b`, looser than
            // every other operator.
            TermKind::Var(eq) if eq == "Eq" && arguments.len() == 3 => {
                let a = describe_in(&arguments[1], shown, 1);
                let b = describe_in(&arguments[2], shown, 1);
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
                n if !n.as_ref().is_some_and(|n| n != "_" && occurs(result, n))
                    && matches!(&*result.kind, TermKind::Var(f) if f == "False") =>
                {
                    format!("¬{}", describe_in(&params[0].1, shown, 3))
                }
                Some(n) if n != "_" && occurs(result, n) => {
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

    fn named_pi(params: &[(&str, &str)], result: T) -> T {
        T::new(
            TermKind::Pi {
                params: params
                    .iter()
                    .map(|(name, domain)| {
                        (
                            (!name.is_empty()).then(|| (*name).into()),
                            T::var(domain, Default::default()),
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
        assert_eq!(free_vars(&ty), ["List", "SynIdent", "SynExpr"]);
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
            assert_eq!(bound, ["existing"]);
            assert!(occurs(&term, "outside"));
            assert!(!occurs(&term, "existing"));
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
        assert_eq!(bound, ["existing"]);
        for name in ["Type", "Outside", "Result"] {
            assert!(occurs(&term, name), "{name}");
        }
        for name in ["A", "value", "existing"] {
            assert!(!occurs(&term, name), "{name}");
        }
        let own_domain = named_pi(&[("A", "A")], T::var("A", Default::default()));
        assert!(occurs(&own_domain, "A"));
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
        assert_eq!(bound, ["existing"]);
        assert!(occurs(&term, "Outside"));
        for name in ["first", "second", "existing"] {
            assert!(!occurs(&term, name), "{name}");
        }
    }

    fn verdict(source: &str, name: &str) -> Verdict {
        check(source)
            .unwrap()
            .into_iter()
            .find(|e| e.name == name)
            .unwrap()
            .verdict
    }

    fn ok(source: &str, name: &str) {
        assert!(
            matches!(verdict(source, name), Verdict::Checked { .. }),
            "{:?}",
            verdict(source, name)
        );
    }

    fn rejected(source: &str, name: &str, why: &str) {
        match verdict(source, name) {
            Verdict::Failed(d) => assert!(d.message.to_string().contains(why), "{d}"),
            other => panic!("expected a failure, got {other:?}"),
        }
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
                    d.message.to_string().contains(
                        "found `main::Seq::Cons(Nat, 0, main::Seq::Cons(Nat, 0, main::Seq::Nil(Nat)))`"
                    ),
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
            assert!(names.iter().any(|n| n == name), "{name}: {names:?}");
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
  match s: Seq {
    Stop => Stop
    More(n, rest) => More(n, r#copy(rest))
  }
}
fn longer(s: Seq): Nat {
  match s: Nat {
    Stop => 0
    More(n, rest) => Succ(longer(rest))
  }
}
fn keep(k: Nat, s: Seq): Seq {
  match k: (Seq) -> Seq {
    Zero => (t: Seq) => r#copy(t)
    Succ(j) => (t: Seq) => t
  }(s)
}
fn step(s: Seq): Seq {
  keep(longer(s), s)
}
fn grow(k: Nat): Seq {
  match k: Seq {
    Zero => More(1, More(2, More(3, Stop)))
    Succ(j) => step(grow(j))
  }
}
theorem t(): grow(16) = More(1, More(2, More(3, Stop))) { Refl }"#;
        let program = parse_program(src).unwrap();
        let mut kernel = Kernel::new();
        declare_prelude(&mut kernel).unwrap();
        let entries = kernel.declare(&program, false);
        let t = entries.iter().find(|e| e.name == "t").unwrap();
        assert!(
            matches!(t.verdict, Verdict::Checked { .. }),
            "{:?}",
            t.verdict
        );
        let steps = kernel
            .timings()
            .iter()
            .find(|t| t.name == "t")
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
            Verdict::Skipped(why) => assert!(why.contains("import std::Text"), "{why}"),
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

/// A generic of `f` bounded by the type of a value, `P: (A) -> Prop`, at
/// where it is written. A function's generics are types, instantiated
/// afresh at every use and bounded by a kind (`shared`, `(shared) -> shared`);
/// a predicate or a proof is an ordinary parameter, as in a theorem.
fn value_generic(f: &FnDecl) -> Option<Diagnostic> {
    const KINDS: [&str; 4] = ["copy", "shared", "affine", "linear"];
    let is_kind = |k: &str| KINDS.contains(&k);
    f.generics
        .iter()
        .zip(&f.bounds)
        .enumerate()
        .find_map(|(i, (g, b))| {
            let b = b.as_deref()?;
            let value = b == "Prop"
                || b.strip_prefix('(')
                    .is_some_and(|rest| match rest.split_once(")->") {
                        Some((arg, result)) => !(is_kind(arg) && is_kind(result)),
                        None => true,
                    });
            value.then(|| {
                Diagnostic::new(
                    format!(
                        "the generic `{g}: {b}` of `{}` is not a type: a function's generics \
                     are types bounded by a kind (`shared`, `linear`, …); \
                     pass the predicate as an ordinary parameter",
                        f.name
                    ),
                    Some(f.bound_spans.get(i).copied().unwrap_or(f.span)),
                )
            })
        })
}

/// Whether `decreasing_by y` names a parameter of `f`: its recursion is
/// structural on it, not well-founded.
pub(crate) fn names_param(f: &FnDecl, y: &T) -> bool {
    matches!(&*y.kind, TermKind::Var(v) if f.params.contains(v))
}

/// Whether the free name `n` occurs in `t`.
fn mentions(t: &T, n: &str) -> bool {
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
        Ok(0) => T::var("Zero", span),
        Ok(k) => T::new(
            TermKind::App {
                function: Box::new(T::var("Succ", span)),
                arguments: vec![T::new(TermKind::Nat((k - 1).to_string()), span)],
            },
            span,
        ),
        Err(_) => t,
    }
}

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
