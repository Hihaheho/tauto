//! The surface term: one AST for types and expressions.
//!
//! The parser keeps the `Type` and `Expr` grammars apart; here both
//! become a [`SurfaceTerm`], so `Vector(i64, n + 1)` holds the term `n + 1`
//! as a term and a type is just a term that happens to be one. Nothing here
//! decides which terms are pure or what their type is; that is the
//! elaborator's job. Syntax this module does not read yet becomes
//! [`TermKind::Other`], keeping its span.

pub use crate::identity::Name;

use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::span::Span;

pub mod dump;
pub mod effect_sets;
pub mod extern_blocks;
pub mod fence;
mod literal;
pub mod loops;
pub mod modules;
pub mod parsed;
pub mod print;
mod program;
pub mod qualify;
pub mod references;
pub mod scoped;
pub mod shift;
pub mod superclasses;
pub mod walk;
pub use literal::{Lexical, LitForm, LitSite, SyntaxLit};

/// How a `□` written outside `⟦ ⟧` is read: an error, as no term stands for it.
/// `(a, b)` read as a term: a parenthesized list is no term (a product is `#(a, b)`).
pub const PAREN_LIST: &str = "parenthesized list";
pub const BOX_OUTSIDE: &str = "`□` outside `⟦ ⟧`";

/// Replaces the `□`s in `t` by the variable `name`, counting them in `found`; `bound` records
/// one written under a binder (`under`). The parts a binder does not scope over (a λ's types,
/// the domain of `∃` and of a function type's first parameter, the value matched) are filled
/// before the rest, so the walk over everything finds no `□` left in them.
pub fn fill_box(t: &mut SurfaceTerm, name: &str, under: bool, found: &mut usize, bound: &mut bool) {
    if matches!(&*t.kind, TermKind::Other(m) if m == BOX_OUTSIDE) {
        *found += 1;
        *bound |= under;
        *t = SurfaceTerm::var(name, t.span);
        return;
    }
    let binds = matches!(
        &*t.kind,
        TermKind::Lam { .. }
            | TermKind::Pi { .. }
            | TermKind::Exists { .. }
            | TermKind::Match { .. }
            | TermKind::Block(_)
            | TermKind::Handle { .. }
            | TermKind::Quote { .. }
            | TermKind::Step(_)
    );
    if binds {
        match Arc::make_mut(&mut t.kind) {
            TermKind::Lam { types, .. } => {
                for ty in types.iter_mut().flatten() {
                    fill_box(ty, name, under, found, bound);
                }
            }
            TermKind::Exists { domain, .. } => fill_box(domain, name, under, found, bound),
            TermKind::Pi { params, .. } => {
                if let Some((_, first)) = params.first_mut() {
                    fill_box(first, name, under, found, bound);
                }
            }
            TermKind::Match { scrutinee, .. } => fill_box(scrutinee, name, under, found, bound),
            _ => {}
        }
    }
    walk::children(t, &mut |c| fill_box(c, name, under || binds, found, bound));
}
pub use program::{
    ClassDecl, CoerceLevel, Constraint, Constructor, DICT, DataCoerce, DataConstructor, DataDecl,
    EffectDecl, ExternInstance, FnDecl, GENERATED_BASE, Generates, GenericBound, Handler,
    InductiveDecl, InferCondition, Instance, InstanceDecl, LawDecl, MatchArm, PRELUDE_BASE,
    ParseError, Pattern, Program, Replace, Step, StepArm, Stmt, SyntaxUse, TextReader, TheoremDecl,
    Vis, WrittenRowEffect, alt_binders, dictionary_name, extern_block_id, extern_fn_has_body,
    extern_is_replaceable, parse_builtin_as_written_at, parse_builtin_at, parse_expr_at,
    parse_program_as_written, parse_program_unresolved_at, place_root, row_parameters_of,
    set_text_reader, with_vis,
};

/// The identity of one surface occurrence. Clones retain the identity; source
/// positions are diagnostic data and do not distinguish generated occurrences.
#[derive(Debug, Clone, Copy)]
pub struct TermId {
    serial: u64,
    span: Span,
}

impl TermId {
    /// A distinct internal occurrence, including a declaration without a body.
    pub fn fresh(span: Span) -> Self {
        Self {
            serial: SurfaceTerm::fresh_identity(),
            span,
        }
    }

    pub fn span(self) -> Span {
        self.span
    }
}

impl PartialEq for TermId {
    fn eq(&self, other: &Self) -> bool {
        self.serial == other.serial
    }
}
impl Eq for TermId {}
impl PartialOrd for TermId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TermId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.serial.cmp(&other.serial)
    }
}
impl Hash for TermId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.serial.hash(state);
    }
}

#[derive(Clone)]
pub struct SurfaceTerm {
    /// Shared: cloning a term costs a reference count, not a copy of the tree,
    /// which the checker does at every substitution and unfolding.
    pub kind: Arc<TermKind>,
    pub span: Span,
    identity: u64,
    /// A call as the source writes it, `f(a, b)`, which must write implicit
    /// arguments by name; the checker's own applications are not marked.
    written_call: bool,
    /// A call a macro writes as syntax (`ExApp`): checked as one the source
    /// writes, though its span is in the expansion's range.
    macro_call: bool,
    /// A field the coercion expansion wrote: the struct's own field, read
    /// without going through its `coerce` field.
    own_field: bool,
    /// A term a loop expansion made. It stands where the loop is written
    /// and has no text of its own, so a pass that rewrites the written
    /// source must leave it alone.
    lowered: bool,
    /// Permission granted to this occurrence by its lexical effect scope.
    perform_scope: Option<TermId>,
}

impl std::fmt::Debug for SurfaceTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            return f
                .debug_struct("SurfaceTerm")
                .field("kind", &self.kind)
                .field("span", &self.span)
                .finish();
        }
        // The text `#[derive(Debug)]` writes, with the last argument of an
        // application written in a loop: a list literal, or a text literal's
        // bytes, nests there once per element and would recurse as deep.
        let mut spans = Vec::new();
        let mut t = self;
        loop {
            write!(f, "SurfaceTerm {{ kind: ")?;
            spans.push(t.span);
            let TermKind::App {
                function,
                arguments,
            } = &*t.kind
            else {
                write!(f, "{:?}", t.kind)?;
                break;
            };
            write!(f, "App {{ function: {function:?}, arguments: [")?;
            let Some((last, init)) = arguments.split_last() else {
                write!(f, "] }}")?;
                break;
            };
            for a in init {
                write!(f, "{a:?}, ")?;
            }
            t = last;
        }
        let innermost = spans.len() - 1;
        for (i, span) in spans.iter().enumerate().rev() {
            if i < innermost {
                write!(f, "] }}")?;
            }
            write!(f, ", span: {span:?} }}")?;
        }
        Ok(())
    }
}

/// Dropped along the last arguments in a loop: a list literal, or a text
/// literal's bytes, nests there once per element, and the drop the compiler
/// writes would recurse as deep.
impl Drop for SurfaceTerm {
    fn drop(&mut self) {
        fn take_last(t: &mut SurfaceTerm) -> Option<SurfaceTerm> {
            match Arc::get_mut(&mut t.kind)? {
                TermKind::App { arguments, .. } => arguments.pop(),
                _ => None,
            }
        }
        let mut next = take_last(self);
        while let Some(mut t) = next {
            next = take_last(&mut t);
        }
    }
}

thread_local! {
    /// Whether [`SurfaceTerm`]'s equality leaves out the terms' positions,
    /// while [`same_term_structure`] looks for a difference.
    static SPANS_LEFT_OUT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

impl PartialEq for SurfaceTerm {
    fn eq(&self, other: &Self) -> bool {
        (self.span == other.span || SPANS_LEFT_OUT.with(|o| o.get())) && self.kind == other.kind
    }
}

/// Compares syntax and references without using term occurrence positions.
/// Declaration metadata in statement-valued syntax remains part of the comparison.
pub fn same_term_structure(left: &SurfaceTerm, right: &SurfaceTerm) -> bool {
    // Two terms that differ even with every term's position left out differ:
    // found without copying them, which a search for a term in another
    // (one comparison at each of its parts) would do at each part. When none
    // is found the two are compared as below, their positions erased.
    struct LeftOut(bool);
    impl Drop for LeftOut {
        fn drop(&mut self) {
            SPANS_LEFT_OUT.with(|o| o.set(self.0));
        }
    }
    let alike = {
        let _restore = LeftOut(SPANS_LEFT_OUT.with(|o| o.replace(true)));
        left == right
    };
    if !alike {
        return false;
    }
    fn erase_positions(term: &SurfaceTerm) -> SurfaceTerm {
        let mut term = term.clone();
        walk::term(&mut term, &mut |part| part.span = Span::new(0, 0));
        term
    }
    erase_positions(left) == erase_positions(right)
}

/// What a budget counts: the machine's steps (`perform budget(n, f)`), or
/// the cells its body allocates (`perform budget_memory(n, f)`:
/// constructors, closures, products, text and collections; see
/// `docs/design/semantics.md`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BudgetLimit {
    Steps,
    Memory,
}

impl BudgetLimit {
    pub fn name(self) -> &'static str {
        match self {
            BudgetLimit::Steps => "steps",
            BudgetLimit::Memory => "memory",
        }
    }

    /// The host's operation that runs a budget of this limit, which is
    /// also the effect a row names for it.
    pub fn operation(self) -> &'static str {
        match self {
            BudgetLimit::Steps => "budget",
            BudgetLimit::Memory => "budget_memory",
        }
    }

    /// The limit of the operation spelled `name`.
    pub fn of_operation(name: &str) -> Option<BudgetLimit> {
        match name {
            "budget" => Some(BudgetLimit::Steps),
            "budget_memory" => Some(BudgetLimit::Memory),
            _ => None,
        }
    }
}

/// `*a`, the place a borrow points to: the term `a` inside it. It is read as
/// the prefix `*` applied to one argument, and stands only on the left of `:=`.
pub fn deref_of(t: &SurfaceTerm) -> Option<&SurfaceTerm> {
    match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } if arguments.len() == 1
            && matches!(&*function.kind, TermKind::Var(f) if f.as_str() == DEREF) =>
        {
            arguments.first()
        }
        _ => None,
    }
}

/// The name the prefix `*` is read as.
pub const DEREF: &str = "*";

#[derive(Debug, Clone, PartialEq)]
pub enum TermKind {
    /// A host-issued declaration capability, with no source literal.
    Declaration(crate::identity::DeclRef),
    /// A name: `Nat`, `n`, `Type`, `Prop`.
    Var(Name),
    Nat(String),
    /// A `Float` literal as written: `1.5`, `2e10`, `6.02e23`.
    Float(String),
    Text(String),
    Bool(bool),
    /// An application, whatever its spelling: `f(x)`, `Eq(a, b)`,
    /// `a + b` (the function is the operator's name), `A ∧ B`.
    App {
        function: Box<SurfaceTerm>,
        arguments: Vec<SurfaceTerm>,
    },
    /// A dependent function type: `(x: A) -> B ! {e}`, `∀ x: A. B`. A
    /// parameter without a name does not occur in the result.
    Pi {
        params: Vec<(Option<Name>, SurfaceTerm)>,
        /// Where `^` is written before each binder, aligned with `params`.
        /// Empty means no binder is marked.
        unused: Vec<Option<Span>>,
        result: Box<SurfaceTerm>,
        /// The effects after `!`, when written.
        effects: Option<Vec<Name>>,
    },
    /// An effect row given to a data type's row parameter:
    /// `Handlers(!{key | e})`. A row variable `| e` is `|e`, as in
    /// [`TermKind::Pi`]'s effects.
    Row(Vec<Name>),
    /// `∃ x: A. B`
    Exists {
        binder: Name,
        /// Where `^` is written before the binder.
        unused: Option<Span>,
        domain: Box<SurfaceTerm>,
        body: Box<SurfaceTerm>,
    },
    Lam {
        params: Vec<Name>,
        /// Where `^` is written before each parameter, aligned with `params`.
        /// Empty means no parameter is marked.
        unused_params: Vec<Option<Span>>,
        body: Box<SurfaceTerm>,
        /// The types written on the parameters: empty when none is, else one
        /// for each parameter. The checker holds the parameters to them; the
        /// kernel's λ has no domain, so they do not reach it.
        types: Vec<Option<SurfaceTerm>>,
    },
    Union(Vec<SurfaceTerm>),
    Tagged {
        tag: String,
        term: Box<SurfaceTerm>,
    },
    If {
        condition: Box<SurfaceTerm>,
        then: Box<SurfaceTerm>,
        otherwise: Option<Box<SurfaceTerm>>,
    },
    Field {
        base: Box<SurfaceTerm>,
        name: String,
    },
    /// `(e: T)`: `e` at the written type `T`. Where `e` is a product, `T` may
    /// take fewer of its members (`(p: A)`, `(p: A × C)`, `(p: @a T)`).
    Ascribe {
        term: Box<SurfaceTerm>,
        ty: Box<SurfaceTerm>,
    },
    /// `{ stmt; stmt; value }`; the value is the last statement's.
    Block(Vec<Stmt>),
    Perform {
        effect: Name,
        args: Vec<SurfaceTerm>,
    },
    /// `handle { body } with { … }`, the handlers in the order written.
    Handle {
        body: Box<SurfaceTerm>,
        handlers: Vec<Handler>,
    },
    /// `perform budget(n, () => { body })` or `perform budget_memory(n, () => { body })`:
    /// the host's operations, read apart from other `perform`s. Both limits are two
    /// budgets, one in the body of the other.
    Budget {
        limit: BudgetLimit,
        /// The count, of steps or of cells as `limit` says.
        steps: Box<SurfaceTerm>,
        body: Box<SurfaceTerm>,
    },
    Match {
        scrutinee: Box<SurfaceTerm>,
        /// `match x -> T { … }`: the result type, which may mention `x`.
        result: Option<Box<SurfaceTerm>>,
        /// `match e eqn h -> T { … }`: the name of the equation between `e`
        /// and the arm's constructor, in the arms.
        binder: Option<Name>,
        /// Where `^` is written before the `eqn` binder.
        binder_unused: Option<Span>,
        arms: Vec<MatchArm>,
    },
    /// A named hole, `?h`: a term not written yet. The checker records its
    /// goal; a declaration that holds one is incomplete and is not added.
    Hole(String),
    /// `Point { x: 1, y: 2 }`: a struct's value, its fields by name.
    /// `Point { x: 1, ..p }` takes the fields not written from `p`
    /// (`base`); reading the program writes them out
    /// (`qualify::record_bases`), so the passes after it see no `base`.
    Record {
        name: Name,
        fields: Vec<(String, SurfaceTerm)>,
        base: Option<Box<SurfaceTerm>>,
    },
    Borrow {
        mutable: bool,
        /// `&orig x` / `&orig T`: the original value, not through `Lend`.
        orig: bool,
        /// `&rc e`: `e` moved into a new counted box, and `&rc T` its type.
        /// Every copy shares the box; the contents are read only through a
        /// shared borrow.
        rc: bool,
        term: Box<SurfaceTerm>,
    },
    /// `affine (A) -> B` or `linear (A) -> B`: a function type with its
    /// kind written. Without one a function type is `shared`.
    FnKind {
        kind: String,
        ty: Box<SurfaceTerm>,
    },
    /// A lambda some of whose parameters are borrowed, `(v: &A) => …`:
    /// for each parameter, `None` when it takes the value, `Some(mutable)`
    /// when it borrows.
    BorrowLam {
        borrows: Vec<Option<bool>>,
        lam: Box<SurfaceTerm>,
    },
    /// ``math`1 + 2` ``: a syntax's literal. `syntax::expand` reads it with the syntax's tables and replaces it
    /// with the typed tree as a term, so the checkers never see one.
    SyntaxLit(Box<SyntaxLit>),
    /// `math!(`1 + 2 = 3`)`, `unroll!(e)`.
    /// `macros::expand` replaces it with what the macro makes.
    MacroCall {
        name: String,
        arg: Box<SurfaceTerm>,
    },
    /// `quote { … }` (`stmts` false) or `quote stmts { … }`: the
    /// syntax of the statements, a value. A name that starts with `$`, and
    /// `Splice`, are filled in; `macros::quote` turns the whole into the
    /// constructor calls that build it, so the checkers never see one.
    Quote {
        stmts: bool,
        body: Vec<Stmt>,
    },
    /// `by t!(arg) -> G0 { Δ ⊢ G => p … }`: a step of a proof.
    /// `macros::expand` replaces it with the term the tactic makes, so the
    /// checkers never see one.
    Step(Box<Step>),
    Splice(Box<SurfaceTerm>),
    Other(String),
}

impl SurfaceTerm {
    fn fresh_identity() -> u64 {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        NEXT.try_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
            .expect("surface occurrence identities exhausted")
    }

    pub fn id(&self) -> TermId {
        TermId {
            serial: self.identity,
            span: self.span,
        }
    }

    /// The applications nested through their last argument from `self`, outermost
    /// first, and the term under the innermost one. A list literal, or a text
    /// literal's bytes, nests there once per element: a pass over terms walks
    /// this spine in a loop instead of recursing as deep as the list is long.
    pub fn last_argument_spine(&self) -> (Vec<&SurfaceTerm>, &SurfaceTerm) {
        let mut spine = Vec::new();
        let mut t = self;
        while let TermKind::App { arguments, .. } = &*t.kind
            && let Some(last) = arguments.last()
        {
            spine.push(t);
            t = last;
        }
        (spine, t)
    }

    /// A pass that rebuilds every application from `part` of its function
    /// and of each argument, run along `last_argument_spine` in a loop.
    /// `part` meets the parts in the order the recursion would: the function
    /// before the arguments when `function_first`, after them otherwise.
    pub fn map_applications<E>(
        &self,
        function_first: bool,
        mut part: impl FnMut(&SurfaceTerm) -> Result<SurfaceTerm, E>,
    ) -> Result<SurfaceTerm, E> {
        let (spine, under) = self.last_argument_spine();
        let mut parts = Vec::with_capacity(spine.len());
        for app in &spine {
            let TermKind::App {
                function,
                arguments,
            } = &*app.kind
            else {
                unreachable!("the spine holds applications")
            };
            let function = if function_first {
                Some(part(function)?)
            } else {
                None
            };
            let init = arguments[..arguments.len() - 1]
                .iter()
                .map(&mut part)
                .collect::<Result<Vec<_>, _>>()?;
            parts.push((function, init));
        }
        let mut last = match &*under.kind {
            TermKind::App { function, .. } => under.with_kind(
                TermKind::App {
                    function: Box::new(part(function)?),
                    arguments: Vec::new(),
                },
                under.span,
            ),
            _ => part(under)?,
        };
        for (app, (function, mut arguments)) in spine.into_iter().zip(parts).rev() {
            let TermKind::App { function: f, .. } = &*app.kind else {
                unreachable!("the spine holds applications")
            };
            let function = match function {
                Some(function) => function,
                None => part(f)?,
            };
            arguments.push(last);
            last = app.with_kind(
                TermKind::App {
                    function: Box::new(function),
                    arguments,
                },
                app.span,
            );
        }
        Ok(last)
    }

    /// `part` of the function (`true` with it) and of each argument of the
    /// applications in `self`, in prefix order, along `last_argument_spine`
    /// in a loop; the first error.
    pub fn try_applications<E>(
        &self,
        mut part: impl FnMut(&SurfaceTerm, bool) -> Result<(), E>,
    ) -> Result<(), E> {
        let (spine, under) = self.last_argument_spine();
        for app in spine.iter().copied().chain(Some(under)) {
            let TermKind::App {
                function,
                arguments,
            } = &*app.kind
            else {
                return part(under, false);
            };
            part(function, true)?;
            for a in &arguments[..arguments.len().saturating_sub(1)] {
                part(a, false)?;
            }
        }
        Ok(())
    }

    pub fn for_each_in_applications(&self, mut part: impl FnMut(&SurfaceTerm)) {
        let _ = self.try_applications(|t, _| {
            part(t);
            Ok::<(), ()>(())
        });
    }

    pub fn any_in_applications(&self, mut part: impl FnMut(&SurfaceTerm, bool) -> bool) -> bool {
        self.try_applications(|t, function| match part(t, function) {
            true => Err(()),
            false => Ok(()),
        })
        .is_err()
    }

    /// The term's kind, shared with no other term when it was not.
    pub fn into_kind(mut self) -> TermKind {
        Arc::unwrap_or_clone(std::mem::replace(
            &mut self.kind,
            Arc::new(TermKind::Bool(false)),
        ))
    }

    /// Marks a copy used as a distinct occurrence, before it is checked.
    pub fn freshen(&mut self) {
        self.identity = Self::fresh_identity();
    }

    /// Rewrites the same occurrence while retaining its identity.
    pub fn with_kind(&self, kind: TermKind, span: Span) -> Self {
        Self {
            kind: Arc::new(kind),
            span,
            identity: self.identity,
            written_call: self.written_call,
            macro_call: self.macro_call,
            own_field: self.own_field,
            lowered: self.lowered,
            perform_scope: self.perform_scope,
        }
    }

    /// Creates a distinct occurrence of a term.
    pub fn new(kind: TermKind, span: Span) -> Self {
        Self {
            kind: Arc::new(kind),
            span,
            identity: Self::fresh_identity(),
            written_call: false,
            macro_call: false,
            own_field: false,
            lowered: false,
            perform_scope: None,
        }
    }

    /// Marks a field the coercion expansion wrote (`own_field`).
    pub fn own_field(mut self) -> Self {
        self.own_field = true;
        self
    }

    /// Whether this field reads the struct's own field (`own_field`).
    pub fn is_own_field(&self) -> bool {
        self.own_field
    }

    /// Marks a term the `for`, `while` or `loop` expansion made (`lowered`).
    pub fn lowered(mut self) -> Self {
        self.lowered = true;
        self
    }

    /// Whether a loop expansion made this term, so that the source has no
    /// text for it (`lowered`).
    pub fn is_lowered(&self) -> bool {
        self.lowered
    }

    /// Marks a call written in the source (`written_call`).
    pub fn written_call(mut self) -> Self {
        self.written_call = true;
        self
    }

    /// Whether the source wrote this call (`written_call`).
    pub fn is_written_call(&self) -> bool {
        self.written_call
    }

    /// Marks a call a macro wrote as syntax (`macro_call`), written as the
    /// source's calls are.
    pub fn macro_call(mut self) -> Self {
        self.written_call = true;
        self.macro_call = true;
        self
    }

    /// Whether a macro wrote this call as syntax (`macro_call`).
    pub fn is_macro_call(&self) -> bool {
        self.macro_call
    }

    pub fn var<N: ?Sized>(name: &N, span: Span) -> Self
    where
        for<'a> Name: From<&'a N>,
    {
        Self::new(TermKind::Var(Name::from(name)), span)
    }

    /// The product type `A × B`: the prelude's `Pair(A, B)`. The reader writes it by the
    /// library's own reference, which no program can spell, so no declaration a file sees can
    /// take it over. `A × B × C` is `A × (B × C)`.
    pub fn pair_type(fst: SurfaceTerm, snd: SurfaceTerm, span: Span) -> Self {
        Self::library_app(crate::bindings::pair_reference(), vec![fst, snd], span)
    }

    /// The product value `#(a, b)`: the prelude's `Pair::Mk(a, b)`, by the library's own
    /// reference as [`Self::pair_type`] is.
    pub fn pair_value(fst: SurfaceTerm, snd: SurfaceTerm, span: Span) -> Self {
        Self::library_app(crate::bindings::pair_mk_reference(), vec![fst, snd], span)
    }

    /// `#(a, b, c)`: `Pair::Mk(a, Pair::Mk(b, c))`, each cell spanning from its member to the
    /// end. No member is the unit `#()`, and one is that member.
    pub fn product_value(items: Vec<SurfaceTerm>, span: Span) -> Self {
        Self::fold_right(items, span, Self::pair_value).unwrap_or_else(|| Self::unit(span))
    }

    /// `A × B × C`: `Pair(A, Pair(B, C))`, folded as [`Self::product_value`] is. No member is
    /// `Unit`.
    pub fn product_type(items: Vec<SurfaceTerm>, span: Span) -> Self {
        Self::fold_right(items, span, Self::pair_type).unwrap_or_else(|| {
            Self::new(
                TermKind::Var(crate::bindings::unit_reference().clone().into()),
                span,
            )
        })
    }

    fn fold_right(
        mut items: Vec<SurfaceTerm>,
        span: Span,
        pair: fn(SurfaceTerm, SurfaceTerm, Span) -> SurfaceTerm,
    ) -> Option<Self> {
        let last = items.pop()?;
        Some(items.into_iter().rev().fold(last, |snd, fst| {
            let cell = Span::new(fst.span.start, span.end.max(snd.span.end));
            pair(fst, snd, cell)
        }))
    }

    fn library_app(
        head: &crate::identity::DeclRef,
        arguments: Vec<SurfaceTerm>,
        span: Span,
    ) -> Self {
        Self::new(
            TermKind::App {
                function: Box::new(Self::new(TermKind::Var(head.clone().into()), span)),
                arguments,
            },
            span,
        )
    }

    /// The unit `#()`: the prelude's `Star`.
    pub fn unit(span: Span) -> Self {
        Self::new(
            TermKind::Var(crate::bindings::star_reference().clone().into()),
            span,
        )
    }

    /// Whether `t` is the unit `#()`.
    pub fn is_unit(&self) -> bool {
        matches!(&*self.kind, TermKind::Var(n) if crate::bindings::is_reader_reference(n, "Star"))
    }

    /// The two members of a product type `Pair(A, B)`.
    pub fn as_pair_type(&self) -> Option<(&SurfaceTerm, &SurfaceTerm)> {
        self.as_library_pair("Pair")
    }

    /// The two members of a product value `Pair::Mk(a, b)`.
    pub fn as_pair_value(&self) -> Option<(&SurfaceTerm, &SurfaceTerm)> {
        self.as_library_pair("Pair::Mk")
    }

    fn as_library_pair(&self, head: &str) -> Option<(&SurfaceTerm, &SurfaceTerm)> {
        match &*self.kind {
            TermKind::App {
                function,
                arguments,
            } if arguments.len() == 2
                && matches!(&*function.kind, TermKind::Var(f) if crate::bindings::is_reader_reference(f, head)) =>
            {
                Some((&arguments[0], &arguments[1]))
            }
            _ => None,
        }
    }

    /// The members of the product type `t` in order, the second's own where it is a product
    /// too (`A × (B × C)` is `A × B × C`); none when `t` is not a product.
    pub fn product_type_members(&self) -> Option<Vec<&SurfaceTerm>> {
        Self::spine(self, Self::as_pair_type)
    }

    /// The members of the product value `t`, as [`Self::product_type_members`] gives a type's.
    pub fn product_value_members(&self) -> Option<Vec<&SurfaceTerm>> {
        Self::spine(self, Self::as_pair_value)
    }

    fn spine<'a>(
        t: &'a SurfaceTerm,
        pair: fn(&SurfaceTerm) -> Option<(&SurfaceTerm, &SurfaceTerm)>,
    ) -> Option<Vec<&'a SurfaceTerm>> {
        let (mut fst, mut snd) = pair(t)?;
        let mut out = Vec::new();
        loop {
            out.push(fst);
            match pair(snd) {
                Some((f, s)) => (fst, snd) = (f, s),
                None => {
                    out.push(snd);
                    return Some(out);
                }
            }
        }
    }

    pub fn app<N: ?Sized>(function: &N, arguments: Vec<SurfaceTerm>, span: Span) -> Self
    where
        for<'a> Name: From<&'a N>,
    {
        Self::new(
            TermKind::App {
                function: Box::new(Self::var(function, span)),
                arguments,
            },
            span,
        )
    }
}

/// The value of a text literal's token: `"…"` with its escapes resolved
/// (`\\ \" \' \n \r \t \0 \u{X…}`), `'…'` and plaintext`…` as written.
pub fn unquote_text(token: &str) -> String {
    let token = token.trim();
    if let Some(raw) = token.strip_prefix("plaintext`") {
        return raw.strip_suffix('`').unwrap_or(raw).to_string();
    }
    let inner = |t: &str| {
        t.get(1..t.len().saturating_sub(1))
            .unwrap_or("")
            .to_string()
    };
    if token.starts_with('\'') {
        return inner(token);
    }
    let body = inner(token);
    let mut out = String::with_capacity(body.len());
    let mut chars = body.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some('0') => out.push('\0'),
            Some('u') => {
                let hex: String = chars.by_ref().skip(1).take_while(|c| *c != '}').collect();
                let code = u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32);
                out.push(code.unwrap_or(char::REPLACEMENT_CHARACTER));
            }
            Some(other) => out.push(other),
            None => {}
        }
    }
    out
}

/// An edit of the file a diagnostic is in: `text` in place of `span`.
#[derive(Debug, Clone, PartialEq)]
pub struct Fix {
    pub title: String,
    pub span: Span,
    pub text: String,
}

/// `$name` for a hole written `$r#name` or `${name}` (`${r#name}` too), `$xs...` for
/// `$r#xs...`; `None` for a hole already written plainly, or a text that is not a hole.
pub fn unhole(text: &str) -> Option<String> {
    let rest = text.strip_prefix('$')?;
    let braced = rest.strip_prefix('{').and_then(|r| r.strip_suffix('}'));
    let inner = braced.unwrap_or(rest);
    let name = unraw(inner);
    (braced.is_some() || name.len() != inner.len()).then(|| format!("${name}"))
}

/// A name written with `r#` on any segment is the name without it: `r#class` is `class`, and
/// `Elab::r#class` is `Elab::class`.
pub fn unraw(text: &str) -> std::borrow::Cow<'_, str> {
    fn raw_segment(rest: &str) -> bool {
        rest.chars()
            .next()
            .is_some_and(|c| c.is_alphabetic() || c == '_')
    }
    let head = match text.strip_prefix("r#") {
        Some(rest) if raw_segment(rest) => rest,
        _ => text,
    };
    if !head.contains("::r#") {
        return std::borrow::Cow::Borrowed(head);
    }
    let mut out = String::with_capacity(head.len());
    let mut segments = head.split("::");
    if let Some(first) = segments.next() {
        out.push_str(first);
    }
    for segment in segments {
        out.push_str("::");
        match segment.strip_prefix("r#") {
            Some(rest) if raw_segment(rest) => out.push_str(rest),
            _ => out.push_str(segment),
        }
    }
    std::borrow::Cow::Owned(out)
}
