//! The surface term: one AST for types and expressions.
//!
//! The parser keeps the `Type` and `Expr` grammars apart; here both
//! become a [`SurfaceTerm`], so `Vector(i64, n + 1)` holds the term `n + 1`
//! as a term and a type is just a term that happens to be one. Nothing here
//! decides which terms are pure or what their type is; that is the
//! elaborator's job. Syntax this module does not read yet becomes
//! [`TermKind::Other`], keeping its span.

use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use tauto_parol::{Cst, NodeId, NonTerminalKind as Nt, Parsed, Span, parse};

pub mod dump;
pub mod effect_sets;
pub mod fence;
mod literal;
pub mod modules;
pub mod parsed;
pub mod print;
mod program;
pub mod qualify;
pub mod walk;
pub use literal::{Lexical, LitForm, LitSite, SyntaxLit, lexical};

/// How a `□` written outside `⟦ ⟧` is read: an error, as no term stands for it.
const BOX_OUTSIDE: &str = "`□` outside `⟦ ⟧`";

/// Replaces the `□`s in `t` by the variable `name`, counting them in `found`; `bound` records
/// one written under a binder (`under`). The parts a binder does not scope over (a λ's types,
/// the domain of `∃` and of a function type's first parameter, the value matched) are filled
/// before the rest, so the walk over everything finds no `□` left in them.
fn fill_box(t: &mut SurfaceTerm, name: &str, under: bool, found: &mut usize, bound: &mut bool) {
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
    ClassDecl, Constraint, Constructor, DICT, DataConstructor, DataDecl, EffectDecl,
    ExternInstance, FnDecl, GENERATED_BASE, Generates, Handler, InductiveDecl, Instance,
    InstanceDecl, LawDecl, MatchArm, PRELUDE_BASE, Pattern, Program, Replace, Step, StepArm, Stmt,
    SyntaxUse, TheoremDecl, Vis, dictionary_name, parse_expr_at, parse_program_as_written,
    parse_program_unresolved_at, row_parameters_of,
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
    /// The file whose macro wrote the global this term names, when an
    /// expansion wrote it: the name is read as that file reads it.
    origin: Option<u32>,
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

impl PartialEq for SurfaceTerm {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.span == other.span
    }
}

/// What a `budget` counts: the machine's steps, or the cells its body
/// allocates (constructors, closures, products, text and collections; see
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
}

#[derive(Debug, Clone, PartialEq)]
pub enum TermKind {
    Var(String),
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
        params: Vec<(Option<String>, SurfaceTerm)>,
        result: Box<SurfaceTerm>,
        /// The effects after `!`, when written.
        effects: Option<Vec<String>>,
    },
    /// An effect row given to a data type's row parameter:
    /// `Handlers(!{key | e})`. A row variable `| e` is `|e`, as in
    /// [`TermKind::Pi`]'s effects.
    Row(Vec<String>),
    Exists {
        binder: String,
        domain: Box<SurfaceTerm>,
        body: Box<SurfaceTerm>,
    },
    Lam {
        params: Vec<String>,
        body: Box<SurfaceTerm>,
        /// The types written on the parameters: empty when none is, else one
        /// for each parameter. The checker holds the parameters to them; the
        /// kernel's λ has no domain, so they do not reach it.
        types: Vec<Option<SurfaceTerm>>,
    },
    Union(Vec<SurfaceTerm>),
    /// `A × B × C` as a type, `a × b × c` as a value: a product whose
    /// members are told apart by their types.
    Product(Vec<SurfaceTerm>),
    /// `#(a, b, c)`: a product's value, its members told apart by their types
    /// (`@a e` for a member with a label), two or more as written; `#()` is the
    /// unit. A member that is itself a product gives its members and one of
    /// type `Unit` none, as in the type. Only the checker's elaboration puts it
    /// as the prelude's `Pair` (`qualify::lower_tuples`); Nib and extraction
    /// keep it a product.
    Tuple(Vec<SurfaceTerm>),
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
        effect: String,
        args: Vec<SurfaceTerm>,
    },
    /// `handle { body } with { … }`, the handlers in the order written.
    Handle {
        body: Box<SurfaceTerm>,
        handlers: Vec<Handler>,
    },
    /// `budget(steps: n) { body }` or `budget(memory: n) { body }`; with
    /// both, `budget(steps: a, memory: b) { body }` is two budgets, the one
    /// written first outside.
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
        binder: Option<String>,
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
        name: String,
        fields: Vec<(String, SurfaceTerm)>,
        base: Option<Box<SurfaceTerm>>,
    },
    Borrow {
        mutable: bool,
        term: Box<SurfaceTerm>,
    },
    /// `affine (A) -> B` or `linear (A) -> B`: a function type with its
    /// kind written. Without one a function type is `shared`.
    FnKind {
        kind: String,
        ty: Box<SurfaceTerm>,
    },
    /// A lambda some of whose parameters are borrowed, `(&v: A) => …`:
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
            TermKind::App { function, .. } => SurfaceTerm::new(
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
            last = SurfaceTerm::new(
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
            origin: self.origin,
        }
    }

    /// The file whose macro wrote the global this term names
    /// (`docs/design/macro.md`「衛生（スコープ集合）」, 6).
    pub fn origin(&self) -> Option<usize> {
        self.origin.map(|f| f as usize)
    }

    pub fn set_origin(&mut self, file: Option<usize>) {
        self.origin = file.and_then(|f| u32::try_from(f).ok());
    }

    pub fn new(kind: TermKind, span: Span) -> Self {
        Self {
            kind: Arc::new(kind),
            span,
            identity: Self::fresh_identity(),
            origin: None,
        }
    }

    pub fn var(name: &str, span: Span) -> Self {
        Self::new(TermKind::Var(name.to_string()), span)
    }

    pub fn app(function: &str, arguments: Vec<SurfaceTerm>, span: Span) -> Self {
        Self::new(
            TermKind::App {
                function: Box::new(Self::var(function, span)),
                arguments,
            },
            span,
        )
    }
}

/// For tests and tools: parses `source` and returns, in the order of the
/// source, the terms of every `Type` and `Expr` that is a direct child of a
/// node of `kind` (such as the type written in a parameter, a result or a
/// `let`).
pub fn terms_in(source: &str, kind: Nt) -> Result<Vec<SurfaceTerm>, String> {
    let parsed = parse(source);
    if let Some(e) = parsed.errors.first() {
        return Err(e.message.clone());
    }
    let reader = Reader::new(&parsed, source);
    let mut out = Vec::new();
    if let Some(root) = parsed.cst.root() {
        reader.collect(root, kind, &mut out);
    }
    Ok(out)
}

struct Reader<'a> {
    cst: &'a Cst,
    source: &'a str,
    /// Added to every span: the prelude's spans start at `PRELUDE_BASE`, so
    /// they never meet a program's.
    base: u32,
}

impl<'a> Reader<'a> {
    pub(super) fn new(parsed: &'a Parsed, source: &'a str) -> Self {
        Self {
            cst: &parsed.cst,
            source,
            base: 0,
        }
    }

    fn span(&self, id: NodeId) -> Span {
        let s = self.cst.span(id);
        Span::new(s.start + self.base, s.end + self.base)
    }

    fn collect(&self, id: NodeId, kind: Nt, out: &mut Vec<SurfaceTerm>) {
        for child in self.cst.children(id) {
            match self.cst.non_terminal(child) {
                Some(k) if k == kind => {
                    for term_node in self.cst.children(child) {
                        if matches!(
                            self.cst.non_terminal(term_node),
                            Some(Nt::Type | Nt::BodyType | Nt::Expr)
                        ) {
                            out.push(self.term(term_node));
                        }
                    }
                }
                _ => self.collect(child, kind, out),
            }
        }
    }

    /// The text of a node. A name written `r#name` is `name`: the `r#` is not part of it.
    fn text(&self, id: NodeId) -> &str {
        let text = self.cst.span(id).text(self.source);
        if matches!(
            self.nt(id),
            Some(Nt::Ident | Nt::FnName | Nt::CondPath | Nt::OperationName)
        ) {
            unraw(text)
        } else {
            text
        }
    }

    fn nt(&self, id: NodeId) -> Option<Nt> {
        self.cst.non_terminal(id)
    }

    fn first(&self, id: NodeId, kind: Nt) -> Option<NodeId> {
        self.cst
            .children_iter(id)
            .find(|c| self.nt(*c) == Some(kind))
    }

    /// The name of a field written under `id`: a name (`t.r#type`, `#{ r#view: v }`).
    fn label_of(&self, id: NodeId) -> Option<NodeId> {
        self.cst
            .children_iter(id)
            .find(|c| self.nt(*c) == Some(Nt::Ident))
    }

    /// The type written under `id`: a `Type`, or a `BodyType` where a `{` or `=>` follows it.
    pub(super) fn ty(&self, id: NodeId) -> Option<NodeId> {
        self.cst
            .children_iter(id)
            .find(|c| matches!(self.nt(*c), Some(Nt::Type | Nt::BodyType)))
    }

    pub(super) fn tys(&self, id: NodeId) -> Vec<NodeId> {
        self.cst
            .children_iter(id)
            .filter(|c| matches!(self.nt(*c), Some(Nt::Type | Nt::BodyType)))
            .collect()
    }

    fn all(&self, id: NodeId, kind: Nt) -> Vec<NodeId> {
        self.cst
            .children_iter(id)
            .filter(|c| self.nt(*c) == Some(kind))
            .collect()
    }

    fn other(&self, id: NodeId) -> SurfaceTerm {
        let kind = self
            .nt(id)
            .map(|k| k.to_string())
            .unwrap_or_else(|| "token".into());
        SurfaceTerm::new(TermKind::Other(kind), self.span(id))
    }

    fn term(&self, id: NodeId) -> SurfaceTerm {
        let id = self.through_levels(id);
        let span = self.span(id);
        let kids = self.cst.children(id);
        let Some(kind) = self.nt(id) else {
            return self.other(id);
        };
        match kind {
            // A flat sequence of operands and operators, and an operand with its prefixes.
            Nt::Type | Nt::BodyType | Nt::Seq | Nt::Cond | Nt::Operand | Nt::CondOperand => {
                self.sequence(id).0
            }
            Nt::AngleType | Nt::GenericKind => self.angle_type(id),
            Nt::EffectRow => SurfaceTerm::new(TermKind::Row(self.row_names(id)), span),
            // `⊢ G from p`: the goal is read by `match_expr`; the arm's term is `p`.
            Nt::ArmBody => match kids.as_slice() {
                [only] => self.term(*only),
                _ => match self.first(id, Nt::Expr) {
                    Some(e) => self.term(e),
                    None => self.other(id),
                },
            },
            Nt::Expr => self.expr(&kids, span),
            Nt::Postfix | Nt::CondPostfix => self.postfix(&kids, span),
            Nt::Primary | Nt::CondPrimary => match kids.as_slice() {
                [only] => self.term(*only),
                _ => self.other(id),
            },
            Nt::PathExpr | Nt::CondPath => self.path(id, &kids, span),
            Nt::Number => self.number(id, &kids, span),
            Nt::HoleExpr => SurfaceTerm::new(
                TermKind::Hole(self.text(id).trim_start_matches('?').to_string()),
                span,
            ),
            Nt::Text => SurfaceTerm::new(TermKind::Text(unquote_text(self.text(id))), span),
            Nt::SyntaxLit => self.syntax_lit(id, span),
            Nt::MacroCall => self.macro_call(id, span),
            Nt::QuoteExpr => self.quote_expr(id, span),
            Nt::SpliceExpr => match self.first(id, Nt::Expr) {
                Some(e) => SurfaceTerm::new(TermKind::Splice(Box::new(self.term(e))), span),
                None => self.other(id),
            },
            Nt::True => SurfaceTerm::new(TermKind::Bool(true), span),
            Nt::False => SurfaceTerm::new(TermKind::Bool(false), span),
            Nt::Paren => self.paren(&kids, span),
            Nt::ListLit => self.list_lit(&kids, span),
            Nt::CalcExpr => self.calc_expr(id, span),
            Nt::CongrExpr => self.congr_expr(id, span),
            Nt::BoxHole => SurfaceTerm::new(TermKind::Other(BOX_OUTSIDE.into()), span),
            Nt::TupleLit => self.tuple_lit(id, span),
            Nt::Brace => match kids.as_slice() {
                [only] => self.term(*only),
                _ => self.other(id),
            },
            Nt::Block => self.block(id, span),
            Nt::IfExpr => self.if_expr(&kids, span),
            Nt::PerformExpr => self.perform(id, span),
            Nt::HandleExpr => self.handle(id, span),
            Nt::BudgetExpr => self.budget(id, span),
            Nt::MatchExpr => self.match_expr(id, span),
            Nt::StepExpr => self.step_expr(id, span),
            Nt::Item => match kids.first() {
                Some(e) => self.term(*e),
                None => self.other(id),
            },
            _ => self.other(id),
        }
    }

    /// The kind of a generic, `Linear` or `(Type) -> Copy`: an operand and, after `->`, a kind.
    fn angle_type(&self, id: NodeId) -> SurfaceTerm {
        let span = self.span(id);
        let id = if self.nt(id) == Some(Nt::GenericKind) {
            match self.first(id, Nt::AngleType) {
                Some(inner) => inner,
                None => return self.other(id),
            }
        } else {
            id
        };
        let Some(head) = self.first(id, Nt::Postfix) else {
            return self.other(id);
        };
        // `A × B × C`: the members in the order written.
        let mut members: Vec<SurfaceTerm> = self.all(id, Nt::Postfix)[1..]
            .iter()
            .map(|p| self.term(*p))
            .collect();
        let mut list = self.first(id, Nt::AngleTypeList);
        while let Some(l) = list {
            members.extend(self.all(l, Nt::Postfix).into_iter().map(|p| self.term(p)));
            list = self.first(l, Nt::AngleTypeList);
        }
        let lhs = if members.is_empty() {
            self.term(head)
        } else {
            members.insert(0, self.term(head));
            let end = members.last().map_or(span.end, |m| m.span.end);
            SurfaceTerm::new(
                TermKind::Product(members),
                Span::new(self.span(head).start, end),
            )
        };
        let Some(rest) = self.first(id, Nt::AngleType) else {
            return lhs;
        };
        let product = matches!(&*lhs.kind, TermKind::Product(_));
        let params = match self.sole_paren(head).filter(|_| !product) {
            Some(paren) => self
                .all(paren, Nt::Item)
                .into_iter()
                .map(|item| self.fn_type_item(item))
                .collect(),
            None => vec![(None, lhs)],
        };
        SurfaceTerm::new(
            TermKind::Pi {
                params,
                result: Box::new(self.angle_type(rest)),
                effects: None,
            },
            span,
        )
    }

    /// An operand with the prefixes that bind to it alone applied (`-x`, `&x`, `@tag x`), and
    /// the ones that stand before a whole sequence left for the caller: `¬` and a binder, which
    /// take the operators tighter than `¬`, and `affine`/`linear`, which stand before an arrow.
    fn piece(&self, operand: NodeId) -> Piece {
        let kids = self.cst.children(operand);
        let Some((&postfix, prefixes)) = kids.split_last() else {
            return Piece::of(self.other(operand));
        };
        let mut acc = self.term(postfix);
        // `affine` and `linear` take the whole arrow, so `affine () -> A` still has a
        // parameter list: no parameter, not one `Unit`.
        let only_kinds = prefixes.iter().all(|p| {
            self.cst
                .children(*p)
                .first()
                .is_some_and(|head| self.nt(*head) == Some(Nt::FnKind))
        });
        let paren = if only_kinds {
            self.sole_paren(postfix)
        } else {
            None
        };
        let mut loose = Vec::new();
        let mut kind = None;
        for &p in prefixes.iter().rev() {
            let Some(head) = self.cst.children(p).first().copied() else {
                continue;
            };
            let span = Span::new(self.span(p).start, acc.span.end);
            match self.nt(head) {
                Some(Nt::NotSign | Nt::Binder) => loose.push(head),
                Some(Nt::FnKind) => kind = Some(head),
                Some(Nt::TagPrefix) => acc = self.tagged(head, acc, span),
                Some(Nt::Borrow) => acc = self.borrowed(head, acc, span),
                _ => acc = SurfaceTerm::app(self.text(p).trim(), vec![acc], span),
            }
        }
        // The prefixes were walked from the last, so the first written is last in `loose`.
        loose.reverse();
        Piece {
            term: acc,
            paren,
            loose,
            kind,
        }
    }

    /// A flat sequence of operands and operators (`Seq`, `BodyType`, `Cond`, or one operand) as the
    /// term the precedences build, and the effect row written after it when no arrow takes it:
    /// `fn f(): A × B ! {e}`. A row binds to the last arrow, `(A) -> B ! {e}`.
    pub(super) fn sequence(&self, id: NodeId) -> (SurfaceTerm, Option<Vec<String>>) {
        let span = self.span(id);
        let mut pieces = Vec::new();
        let mut ops = Vec::new();
        let mut row = None;
        if matches!(self.nt(id), Some(Nt::Operand | Nt::CondOperand)) {
            pieces.push(self.piece(id));
        } else {
            for k in self.cst.children(id) {
                match self.nt(k) {
                    Some(Nt::Operand | Nt::CondOperand) => pieces.push(self.piece(k)),
                    Some(Nt::Op | Nt::CondOp) => {
                        ops.push((sign(self.text(k).trim()).to_string(), self.span(k)))
                    }
                    Some(Nt::EffectRow) => row = Some(self.row_names(k)),
                    _ => {}
                }
            }
        }
        if pieces.is_empty() || ops.len() + 1 != pieces.len() {
            return (self.other(id), None);
        }
        let arrow = ops.iter().rposition(|(o, _)| o == "->");
        let mut climb = Climb {
            reader: self,
            taken: vec![0; pieces.len()],
            pieces,
            ops,
            arrow,
            row: if arrow.is_some() { row.clone() } else { None },
        };
        let (parsed, _) = climb.climb(0, 0);
        let term = self.finish(parsed);
        let _ = span;
        (term, if arrow.is_some() { None } else { row })
    }

    /// An operand with `affine` or `linear` written before it, kept as the kind of its type.
    fn finish(&self, parsed: Part) -> SurfaceTerm {
        match parsed.kind {
            Some(kind) => {
                let span = parsed.term.span;
                self.fn_kind(kind, parsed.term, span)
            }
            None => parsed.term,
        }
    }

    fn fn_kind(&self, kind: NodeId, ty: SurfaceTerm, span: Span) -> SurfaceTerm {
        SurfaceTerm::new(
            TermKind::FnKind {
                kind: self.text(kind).trim().to_string(),
                ty: Box::new(ty),
            },
            span,
        )
    }

    fn borrowed(&self, borrow: NodeId, term: SurfaceTerm, span: Span) -> SurfaceTerm {
        SurfaceTerm::new(
            TermKind::Borrow {
                mutable: self.first(borrow, Nt::KwMut).is_some(),
                term: Box::new(term),
            },
            span,
        )
    }

    fn tagged(&self, prefix: NodeId, term: SurfaceTerm, span: Span) -> SurfaceTerm {
        let tag = self
            .first(prefix, Nt::Ident)
            .map(|i| self.text(i).to_string())
            .unwrap_or_default();
        SurfaceTerm::new(
            TermKind::Tagged {
                tag,
                term: Box::new(term),
            },
            span,
        )
    }

    /// The names in an effect row; a row variable `| e` is `|e`. An entry
    /// with type arguments keeps them as written (`res(Pos)`), so that it
    /// names no declared effect and is rejected rather than read as `res`.
    pub(super) fn row_names(&self, row: NodeId) -> Vec<String> {
        let mut literals = Vec::new();
        let mut variables = Vec::new();
        for set in self.all(row, Nt::EffectSet) {
            for term in self.all(set, Nt::EffectTerm) {
                match self.first(term, Nt::EffectLit) {
                    Some(lit) => literals.push(lit),
                    None => variables.extend(self.first(term, Nt::Ident)),
                }
            }
        }
        let mut names: Vec<String> = literals
            .into_iter()
            .flat_map(|lit| self.all(lit, Nt::EffectName))
            .filter_map(|n| {
                let name = self.text(self.first(n, Nt::Ident)?);
                let entry = match self.first(n, Nt::TypeCall) {
                    Some(args) => format!("{name}{}", self.text(args)),
                    None => name.to_string(),
                };
                // `∀ A. res(A)` is kept as written, `∀ ` and the names
                // first: `types/instances.rs` reads it.
                Some(match self.first(n, Nt::EffectForall) {
                    Some(f) => {
                        let names: Vec<&str> = self
                            .all(f, Nt::Ident)
                            .into_iter()
                            .map(|i| self.text(i))
                            .collect();
                        format!("∀ {}. {entry}", names.join(", "))
                    }
                    None => entry,
                })
            })
            .collect();
        if let Some(var) = variables.first() {
            names.push(format!("|{}", self.text(*var)));
        }
        names
    }

    /// `∀ x: A. B` and `∃ x: A. B`: the binder, with the body it takes.
    /// `∀ x: A, y: B. P` is `∀ x: A. ∀ y: B. P`, one binder per name, the first outermost.
    fn quantified(&self, binder: NodeId, body: SurfaceTerm) -> SurfaceTerm {
        let kids = self.cst.children(binder);
        let quantifier = kids.first().map(|k| self.text(*k).trim()).unwrap_or("");
        let names: Vec<String> = kids
            .iter()
            .filter(|k| self.nt(**k) == Some(Nt::Ident))
            .map(|k| self.text(*k).to_string())
            .collect();
        let domains: Vec<NodeId> = kids
            .iter()
            .copied()
            .filter(|k| self.nt(*k) == Some(Nt::Type))
            .collect();
        let start = self.span(binder).start;
        let span = Span::new(start, body.span.end);
        if names.is_empty() || names.len() != domains.len() {
            return SurfaceTerm::new(TermKind::Other("Binder".into()), span);
        }
        let mut body = body;
        for (name, domain) in names.into_iter().zip(domains).rev() {
            body = self.quantified_one(quantifier, name, self.term(domain), body, span);
        }
        body
    }

    fn quantified_one(
        &self,
        quantifier: &str,
        binder: String,
        domain: SurfaceTerm,
        body: SurfaceTerm,
        span: Span,
    ) -> SurfaceTerm {
        if matches!(quantifier, "∃" | "\\exists") {
            SurfaceTerm::new(
                TermKind::Exists {
                    binder,
                    domain: Box::new(domain),
                    body: Box::new(body),
                },
                span,
            )
        } else {
            SurfaceTerm::new(
                TermKind::Pi {
                    params: vec![(Some(binder), domain)],
                    result: Box::new(body),
                    effects: None,
                },
                span,
            )
        }
    }

    fn expr(&self, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let parts: Vec<NodeId> = kids
            .iter()
            .copied()
            .filter(|k| {
                matches!(self.nt(*k), Some(nt) if !matches!(nt, Nt::Gap | Nt::FatArrow | Nt::ThinArrow))
            })
            .collect();
        if parts.iter().any(|k| self.nt(*k) == Some(Nt::Generated)) {
            // `=> fn a, theorem b` is read where a macro call statement or `decreasing_by` is.
            return SurfaceTerm::new(
                TermKind::Other("a list of generated declarations".into()),
                span,
            );
        }
        let [lhs, rhs] = parts.as_slice() else {
            return match parts.as_slice() {
                [only] => self.term(*only),
                _ => SurfaceTerm::new(TermKind::Other("Expr".into()), span),
            };
        };
        let param = |a: &SurfaceTerm| match &*a.kind {
            TermKind::Var(name) => Some((name.clone(), None)),
            TermKind::Borrow { mutable, term } => match &*term.kind {
                TermKind::Var(name) => Some((name.clone(), Some(*mutable))),
                _ => None,
            },
            _ => None,
        };
        let types: Vec<Option<SurfaceTerm>> = match self.sole_paren(*lhs) {
            Some(paren) => self
                .all(paren, Nt::Item)
                .into_iter()
                .map(|item| self.first(item, Nt::Type).map(|ty| self.term(ty)))
                .collect(),
            None => Vec::new(),
        };
        let types = if types.iter().any(Option::is_some) {
            types
        } else {
            Vec::new()
        };
        // `() => e` takes no parameter; `()` is nothing else, the unit being `#()`.
        let empty = self
            .sole_paren(*lhs)
            .is_some_and(|paren| self.all(paren, Nt::Item).is_empty());
        // `(x: A) => …` names its one parameter: the item is read without the type.
        let lhs = match self.sole_paren(*lhs).map(|paren| self.all(paren, Nt::Item)) {
            Some(items) if items.len() == 1 && !types.is_empty() => self.term(items[0]),
            _ => self.term(*lhs),
        };
        let params: Option<Vec<(String, Option<bool>)>> = match &*lhs.kind {
            _ if empty => Some(Vec::new()),
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(f) if f == "Tuple") => {
                arguments.iter().map(param).collect()
            }
            _ => param(&lhs).map(|p| vec![p]),
        };
        match params {
            Some(params) => {
                let borrows: Vec<Option<bool>> = params.iter().map(|(_, b)| *b).collect();
                let lam = SurfaceTerm::new(
                    TermKind::Lam {
                        params: params.into_iter().map(|(n, _)| n).collect(),
                        body: Box::new(self.term(*rhs)),
                        types,
                    },
                    span,
                );
                if borrows.iter().all(Option::is_none) {
                    lam
                } else {
                    SurfaceTerm::new(
                        TermKind::BorrowLam {
                            borrows,
                            lam: Box::new(lam),
                        },
                        span,
                    )
                }
            }
            None => SurfaceTerm::new(TermKind::Other("Expr".into()), span),
        }
    }

    /// The node under the precedence levels that hold only it. An operand
    /// sits under every level of the grammar, and reading each level by
    /// recursion makes the depth of the reader grow with the levels times
    /// the nesting of the source, enough to overflow a thread's stack on a
    /// large program.
    fn through_levels(&self, id: NodeId) -> NodeId {
        let mut at = id;
        while let Some(
            Nt::Type
            | Nt::BodyType
            | Nt::Seq
            | Nt::Cond
            | Nt::Operand
            | Nt::CondOperand
            | Nt::Postfix
            | Nt::CondPostfix
            | Nt::Primary
            | Nt::CondPrimary
            | Nt::Brace
            | Nt::ArmBody,
        ) = self.nt(at)
        {
            match self.cst.children(at).as_slice() {
                [only] => at = *only,
                _ => break,
            }
        }
        at
    }

    /// The parenthesized list `id` is, when it is nothing else.
    fn sole_paren(&self, id: NodeId) -> Option<NodeId> {
        let mut at = id;
        loop {
            if self.nt(at) == Some(Nt::Paren) {
                return Some(at);
            }
            match self.cst.children(at).as_slice() {
                [only] => at = *only,
                _ => return None,
            }
        }
    }

    fn fn_type_item(&self, item: NodeId) -> (Option<String>, SurfaceTerm) {
        let (Some(name), Some(ty)) = (self.first(item, Nt::Expr), self.first(item, Nt::Type))
        else {
            return (None, self.term(item));
        };
        let ty = self.term(ty);
        match self.term(name).into_kind() {
            TermKind::Borrow { mutable, .. } => (
                None,
                SurfaceTerm::new(
                    TermKind::Borrow {
                        mutable,
                        term: Box::new(ty.clone()),
                    },
                    ty.span,
                ),
            ),
            TermKind::Var(name) => (Some(name), ty),
            _ => (None, ty),
        }
    }

    fn postfix(&self, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let Some((&primary, ops)) = kids.split_first() else {
            return SurfaceTerm::new(TermKind::Other("Postfix".into()), span);
        };
        let acc = self.term(primary);
        self.apply_post(acc, ops, span)
    }

    fn apply_post(&self, mut acc: SurfaceTerm, ops: &[NodeId], _span: Span) -> SurfaceTerm {
        for &op in ops {
            let Some(inner) = self.cst.children(op).into_iter().next() else {
                continue;
            };
            let end = self.span(op).end;
            let span = Span::new(acc.span.start, end);
            acc = match self.nt(inner) {
                Some(Nt::Call) => {
                    let arguments = self
                        .all(inner, Nt::Item)
                        .into_iter()
                        .map(|i| self.term(i))
                        .collect();
                    SurfaceTerm::new(
                        TermKind::App {
                            function: Box::new(acc),
                            arguments,
                        },
                        span,
                    )
                }
                Some(Nt::Field) => {
                    let name = self
                        .label_of(inner)
                        .map(|i| self.text(i).trim().to_string())
                        .unwrap_or_default();
                    SurfaceTerm::new(
                        TermKind::Field {
                            base: Box::new(acc),
                            name,
                        },
                        span,
                    )
                }
                _ => SurfaceTerm::new(TermKind::Other(inner_name(self, inner)), span),
            };
        }
        acc
    }

    fn path(&self, id: NodeId, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let only_names = kids.iter().all(|k| matches!(self.nt(*k), Some(Nt::Ident)));
        if only_names {
            let name: String = kids.iter().map(|k| self.text(*k).trim()).collect();
            return SurfaceTerm::var(&name, span);
        }
        let name: String = kids
            .iter()
            .filter(|k| matches!(self.nt(**k), Some(Nt::Ident)))
            .map(|k| self.text(*k).trim())
            .collect();
        // `F { }` is a struct without fields.
        let Some(body) = self.first(id, Nt::RecordBody) else {
            return self.other(id);
        };
        let mut inits = Vec::new();
        let mut base = None;
        self.push_field_inits(body, &mut inits, &mut base);
        let fields = inits
            .into_iter()
            .map(|f| {
                let field = self
                    .label_of(f)
                    .map(|i| self.text(i).trim().to_string())
                    .unwrap_or_default();
                let value = match self.first(f, Nt::Expr) {
                    Some(e) => self.term(e),
                    None => self.other(f),
                };
                (field, value)
            })
            .collect();
        let base = base
            .and_then(|b| self.first(b, Nt::Expr))
            .map(|e| Box::new(self.term(e)));
        SurfaceTerm::new(TermKind::Record { name, fields, base }, span)
    }

    /// The fields of a record's body, and its `..b` when written.
    fn push_field_inits(&self, node: NodeId, out: &mut Vec<NodeId>, base: &mut Option<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::FieldInit) => out.push(c),
                Some(Nt::RecordBase) => *base = Some(c),
                Some(_) => self.push_field_inits(c, out, base),
                _ => {}
            }
        }
    }

    fn number(&self, id: NodeId, kids: &[NodeId], span: Span) -> SurfaceTerm {
        match kids
            .iter()
            .map(|k| self.nt(*k))
            .collect::<Vec<_>>()
            .as_slice()
        {
            [Some(Nt::Integer)] => {
                SurfaceTerm::new(TermKind::Nat(self.text(id).replace('_', "").into()), span)
            }
            [Some(Nt::Float | Nt::Decimal)] => {
                SurfaceTerm::new(TermKind::Float(self.text(id).into()), span)
            }
            _ => self.other(id),
        }
    }

    fn paren(&self, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let items: Vec<SurfaceTerm> = kids
            .iter()
            .filter(|k| self.nt(**k) == Some(Nt::Item))
            .map(|k| self.term(*k))
            .collect();
        let has_comma = kids.iter().any(|k| self.nt(*k) == Some(Nt::Comma));
        let written = kids
            .iter()
            .find(|k| self.nt(**k) == Some(Nt::Item))
            .and_then(|item| self.first(*item, Nt::Type));
        match (items.as_slice(), has_comma) {
            ([only], false) => match written {
                Some(ty) => SurfaceTerm::new(
                    TermKind::Ascribe {
                        term: Box::new(only.clone()),
                        ty: Box::new(self.term(ty)),
                    },
                    span,
                ),
                None => only.clone(),
            },
            _ => SurfaceTerm::app("Tuple", items, span),
        }
    }

    /// `calc a { = b from p; = c from q }`: each step proves that the expression before it
    /// equals the one it writes. The steps are named by `let`s with the equation as their type,
    /// so every written expression is checked, and composed to the right:
    /// `Eq::trans(p, Eq::trans(q, …))`. A chain of `↔` composes with `Iff::trans`. A chain has
    /// one relation: `=` and `↔` are not mixed.
    fn calc_expr(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let Some(start) = self.first(id, Nt::Cond) else {
            return self.other(id);
        };
        let mut steps = Vec::new();
        self.push_calc_steps(id, &mut steps);
        if steps.is_empty() {
            return SurfaceTerm::new(TermKind::Other("`calc` without a step".into()), span);
        }
        let mut prev = self.term(start);
        let mut iff: Option<bool> = None;
        let mut stmts = Vec::new();
        let mut names = Vec::new();
        for (k, step) in steps.iter().enumerate() {
            let kids = self.cst.children(*step);
            let is_iff = kids
                .iter()
                .any(|c| matches!(self.text(*c).trim(), "↔" | "\\iff"));
            if iff.is_some_and(|i| i != is_iff) {
                return SurfaceTerm::new(
                    TermKind::Other("`calc` mixes `=` and `↔`".into()),
                    self.span(*step),
                );
            }
            iff = Some(is_iff);
            let exprs: Vec<NodeId> = kids
                .iter()
                .copied()
                .filter(|c| self.nt(*c) == Some(Nt::Expr))
                .collect();
            let [next, proof] = exprs.as_slice() else {
                return self.other(*step);
            };
            let next = self.term(*next);
            let proof = self.term(*proof);
            let at = self.span(*step);
            let rel = if is_iff { "Iff" } else { "=" };
            let name = format!("calc@{}", k + 1);
            stmts.push(Stmt::Let {
                name: name.clone(),
                ty: Some(SurfaceTerm::app(rel, vec![prev, next.clone()], at)),
                value: proof,
                borrow: false,
                borrow_mut: false,
            });
            names.push((name, at));
            prev = next;
        }
        let trans = if iff == Some(true) {
            "Iff::trans"
        } else {
            "Eq::trans"
        };
        let mut names = names.into_iter().rev();
        let (last, at) = names.next().expect("one step or more");
        let proof = names.fold(SurfaceTerm::var(&last, at), |rest, (name, at)| {
            SurfaceTerm::app(trans, vec![SurfaceTerm::var(&name, at), rest], span)
        });
        stmts.push(Stmt::Expr(proof));
        SurfaceTerm::new(TermKind::Block(stmts), span)
    }

    fn push_calc_steps(&self, node: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::CalcStep) => out.push(c),
                Some(Nt::CalcSteps | Nt::CalcStepsTail) => self.push_calc_steps(c, out),
                _ => {}
            }
        }
    }

    /// `⟦and(or(x1, □), y)⟧`: the function `z => and(or(x1, z), y)`. The `□` is written once,
    /// and not under a binder written inside the brackets; the parameter's name is one no
    /// program can write, so it captures nothing. Its type is the one the context expects.
    fn congr_expr(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let Some(inner) = self.first(id, Nt::Expr) else {
            return self.other(id);
        };
        let mut body = self.term(inner);
        let name = "congr@hole";
        let (mut found, mut bound) = (0usize, false);
        fill_box(&mut body, name, false, &mut found, &mut bound);
        let message = match (found, bound) {
            (0, _) => Some("`⟦ ⟧` without a `□`"),
            (1, false) => None,
            (1, true) => Some("`□` under a binder inside `⟦ ⟧`"),
            _ => Some("more than one `□` in `⟦ ⟧`"),
        };
        if let Some(message) = message {
            return SurfaceTerm::new(TermKind::Other(message.into()), span);
        }
        SurfaceTerm::new(
            TermKind::Lam {
                params: vec![name.to_string()],
                body: Box::new(body),
                types: Vec::new(),
            },
            span,
        )
    }

    /// `[a, b]`: `Cons(a, Cons(b, Nil))`, the terms the constructors make,
    /// as a tuple is `Tuple(…)`. Each cell spans from its item to the `]`.
    fn list_lit(&self, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let items: Vec<SurfaceTerm> = kids
            .iter()
            .filter(|k| self.nt(**k) == Some(Nt::Expr))
            .map(|k| self.term(*k))
            .collect();
        items
            .into_iter()
            .rev()
            .fold(SurfaceTerm::var("Nil", span), |rest, item| {
                let cell = Span::new(item.span.start, span.end);
                SurfaceTerm::app("Cons", vec![item, rest], cell)
            })
    }

    /// `#(a, b)`: `Pair { fst: a, snd: b }`, and `#(a, b, c)` nests to the
    /// right as `A × B × C` does. `#()` is the unit.
    /// `#(a, b, …)` as written: the members are not spliced here, so that the
    /// program prints back as it is written.
    fn tuple_lit(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let items: Vec<SurfaceTerm> = self
            .all(id, Nt::Expr)
            .into_iter()
            .map(|e| self.term(e))
            .collect();
        match items.len() {
            0 => SurfaceTerm::app("Tuple", Vec::new(), span),
            1 => self.other(id),
            _ => SurfaceTerm::new(TermKind::Tuple(items), span),
        }
    }

    fn macro_call(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let name = self
            .first(id, Nt::MacroName)
            .map(|b| self.text(b).trim().trim_end_matches('!').to_string())
            .unwrap_or_default();
        // `name!()` passes the unit.
        let arg = match self.first(id, Nt::Expr) {
            Some(e) => self.term(e),
            None => SurfaceTerm::app("Tuple", Vec::new(), span),
        };
        SurfaceTerm::new(
            TermKind::MacroCall {
                name,
                arg: Box::new(arg),
            },
            span,
        )
    }

    fn quote_expr(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let stmts = self
            .first(id, Nt::Ident)
            .is_some_and(|i| self.text(i) == "stmts");
        let body = self
            .first(id, Nt::Block)
            .and_then(|b| self.first(b, Nt::Stmts))
            .map(|s| self.collect_stmts(s))
            .unwrap_or_default()
            .into_iter()
            .map(|s| self.stmt(s))
            .collect();
        SurfaceTerm::new(TermKind::Quote { stmts, body }, span)
    }

    /// A block holding one expression is that expression.
    fn block(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let stmts: Vec<NodeId> = self
            .first(id, Nt::Stmts)
            .map(|s| self.collect_stmts(s))
            .unwrap_or_default();
        let read: Vec<Stmt> = stmts.iter().map(|s| self.stmt(*s)).collect();
        match read.as_slice() {
            [Stmt::Expr(only)] => only.clone(),
            _ => SurfaceTerm::new(TermKind::Block(read), span),
        }
    }

    /// The `Stmt`s of `Stmts: … [ Stmt StmtsTail ]`, through the tails.
    fn collect_stmts(&self, stmts: NodeId) -> Vec<NodeId> {
        let mut out = Vec::new();
        self.push_stmts(stmts, &mut out);
        out
    }

    fn push_stmts(&self, node: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::Stmt) => out.push(c),
                Some(Nt::StmtsTail) => self.push_stmts(c, out),
                _ => {}
            }
        }
    }

    fn if_expr(&self, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let cond = kids.iter().find(|k| self.nt(**k) == Some(Nt::Cond));
        let then = kids.iter().find(|k| self.nt(**k) == Some(Nt::Block));
        let otherwise = kids.iter().find(|k| self.nt(**k) == Some(Nt::ElseBranch));
        let (Some(cond), Some(then)) = (cond, then) else {
            return SurfaceTerm::new(TermKind::Other("IfExpr".into()), span);
        };
        let otherwise = otherwise.and_then(|e| self.cst.children(*e).into_iter().next());
        SurfaceTerm::new(
            TermKind::If {
                condition: Box::new(self.term(*cond)),
                then: Box::new(self.term(*then)),
                otherwise: otherwise.map(|o| Box::new(self.term(o))),
            },
            span,
        )
    }
}

fn inner_name(reader: &Reader<'_>, id: NodeId) -> String {
    reader
        .nt(id)
        .map(|k| k.to_string())
        .unwrap_or_else(|| "token".into())
}

#[cfg(test)]
mod tests;

/// The value of a text literal's token: `"…"` with its escapes resolved
/// (`\\ \" \' \n \r \t \0 \u{X…}`), `'…'` and plaintext`…` as written.
pub(crate) fn unquote_text(token: &str) -> String {
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

pub use program::parse_program_as_written_at;

/// An edit of the file a diagnostic is in: `text` in place of `span`.
#[derive(Debug, Clone, PartialEq)]
pub struct Fix {
    pub title: String,
    pub span: Span,
    pub text: String,
}

/// The sign an ASCII escape stands for, `\times` for `×`.
fn sign(op: &str) -> &str {
    match op {
        "\\times" => "×",
        "\\land" => "∧",
        "\\lor" => "∨",
        "\\iff" => "↔",
        op => op,
    }
}

/// One operand of a sequence: its term with the prefixes that bind to it alone applied, the
/// parenthesized list it is when it is nothing else (a candidate for the parameters of `->`),
/// and the prefixes that stand before a whole sequence.
struct Piece {
    term: SurfaceTerm,
    paren: Option<NodeId>,
    /// `¬` and binders, the first written first.
    loose: Vec<NodeId>,
    kind: Option<NodeId>,
}

impl Piece {
    fn of(term: SurfaceTerm) -> Self {
        Piece {
            term,
            paren: None,
            loose: Vec::new(),
            kind: None,
        }
    }
}

/// How a run of one operator was built: `A | B | C` is one union, `A × B × C` one product.
#[derive(Clone, Copy, PartialEq)]
enum Flat {
    No,
    Union,
    Product,
}

/// A term read from a part of a sequence, with what a later operator needs to know of it.
#[derive(Clone)]
struct Part {
    term: SurfaceTerm,
    paren: Option<NodeId>,
    kind: Option<NodeId>,
    flat: Flat,
}

#[derive(Clone, Copy, PartialEq)]
enum Assoc {
    Left,
    Right,
    /// `a = b = c` and `a ↔ b ↔ c` are refused.
    None,
}

/// The level of a binary operator and how it chains. From the loosest: `↔`, `->`, `∨ |`, `∧ ×`,
/// `=`, `||`, `&&`, the comparisons `== != < <= > >=`, `+ -`, `* /`.
fn level(op: &str) -> (u8, Assoc) {
    match op {
        "↔" => (0, Assoc::None),
        "->" => (1, Assoc::Right),
        "∨" | "|" => (2, Assoc::Right),
        "∧" | "×" => (3, Assoc::Right),
        "=" => (EQUAL, Assoc::None),
        "||" => (5, Assoc::Left),
        "&&" => (6, Assoc::Left),
        "==" | "!=" | "<" | "<=" | ">" | ">=" => (7, Assoc::None),
        "+" | "-" => (8, Assoc::Left),
        _ => (9, Assoc::Left),
    }
}

/// The level of `=`: the operand of `¬` is read at this level and above.
const EQUAL: u8 = 4;

struct Climb<'r, 'a> {
    reader: &'r Reader<'a>,
    pieces: Vec<Piece>,
    /// `ops[k]` stands between `pieces[k]` and `pieces[k + 1]`.
    ops: Vec<(String, Span)>,
    /// How many of each piece's `loose` prefixes are applied.
    taken: Vec<usize>,
    /// The index of the last `->`, which takes the effect row written after the sequence.
    arrow: Option<usize>,
    row: Option<Vec<String>>,
}

impl Climb<'_, '_> {
    /// The operand at `k` and the operators of at least `min` after it. Returns the term and the
    /// index of the last operand it holds.
    fn climb(&mut self, k: usize, min: u8) -> (Part, usize) {
        let (mut lhs, mut k) = self.operand(k);
        while k < self.ops.len() {
            let (level_of, assoc) = level(&self.ops[k].0);
            if level_of < min {
                break;
            }
            let next = if assoc == Assoc::Right {
                level_of
            } else {
                level_of + 1
            };
            let (rhs, end) = self.climb(k + 1, next);
            lhs = self.combine(lhs, k, rhs);
            if assoc == Assoc::None && end < self.ops.len() && level(&self.ops[end].0).0 == level_of
            {
                let (op, at) = self.ops[end].clone();
                let span = Span::new(lhs.term.span.start, at.end);
                lhs = Part {
                    term: SurfaceTerm::new(TermKind::Other(format!("`{op}` after a chain")), span),
                    paren: None,
                    kind: None,
                    flat: Flat::No,
                };
                return (lhs, self.pieces.len() - 1);
            }
            k = end;
        }
        (lhs, k)
    }

    /// The operand at `k`, with the prefixes written before it that take a sequence.
    fn operand(&mut self, k: usize) -> (Part, usize) {
        let at = self.taken[k];
        if let Some(&prefix) = self.pieces[k].loose.get(at) {
            self.taken[k] += 1;
            // `¬` takes `=` and what binds tighter; a binder takes all that follows.
            let (inner, end) = self.climb(
                k,
                if self.reader.nt(prefix) == Some(Nt::Binder) {
                    0
                } else {
                    EQUAL
                },
            );
            let body = self.reader.finish(inner);
            let term = match self.reader.nt(prefix) {
                Some(Nt::Binder) => self.reader.quantified(prefix, body),
                _ => {
                    let span = Span::new(self.reader.span(prefix).start, body.span.end);
                    // `¬P` is `(P) -> False`: the kernel receives the function type.
                    SurfaceTerm::new(
                        TermKind::Pi {
                            params: vec![(None, body)],
                            result: Box::new(SurfaceTerm::var("False", span)),
                            effects: None,
                        },
                        span,
                    )
                }
            };
            return (
                Part {
                    term,
                    paren: None,
                    kind: None,
                    flat: Flat::No,
                },
                end,
            );
        }
        let piece = &self.pieces[k];
        (
            Part {
                term: piece.term.clone(),
                paren: piece.paren,
                kind: piece.kind,
                flat: Flat::No,
            },
            k,
        )
    }

    fn combine(&mut self, lhs: Part, k: usize, rhs: Part) -> Part {
        let op = self.ops[k].0.clone();
        if op == "->" {
            return self.arrow(lhs, k, rhs);
        }
        let lhs = self.reader.finish(lhs);
        let flat_rhs = rhs.flat;
        let rhs = self.reader.finish(rhs);
        let span = Span::new(lhs.span.start, rhs.span.end);
        let chained = |flat: Flat, lhs: SurfaceTerm, rhs: SurfaceTerm| {
            let mut members = vec![lhs];
            match (&*rhs.kind, flat_rhs == flat) {
                (TermKind::Union(rest) | TermKind::Product(rest), true) => {
                    members.extend(rest.iter().cloned())
                }
                _ => members.push(rhs),
            }
            if flat == Flat::Union {
                TermKind::Union(members)
            } else {
                TermKind::Product(members)
            }
        };
        let (term, flat) = match op.as_str() {
            "|" => (
                SurfaceTerm::new(chained(Flat::Union, lhs, rhs), span),
                Flat::Union,
            ),
            "×" => (
                SurfaceTerm::new(chained(Flat::Product, lhs, rhs), span),
                Flat::Product,
            ),
            "∧" => (SurfaceTerm::app("And", vec![lhs, rhs], span), Flat::No),
            "∨" => (SurfaceTerm::app("Or", vec![lhs, rhs], span), Flat::No),
            "↔" => (SurfaceTerm::app("Iff", vec![lhs, rhs], span), Flat::No),
            op => (SurfaceTerm::app(op, vec![lhs, rhs], span), Flat::No),
        };
        Part {
            term,
            paren: None,
            kind: None,
            flat,
        }
    }

    /// `(x: A, &y: B) -> C`: the parenthesized left is read as a parameter list. A parameter
    /// `x: A` is of type `A` and binds `x` in the later parameters and the result; `&x: A` is `A`
    /// borrowed. An operand that is not a parenthesized list is the one parameter, unnamed.
    fn arrow(&mut self, lhs: Part, k: usize, rhs: Part) -> Part {
        let kind = lhs.kind;
        let params = match lhs.paren {
            Some(paren) => self
                .reader
                .all(paren, Nt::Item)
                .into_iter()
                .map(|item| self.reader.fn_type_item(item))
                .collect(),
            None => vec![(None, lhs.term.clone())],
        };
        let result = self.reader.finish(rhs);
        let span = Span::new(lhs.term.span.start, result.span.end);
        let effects = if self.arrow == Some(k) {
            self.row.take()
        } else {
            None
        };
        let term = SurfaceTerm::new(
            TermKind::Pi {
                params,
                result: Box::new(result),
                effects,
            },
            span,
        );
        let term = match kind {
            Some(kind) => self.reader.fn_kind(kind, term, span),
            None => term,
        };
        Part {
            term,
            paren: None,
            kind: None,
            flat: Flat::No,
        }
    }
}

pub fn unraw(text: &str) -> &str {
    match text.strip_prefix("r#") {
        Some(rest)
            if rest
                .chars()
                .next()
                .is_some_and(|c| c.is_alphabetic() || c == '_') =>
        {
            rest
        }
        _ => text,
    }
}
