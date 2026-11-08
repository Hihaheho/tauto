//! Statements, patterns, handlers and the program: the executable parts of
//! the surface syntax, read from the same concrete syntax tree as types and
//! expressions (see the parent module).

use std::collections::HashMap;
use std::sync::Mutex;

use tauto_message::{Message, msg};
use tauto_parol::{NodeId, NonTerminalKind as Nt, Span, parse};

use super::qualify::SEPARATOR;
use super::{BudgetLimit, Name, Reader, SurfaceTerm, SyntaxLit, TermKind};

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub stmts: Vec<Stmt>,
    /// What reading the modules found wrong, for the type check to report.
    pub errors: Vec<(Message, Span)>,
}

/// A generic bound, with effect-set members carried as references after binding.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericBound {
    written: String,
    effects: Option<Vec<Name>>,
}

impl GenericBound {
    /// Source rewriting is allowed only before the members have been bound.
    pub fn edit_spelling(&mut self, edit: &mut dyn FnMut(&mut String)) {
        if self
            .effects
            .as_ref()
            .is_some_and(|members| members.iter().any(Name::is_resolved))
        {
            return;
        }
        edit(&mut self.written);
        self.effects = super::effect_sets::set_of_bound(&self.written)
            .map(|(_, effects)| effects.into_iter().map(Name::from).collect());
    }

    pub fn effects_mut(&mut self) -> Option<&mut Vec<Name>> {
        self.effects.as_mut()
    }
    pub fn effect_set(&self) -> Option<(&str, &[Name])> {
        Some((self.written.split_once('{')?.0, self.effects.as_deref()?))
    }
}
impl From<String> for GenericBound {
    fn from(written: String) -> Self {
        let effects = super::effect_sets::set_of_bound(&written)
            .map(|(_, effects)| effects.into_iter().map(Name::from).collect());
        Self { written, effects }
    }
}
impl From<&str> for GenericBound {
    fn from(written: &str) -> Self {
        written.to_string().into()
    }
}
impl AsRef<str> for GenericBound {
    fn as_ref(&self) -> &str {
        &self.written
    }
}
impl std::ops::Deref for GenericBound {
    type Target = str;
    fn deref(&self) -> &str {
        &self.written
    }
}
impl std::fmt::Display for GenericBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.written)
    }
}

/// `=> fn a, theorem b`: the complete list (kind and name) of the declarations a
/// declaration or a call makes besides itself.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Generates {
    pub items: Vec<(String, String)>,
    pub written: bool,
    /// The clause from `=>` to the last name, or, when it is not written, the
    /// empty span where it goes.
    pub at: Span,
    /// Whether the list may be broken over lines. The grammar takes a newline after a comma
    /// only in the list of a declaration or an attribute; the list after a call or a
    /// `decreasing_by` ends at the end of its line.
    pub breaks: bool,
}

/// `=> replace fn f, …` in an attribute: the declaration the macro is given, which it changes.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Replace {
    /// The word before the declaration's kind; anything but `replace` is an error.
    pub word: String,
    pub kind: String,
    pub name: Name,
    /// From the word to the name.
    pub at: Span,
}

impl Generates {
    pub fn shown(&self) -> String {
        let list: Vec<String> = self.items.iter().map(|(k, n)| format!("{k} {n}")).collect();
        format!("=> {}", list.join(", "))
    }
}

/// Who may see a declaration (`docs/design/visibility.md`): by default only its
/// file; `pub` its name to the files that import it; `pub(open)` also what is
/// inside it, a type's constructors and fields and an effect's operation, to
/// the arms of a `handle` in other files.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub enum Vis {
    #[default]
    Private,
    Pub,
    Open,
}

impl Vis {
    /// The words written before the declaration, with a space after them.
    pub fn written(self) -> &'static str {
        match self {
            Vis::Private => "",
            Vis::Pub => "pub ",
            Vis::Open => "pub(open) ",
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// `let x: T = e`; the type is optional in programs and proofs. Proof
    /// annotations remain explicit type ascriptions in the substituted term.
    /// `let &x = f(&v)` (`borrow`) binds the borrow `f` returns, `let &mut x`
    /// (`borrow_mut`) a `&mut` borrow.
    Let {
        name: Name,
        ty: Option<SurfaceTerm>,
        value: SurfaceTerm,
        borrow: bool,
        borrow_mut: bool,
    },
    /// `var &x = f(&v)` (`borrow`) binds a view that is advanced with
    /// `&mut x`.
    Var {
        name: Name,
        ty: Option<SurfaceTerm>,
        value: SurfaceTerm,
        borrow: bool,
    },
    /// `x := v`, or `x.f.g := v`: writes the `var` or `&mut` binding `x`,
    /// or the field of it that `place` (the whole `x.f.g`) names.
    Assign {
        name: Name,
        place: Option<SurfaceTerm>,
        value: SurfaceTerm,
    },
    Fn(FnDecl),
    /// `@name!(arg) stmt` or `@name!(arg) => fn a, theorem b stmt` (the attribute on its own line): an attribute
    /// macro is given the declaration and makes declarations besides it. `generates` is the complete list (kind and
    /// name) of them. With `replace` (`=> replace fn f, theorem b`) the macro also changes the declaration, which
    /// it makes again; without it the declaration stays as written. The expansion removes the attribute, so the
    /// checkers never see one.
    Attributed {
        name: String,
        arg: SurfaceTerm,
        generates: Generates,
        replace: Option<Replace>,
        stmt: Box<Stmt>,
        span: Span,
    },
    /// `theorem` and `axiom`: a named proposition with a proof term (an
    /// axiom has none).
    Theorem(TheoremDecl),
    /// `def name(params): T := body`, the body being a type.
    Def(TheoremDecl),
    /// `mutual { … }`: inductive families, or functions/theorems, declared together.
    Mutual {
        items: Vec<Stmt>,
        span: Span,
    },
    /// `import "path"`, relative to the importing file, or `import std::List`
    /// (`module`), a module of the standard library or of a dependency.
    /// `names` is the list `{ List, map }` of what it brings, when written.
    Import {
        path: String,
        module: bool,
        names: Option<Vec<(String, Span)>>,
        span: Span,
    },
    Inductive(InductiveDecl),
    /// `module M { … }`: `modules::resolve`
    /// flattens it, so the checkers never see one.
    Module {
        name: String,
        items: Vec<Stmt>,
        span: Span,
    },
    Effect(EffectDecl),
    /// `struct Name(G: Type) { field: T, … }`, with its kind when written.
    Struct(DataDecl),
    /// `enum Name(G: Type) { C(T, …), D { f: T }, E }`, with its kind when written.
    Enum(DataDecl),
    /// `extern { fn … }`: signatures without bodies. The prelude's are the
    /// functions the evaluator and the backends implement themselves.
    Extern {
        fns: Vec<FnDecl>,
        instances: Vec<ExternInstance>,
        /// `type T`: types the host provides. The reader puts a `Struct` with
        /// `host` set before the block for each, so what follows sees a
        /// struct; these are kept for printing the block as written.
        types: Vec<DataDecl>,
        span: Span,
    },
    Class(ClassDecl),
    Instance(InstanceDecl),
    While {
        condition: SurfaceTerm,
        body: SurfaceTerm,
    },
    Return(Option<SurfaceTerm>),
    Expr(SurfaceTerm),
    /// `name!(…) => fn a, theorem b`: a macro call that makes statements, with the complete list of
    /// the declarations it makes. The expansion removes it, so the checkers never see one.
    Called {
        call: SurfaceTerm,
        generates: Generates,
        span: Span,
    },
    /// ``syntax!(math, ```par … ```) ``: a grammar. `syntax::expand` replaces it with the types it makes.
    Syntax {
        name: String,
        grammar: SyntaxLit,
        /// `inductive_syntax!(…)`: the proof side's `inductive` types are made too.
        inductive: bool,
        generates: Generates,
        /// `syntax math … with fmt math_fmt, tokens math_tokens = …`: the functions it registers.
        uses: Vec<SyntaxUse>,
        span: Span,
    },
    /// `macro fn math(…) …`: a function that is also registered as a macro.
    Macro {
        name: String,
        function: String,
        span: Span,
    },
    Other(String, Span),
}

/// `fmt math_fmt` of `syntax math … with fmt math_fmt, tokens math_tokens`: what a function is
/// registered for, and its name.
#[derive(Debug, Clone, PartialEq)]
pub struct SyntaxUse {
    pub role: String,
    pub function: Name,
    pub span: Span,
}

/// What the record of a class is called where a `where` makes it a parameter
/// (`crates/tauto-kernel/src/check/classes.rs`): a call finds it by its type.
pub const DICT: &str = "inst@";

pub fn dictionary_name(class: &str, index: usize) -> String {
    format!("{DICT}{class}{index}")
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExternInstance {
    pub class: Name,
    pub ty: SurfaceTerm,
    pub span: Span,
}

/// `class C(A: bound) { … }`: the methods' signatures (their bodies are
/// `Other` terms, never run) and the laws.
#[derive(Debug, Clone, PartialEq)]
pub struct ClassDecl {
    /// All class parameters, in dependency order.
    pub parameters: Vec<(Name, SurfaceTerm)>,
    pub name: Name,
    /// `pub` or `pub(open)` as written before the declaration.
    pub vis: Vis,
    pub param: Name,
    /// How many parameters were written; a class has one.
    pub arity: usize,
    /// The bound of the parameter as written: a kind.
    pub bound: Option<String>,
    pub methods: Vec<FnDecl>,
    pub laws: Vec<LawDecl>,
    pub span: Span,
}

impl ClassDecl {
    /// Whether the proof language can read the class's parameter: one
    /// parameter of kind `Type`. A class over a type constructor
    /// (`F: (Shared) -> Shared`) is a class of the program only.
    pub fn over_types(&self) -> bool {
        self.arity != 0 && !self.bound.as_deref().is_some_and(|b| b.contains("->"))
    }
}

/// A `law` item: a theorem schema in a class, a
/// theorem to prove in an instance. Nib reads past it.
#[derive(Debug, Clone, PartialEq)]
pub struct LawDecl {
    pub name: Name,
    pub span: Span,
    /// Its generics and parameters, the proposition, and the proof when there
    /// is one.
    pub theorem: TheoremDecl,
}

#[derive(Debug, Clone, PartialEq)]
pub struct InstanceDecl {
    /// Argument types of the instance telescope.
    pub generic_types: Vec<SurfaceTerm>,
    /// Arguments after the first class argument.
    pub arguments: Vec<SurfaceTerm>,
    pub generics: Vec<Name>,
    pub bounds: Vec<Option<GenericBound>>,
    pub class: Name,
    pub head: SurfaceTerm,
    pub where_: Vec<Constraint>,
    pub methods: Vec<FnDecl>,
    pub laws: Vec<LawDecl>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EffectDecl {
    pub name: Name,
    /// `pub` or `pub(open)` as written before the declaration.
    pub vis: Vis,
    pub generics: Vec<Name>,
    /// For each generic: whether it is declared a row variable, `!e`.
    pub rows: Vec<bool>,
    /// The written parameter types; `None` when a parameter has none.
    pub params: Vec<Option<SurfaceTerm>>,
    /// The written parameter names, one for each of `params`; empty when
    /// the declaration came from somewhere that carries none (a macro).
    pub param_names: Vec<Name>,
    /// `None` for `()`.
    pub result: Option<SurfaceTerm>,
    /// `resume 0`, `resume <=1`, `resume 1`, `resume ω` or `direct` as
    /// written (`"0"`, `"<=1"`, `"1"`, `"ω"`, `"direct"`); `None` when
    /// nothing is written.
    pub resume: Option<String>,
    /// `effect Host {Div, stdout}`: the effects the name stands for, as a
    /// row writes them; such a declaration has no operation of its own.
    /// `modules::resolve` writes the effects in its place in every row and
    /// drops the declaration, so the checkers never see one.
    pub set: Option<Vec<String>>,
    pub span: Span,
}

/// A `struct` (one constructor, named as the type) or an `enum`.
#[derive(Debug, Clone, PartialEq)]
pub struct DataDecl {
    /// `copy`, `shared`, `affine` or `linear`, when written.
    pub kind: Option<String>,
    pub name: Name,
    /// `pub` or `pub(open)` as written before the declaration.
    pub vis: Vis,
    pub generics: Vec<Name>,
    /// For each generic: whether it is declared a row variable, `!e`.
    pub rows: Vec<bool>,
    pub constructors: Vec<DataConstructor>,
    /// `extern { type Name }`: a type the host provides. Its one constructor
    /// has no fields, and only extern functions make its values.
    pub host: bool,
    pub span: Span,
}

impl DataDecl {
    /// The positions of the generics declared as row variables, `!e`
    /// (`docs/design/row-parameters.md`). `known` is not read: a generic is a
    /// row parameter because it is declared one, not because of how a field
    /// uses it ([`row_parameters_of`] finds them all).
    pub fn row_parameters(&self, _known: &HashMap<Name, Vec<usize>>) -> Vec<usize> {
        self.rows
            .iter()
            .enumerate()
            .filter(|(_, row)| **row)
            .map(|(i, _)| i)
            .collect()
    }

    /// The row variables the fields write, `e`, that are not declared with `!`.
    pub fn undeclared_rows(&self) -> Vec<String> {
        let mut used = Vec::<String>::new();
        for c in &self.constructors {
            for (_, ty) in &c.fields {
                let mut ty = ty.clone();
                super::walk::term(&mut ty, &mut |t| match &*t.kind {
                    TermKind::Pi {
                        effects: Some(row), ..
                    }
                    | TermKind::Row(row) => used.extend(
                        row.iter()
                            .filter_map(|e| e.strip_prefix('|').map(str::to_string)),
                    ),
                    _ => {}
                });
            }
        }
        used.sort();
        used.dedup();
        used.retain(|v| {
            !self
                .generics
                .iter()
                .zip(&self.rows)
                .any(|(g, row)| g.spelling() == Some(v.as_str()) && *row)
        });
        used
    }
}

/// The row parameters of each declaration in `decls`, by name: the least
/// solution of [`DataDecl::row_parameters`], since a declaration may pass its
/// generic to another's row parameter (`struct App(!e) { a: Answer(e) }`).
pub fn row_parameters_of<'a>(
    decls: impl IntoIterator<Item = &'a DataDecl>,
) -> HashMap<Name, Vec<usize>> {
    let decls: Vec<&DataDecl> = decls.into_iter().collect();
    let mut known = HashMap::new();
    loop {
        let next: HashMap<Name, Vec<usize>> = decls
            .iter()
            .map(|d| (d.name.clone(), d.row_parameters(&known)))
            .collect();
        if next == known {
            return known;
        }
        known = next;
    }
}

/// A constructor's fields; a positional field has no name.
#[derive(Debug, Clone, PartialEq)]
pub struct DataConstructor {
    pub name: Name,
    pub fields: Vec<(Option<String>, SurfaceTerm)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub name: Name,
    /// `pub` or `pub(open)` as written before the declaration.
    pub vis: Vis,
    /// Implicit parameters, in telescope order.
    pub generics: Vec<Name>,
    /// Their types. Missing entries mean `Type` for generated declarations.
    pub generic_types: Vec<SurfaceTerm>,
    /// For each generic: whether it is declared a row variable, `!e`.
    pub rows: Vec<bool>,
    /// A bound for each generic when written: `shared`, `linear`, `<=1`.
    pub bounds: Vec<Option<GenericBound>>,
    /// Where each generic is written, when the source says.
    pub bound_spans: Vec<Span>,
    pub params: Vec<Name>,
    /// For each parameter: `None` takes the value, `Some(false)` a borrow
    /// (`&x`), `Some(true)` a mutable borrow (`&mut x`).
    pub borrows: Vec<Option<bool>>,
    /// The written parameter types, aligned with `params`.
    pub param_types: Vec<Option<SurfaceTerm>>,
    pub result: Option<SurfaceTerm>,
    /// The row written after `!`, when there is one.
    pub effects: Option<Vec<Name>>,
    /// `where C(T), …`, in the order written.
    pub where_: Vec<Constraint>,
    pub span: Span,
    /// `opaque fn`: the kernel does not unfold the function; the equation
    /// `f::eq` it makes unfolds it once.
    pub opaque: bool,
    /// `decreasing_by W`: the recursion is well-founded recursion on the
    /// first parameter, by the `WfRel` `W` (`std/WellFounded.taut`).
    pub decreasing_by: Option<SurfaceTerm>,
    /// `decreasing_by W => theorem f::eq` and `opaque fn f(…): B => theorem f::eq`: what the declaration
    /// makes. Present exactly when `decreasing_by` or `opaque` is.
    pub generates: Option<Generates>,
    /// `budget N` after the result: the kernel checks the declaration with at
    /// most `N` steps of reduction, in place of the default limit.
    pub budget: Option<u64>,
    pub body: SurfaceTerm,
}

impl FnDecl {
    /// The explicit types of implicit binders, in declaration order.
    pub fn generic_parameters(&self) -> Vec<(Name, SurfaceTerm)> {
        self.generics
            .iter()
            .enumerate()
            .map(|(i, name)| {
                (
                    name.clone(),
                    self.generic_types.get(i).cloned().unwrap_or_else(|| {
                        SurfaceTerm::var(&crate::bindings::library_name("Type"), self.span)
                    }),
                )
            })
            .collect()
    }
}

/// `C(T)` in a `where`: `T` has the class `C`.
#[derive(Debug, Clone, PartialEq)]
pub struct Constraint {
    /// Arguments after the first class argument.
    pub arguments: Vec<SurfaceTerm>,
    pub class: Name,
    pub ty: SurfaceTerm,
    pub span: Span,
}

/// `inductive T(p: A): Sort { c(x: B): T(p) }`.
#[derive(Debug, Clone, PartialEq)]
pub struct InductiveDecl {
    pub name: Name,
    /// `pub` or `pub(open)` as written before the declaration.
    pub vis: Vis,
    pub params: Vec<(Name, SurfaceTerm)>,
    pub sort: SurfaceTerm,
    pub constructors: Vec<Constructor>,
    /// `inductive T(): Type => fn T::beq, … { … }`: what is made besides the eliminators.
    pub generates: Generates,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Constructor {
    pub name: Name,
    /// How many leading `params` are generics, which a call or a pattern may
    /// leave out.
    pub implicit: usize,
    pub params: Vec<(Name, SurfaceTerm)>,
    pub result: SurfaceTerm,
}

/// `theorem name<G>(x: A): T { proof }` or `axiom name<G>(x: A): T`. Generics
/// come first among `params`, typed `Type` unless a kind is written; they
/// are implicit: a call that leaves them out has them inferred.
#[derive(Debug, Clone, PartialEq)]
pub struct TheoremDecl {
    pub name: Name,
    /// `pub` or `pub(open)` as written before the declaration.
    pub vis: Vis,
    /// How many leading `params` are generics.
    pub implicit: usize,
    pub params: Vec<(Name, SurfaceTerm)>,
    pub ty: SurfaceTerm,
    pub body: Option<SurfaceTerm>,
    /// `decreasing_by x`: the parameter the recursion is structural on.
    pub decreasing_by: Option<SurfaceTerm>,
    pub budget: Option<u64>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Wild,
    Bind(Name),
    Int(i64),
    Bool(bool),
    Text(String),
    /// `Succ(k)`, or a bare name that turns out to be a constructor.
    Ctor {
        name: Name,
        args: Vec<Pattern>,
    },
    /// `Point { x, y: 0 }`: a struct's fields by name; `x` alone binds `x`.
    Record {
        name: Name,
        fields: Vec<(String, Pattern)>,
    },
    /// `#(p, q)`: a product's pattern, two or more members as written. Only the
    /// checker's elaboration puts it as the prelude's `Pair`
    /// (`qualify::lower_tuples`); Nib and extraction keep it a product.
    Tuple(Vec<Pattern>),
    Other(String),
}

impl Pattern {
    /// `@a p`, the pattern `p` under the label `a`: the constructor `@a` with `p` for
    /// its one argument. No declaration has a name with `@`, so the name says it is a
    /// label; the checker reads it as the constructor of the label's type, and a Nib
    /// program as `p` on the labelled value.
    pub fn labelled(tag: &str, p: Pattern) -> Pattern {
        Pattern::Ctor {
            name: format!("@{tag}").into(),
            args: vec![p],
        }
    }

    /// The label and the pattern under it, when `self` is `@a p`.
    pub fn label(&self) -> Option<(&str, &Pattern)> {
        match self {
            Pattern::Ctor { name, args } => match (name.strip_prefix('@'), args.as_slice()) {
                (Some(tag), [p]) => Some((tag, p)),
                _ => None,
            },
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<SurfaceTerm>,
    /// `Less => ⊢ G from body`: the goal of the arm as written.
    pub goal: Option<SurfaceTerm>,
    pub body: SurfaceTerm,
}

/// `by t!(arg): G0 { Δ ⊢ G from p … }`.
#[derive(Debug, Clone, PartialEq)]
pub struct Step {
    pub tactic: String,
    /// What the call has in its parentheses, not checked.
    pub arg: SurfaceTerm,
    pub call: Span,
    /// `-> G0`; `None` where the step is the whole proof of a step's arm.
    pub before: Option<SurfaceTerm>,
    pub arms: Vec<StepArm>,
}

/// `x: A, h: P ⊢ G from p`: a goal the tactic leaves, the variables it adds, and
/// its proof.
#[derive(Debug, Clone, PartialEq)]
pub struct StepArm {
    pub binders: Vec<(Name, SurfaceTerm)>,
    pub goal: SurfaceTerm,
    pub body: SurfaceTerm,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Handler {
    /// `return x => body`
    Return { pattern: Pattern, body: SurfaceTerm },
    /// `op(p, …), k if guard => body`
    Operation {
        effect: Name,
        /// The instance the arm answers.
        instance: Instance,
        patterns: Vec<Pattern>,
        cont: Option<Name>,
        guard: Option<SurfaceTerm>,
        body: SurfaceTerm,
    },
}

/// The instance of an operation an arm answers: `ask<Text, i64>(k)` fixes the
/// operation's generics, `∀ A. show<A>(n, v)` takes every instance, with `A`
/// bound. Both are empty for an operation without generics.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Instance {
    /// The names bound by `∀ … .`.
    pub forall: Vec<Name>,
    /// The type arguments, in the order of the operation's generics.
    pub args: Vec<SurfaceTerm>,
}

pub const PRELUDE_BASE: u32 = 1 << 31;

/// Where the spans of the terms the class expansion makes start, below the
/// prelude's: no written term of a program has one.
pub const GENERATED_BASE: u32 = 1 << 30;

/// The program as written, without running macros, its
/// modules resolved. This is what `totes/surface` reads, so what the
/// self-hosted checkers are compared on.
pub fn parse_program_as_written(source: &str) -> Result<Program, String> {
    parse_program_as_written_at(source, 0)
}

pub fn parse_program_as_written_at(source: &str, base: u32) -> Result<Program, String> {
    let mut program = parse_program_unresolved_at(source, base)?;
    let (stmts, mut errors) = super::modules::resolve(std::mem::take(&mut program.stmts));
    errors.extend(std::mem::take(&mut program.errors));
    program.stmts = stmts;
    program.errors = errors;
    Ok(program)
}

/// An expression written alone, with spans from `base`: what a syntax's
/// `${ … }` holds.
pub fn parse_expr_at(source: &str, base: u32) -> Result<SurfaceTerm, String> {
    let program = parse_program_unresolved_at(source, base)?;
    match program.stmts.as_slice() {
        [Stmt::Expr(t)] => Ok(t.clone()),
        _ => Err(msg!("surface-expected-one-expression").to_string()),
    }
}

/// A program with the modules left as written: a program of
/// several files resolves them once all its files are read.
pub fn parse_program_unresolved_at(source: &str, base: u32) -> Result<Program, String> {
    parse_program_located_at(source, base).map_err(|e| e.to_string())
}

/// Why a text does not read as a program, and where.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    /// The byte it is at, counted from the `base` the text was read from;
    /// `None` when the parser gave no place.
    pub at: Option<u32>,
}

/// `message at byte N`, the way the toolchain has shown it.
impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.at {
            Some(at) => write!(f, "{} at byte {at}", self.message),
            None => f.write_str(&self.message),
        }
    }
}

/// [`parse_program_unresolved_at`] with the place of a failure as data.
pub fn parse_program_located_at(source: &str, base: u32) -> Result<Program, ParseError> {
    if !super::parsed::kept() {
        return read_program_at(source, base);
    }
    super::parsed::get_or_read(source, base, || read_program_at(source, base))
}

fn read_program_at(source: &str, base: u32) -> Result<Program, ParseError> {
    let failed = |message: String, at: Option<u32>| ParseError {
        message,
        at: at.map(|a| (base as u64 + a as u64) as u32),
    };
    let parsed = parse(source);
    if let Some(e) = parsed.errors.first() {
        let at = e.span.map(|s| s.start as u32);
        // `extern "rust" { … }`: the rust path is not written in the source.
        let after_extern = e.span.is_some_and(|s| {
            source[..(s.start as usize).min(source.len())]
                .trim_end()
                .ends_with("extern")
        });
        if after_extern {
            return Err(failed(msg!("surface-extern-rust-path").to_string(), at));
        }
        return Err(failed(e.message.to_string(), at));
    }
    let mut reader = Reader::new(&parsed, source);
    reader.base = base;
    let root = parsed
        .cst
        .root()
        .ok_or_else(|| failed("empty parse".to_string(), None))?;
    if let Some(at) = reader.bare_kind(root) {
        return Err(failed(
            msg!(
                "surface-bare-kind",
                kind = source[at.0 as usize..at.1 as usize].trim(),
                written = match source[at.0 as usize..at.1 as usize].trim() {
                    "copy" => "Copy",
                    "shared" => "Shared",
                    "linear" => "Linear",
                    _ => "Type",
                }
            )
            .to_string(),
            Some(at.0 as u32),
        ));
    }
    if let Some((at, message)) = reader.refused_form(root) {
        return Err(failed(message.to_string(), Some(at as u32)));
    }
    let mut stmts = Vec::new();
    if let Some(program) = reader.find(root, Nt::Program)
        && let Some(list) = reader.first(program, Nt::Stmts)
    {
        for s in reader.collect_stmts(list) {
            reader.read_into(&mut stmts, s);
        }
    }
    Ok(Program {
        stmts,
        errors: Vec::new(),
    })
}

/// Pushes `stmt`, and before an `extern` block the structs of its types.
fn push_stmt(stmts: &mut Vec<Stmt>, stmt: Stmt) {
    if let Stmt::Extern { types, .. } = &stmt {
        stmts.extend(types.iter().cloned().map(Stmt::Struct));
    }
    stmts.push(stmt);
}

impl Reader<'_> {
    pub(super) fn find(&self, id: NodeId, kind: Nt) -> Option<NodeId> {
        for c in self.cst.children(id) {
            if self.nt(c) == Some(kind) {
                return Some(c);
            }
            if let Some(f) = self.find(c, kind) {
                return Some(f);
            }
        }
        None
    }

    /// Every node of `kind` below `id`, not looking inside one found.
    fn descend(&self, id: NodeId, kind: Nt, out: &mut Vec<NodeId>) {
        for c in self.cst.children(id) {
            match self.nt(c) {
                Some(k) if k == kind => out.push(c),
                Some(_) => self.descend(c, kind, out),
                None => {}
            }
        }
    }

    fn name_of(&self, id: NodeId) -> String {
        self.text(id).to_string()
    }

    pub(super) fn stmt(&self, id: NodeId) -> Stmt {
        let Some(attr) = self.first(id, Nt::Attribute) else {
            return self.visible_stmt(id);
        };
        let span = self.span(id);
        let (name, arg) = match self
            .first(attr, Nt::MacroCall)
            .map(|c| self.term(c).kind.clone())
        {
            Some(kind) => match &*kind {
                TermKind::MacroCall { name, arg } => (name.clone(), (**arg).clone()),
                _ => return Stmt::Other("Attribute".into(), span),
            },
            _ => return Stmt::Other("Attribute".into(), span),
        };
        let list = self.first(attr, Nt::AttrGenerates);
        let mut generates = self.generates_clause(
            list,
            self.first(attr, Nt::MacroCall)
                .map_or(span.end, |c| self.span(c).end),
        );
        let replace = list.and_then(|l| self.replace_of(l, &mut generates));
        Stmt::Attributed {
            name,
            arg,
            generates,
            replace,
            stmt: Box::new(self.visible_stmt(id)),
            span: self.span(attr),
        }
    }

    /// Pushes the statements `id` is: a `macro fn m(…) … { … }` is the function `m` and the registration
    /// of `m` as a macro, in that order.
    pub(super) fn read_into(&self, out: &mut Vec<Stmt>, id: NodeId) {
        let macro_fn = if self.first(id, Nt::Attribute).is_none() {
            self.first(id, Nt::OtherStmt)
                .and_then(|o| self.cst.children(o).into_iter().next())
                .filter(|inner| self.nt(*inner) == Some(Nt::MacroFnDecl))
        } else {
            None
        };
        let Some(inner) = macro_fn else {
            push_stmt(out, self.stmt(id));
            return;
        };
        let span = self.span(id);
        let Some(decl) = self.first(inner, Nt::FnDecl) else {
            out.push(Stmt::Other("macro fn".into(), span));
            return;
        };
        let function = self.fn_decl(decl);
        let name = match &function {
            Stmt::Fn(f) => f.name.clone(),
            _ => crate::identity::Name::Spelled(String::new()),
        };
        let function = match self.first(id, Nt::Visibility) {
            Some(v) => with_vis(function, self.vis(v), self.span(v)),
            None => function,
        };
        out.push(function);
        out.push(Stmt::Macro {
            function: name.to_string(),
            name: name.to_string(),
            span,
        });
    }

    /// `syntax!(name, ```par … ```, with(fmt: f, tokens: g)) => struct a, …` and `inductive_syntax!(…)`.
    fn syntax_decl(&self, inner: NodeId, span: Span) -> Stmt {
        let exprs = self.all(inner, Nt::Expr);
        let [name_expr, grammar_expr] = exprs.as_slice() else {
            return Stmt::Other("SyntaxDecl".into(), span);
        };
        let name = self
            .find(*name_expr, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        let Some(lit) = self.find(*grammar_expr, Nt::SyntaxLit) else {
            return Stmt::Other("SyntaxDecl".into(), span);
        };
        let uses = self
            .first(inner, Nt::SyntaxWith)
            .map(|with| self.all(with, Nt::Item))
            .unwrap_or_default()
            .into_iter()
            .map(|u| {
                let mut names = Vec::new();
                self.descend(u, Nt::Ident, &mut names);
                SyntaxUse {
                    role: names.first().map(|n| self.name_of(*n)).unwrap_or_default(),
                    function: crate::identity::Name::Spelled(
                        names.get(1).map(|n| self.name_of(*n)).unwrap_or_default(),
                    ),
                    span: self.span(u),
                }
            })
            .collect();
        Stmt::Syntax {
            inductive: self.descend_first(inner, Nt::KwInductiveSyntaxMacro),
            name,
            generates: self.generates_clause(
                self.first(inner, Nt::Generates),
                self.first(inner, Nt::RParen)
                    .map_or(span.end, |p| self.span(p).end),
            ),
            uses,
            grammar: self.lit(lit),
            span,
        }
    }

    /// The word written before the first item of an attribute's list (`=> replace fn f, …`): that item is the
    /// declaration the macro changes, and is taken out of `generates`.
    fn replace_of(&self, list: NodeId, generates: &mut Generates) -> Option<Replace> {
        let word = self.all(list, Nt::Ident).into_iter().next()?;
        let first = self.all(list, Nt::Generated).into_iter().next()?;
        if self.span(word).start >= self.span(first).start {
            return None;
        }
        if generates.items.is_empty() {
            return None;
        }
        let (kind, name) = generates.items.remove(0);
        Some(Replace {
            word: self.name_of(word),
            kind,
            name: crate::identity::Name::Spelled(name),
            at: Span::new(self.span(word).start, self.span(first).end),
        })
    }

    fn visible_stmt(&self, id: NodeId) -> Stmt {
        let stmt = self.plain_stmt(id);
        match self.first(id, Nt::Visibility) {
            Some(v) => with_vis(stmt, self.vis(v), self.span(v)),
            None => stmt,
        }
    }

    fn vis(&self, v: NodeId) -> Vis {
        if self.descend_first(v, Nt::KwPubOpen) {
            Vis::Open
        } else {
            Vis::Pub
        }
    }

    fn descend_first(&self, id: NodeId, kind: Nt) -> bool {
        let mut found = Vec::new();
        self.descend(id, kind, &mut found);
        !found.is_empty()
    }

    fn plain_stmt(&self, id: NodeId) -> Stmt {
        let span = self.span(id);
        let Some(other) = self.first(id, Nt::OtherStmt) else {
            return Stmt::Other("Stmt".into(), span);
        };
        let Some(inner) = self.cst.children(other).into_iter().next() else {
            return Stmt::Other("OtherStmt".into(), span);
        };
        let kind = self.nt(inner);
        let ident = |s: &Self| {
            s.first(inner, Nt::Ident)
                .map(|i| s.name_of(i))
                .unwrap_or_default()
        };
        let expr = |s: &Self| {
            s.first(inner, Nt::Expr)
                .map(|e| s.term(e))
                .unwrap_or_else(|| s.other(inner))
        };
        match kind {
            Some(Nt::LetDecl) => Stmt::Let {
                name: crate::identity::Name::Spelled(ident(self)),
                ty: self.ty(inner).map(|t| self.term(t)),
                value: expr(self),
                borrow: self.first(inner, Nt::Borrow).is_some(),
                borrow_mut: self
                    .first(inner, Nt::Borrow)
                    .is_some_and(|b| self.first(b, Nt::KwMut).is_some()),
            },
            Some(Nt::VarDecl) => Stmt::Var {
                name: crate::identity::Name::Spelled(ident(self)),
                ty: self.ty(inner).map(|t| self.term(t)),
                value: expr(self),
                borrow: self.first(inner, Nt::Amp).is_some(),
            },
            Some(Nt::FnDecl) => self.fn_decl(inner),
            Some(Nt::TheoremDecl | Nt::AxiomDecl) => self.theorem_decl(inner, span),
            Some(Nt::DefDecl) => self.def_decl(inner, span),
            Some(Nt::MutualDecl) => {
                let mut nodes = Vec::new();
                self.push_mutual(inner, &mut nodes);
                let items = nodes
                    .into_iter()
                    .filter_map(|item| {
                        let member = self.first(item, Nt::MutualMember)?;
                        let decl = self.cst.children(member).into_iter().next()?;
                        let sp = self.span(decl);
                        let stmt = match self.nt(decl) {
                            Some(Nt::InductiveDecl) => self.inductive_decl(decl, sp),
                            Some(Nt::FnDecl) => self.fn_decl(decl),
                            Some(Nt::TheoremDecl) => self.theorem_decl(decl, sp),
                            _ => return None,
                        };
                        Some(match self.first(item, Nt::Visibility) {
                            Some(v) => with_vis(stmt, self.vis(v), self.span(v)),
                            None => stmt,
                        })
                    })
                    .collect();
                Stmt::Mutual { items, span }
            }
            Some(Nt::ModuleDecl) => {
                let items = self
                    .first(inner, Nt::Block)
                    .and_then(|b| self.first(b, Nt::Stmts))
                    .map(|list| {
                        let mut items = Vec::new();
                        for s in self.collect_stmts(list) {
                            self.read_into(&mut items, s);
                        }
                        items
                    })
                    .unwrap_or_default();
                Stmt::Module {
                    name: ident(self),
                    items,
                    span,
                }
            }
            Some(Nt::ImportDecl) => {
                // `{ Text, concat }`: the names the import brings.
                let names = self.first(inner, Nt::ImportList).map(|list| {
                    let mut idents = Vec::new();
                    self.descend(list, Nt::Ident, &mut idents);
                    idents
                        .into_iter()
                        .map(|i| (self.name_of(i), self.span(i)))
                        .collect::<Vec<_>>()
                });
                match self.first(inner, Nt::Text) {
                    Some(t) => Stmt::Import {
                        path: super::unquote_text(&self.text(t)),
                        module: false,
                        names,
                        span,
                    },
                    // `import std::List` is kept as the path `std::List`.
                    None => Stmt::Import {
                        path: self
                            .all(inner, Nt::Ident)
                            .into_iter()
                            .map(|i| self.text(i).to_string())
                            .collect::<Vec<_>>()
                            .join(SEPARATOR),
                        module: true,
                        names,
                        span,
                    },
                }
            }
            Some(Nt::SyntaxDecl) => self.syntax_decl(inner, span),
            // Read as the function and its registration by `read_into`.
            Some(Nt::MacroFnDecl) => Stmt::Other("macro fn".into(), span),
            Some(Nt::InductiveDecl) => self.inductive_decl(inner, span),
            Some(Nt::EffectDecl) => self.effect_decl(inner),
            Some(Nt::StructDecl) => Stmt::Struct(self.struct_decl(inner)),
            Some(Nt::EnumDecl) => Stmt::Enum(self.enum_decl(inner)),
            Some(Nt::ClassDecl) => {
                let (generics, bounds) = self.generic_bounds(inner);
                let mut methods = Vec::new();
                self.descend(inner, Nt::ExternFn, &mut methods);
                Stmt::Class(ClassDecl {
                    parameters: self.generics(inner),
                    vis: Vis::Private,
                    name: crate::identity::Name::Spelled(ident(self)),
                    arity: generics.len(),
                    param: crate::identity::Name::Spelled(
                        generics.first().cloned().unwrap_or_default(),
                    ),
                    bound: bounds.into_iter().next().flatten(),
                    methods: methods.into_iter().map(|m| self.method(m)).collect(),
                    laws: self.laws(inner),
                    span,
                })
            }
            Some(Nt::InstanceDecl) => {
                let (generics, bounds) = self.generic_bounds(inner);
                let mut methods = Vec::new();
                self.descend(inner, Nt::FnDecl, &mut methods);
                Stmt::Instance(InstanceDecl {
                    generic_types: self.generics(inner).into_iter().map(|(_, t)| t).collect(),
                    arguments: self
                        .all(inner, Nt::Type)
                        .into_iter()
                        .skip(1)
                        .map(|t| self.term(t))
                        .collect(),
                    generics: generics.into_iter().map(Name::from).collect(),
                    bounds: bounds.into_iter().map(|b| b.map(Into::into)).collect(),
                    class: crate::identity::Name::Spelled(ident(self)),
                    head: self
                        .ty(inner)
                        .map(|t| self.term(t))
                        .unwrap_or_else(|| self.other(inner)),
                    where_: self.where_clause(inner),
                    methods: methods.into_iter().map(|m| self.method(m)).collect(),
                    laws: self.laws(inner),
                    span,
                })
            }
            Some(Nt::ExternDecl) => {
                let mut nodes = Vec::new();
                self.descend(inner, Nt::ExternFn, &mut nodes);
                let mut instances = Vec::new();
                self.descend(inner, Nt::ExternInstance, &mut instances);
                let instances = instances
                    .into_iter()
                    .map(|i| ExternInstance {
                        class: crate::identity::Name::Spelled(
                            self.first(i, Nt::Ident)
                                .map(|n| self.name_of(n))
                                .unwrap_or_default(),
                        ),
                        ty: self
                            .ty(i)
                            .map(|t| self.term(t))
                            .unwrap_or_else(|| self.other(i)),
                        span: self.span(i),
                    })
                    .collect();
                let mut types = Vec::new();
                self.descend(inner, Nt::ExternType, &mut types);
                let types = types
                    .into_iter()
                    .map(|t| {
                        let name = self
                            .first(t, Nt::Ident)
                            .map(|n| self.name_of(n))
                            .unwrap_or_default();
                        DataDecl {
                            vis: Vis::Private,
                            kind: self.data_kind(t),
                            name: crate::identity::Name::Spelled(name.clone()),
                            generics: Vec::new(),
                            rows: Vec::new(),
                            constructors: vec![DataConstructor {
                                name: crate::identity::Name::Spelled(name),
                                fields: Vec::new(),
                            }],
                            host: true,
                            span: self.span(t),
                        }
                    })
                    .collect();
                Stmt::Extern {
                    instances,
                    types,
                    fns: nodes
                        .into_iter()
                        .map(|f| match self.fn_decl(f) {
                            Stmt::Fn(f) => f,
                            _ => unreachable!(),
                        })
                        .collect(),
                    span,
                }
            }
            Some(Nt::WhileStmt) => {
                let condition = self
                    .first(inner, Nt::Cond)
                    .map(|e| self.term(e))
                    .unwrap_or_else(|| self.other(inner));
                let body = self
                    .first(inner, Nt::Block)
                    .map(|b| self.term(b))
                    .unwrap_or_else(|| self.other(inner));
                Stmt::While { condition, body }
            }
            Some(Nt::ReturnStmt) => Stmt::Return(self.first(inner, Nt::Expr).map(|e| self.term(e))),
            Some(Nt::ExprStmt) => {
                let exprs = self.all(inner, Nt::Expr);
                match exprs.as_slice() {
                    [only] => match self.expr_generates(*only) {
                        Some((call, _)) => Stmt::Called {
                            call: self.term(call),
                            generates: self.generated_items(*only),
                            span,
                        },
                        None => Stmt::Expr(self.term(*only)),
                    },
                    [target, value] => {
                        let target = self.term(*target);
                        match &*target.kind {
                            TermKind::Var(name) => Stmt::Assign {
                                name: name.clone(),
                                place: None,
                                value: self.term(*value),
                            },
                            _ => match place_root(&target) {
                                Some(name) => Stmt::Assign {
                                    name,
                                    place: Some(target),
                                    value: self.term(*value),
                                },
                                None => Stmt::Other("assignment target".into(), span),
                            },
                        }
                    }
                    _ => Stmt::Other("ExprStmt".into(), span),
                }
            }
            Some(k) => Stmt::Other(k.to_string(), span),
            None => Stmt::Other("token".into(), span),
        }
    }

    fn fn_decl(&self, decl: NodeId) -> Stmt {
        let name = self
            .first(decl, Nt::FnName)
            .map(|n| self.name_of(n))
            .unwrap_or_default();
        let params = self
            .all(decl, Nt::Param)
            .into_iter()
            .filter_map(|p| self.first(p, Nt::Ident).map(|i| self.name_of(i).into()))
            .collect();
        // An `extern` function has no block: its body is an `Other` term,
        // never run.
        let body = self
            .first(decl, Nt::Block)
            .map(|b| self.term(b))
            .unwrap_or_else(|| self.other(decl));
        let borrows = self
            .all(decl, Nt::Param)
            .into_iter()
            .map(|p| {
                self.first(p, Nt::Borrow)
                    .map(|b| self.first(b, Nt::KwMut).is_some())
            })
            .collect();
        let param_types = self
            .all(decl, Nt::Param)
            .into_iter()
            .map(|p| self.ty(p).map(|t| self.term(t)))
            .collect();
        // The row after the result type, `: &A ! {out_of_bounds}`; a row after a function type
        // is that arrow's.
        let written = self
            .first(decl, Nt::FnResult)
            .and_then(|r| self.first(r, Nt::BodyType));
        let (result, unattached) = match written {
            Some(r) => {
                let (term, row) = self.sequence(r);
                (Some(term), row)
            }
            None => (None, None),
        };
        let row = self
            .first(decl, Nt::FnResult)
            .and_then(|r| self.first(r, Nt::EffectRow));
        let effects = row.map(|row| self.row_names(row)).or(unattached);
        let where_ = self.where_clause(decl);
        let (generics, bounds) = self.generic_bounds(decl);
        let rows = self.generic_rows(decl);
        let opaque = self.first(decl, Nt::KwOpaque).is_some();
        let decreasing_by = self
            .first(decl, Nt::DecreasingBy)
            .and_then(|d| self.first(d, Nt::Cond))
            .map(|c| self.term(c));
        // The list after `=>`; when it is missing, an empty one where it goes,
        // so that the kernel reports what is missing.
        let generates = match self.first(decl, Nt::Generates) {
            Some(g) => Some(self.generated_items(g)),
            None if decreasing_by.is_some() || opaque => {
                let end = match &decreasing_by {
                    Some(term) => term.span.end,
                    None => [Nt::WhereClause, Nt::FnResult, Nt::RParen]
                        .into_iter()
                        .find_map(|k| self.first(decl, k))
                        .map_or(self.span(decl).start, |n| self.span(n).end),
                };
                Some(crate::generated::unwritten(end))
            }
            None => None,
        };
        Stmt::Fn(FnDecl {
            vis: Vis::Private,
            name: crate::identity::Name::Spelled(name),
            generic_types: self.generics(decl).into_iter().map(|(_, ty)| ty).collect(),
            generics: generics.into_iter().map(Name::from).collect(),
            rows,
            bounds: bounds.into_iter().map(|b| b.map(Into::into)).collect(),
            bound_spans: self.generic_spans(decl),
            params,
            borrows,
            param_types,
            result,
            effects,
            where_,
            span: self.span(decl),
            opaque,
            decreasing_by,
            generates,
            budget: self.decl_budget(decl),
            body,
        })
    }

    fn where_clause(&self, decl: NodeId) -> Vec<Constraint> {
        self.first(decl, Nt::WhereClause)
            .map(|w| {
                self.all(w, Nt::Constraint)
                    .into_iter()
                    .map(|c| Constraint {
                        arguments: self
                            .all(c, Nt::Type)
                            .into_iter()
                            .skip(1)
                            .map(|t| self.term(t))
                            .collect(),
                        class: crate::identity::Name::Spelled(
                            self.first(c, Nt::Ident)
                                .map(|i| self.name_of(i))
                                .unwrap_or_default(),
                        ),
                        ty: self
                            .ty(c)
                            .map(|t| self.term(t))
                            .unwrap_or_else(|| self.other(c)),
                        span: self.span(c),
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn method(&self, decl: NodeId) -> FnDecl {
        match self.fn_decl(decl) {
            Stmt::Fn(f) => f,
            _ => unreachable!(),
        }
    }

    fn laws(&self, decl: NodeId) -> Vec<LawDecl> {
        let mut nodes = Vec::new();
        self.descend(decl, Nt::LawDecl, &mut nodes);
        nodes
            .into_iter()
            .map(|l| {
                let span = self.span(l);
                let Stmt::Theorem(theorem) = self.theorem_decl(l, span) else {
                    unreachable!()
                };
                LawDecl {
                    name: theorem.name.clone(),
                    span,
                    theorem,
                }
            })
            .collect()
    }

    fn effect_decl(&self, decl: NodeId) -> Stmt {
        let name = self
            .first(decl, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        let signature = self
            .first(decl, Nt::EffectBody)
            .and_then(|b| self.first(b, Nt::EffectSignature));
        let alias = self
            .first(decl, Nt::EffectBody)
            .and_then(|b| self.first(b, Nt::EffectAlias));
        // `effect ask(question: Text): i64` has the operation's parameters
        // in the parentheses; `effect State(T: Type) {…}` has the set's
        // type parameters.
        let written: Vec<NodeId> = self
            .first(decl, Nt::EffectParams)
            .map(|p| self.all(p, Nt::Param))
            .unwrap_or_default();
        let param_name = |p: NodeId| {
            self.first(p, Nt::Ident)
                .map(|i| self.name_of(i))
                .unwrap_or_default()
        };
        let (param_names, params): (Vec<Name>, Vec<Option<SurfaceTerm>>) = if signature.is_some() {
            written
                .iter()
                .map(|&p| (param_name(p).into(), self.ty(p).map(|t| self.term(t))))
                .unzip()
        } else {
            Default::default()
        };
        let generics: Vec<Name> = if alias.is_some() {
            written.iter().map(|&p| param_name(p).into()).collect()
        } else {
            self.generics(decl).into_iter().map(|(g, _)| g).collect()
        };
        let rows = if alias.is_some() {
            vec![false; generics.len()]
        } else {
            self.generic_rows(decl)
        };
        let result = signature.and_then(|sig| self.ty(sig)).map(|t| self.term(t));
        let resume = signature
            .and_then(|sig| self.first(sig, Nt::EffectMode))
            .map(|mode| match self.first(mode, Nt::Quant) {
                Some(q) => self.text(q).replace(char::is_whitespace, ""),
                None => "direct".to_string(),
            });
        Stmt::Effect(EffectDecl {
            vis: Vis::Private,
            name: crate::identity::Name::Spelled(name),
            generics: generics.into_iter().map(Name::from).collect(),
            rows,
            params,
            param_names,
            result,
            resume,
            // `{Div, stdout}` lists names, not a row's set expression.
            set: alias.map(|a| {
                self.all(a, Nt::EffectName)
                    .into_iter()
                    .filter_map(|n| {
                        let name = self.text(self.first(n, Nt::Ident)?);
                        Some(match self.first(n, Nt::TypeCall) {
                            Some(args) => format!("{name}{}", self.text(args)),
                            None => name.to_string(),
                        })
                    })
                    .collect()
            }),
            span: self.span(decl),
        })
    }

    /// The node of a declaration's generics: `<A>` of a function, theorem or
    /// operation, or `(A: Type)` of a type declaration.
    fn generic_node(&self, node: NodeId) -> Option<NodeId> {
        self.first(node, Nt::Generics)
            .or_else(|| self.first(node, Nt::TypeParams))
    }

    /// A form the grammar reads but the language does not have: an effect operation written as
    /// `effect ask: (q: T) -> R` (it is `effect ask(q: T): R`), and an effect row with two row
    /// variables or a set literal that writes an effect twice.
    fn refused_form(&self, root: NodeId) -> Option<(u32, Message)> {
        for (kind, span) in self.cst.terminals() {
            if kind == tauto_parol::TerminalKind::Ident && span.text(self.source) == "r#_" {
                return Some((span.start, msg!("surface-raw-underscore")));
            }
        }
        let mut effects = Vec::new();
        self.descend(root, Nt::EffectDecl, &mut effects);
        for e in effects {
            let old = self.first(e, Nt::EffectParams).is_none()
                && self
                    .first(e, Nt::EffectBody)
                    .and_then(|b| self.first(b, Nt::EffectSignature))
                    .and_then(|s| self.ty(s))
                    .is_some_and(|t| {
                        self.descend_first(t, Nt::ThinArrow)
                            && self.text(t).trim_start().starts_with('(')
                    });
            if old {
                return Some((self.span(e).start, msg!("surface-old-effect-operation")));
            }
        }
        let mut rows = Vec::new();
        self.descend(root, Nt::EffectSet, &mut rows);
        for row in rows {
            let mut variables = 0;
            for term in self.all(row, Nt::EffectTerm) {
                if self.first(term, Nt::Ident).is_some()
                    && self.first(term, Nt::EffectLit).is_none()
                {
                    variables += 1;
                }
                if let Some(lit) = self.first(term, Nt::EffectLit) {
                    let mut seen: Vec<String> = Vec::new();
                    for name in self.all(lit, Nt::EffectName) {
                        let written = self.text(name).trim().to_string();
                        if seen.contains(&written) {
                            return Some((
                                self.span(name).start,
                                msg!("surface-row-repeats-effect", name = written),
                            ));
                        }
                        seen.push(written);
                    }
                }
            }
            if variables > 1 {
                return Some((self.span(row).start, msg!("surface-row-variables")));
            }
        }
        None
    }

    /// Where a kind is written as a lowercase word, as in `<A: shared>`: it is
    /// written `Shared`.
    fn bare_kind(&self, id: NodeId) -> Option<(u32, u32)> {
        if matches!(self.nt(id), Some(Nt::Generic | Nt::TypeParam))
            && let Some(kind) = self.first(id, Nt::GenericKind)
        {
            let mut names = Vec::new();
            self.descend(kind, Nt::Ident, &mut names);
            for n in names {
                if matches!(self.text(n).trim(), "copy" | "shared" | "affine" | "linear") {
                    let at = self.cst.span(n);
                    return Some((at.start, at.end));
                }
            }
        }
        self.cst.children_iter(id).find_map(|c| self.bare_kind(c))
    }

    fn generic_items(&self, generics: NodeId) -> Vec<NodeId> {
        self.cst
            .children_iter(generics)
            .filter(|c| matches!(self.nt(*c), Some(Nt::Generic | Nt::TypeParam)))
            .collect()
    }

    fn generic_spans(&self, node: NodeId) -> Vec<Span> {
        let Some(generics) = self.generic_node(node) else {
            return Vec::new();
        };
        self.generic_items(generics)
            .into_iter()
            .map(|g| self.span(g))
            .collect()
    }

    /// For each generic of a declaration: whether it is written with `!`, a row variable.
    fn generic_rows(&self, node: NodeId) -> Vec<bool> {
        let Some(generics) = self.generic_node(node) else {
            return Vec::new();
        };
        self.generic_items(generics)
            .into_iter()
            .map(|g| self.first(g, Nt::Bang).is_some())
            .collect()
    }

    /// The generics' names, and each one's bound as the checker reads it:
    /// `Shared` is `shared`, `(Shared) -> Shared` is
    /// `(shared)->shared`, and a row variable's `!e: <=1` is `<=1`. A bare
    /// `Type` has none.
    fn generic_bounds(&self, node: NodeId) -> (Vec<String>, Vec<Option<String>>) {
        let Some(generics) = self.generic_node(node) else {
            return (Vec::new(), Vec::new());
        };
        self.generic_items(generics)
            .into_iter()
            .map(|g| {
                let name = self
                    .first(g, Nt::Ident)
                    .map(|i| self.name_of(i))
                    .unwrap_or_default();
                let bound = match (self.first(g, Nt::RowBound), self.first(g, Nt::GenericKind)) {
                    (Some(b), _) => Some(self.text(b).replace(char::is_whitespace, "")),
                    (None, Some(k)) => self.kind_bound(k),
                    (None, None) => None,
                };
                (name, bound)
            })
            .unzip()
    }

    /// A kind as the checker's bound string: the universe names `Copy`,
    /// `Shared` and `Linear` are `copy`, `shared` and `linear`, `Type` is
    /// `affine`, the whitespace is dropped, and `Type` alone is none.
    fn kind_bound(&self, kind: NodeId) -> Option<String> {
        let out: String = self.text(kind).split_whitespace().collect();
        if out == "Type" || out.starts_with("Type(") {
            return None;
        }
        let is_kind = |w: &str| matches!(w, "Copy" | "Shared" | "Type" | "Linear");
        let words = || out.split(|c: char| !(c.is_alphanumeric() || c == '_'));
        if !words().filter(|w| !w.is_empty()).all(is_kind) {
            return Some(out);
        }
        let mut written = String::new();
        let mut word = String::new();
        for c in out.chars().chain(std::iter::once(' ')) {
            if c.is_alphanumeric() || c == '_' {
                word.push(c);
                continue;
            }
            written.push_str(match word.as_str() {
                "Copy" => "copy",
                "Shared" => "shared",
                "Linear" => "linear",
                "Type" => "affine",
                w => w,
            });
            word.clear();
            if c != ' ' {
                written.push(c);
            }
        }
        Some(written)
    }

    /// The kernel's reading of a kind: every universe name is `Type`.
    fn kind_term(&self, t: &SurfaceTerm) -> SurfaceTerm {
        match &*t.kind {
            TermKind::Var(n) if matches!(n.as_str(), "Copy" | "Shared" | "Linear") => {
                SurfaceTerm::var("Type", t.span)
            }
            TermKind::Pi {
                params,
                result,
                effects,
            } => SurfaceTerm::new(
                TermKind::Pi {
                    params: params
                        .iter()
                        .map(|(n, p)| (n.clone(), self.kind_term(p)))
                        .collect(),
                    result: Box::new(self.kind_term(result)),
                    effects: effects.clone(),
                },
                t.span,
            ),
            _ => t.clone(),
        }
    }

    fn data_kind(&self, decl: NodeId) -> Option<String> {
        let kind = self.first(decl, Nt::DataKind)?;
        self.first(kind, Nt::Kind)
            .or_else(|| self.first(kind, Nt::KwInductive))
            .map(|k| self.text(k).trim().to_string())
    }

    fn data_fields(&self, fields: NodeId) -> Vec<(Option<String>, SurfaceTerm)> {
        let mut nodes = Vec::new();
        self.descend(fields, Nt::FieldDecl, &mut nodes);
        nodes
            .into_iter()
            .map(|f| {
                let name = self.first(f, Nt::Ident).map(|i| self.name_of(i));
                let ty = match self.ty(f) {
                    Some(t) => self.term(t),
                    None => self.other(f),
                };
                (name.into(), ty)
            })
            .collect()
    }

    fn struct_decl(&self, decl: NodeId) -> DataDecl {
        let name = self
            .first(decl, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        let fields = self
            .first(decl, Nt::StructBody)
            .and_then(|b| self.first(b, Nt::Fields))
            .map(|f| self.data_fields(f))
            .unwrap_or_default();
        DataDecl {
            vis: Vis::Private,
            kind: self.data_kind(decl),
            name: crate::identity::Name::Spelled(name.clone()),
            generics: self.generics(decl).into_iter().map(|(g, _)| g).collect(),
            rows: self.generic_rows(decl),
            constructors: vec![DataConstructor {
                name: crate::identity::Name::Spelled(name),
                fields,
            }],
            host: false,
            span: self.span(decl),
        }
    }

    fn enum_decl(&self, decl: NodeId) -> DataDecl {
        let name = self
            .first(decl, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        let mut variants = Vec::new();
        self.descend(decl, Nt::Variant, &mut variants);
        let constructors = variants
            .into_iter()
            .map(|v| {
                let name = self
                    .first(v, Nt::Ident)
                    .map(|i| self.name_of(i))
                    .unwrap_or_default();
                let fields = match self.first(v, Nt::VariantBody) {
                    None => Vec::new(),
                    Some(body) => match self.first(body, Nt::Fields) {
                        Some(f) => self.data_fields(f),
                        None => self
                            .tys(body)
                            .into_iter()
                            .map(|t| (None, self.term(t)))
                            .collect(),
                    },
                };
                DataConstructor {
                    name: crate::identity::Name::Spelled(name),
                    fields,
                }
            })
            .collect();
        DataDecl {
            vis: Vis::Private,
            kind: self.data_kind(decl),
            name: crate::identity::Name::Spelled(name),
            generics: self.generics(decl).into_iter().map(|(g, _)| g).collect(),
            rows: self.generic_rows(decl),
            constructors,
            host: false,
            span: self.span(decl),
        }
    }

    /// `<A, n: Nat>` or `(A: Type, n: Nat)`: the generics, typed `Type`
    /// unless a kind is written; `Shared` is read as `Type`.
    fn generics(&self, node: NodeId) -> Vec<(Name, SurfaceTerm)> {
        let Some(generics) = self.generic_node(node) else {
            return Vec::new();
        };
        self.generic_items(generics)
            .into_iter()
            .map(|g| {
                let name = self
                    .first(g, Nt::Ident)
                    .map(|i| self.name_of(i))
                    .unwrap_or_default();
                let kind = match (self.first(g, Nt::RowBound), self.first(g, Nt::GenericKind)) {
                    (Some(b), _) => SurfaceTerm::var(
                        &self.text(b).replace(char::is_whitespace, ""),
                        self.span(b),
                    ),
                    (None, Some(k)) => self.kind_term(&self.term(k)),
                    (None, None) => SurfaceTerm::var("Type", self.span(g)),
                };
                (name.into(), kind)
            })
            .collect()
    }

    fn typed_params(&self, node: NodeId) -> Vec<(Name, SurfaceTerm)> {
        self.all(node, Nt::Param)
            .into_iter()
            .map(|p| {
                let name = self
                    .first(p, Nt::Ident)
                    .map(|i| self.name_of(i))
                    .unwrap_or_default();
                let ty = match self.ty(p) {
                    Some(t) => self.term(t),
                    None => self.other(p),
                };
                (name.into(), ty)
            })
            .collect()
    }

    /// The names of a `Generates` node, or an unwritten clause at `at`.
    fn generates_clause(&self, node: Option<NodeId>, at: u32) -> Generates {
        let clause = match node {
            Some(n) => self.generated_items(n),
            None => Generates {
                at: Span::new(at, at),
                ..Generates::default()
            },
        };
        Generates {
            breaks: true,
            ..clause
        }
    }

    /// The `Generated` children of `node` (a `Generates`, or an `Expr` that ends in the list), as a
    /// clause that starts at its first `=>`.
    fn generated_items(&self, node: NodeId) -> Generates {
        let items: Vec<(String, String)> = self
            .all(node, Nt::Generated)
            .into_iter()
            .filter_map(|g| {
                let kind = self.first(g, Nt::GeneratedKind).map(|k| self.name_of(k))?;
                let parts: Vec<String> = self
                    .all(g, Nt::Ident)
                    .into_iter()
                    .map(|i| self.name_of(i))
                    .collect();
                if parts.is_empty() {
                    return None;
                }
                Some((kind, parts.join(SEPARATOR)))
            })
            .collect();
        let arrow = self.first(node, Nt::FatArrow);
        let last = self.all(node, Nt::Generated).last().copied();
        let at = match (arrow, last) {
            (Some(a), Some(l)) => Span::new(self.span(a).start, self.span(l).end),
            _ => Span::default(),
        };
        Generates {
            items,
            written: true,
            at,
            breaks: false,
        }
    }

    /// For an `Expr` that is `call => fn a, theorem b`: the call and the list.
    pub(super) fn expr_generates(&self, expr: NodeId) -> Option<(NodeId, Vec<(String, String)>)> {
        self.first(expr, Nt::Generated)?;
        let call = self
            .cst
            .children(expr)
            .into_iter()
            .find(|c| matches!(self.nt(*c), Some(nt) if nt != Nt::Gap && nt != Nt::FatArrow))?;
        Some((call, self.generated_items(expr).items))
    }

    fn inductive_decl(&self, decl: NodeId, span: Span) -> Stmt {
        let name = self
            .first(decl, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        let sort = match self.ty(decl) {
            Some(t) => self.term(t),
            None => self.other(decl),
        };
        let mut ctors = Vec::new();
        if let Some(list) = self.first(decl, Nt::Constructors) {
            self.push_constructors(list, &mut ctors);
        }
        let constructors = ctors
            .into_iter()
            .map(|c| {
                let mut params = self.generics(c);
                let implicit = params.len();
                params.extend(self.typed_params(c));
                // `false` and `true`, the constructors of `Bool`, are words.
                let name = if let Some(i) = self.first(c, Nt::Ident) {
                    self.name_of(i)
                } else if self.first(c, Nt::True).is_some() {
                    "true".to_string()
                } else if self.first(c, Nt::False).is_some() {
                    "false".to_string()
                } else {
                    String::new()
                };
                Constructor {
                    name: crate::identity::Name::Spelled(name),
                    implicit,
                    params,
                    result: match self.ty(c) {
                        Some(t) => self.term(t),
                        None => self.other(c),
                    },
                }
            })
            .collect();
        let generates = self.generates_clause(
            self.first(decl, Nt::Generates),
            self.ty(decl).map_or(span.end, |t| self.span(t).end),
        );
        Stmt::Inductive(InductiveDecl {
            vis: Vis::Private,
            name: crate::identity::Name::Spelled(name),
            params: self.typed_params(decl),
            sort,
            constructors,
            generates,
            span,
        })
    }

    fn push_mutual(&self, node: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::MutualItem) => out.push(c),
                Some(Nt::MutualItems | Nt::MutualTail) => self.push_mutual(c, out),
                _ => {}
            }
        }
    }

    fn push_constructors(&self, node: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::Constructor) => out.push(c),
                Some(Nt::ConstructorsTail) => self.push_constructors(c, out),
                _ => {}
            }
        }
    }

    fn def_decl(&self, decl: NodeId, span: Span) -> Stmt {
        let Stmt::Theorem(mut t) = self.theorem_decl(decl, span) else {
            unreachable!()
        };
        // `Colon Type Assign Gap Type`: the first `Type` is the result, the
        // second the body.
        let types = self.tys(decl);
        if let [result, body] = types.as_slice() {
            t.ty = self.term(*result);
            t.body = Some(self.term(*body));
        }
        Stmt::Def(t)
    }

    fn theorem_decl(&self, decl: NodeId, span: Span) -> Stmt {
        let name = self
            .first(decl, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        let mut params = self.generics(decl);
        let n_generics = params.len();
        // `where C(T)` is a parameter after the generics, the record of the
        // class (`crates/tauto-kernel/src/check/classes.rs`).
        for (i, c) in self.where_clause(decl).into_iter().enumerate() {
            let span = c.span;
            let class = SurfaceTerm::var(&c.class, span);
            params.push((
                crate::identity::Name::Spelled(dictionary_name(&c.class, i)),
                SurfaceTerm::new(
                    TermKind::App {
                        function: Box::new(class),
                        arguments: std::iter::once(c.ty).chain(c.arguments).collect(),
                    },
                    span,
                ),
            ));
        }
        for p in self.all(decl, Nt::Param) {
            let pname = self
                .first(p, Nt::Ident)
                .map(|i| self.name_of(i))
                .unwrap_or_default();
            let ty = match self.ty(p) {
                Some(t) => self.term(t),
                None => self.other(p),
            };
            params.push((crate::identity::Name::Spelled(pname), ty));
        }
        let ty = match self.ty(decl) {
            Some(t) => self.term(t),
            None => self.other(decl),
        };
        let body = self.first(decl, Nt::Block).map(|b| self.term(b));
        let implicit = n_generics;
        let decreasing_by = self
            .first(decl, Nt::DecreasingBy)
            .and_then(|d| self.first(d, Nt::Cond))
            .map(|c| self.term(c));
        Stmt::Theorem(TheoremDecl {
            vis: Vis::Private,
            name: crate::identity::Name::Spelled(name),
            implicit,
            params,
            ty,
            body,
            decreasing_by,
            budget: self.decl_budget(decl),
            span,
        })
    }

    fn decl_budget(&self, decl: NodeId) -> Option<u64> {
        self.first(decl, Nt::DeclBudget)
            .and_then(|b| self.first(b, Nt::Integer))
            .and_then(|i| self.text(i).replace('_', "").parse().ok())
    }

    pub(super) fn perform(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let effect = self
            .first(id, Nt::OperationName)
            .map(|n| self.name_of(n))
            .unwrap_or_default();
        let args = self
            .first(id, Nt::Call)
            .map(|c| {
                self.all(c, Nt::Item)
                    .into_iter()
                    .map(|i| self.term(i))
                    .collect()
            })
            .unwrap_or_default();
        SurfaceTerm::new(
            TermKind::Perform {
                effect: crate::identity::Name::Spelled(effect),
                args,
            },
            span,
        )
    }

    pub(super) fn budget(&self, id: NodeId, span: Span) -> SurfaceTerm {
        // `name: n` pairs in the order written; the first is outermost.
        let mut names = Vec::new();
        let mut counts = Vec::new();
        self.budget_args(id, &mut names, &mut counts);
        let body = self.first(id, Nt::Block).map(|b| self.term(b));
        let (Some(mut term), true) = (body, !names.is_empty() && names.len() == counts.len())
        else {
            return self.other(id);
        };
        let mut limits = Vec::new();
        for name in &names {
            let limit = match &*self.text(*name) {
                "steps" => BudgetLimit::Steps,
                "memory" => BudgetLimit::Memory,
                _ => return self.other(id),
            };
            if limits.contains(&limit) {
                return self.other(id);
            }
            limits.push(limit);
        }
        for (limit, count) in limits.into_iter().zip(counts).rev() {
            term = SurfaceTerm::new(
                TermKind::Budget {
                    limit,
                    steps: Box::new(self.term(count)),
                    body: Box::new(term),
                },
                span,
            );
        }
        term
    }

    /// The `Ident`s and `Expr`s of a `budget`'s arguments, not looking into
    /// an `Expr` or the block.
    fn budget_args(&self, id: NodeId, names: &mut Vec<NodeId>, counts: &mut Vec<NodeId>) {
        for c in self.cst.children(id) {
            match self.nt(c) {
                Some(Nt::Ident) => names.push(c),
                Some(Nt::Expr) => counts.push(c),
                Some(Nt::Block) | None => {}
                Some(_) => self.budget_args(c, names, counts),
            }
        }
    }

    pub(super) fn match_expr(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let Some(scrutinee) = self.first(id, Nt::Cond) else {
            return self.other(id);
        };
        let mut arms = Vec::new();
        let mut nodes = Vec::new();
        // Only under `Arms`: a `match` in the scrutinee has arms of its own.
        if let Some(body) = self.first(id, Nt::Arms) {
            self.descend(body, Nt::Arm, &mut nodes);
        }
        for arm in nodes {
            let pattern = self
                .first(arm, Nt::Pattern)
                .map(|p| self.pattern(p))
                .unwrap_or(Pattern::Other("Arm".into()));
            let guard = self.first(arm, Nt::Cond).map(|g| self.term(g));
            // `C => ⊢ G from p`: the goal and the proof are under the arm's body.
            let goal = self
                .first(arm, Nt::ArmBody)
                .and_then(|b| self.goal_expr(b))
                .and_then(|g| self.ty(g))
                .map(|g| self.term(g));
            // The arm's goal is checked by the arm itself; its body is the `p` under it.
            let body = match self.first(arm, Nt::ArmBody) {
                Some(b) => match self.goal_expr(b) {
                    Some(g) => self.goal_body(g),
                    None => self.term(b),
                },
                None => self.other(arm),
            };
            arms.push(MatchArm {
                pattern,
                guard,
                goal,
                body,
            });
        }
        SurfaceTerm::new(
            TermKind::Match {
                // `match x: T`: the scrutinee's type, as `(x: T)`.
                scrutinee: Box::new(match self.ty(id) {
                    Some(ty) => SurfaceTerm::new(
                        TermKind::Ascribe {
                            term: Box::new(self.term(scrutinee)),
                            ty: Box::new(self.term(ty)),
                        },
                        self.span(scrutinee),
                    ),
                    None => self.term(scrutinee),
                }),
                result: None,
                binder: self.first(id, Nt::Ident).map(|i| self.name_of(i).into()),
                arms,
            },
            span,
        )
    }

    /// `by t!(arg): G0 { Δ ⊢ G from p … }`.
    pub(super) fn step_expr(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let Some(call) = self.first(id, Nt::MacroCall) else {
            return self.other(id);
        };
        let TermKind::MacroCall { name, arg } = (*self.term(call).kind).clone() else {
            return self.other(id);
        };
        let mut arms = Vec::new();
        let mut nodes = Vec::new();
        if let Some(body) = self.first(id, Nt::StepBody) {
            self.descend(body, Nt::StepArm, &mut nodes);
        }
        for arm in nodes {
            let binders = self
                .all(arm, Nt::StepBinder)
                .into_iter()
                .map(|b| {
                    let name = self
                        .first(b, Nt::Ident)
                        .map(|i| self.name_of(i))
                        .unwrap_or_default();
                    let ty = self
                        .ty(b)
                        .map(|t| self.term(t))
                        .unwrap_or_else(|| self.other(b));
                    (name.into(), ty)
                })
                .collect();
            let goal = self
                .ty(arm)
                .map(|t| self.term(t))
                .unwrap_or_else(|| self.other(arm));
            let body = self
                .first(arm, Nt::Expr)
                .map(|e| self.term(e))
                .unwrap_or_else(|| self.other(arm));
            arms.push(StepArm {
                binders,
                goal,
                body,
                span: self.span(arm),
            });
        }
        SurfaceTerm::new(
            TermKind::Step(Box::new(Step {
                tactic: name,
                arg: *arg,
                call: self.span(call),
                before: self.ty(id).map(|t| self.term(t)),
                arms,
            })),
            span,
        )
    }

    fn field_patterns(&self, node: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::FieldPattern) => out.push(c),
                Some(Nt::FieldPatternsTail) => self.field_patterns(c, out),
                _ => {}
            }
        }
    }

    pub(super) fn pattern(&self, id: NodeId) -> Pattern {
        let alts = self.all(id, Nt::PatternAlt);
        let [alt] = alts.as_slice() else {
            return Pattern::Other("alternatives".into());
        };
        self.pattern_alt(*alt)
    }

    fn pattern_alt(&self, alt: NodeId) -> Pattern {
        let alt = &alt;
        // `@a p`: `p` on the member labelled `a`.
        if let Some(label) = self.first(*alt, Nt::LabelPattern) {
            let tag = self
                .first(label, Nt::TagPrefix)
                .and_then(|t| self.first(t, Nt::Ident))
                .map(|i| self.text(i).trim().to_string())
                .unwrap_or_default();
            return match self.first(label, Nt::PatternAlt) {
                Some(inner) => Pattern::labelled(&tag, self.pattern_alt(inner)),
                None => Pattern::Other("LabelPattern".into()),
            };
        }
        if let Some(path) = self.first(*alt, Nt::PathPattern) {
            let text = self.text(path);
            let text = text.trim();
            let simple = self.first(path, Nt::PatternArgs).is_none()
                && self.first(path, Nt::PatternImplicits).is_none()
                && self.all(path, Nt::Ident).len() == 1
                && self.all(path, Nt::Dot).is_empty();
            if simple {
                return if text == "_" {
                    Pattern::Wild
                } else {
                    Pattern::Bind(crate::identity::Name::Spelled(
                        super::unraw(text).to_string(),
                    ))
                };
            }
            let name = self
                .all(path, Nt::Ident)
                .iter()
                .map(|id| self.text(*id).trim().to_owned())
                .collect::<Vec<_>>()
                .join(SEPARATOR);
            // `C<n: m>(…)`: the implicit arguments named, carried first as a
            // record the elaborator places by the generics' names.
            let implicits: Vec<Pattern> = self
                .first(path, Nt::PatternImplicits)
                .map(|list| {
                    let fields = self
                        .all(list, Nt::PatternImplicit)
                        .into_iter()
                        .filter_map(|i| {
                            let n = self.first(i, Nt::Ident)?;
                            let p = self.first(i, Nt::Pattern)?;
                            Some((
                                super::unraw(self.text(n).trim()).to_string(),
                                self.pattern(p),
                            ))
                        })
                        .collect();
                    vec![Pattern::Record {
                        name: crate::IMPLICITS.into(),
                        fields,
                    }]
                })
                .unwrap_or_default();
            let Some(args) = self.first(path, Nt::PatternArgs) else {
                return Pattern::Ctor {
                    name: crate::identity::Name::Spelled(name),
                    args: implicits,
                };
            };
            if let Some(list) = self.first(args, Nt::FieldPatterns) {
                let mut fields = Vec::new();
                let mut found = Vec::new();
                self.field_patterns(list, &mut found);
                for f in found {
                    let Some(field) = self.label_of(f) else {
                        continue;
                    };
                    let field = self.text(field).to_string();
                    let p = match self.first(f, Nt::Pattern) {
                        Some(p) => self.pattern(p),
                        None => Pattern::Bind(crate::identity::Name::Spelled(field.clone())),
                    };
                    fields.push((field, p));
                }
                return Pattern::Record {
                    name: crate::identity::Name::Spelled(name),
                    fields,
                };
            }
            let mut all = implicits;
            all.extend(
                self.all(args, Nt::Pattern)
                    .into_iter()
                    .map(|p| self.pattern(p)),
            );
            return Pattern::Ctor {
                name: crate::identity::Name::Spelled(name),
                args: all,
            };
        }
        // `#(a, b)`: a product's pattern; `#()` is the constructor `Star` of the
        // unit, written with the prelude's full name, so a file's own `Star` is
        // not meant.
        if let Some(tuple) = self.first(*alt, Nt::TuplePattern) {
            let items: Vec<Pattern> = self
                .all(tuple, Nt::Pattern)
                .into_iter()
                .map(|p| self.pattern(p))
                .collect();
            return match items.len() {
                0 => Pattern::Ctor {
                    name: crate::identity::Name::Spelled(prelude_name("Star")),
                    args: Vec::new(),
                },
                1 => Pattern::Other("one-element tuple".into()),
                _ => Pattern::Tuple(items),
            };
        }
        // `[x, ..rest]`: `Cons(x, rest)`, and `[]` is `Nil`, the patterns the
        // constructors make, as `[x, ..rest]` the term does.
        if let Some(list) = self.first(*alt, Nt::ListPattern) {
            let mut items: Vec<Pattern> = Vec::new();
            let mut tail = None;
            let mut next = self.first(list, Nt::ListPatternItems);
            while let Some(at) = next {
                next = None;
                for c in self.cst.children(at) {
                    match self.nt(c) {
                        Some(Nt::Pattern) => items.push(self.pattern(c)),
                        Some(Nt::ListPatternRest) => {
                            tail = self.first(c, Nt::Ident).map(|i| {
                                let text = self.text(i);
                                let text = text.trim();
                                if text == "_" {
                                    Pattern::Wild
                                } else {
                                    Pattern::Bind(crate::identity::Name::Spelled(
                                        super::unraw(text).to_string(),
                                    ))
                                }
                            });
                        }
                        Some(Nt::ListPatternItems) => next = Some(c),
                        _ => {}
                    }
                }
            }
            let nil = Pattern::Ctor {
                name: crate::identity::Name::Spelled("Nil".into()),
                args: Vec::new(),
            };
            return items
                .into_iter()
                .rev()
                .fold(tail.unwrap_or(nil), |rest, item| Pattern::Ctor {
                    name: crate::identity::Name::Spelled("Cons".into()),
                    args: vec![item, rest],
                });
        }
        let Some(lit) = self.first(*alt, Nt::LiteralPattern) else {
            return Pattern::Other("PatternAlt".into());
        };
        let text = self.text(lit);
        let text = text.trim();
        if self.first(lit, Nt::True).is_some() {
            Pattern::Bool(true)
        } else if self.first(lit, Nt::False).is_some() {
            Pattern::Bool(false)
        } else if self.first(lit, Nt::Text).is_some() {
            Pattern::Text(super::unquote_text(text))
        } else {
            match text.replace([' ', '_'], "").parse::<i64>() {
                Ok(n) => Pattern::Int(n),
                Err(_) => Pattern::Other("number pattern".into()),
            }
        }
    }

    pub(super) fn handle(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let Some(subject) = self.first(id, Nt::HandleSubject) else {
            return self.other(id);
        };
        let Some(body) = self.first(subject, Nt::Block) else {
            return self.other(id);
        };
        let mut handlers = Vec::new();
        let mut withs = Vec::new();
        // Only the tail: the body block can hold `handle`s of its own, whose
        // `with`s are not this one's.
        if let Some(tail) = self.first(subject, Nt::HandleTail) {
            self.descend(tail, Nt::HandleWith, &mut withs);
        }
        // Each `with` wraps the ones before it; the evaluator reads the list as
        // written, so the nesting is kept as nested `Handle` terms.
        let mut term = self.term(body);
        for with in withs {
            handlers.clear();
            let mut hs = Vec::new();
            self.descend(with, Nt::Handler, &mut hs);
            for h in hs {
                handlers.push(self.handler(h));
            }
            term = SurfaceTerm::new(
                TermKind::Handle {
                    body: Box::new(term),
                    handlers: std::mem::take(&mut handlers),
                },
                span,
            );
        }
        term
    }

    fn handler(&self, id: NodeId) -> Handler {
        let body = |s: &Self| {
            s.first(id, Nt::Expr)
                .map(|e| s.term(e))
                .unwrap_or_else(|| s.other(id))
        };
        if let Some(r) = self.first(id, Nt::ReturnHandler) {
            let pattern = self
                .first(r, Nt::Pattern)
                .map(|p| self.pattern(p))
                .unwrap_or(Pattern::Other("return".into()));
            let body = self
                .first(r, Nt::Expr)
                .map(|e| self.term(e))
                .unwrap_or_else(|| self.other(r));
            return Handler::Return { pattern, body };
        }
        let Some(op) = self.first(id, Nt::OperationHandler) else {
            return Handler::Return {
                pattern: Pattern::Wild,
                body: body(self),
            };
        };
        let effect = self
            .first(op, Nt::OperationName)
            .map(|n| self.name_of(n))
            .unwrap_or_default();
        let instance = Instance {
            forall: self
                .first(op, Nt::EffectForall)
                .map(|f| {
                    self.all(f, Nt::Ident)
                        .into_iter()
                        .map(|i| self.name_of(i).into())
                        .collect()
                })
                .unwrap_or_default(),
            args: self
                .first(op, Nt::OperationTypes)
                .map(|t| {
                    self.all(t, Nt::OperationType)
                        .into_iter()
                        .map(|a| self.term(a))
                        .collect()
                })
                .unwrap_or_default(),
        };
        let patterns = self
            .all(op, Nt::Pattern)
            .into_iter()
            .map(|p| self.pattern(p))
            .collect();
        // `, k` is the identifier after the closing parenthesis.
        let cont = self
            .cst
            .children(op)
            .into_iter()
            .rfind(|c| self.nt(*c) == Some(Nt::Ident))
            .map(|i| self.name_of(i));
        let guard = self.first(op, Nt::Cond).map(|g| self.term(g));
        let body = self
            .first(op, Nt::Expr)
            .map(|e| self.term(e))
            .unwrap_or_else(|| self.other(op));
        Handler::Operation {
            effect: crate::identity::Name::Spelled(effect),
            instance,
            patterns,
            cont: cont.map(Name::from),
            guard,
            body,
        }
    }
}

/// The variable under a field path `x.f.g` written before `:=`.
fn place_root(t: &SurfaceTerm) -> Option<Name> {
    match &*t.kind {
        TermKind::Var(name) => Some(name.clone()),
        TermKind::Field { base, .. } => place_root(base),
        _ => None,
    }
}

/// `stmt` with `vis` written before it. A statement that declares no name
/// another file could see (a `let`, an `import`, an `extern` block) takes
/// no `pub`: it is read as an error there.
/// What a `pub` before a statement that declares nothing is read as, after the word.
pub const NOT_A_DECLARATION: &str = "before a statement that declares nothing";

pub fn with_vis(mut stmt: Stmt, vis: Vis, span: Span) -> Stmt {
    match stmt.vis_mut() {
        Some(v) => {
            *v = vis;
            // The declaration starts at its `pub`, so that what is cut out of
            // the text with it takes the word along.
            let at = match &mut stmt {
                Stmt::Fn(f) => Some(&mut f.span),
                Stmt::Theorem(d) | Stmt::Def(d) => Some(&mut d.span),
                Stmt::Inductive(d) => Some(&mut d.span),
                Stmt::Struct(d) | Stmt::Enum(d) => Some(&mut d.span),
                Stmt::Effect(e) => Some(&mut e.span),
                Stmt::Class(c) => Some(&mut c.span),
                _ => None,
            };
            if let Some(at) = at
                && span.start < at.start
            {
                at.start = span.start;
            }
            stmt
        }
        None => Stmt::Other(format!("{}{NOT_A_DECLARATION}", vis.written()), span),
    }
}

impl Stmt {
    pub fn vis(&self) -> Option<Vis> {
        match self {
            Stmt::Fn(f) => Some(f.vis),
            Stmt::Theorem(d) | Stmt::Def(d) => Some(d.vis),
            Stmt::Inductive(d) => Some(d.vis),
            Stmt::Struct(d) | Stmt::Enum(d) => Some(d.vis),
            Stmt::Effect(e) => Some(e.vis),
            Stmt::Class(c) => Some(c.vis),
            Stmt::Attributed { stmt, .. } => stmt.vis(),
            _ => None,
        }
    }

    pub fn vis_mut(&mut self) -> Option<&mut Vis> {
        match self {
            Stmt::Fn(f) => Some(&mut f.vis),
            Stmt::Theorem(d) | Stmt::Def(d) => Some(&mut d.vis),
            Stmt::Inductive(d) => Some(&mut d.vis),
            Stmt::Struct(d) | Stmt::Enum(d) => Some(&mut d.vis),
            Stmt::Effect(e) => Some(&mut e.vis),
            Stmt::Class(c) => Some(&mut c.vis),
            Stmt::Attributed { stmt, .. } => stmt.vis_mut(),
            _ => None,
        }
    }
}

/// The full name of a declaration of the prelude (`std::prelude::Pair`).
fn prelude_name(n: &str) -> String {
    format!(
        "{}{}{n}",
        super::qualify::PRELUDE_MODULE,
        super::qualify::SEPARATOR
    )
}

/// What a text of the prelude reads as, with spans from 0, read once in a
/// process: the prelude's name tables each look at the same few texts.
pub(super) fn prelude_unresolved(source: &str) -> &'static Result<Program, String> {
    static READ: PreludeMemo = Mutex::new(None);
    prelude_memo(&READ, source, || parse_program_unresolved_at(source, 0))
}

/// [`prelude_unresolved`], with modules resolved as [`parse_program_as_written`] does.
pub(super) fn prelude_as_written(source: &str) -> &'static Result<Program, String> {
    static READ: PreludeMemo = Mutex::new(None);
    prelude_memo(&READ, source, || parse_program_as_written(source))
}

type PreludeMemo = Mutex<Option<HashMap<String, &'static Result<Program, String>>>>;

/// The lock is not held while reading: reading may ask a name table, which
/// asks for a text here.
fn prelude_memo(
    memo: &PreludeMemo,
    source: &str,
    read: impl FnOnce() -> Result<Program, String>,
) -> &'static Result<Program, String> {
    if let Some(found) = memo
        .lock()
        .unwrap()
        .as_ref()
        .and_then(|texts| texts.get(source))
    {
        return found;
    }
    let read: &'static _ = Box::leak(Box::new(read()));
    memo.lock()
        .unwrap()
        .get_or_insert_default()
        .entry(source.to_string())
        .or_insert(read)
}
