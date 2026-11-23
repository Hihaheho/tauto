//! Statements, patterns, handlers and the program: the executable parts of
//! the surface syntax, read from the same concrete syntax tree as types and
//! expressions (see the parent module).

use std::collections::HashMap;
use std::sync::Mutex;

use crate::span::Span;
use tauto_message::{Message, msg};

use super::qualify::SEPARATOR;
use super::{BudgetLimit, Name, SurfaceTerm, SyntaxLit, TermKind};

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
    Handle,
    Open,
}

impl Vis {
    /// The words written before the declaration, with a space after them.
    pub fn written(self) -> &'static str {
        match self {
            Vis::Private => "",
            Vis::Pub => "pub ",
            Vis::Handle => "pub(handle) ",
            Vis::Open => "pub(open) ",
        }
    }
}

/// A second spelling for a declaration in the same file.
#[derive(Debug, Clone, PartialEq)]
pub struct ExportAlias {
    pub name: String,
    pub target: String,
    pub effect: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// `let x: T = e`; the type is optional in programs and proofs. Proof
    /// annotations remain explicit type ascriptions in the substituted term.
    /// Whether `x` borrows is read from the value's type. `borrow` and
    /// `borrow_mut` are always false: there is no `let &x` to set them.
    Let {
        name: Name,
        ty: Option<SurfaceTerm>,
        value: SurfaceTerm,
        borrow: bool,
        borrow_mut: bool,
        /// The word in `let(stack) x := e`: `x` is placed in the frame's slot,
        /// with no allocation made for it. The checker rejects any other word.
        stack: Option<String>,
        /// Where `^` is written before the name: the binding is asserted unused.
        unused: Option<Span>,
    },
    /// `var it := iter(&v)` binds a view that is advanced with `&mut it`;
    /// it is one when the value's type holds a borrow.
    Var {
        name: Name,
        ty: Option<SurfaceTerm>,
        value: SurfaceTerm,
        borrow: bool,
        /// The word in `var(stack)`, which the checker rejects: only a `let`
        /// takes `stack`.
        stack: Option<String>,
        /// Where `^` is written before the name: the binding is asserted unused.
        unused: Option<Span>,
    },
    /// `x := v`, or `x.f.g := v`: writes the `var` binding `x`, or the field
    /// of `x` that `place` (the whole `x.f.g`) names. With `deref` (where
    /// the `*…` is written), `*x := v` or `*x.f := v`: writes where the
    /// `&mut` borrow `x`, or the one in the field, points.
    Assign {
        name: Name,
        place: Option<SurfaceTerm>,
        value: SurfaceTerm,
        deref: Option<Span>,
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
    /// `import "path"`, relative to the importing file, or `import std::list`
    /// (`module`), a module of the standard library or of a dependency.
    /// `names` is the list `{ List, map }` of what it brings, when written.
    Import {
        path: String,
        module: bool,
        names: Option<Vec<(String, Span)>>,
        span: Span,
    },
    Reexport {
        module: String,
        names: Vec<(String, Span)>,
        aliases: Option<Vec<ExportAlias>>,
        span: Span,
    },
    Inductive(InductiveDecl),
    /// `module M { … }`: `modules::resolve`
    /// flattens it, so the checkers never see one.
    Module {
        name: String,
        vis: Vis,
        items: Vec<Stmt>,
        span: Span,
    },
    Effect(EffectDecl),
    /// `struct Name(G: Type) { field: T, … }`, with its kind when written.
    Struct(DataDecl),
    /// `enum Name(G: Type) { C(T, …), D { f: T }, E }`, with its kind when written.
    Enum(DataDecl),
    /// `extern { … }`: host signatures, or a replaceable block with Tauto
    /// fallback bodies and `struct`/`enum`. The prelude's bodiless ones are
    /// the functions the evaluator and the backends implement themselves.
    Extern {
        fns: Vec<FnDecl>,
        instances: Vec<ExternInstance>,
        /// `type T`: opaque types the host provides. The reader puts a
        /// `Struct` with `host` set before the block for each.
        types: Vec<DataDecl>,
        /// `struct` / `enum` inside a replaceable extern: injected as ordinary
        /// data decls before the block, kept here for printing and for the
        /// representation boundary of the block.
        structs: Vec<DataDecl>,
        enums: Vec<DataDecl>,
        span: Span,
    },
    Class(ClassDecl),
    Instance(InstanceDecl),
    While {
        condition: SurfaceTerm,
        body: SurfaceTerm,
    },
    /// `for pat in e { … }`: a finite owned traversal. `lower_fors` expands it into
    /// `iterator_ready` and `fold_finite` (and rewrites its `break`/`continue`), so the
    /// checkers never see one.
    For {
        pattern: Pattern,
        source: SurfaceTerm,
        body: SurfaceTerm,
    },
    /// `loop { … }`: read as a block of this one statement, and written back as `loop`.
    /// `lower_loops` expands it (and `break` and `continue`) into a `while` and `var`s, so
    /// the checkers never see one.
    Loop {
        body: SurfaceTerm,
    },
    /// `break`; a value (`break e`) is read, and `lower_loops` refuses it when it is
    /// outside a `for` (after `lower_fors`) or `while`/`loop`.
    Break(Option<SurfaceTerm>),
    Continue,
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
        /// `pub macro fn`: other files may call it. Without `pub`, the macro is its file's own,
        /// as a function is.
        public: bool,
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
    pub parents: Vec<Constraint>,
    /// All class parameters, in dependency order.
    pub parameters: Vec<(Name, SurfaceTerm)>,
    /// Where `^` is written before each class parameter, aligned with
    /// `parameters`.
    pub unused_parameters: Vec<Option<Span>>,
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
    /// `inductive class`: also a class of the proof language, which the
    /// kernel checks. Any other class is a class of the program only.
    pub inductive: bool,
    pub span: Span,
}

impl ClassDecl {
    /// Whether the proof language can read the class: it has a parameter.
    /// The parameter may be a type constructor (`F: (Type) -> Type`).
    pub fn over_types(&self) -> bool {
        self.arity != 0
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
    /// Where `^` is written before each generic, aligned with `generics`.
    pub unused_generics: Vec<Option<Span>>,
    pub bounds: Vec<Option<GenericBound>>,
    pub class: Name,
    pub head: SurfaceTerm,
    pub infer_from: Option<InferCondition>,
    pub where_: Vec<Constraint>,
    pub methods: Vec<FnDecl>,
    pub laws: Vec<LawDecl>,
    pub span: Span,
}

/// Known class type arguments required to infer the remaining arguments.
#[derive(Debug, Clone, PartialEq)]
pub enum InferCondition {
    Parameter(Name),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct EffectDecl {
    pub name: Name,
    /// Identity and member visibility of an operation declared in a module.
    /// The file's visibility can be narrower than the member visibility.
    pub module_scope: Option<(super::TermId, Vis)>,
    /// `pub` or `pub(open)` as written before the declaration.
    pub vis: Vis,
    pub generics: Vec<Name>,
    /// A bound for each generic when written (`<A: Shared>`), aligned with
    /// `generics`; empty when the declaration came from somewhere that
    /// carries none.
    pub bounds: Vec<Option<GenericBound>>,
    /// Where `^` is written before each generic, aligned with `generics`.
    pub unused_generics: Vec<Option<Span>>,
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
    /// `effect Host {div, stdout}`: the effects the name stands for, as a
    /// row writes them; such a declaration has no operation of its own.
    /// `modules::resolve` writes the effects in its place in every row and
    /// drops the declaration, so the checkers never see one.
    pub set: Option<Vec<Name>>,
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
    /// Where `^` is written before each generic, aligned with `generics`.
    pub unused_generics: Vec<Option<Span>>,
    /// Where `^` is written before each field of a struct (`struct P { ^x: T }`),
    /// aligned with the fields of its one constructor; empty when none is.
    pub unused_fields: Vec<Option<Span>>,
    /// For each generic: whether it is declared a row variable, `!e`.
    pub rows: Vec<bool>,
    pub constructors: Vec<DataConstructor>,
    /// `extern { type Name }`: a type the host provides. Its one constructor
    /// has no fields, and only extern functions make its values.
    pub host: bool,
    /// The field written with `coerce` (a struct has at most one): the struct
    /// is read as that field's type where that type is expected.
    pub coerce: Option<DataCoerce>,
    /// `struct &T { … }`: the borrow of `T`, declared in `T`'s module.
    /// Its name is `T`'s.
    pub borrowed: bool,
    pub span: Span,
}

/// `coerce`, `coerce(mut)` or `coerce(owned)` before a struct's field.
#[derive(Debug, Clone, PartialEq)]
pub struct DataCoerce {
    /// The field's index in the struct's one constructor.
    pub field: usize,
    pub level: CoerceLevel,
}

/// What a `coerce` field lets the struct be read as; each level allows what
/// the one before it does.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CoerceLevel {
    /// `coerce`: `&W` as `&T`, and the fields of `T` read through `w.x`.
    Ref,
    /// `coerce(mut)`: also `&mut W` as `&mut T`, and `w.x := e`.
    Mut,
    /// `coerce(owned)`: also a `W` as a `T`.
    Owned,
}

impl CoerceLevel {
    /// The word as written: `coerce`, `coerce(mut)`, `coerce(owned)`.
    pub fn written(self) -> &'static str {
        match self {
            CoerceLevel::Ref => "coerce",
            CoerceLevel::Mut => "coerce(mut)",
            CoerceLevel::Owned => "coerce(owned)",
        }
    }
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

/// One effect or set name as written in a function's row, before expansion.
#[derive(Debug, Clone, PartialEq)]
pub struct WrittenRowEffect {
    pub name: Name,
    /// Where `^` is written before the name: asserted unused in this row.
    pub unused: Option<Span>,
    pub span: Span,
    /// When the name is an effect set, the members it expands to (filled when
    /// sets are written out). `None` means an atomic effect or a row variable.
    pub members: Option<Vec<Name>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub name: Name,
    /// Where `^` is written before the function name: asserted unused.
    pub unused: Option<Span>,
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
    /// Where `^` is written before each type parameter, aligned with
    /// `generics`.
    pub unused_generics: Vec<Option<Span>>,
    pub params: Vec<Name>,
    /// Where `^` is written before each parameter, aligned with `params`.
    pub unused_params: Vec<Option<Span>>,
    /// For each parameter: `None` takes the value, `Some(false)` a borrow
    /// (`&x`), `Some(true)` a mutable borrow (`&mut x`).
    pub borrows: Vec<Option<bool>>,
    /// The written parameter types, aligned with `params`.
    pub param_types: Vec<Option<SurfaceTerm>>,
    pub result: Option<SurfaceTerm>,
    /// `borrows(m, x.f)` after the result: the parameters (and their fields,
    /// dotted) the result may borrow from. `None` is every borrowed parameter.
    pub lends: Option<Vec<String>>,
    /// The row written after `!`, when there is one.
    pub effects: Option<Vec<Name>>,
    /// Members of the row as written, before set names expand. Used to warn on
    /// unused effects and to check `^` unused assertions on row members.
    /// Absent when the row was not written (`!?` or no row).
    pub written_effects: Option<Vec<WrittenRowEffect>>,
    /// `!?` after the result: the row is not written yet. `effects` is `None`, the row is the one
    /// the body performs, and the declaration is incomplete. Where `!?` is written.
    pub row_hole: Option<Span>,
    /// `where C(T), …`, in the order written.
    pub where_: Vec<Constraint>,
    pub span: Span,
    /// `opaque fn`: the kernel does not unfold the function; the equation
    /// `f::eq` it makes unfolds it once.
    pub opaque: bool,
    /// `ghost fn`: only proofs and types use the function. The kernel reads it as it reads a `fn`;
    /// extraction never writes it, and a program that runs it is refused.
    pub ghost: bool,
    /// `decreasing_by W`: the recursion is well-founded recursion on the
    /// first parameter, by the `WfRel` `W` (`std/well_founded.taut`).
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
    /// Where `^` is written before the declaration name: asserted unused.
    pub unused: Option<Span>,
    /// `pub` or `pub(open)` as written before the declaration.
    pub vis: Vis,
    /// How many leading `params` are generics.
    pub implicit: usize,
    pub params: Vec<(Name, SurfaceTerm)>,
    /// Where `^` is written before each parameter name, aligned with `params`.
    pub unused_params: Vec<Option<Span>>,
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
    /// A name that binds; `unused` is where `^` is written before it.
    Bind {
        name: Name,
        unused: Option<Span>,
    },
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
    /// `y: T =>`, only a `match` arm's whole pattern: on a union, the values whose head is
    /// one of the heads of `T`'s members, bound to `name` at `T`.
    /// `unused` is where `^` is written before the name.
    Typed {
        name: Name,
        ty: Box<SurfaceTerm>,
        unused: Option<Span>,
    },
    Other(String),
}

impl Pattern {
    /// A binding pattern with no unused marker.
    pub fn bind(name: impl Into<Name>) -> Self {
        Pattern::Bind {
            name: name.into(),
            unused: None,
        }
    }

    /// `#(p, q, r)`: the product's constructor `Pair::Mk` nested to the right,
    /// `Pair::Mk(p, Pair::Mk(q, r))`, as the value `#(a, b, c)` is. The reader writes the
    /// constructor by the library's own reference, which no program can spell.
    pub fn product(mut members: Vec<Pattern>) -> Pattern {
        let pair = |fst, snd| Pattern::Ctor {
            name: crate::bindings::pair_mk_reference().clone().into(),
            args: vec![fst, snd],
        };
        let last = members.pop().expect("a product has members");
        members
            .into_iter()
            .rev()
            .fold(last, |snd, fst| pair(fst, snd))
    }

    /// The two members of a product pattern `Pair::Mk(p, q)`.
    pub fn as_pair(&self) -> Option<(&Pattern, &Pattern)> {
        match self {
            Pattern::Ctor { name, args }
                if args.len() == 2 && crate::bindings::is_reader_reference(name, "Pair::Mk") =>
            {
                Some((&args[0], &args[1]))
            }
            _ => None,
        }
    }

    /// The members of a product pattern in order, the second's own where it is a product too;
    /// none when `self` is not a product.
    pub fn product_members(&self) -> Option<Vec<&Pattern>> {
        let (mut fst, mut snd) = self.as_pair()?;
        let mut out = Vec::new();
        loop {
            out.push(fst);
            match snd.as_pair() {
                Some((f, s)) => (fst, snd) = (f, s),
                None => {
                    out.push(snd);
                    return Some(out);
                }
            }
        }
    }

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

/// The names an alternative binds, sorted. A bare name at the top is a
/// constructor of the scrutinee, so it binds nothing here.
pub fn alt_binders(p: &Pattern) -> Vec<String> {
    fn go(p: &Pattern, top: bool, out: &mut Vec<String>) {
        match p {
            Pattern::Bind { name: n, .. } if !top => out.push(n.to_string()),
            Pattern::Ctor { args, .. } => args.iter().for_each(|a| go(a, false, out)),
            Pattern::Record { fields, .. } => fields.iter().for_each(|(_, a)| go(a, false, out)),
            Pattern::Typed { name, .. } => out.push(name.to_string()),
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(p, true, &mut out);
    out.sort();
    out
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
    /// Where `^` is written before each step binder, aligned with `binders`.
    pub unused_binders: Vec<Option<Span>>,
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
        /// Where `^` is written before the continuation name.
        cont_unused: Option<Span>,
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

/// The variable under a field path `x.f.g` written before `:=`.
pub fn place_root(t: &SurfaceTerm) -> Option<Name> {
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
    if vis == Vis::Handle && !matches!(&stmt, Stmt::Effect(effect) if effect.set.is_none())
        || vis == Vis::Open && matches!(&stmt, Stmt::Module { .. })
    {
        return Stmt::Other(format!("{}{NOT_A_DECLARATION}", vis.written()), span);
    }
    if vis == Vis::Pub
        && let Stmt::Import {
            path,
            module: true,
            names: Some(names),
            ..
        } = stmt
    {
        return Stmt::Reexport {
            module: path,
            names,
            aliases: None,
            span,
        };
    }
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
                Stmt::Module { span, .. } => Some(span),
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
            Stmt::Module { vis, .. } => Some(*vis),
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
            Stmt::Module { vis, .. } => Some(vis),
            Stmt::Class(c) => Some(&mut c.vis),
            Stmt::Attributed { stmt, .. } => stmt.vis_mut(),
            _ => None,
        }
    }
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

/// What reads the texts of the standard library that the name tables are
/// made from. This crate holds the syntax as data and reads no text itself;
/// the reader (`tauto_parse::install`) sets it before the first program is
/// read.
#[derive(Clone, Copy)]
pub struct TextReader {
    pub builtin_at: fn(&'static str, u32) -> Result<Program, String>,
    pub builtin_as_written_at: fn(&'static str, u32) -> Result<Program, String>,
    pub program_unresolved_at: fn(&str, u32) -> Result<Program, String>,
    pub expr_at: fn(&str, u32) -> Result<SurfaceTerm, String>,
    pub program_as_written: fn(&str) -> Result<Program, String>,
}

static TEXT_READER: std::sync::OnceLock<TextReader> = std::sync::OnceLock::new();

/// Sets what reads the standard library's texts, once for the process; a
/// later setting is ignored.
pub fn set_text_reader(reader: TextReader) {
    let _ = TEXT_READER.set(reader);
}

pub(crate) fn text_reader() -> &'static TextReader {
    TEXT_READER
        .get()
        .expect("the standard library is read before a reader is set: call tauto_parse::install")
}

/// A text of the standard library read as [`TextReader::builtin_at`] reads it.
pub fn parse_builtin_at(source: &'static str, base: u32) -> Result<Program, String> {
    (text_reader().builtin_at)(source, base)
}

/// [`parse_builtin_at`], with modules resolved.
pub fn parse_builtin_as_written_at(source: &'static str, base: u32) -> Result<Program, String> {
    (text_reader().builtin_as_written_at)(source, base)
}

/// A text read by the reader that is set, its names not yet resolved: what
/// a crate that knows no reader (the kernel, the checker) reads its own
/// texts with.
pub fn parse_program_unresolved_at(source: &str, base: u32) -> Result<Program, String> {
    (text_reader().program_unresolved_at)(source, base)
}

/// A text read by the reader that is set, with modules resolved.
pub fn parse_program_as_written(source: &str) -> Result<Program, String> {
    (text_reader().program_as_written)(source)
}

/// An expression read by the reader that is set.
pub fn parse_expr_at(source: &str, base: u32) -> Result<SurfaceTerm, String> {
    (text_reader().expr_at)(source, base)
}

/// What a text of the prelude reads as, with spans from 0, read once in a
/// process: the prelude's name tables each look at the same few texts.
pub(crate) fn prelude_unresolved(source: &'static str) -> &'static Result<Program, String> {
    static READ: PreludeMemo = Mutex::new(None);
    prelude_memo(&READ, source, || (text_reader().builtin_at)(source, 0))
}

/// [`prelude_unresolved`], with modules resolved as [`parse_program_as_written`] does.
pub(crate) fn prelude_as_written(source: &'static str) -> &'static Result<Program, String> {
    static READ: PreludeMemo = Mutex::new(None);
    prelude_memo(&READ, source, || {
        (text_reader().builtin_as_written_at)(source, 0)
    })
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

/// Whether an extern function has a Tauto fallback body (not a placeholder).
pub fn extern_fn_has_body(f: &FnDecl) -> bool {
    !matches!(&*f.body.kind, TermKind::Other(_))
}

/// Stable identity of one `extern` block for binding completeness: the
/// sorted member spellings joined by `\0`. Not a source location.
pub fn extern_block_id(
    fns: &[FnDecl],
    types: &[DataDecl],
    structs: &[DataDecl],
    enums: &[DataDecl],
) -> String {
    let mut names: Vec<String> = fns
        .iter()
        .map(|f| f.name.to_string())
        .chain(types.iter().map(|d| d.name.to_string()))
        .chain(structs.iter().map(|d| d.name.to_string()))
        .chain(enums.iter().map(|d| d.name.to_string()))
        .collect();
    names.sort();
    names.join("\0")
}

/// A replaceable extern holds only bodyful functions and `struct`/`enum`
/// (no opaque `type`, no bodiless `fn`, no host `instance`).
pub fn extern_is_replaceable(
    fns: &[FnDecl],
    instances: &[ExternInstance],
    types: &[DataDecl],
    structs: &[DataDecl],
    enums: &[DataDecl],
) -> bool {
    if !instances.is_empty() || !types.is_empty() {
        return false;
    }
    if !structs.is_empty() || !enums.is_empty() {
        return fns.iter().all(extern_fn_has_body);
    }
    !fns.is_empty() && fns.iter().all(extern_fn_has_body)
}
