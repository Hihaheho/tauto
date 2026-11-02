//! Sugar for programs in the proof language, read
//! before a declaration is checked. Each rewrite is syntactic and makes the
//! terms the kernel already takes; extraction reads the declaration as
//! written.
//!
//! * `false` and `true` are the constructors of the prelude's `Bool`, in
//!   terms and in patterns, as a numeral is `Zero` and `Succ`s.
//! * Once `std/Text.taut` has declared `inductive Text { Mk(bytes:
//!   List(Nat)) }`, a literal `"ab"` is `Text.Mk(Cons(Nat, 97, Cons(Nat, 98,
//!   Nil(Nat))))`: its UTF-8 bytes. The sugar writes `Cons(97, …)` and
//!   leaves the element type to elaboration, which fills it in from the
//!   first byte: the kernel gets the same term. A `Cons` with `Nat` written
//!   out is first tried as a call writing its generic out, which types the
//!   whole call again, and a literal of n bytes would be typed n times over.
//!   A `match` whose arms are `Text` literals and a last arm of the other
//!   values is the branches on `==` it stands for (`literal_chain`). So is a
//!   `match` on an `Int` whose arms are numerals, read where the type is known
//!   (`matching.rs`): a numeral pattern on a `Nat` is its constructors.
//! * Once `std/Float.taut` has declared `inductive Float { Mk(bits:
//!   U64) }`, a literal `1.5` is `Float::of_raw(4609434218613702656)`: the
//!   bits of the nearest `Float`, as Rust's `str::parse` reads it. A literal
//!   too large for a `Float` is left as it is, and the kernel rejects it.
//!   `-1.5` is the literal of the negative one.
//! * The operators on numbers and decisions are functions of the prelude
//!   and `std/Base.taut`, each read so once its function is declared: `a - b`
//!   is `Nat::sub(a, b)`, `a < b` is `Nat::lt(a, b)`, `a > b` is
//!   `Nat::lt(b, a)`, `a && b` is `Bool::and(a, b)`, and so on. (`==` and `!=`
//!   depend on the type of their operands and are read where it is known, in
//!   `matching.rs`. `+` and `*` are never read as functions: they stay the
//!   kernel's, which `Nat::add` and `Nat::mul` are defined as.)
//! * For a family with one constructor, `T { f: e, … }` is that
//!   constructor applied to the fields in their order, and so is the
//!   pattern `T { f: p, g }` (a field not named is `_`, a field named alone
//!   binds its name).
//! * A label `@a T` is the family `@label.a` applied to `T` (`label_family`): a type
//!   with one constructor `Mk(value: T)`, which the checker declares where a label is
//!   first written (`Kernel::declare_labels`). Its name has an `@`, so no program writes
//!   it, and no `=>` list names it. The pattern `@a p` is `@label.a.Mk(p)`; the value
//!   `@a e` is read where its type is known (`Kernel::elaborate_at`): `@label.a.Mk(e)`
//!   for a value, the family for a type.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};

use super::{Kernel, T};
use crate::surface::{MatchArm, Pattern, Stmt, TermKind};

/// Whether `name` is the constructor `Mk` of some type: `Mk`, `Text::Mk`, `std::Text::Text::Mk`.
fn is_mk(name: &str) -> bool {
    let short = tauto_surface::surface::qualify::short(name);
    short == "Mk" || short.ends_with("::Mk")
}

struct Sugar {
    /// Whether `#(…)` patterns stay products: extraction writes them back for
    /// Nib, where a product is not the `Pair` the kernel matches.
    keep_products: bool,
    /// `C::m` for the methods and laws of the classes (`check/classes.rs`):
    /// what `C::m(…)` is written as, a call of the projection.
    members: HashSet<String>,
    /// The constructor of `Text` a literal is made with, when `Text` is
    /// declared: `Text::Mk`, or its full name `std::Text::Text::Mk` when another
    /// file declares a `Text` constructor of that name too, so a literal still means std's.
    text: Option<String>,
    /// `Float::of_raw` (or its full name) beside the constructor of `Float`,
    /// when `Float` is declared.
    float: Option<String>,
    /// The functions of [`Sugar::OPERATORS`] that are declared: an operator
    /// is read as its function only when that function is.
    ops: HashSet<&'static str>,
    bools: bool,
    records: Records,
    /// The labels met, when `@a T` is read as its family; `None` (extraction) leaves
    /// `@a T` as it is written.
    labels: Option<RefCell<BTreeSet<String>>>,
}

/// The family a label `@a T` is `@label.a(T)` of.
pub(super) fn label_family(tag: &str) -> String {
    format!("@label.{tag}")
}

/// The label `a` of the family `@label.a`. A name inside the family, such as its
/// constructor `@label.a::Mk`, is not the family: `@label.a::Mk(e)` is the value
/// already wrapped, and reading it as `@a e` again would wrap it without end.
pub(super) fn label_of(family: &str) -> Option<&str> {
    family
        .strip_prefix("@label.")
        .filter(|label| !label.is_empty() && !label.contains("::"))
}

/// For each family with one constructor: that constructor and the names of
/// its fields (after its implicit arguments).
pub type Records = HashMap<String, (String, Vec<String>)>;

impl Kernel {
    pub(super) fn program_sugar(&self, stmt: &Stmt) -> Stmt {
        self.program_sugar_labels(stmt).0
    }

    pub(super) fn program_sugar_labels(&self, stmt: &Stmt) -> (Stmt, BTreeSet<String>) {
        let text = self
            .inds
            .get("Text")
            .and_then(|i| match i.ctors.as_slice() {
                [c] if is_mk(&c.name) => Some(c.name.clone()),
                _ => None,
            });
        let float = self
            .inds
            .iter()
            .find(|(n, _)| tauto_surface::surface::qualify::short(n) == "Float")
            .and_then(|(_, i)| match i.ctors.as_slice() {
                [c] if is_mk(&c.name) => {
                    // `Float::of_raw`, in the module of the type whose
                    // constructor is `Float::Mk`.
                    let family = c.name.strip_suffix("::Mk")?;
                    [family, tauto_surface::surface::qualify::short(family)]
                        .into_iter()
                        .map(|t| format!("{t}::of_raw"))
                        .find(|f| self.globals.contains_key(f.as_str()))
                }
                _ => None,
            });
        // An operator is sugar for a function the program has: `Nat::lt` and
        // `Bool::and` are the prelude's, `Nat::le` and `Bool::or` are std's.
        let ops = if self.inds.contains_key("Bool") {
            Sugar::OPERATORS
                .iter()
                .map(|(_, f, _)| *f)
                .filter(|f| self.globals.contains_key(*f))
                .collect()
        } else {
            HashSet::new()
        };
        let sugar = Sugar {
            keep_products: false,
            members: self.classes.members().clone(),
            text,
            float,
            ops,
            bools: true,
            records: self.records(),
            labels: Some(RefCell::new(BTreeSet::new())),
        };
        let stmt = sugar.stmt(stmt);
        let labels = sugar.labels.map(|l| l.into_inner()).unwrap_or_default();
        (stmt, labels)
    }

    /// The family of each label in `labels` not declared yet (`label_family`):
    /// `inductive @label.a(T: Type): Type { Mk(value: T): @label.a(T) }`, checked as a
    /// written `inductive` is. A label is a type of its own (`@a Nat` and `@b Nat` differ),
    /// and the kernel takes it as any one-constructor family.
    pub(super) fn declare_labels(
        &mut self,
        labels: &BTreeSet<String>,
    ) -> Result<(), super::Diagnostic> {
        use crate::surface::{Constructor, Generates, InductiveDecl, SurfaceTerm, Vis};
        for tag in labels {
            let family = label_family(tag);
            if self.inds.contains_key(&family) {
                continue;
            }
            let sp = tauto_parol::Span::default();
            let param = SurfaceTerm::var("T", sp);
            let decl = InductiveDecl {
                name: family.clone(),
                vis: Vis::Open,
                params: vec![("T".into(), SurfaceTerm::var("Type", sp))],
                sort: SurfaceTerm::var("Type", sp),
                constructors: vec![Constructor {
                    name: format!("{family}::Mk"),
                    implicit: 0,
                    params: vec![("value".into(), param.clone())],
                    result: app(&family, vec![param.clone()], &param),
                }],
                generates: Generates::default(),
                span: sp,
            };
            if let super::Verdict::Failed(d) = self.inductive(&decl) {
                return Err(d);
            }
        }
        Ok(())
    }

    pub(super) fn records(&self) -> Records {
        let mut records = HashMap::new();
        for (name, ind) in &self.inds {
            if let [c] = ind.ctors.as_slice()
                && ind.alias.is_none()
            {
                let fields = c.fields[c.implicit..].to_vec();
                records.insert(name.clone(), (c.name.clone(), fields));
            }
        }
        records
    }
}

/// `stmt` with only its records read: what extraction does, since Nib
/// has the literals and operators itself.
pub fn record_sugar(records: &Records, stmt: &Stmt) -> Stmt {
    Sugar {
        keep_products: true,
        members: HashSet::new(),
        text: None,
        float: None,
        ops: HashSet::new(),
        bools: false,
        records: records.clone(),
        labels: None,
    }
    .stmt(stmt)
}

impl Sugar {
    fn stmt(&self, stmt: &Stmt) -> Stmt {
        match stmt {
            Stmt::Fn(f) => {
                let mut f = f.clone();
                f.param_types = f
                    .param_types
                    .iter()
                    .map(|t| t.as_ref().map(|t| self.ty(t)))
                    .collect();
                f.result = f.result.as_ref().map(|t| self.ty(t));
                f.body = self.term(&f.body);
                Stmt::Fn(f)
            }
            // An instance's methods are functions: extraction reads their
            // bodies as it reads a function's.
            Stmt::Instance(i) => {
                let mut i = i.clone();
                for m in &mut i.methods {
                    if let Stmt::Fn(f) = self.stmt(&Stmt::Fn(m.clone())) {
                        *m = f;
                    }
                }
                Stmt::Instance(i)
            }
            Stmt::Theorem(t) | Stmt::Def(t) => {
                let mut t2 = t.clone();
                t2.params = t
                    .params
                    .iter()
                    .map(|(n, d)| (n.clone(), self.ty(d)))
                    .collect();
                t2.ty = self.ty(&t.ty);
                t2.body = t.body.as_ref().map(|b| self.term(b));
                match stmt {
                    Stmt::Theorem(_) => Stmt::Theorem(t2),
                    _ => Stmt::Def(t2),
                }
            }
            Stmt::Let {
                name,
                ty,
                value,
                borrow,
                borrow_mut,
            } => Stmt::Let {
                name: name.clone(),
                ty: ty.as_ref().map(|t| self.term(t)),
                value: self.term(value),
                borrow: *borrow,
                borrow_mut: *borrow_mut,
            },
            Stmt::Var {
                name,
                ty,
                value,
                borrow,
            } => Stmt::Var {
                name: name.clone(),
                ty: ty.as_ref().map(|t| self.term(t)),
                value: self.term(value),
                borrow: *borrow,
            },
            Stmt::Assign { name, place, value } => Stmt::Assign {
                name: name.clone(),
                place: place.as_ref().map(|p| self.term(p)),
                value: self.term(value),
            },
            Stmt::Expr(e) => Stmt::Expr(self.term(e)),
            Stmt::Inductive(i) => {
                let mut i = i.clone();
                for (_, t) in &mut i.params {
                    *t = self.term(t);
                }
                i.sort = self.term(&i.sort);
                for c in &mut i.constructors {
                    for (_, t) in &mut c.params {
                        *t = self.term(t);
                    }
                    c.result = self.term(&c.result);
                }
                Stmt::Inductive(i)
            }
            Stmt::Mutual { items, span } => Stmt::Mutual {
                items: items.iter().map(|s| self.stmt(s)).collect(),
                span: *span,
            },
            other => other.clone(),
        }
    }

    fn literal(&self, ctor: &str, s: &str, t: &T) -> T {
        let sp = t.span;
        let mut list = app("Nil", vec![T::var("Nat", sp)], t);
        for b in s.bytes().rev() {
            list = app(
                "Cons",
                vec![T::new(TermKind::Nat(b.to_string()), sp), list],
                t,
            );
        }
        app(ctor, vec![list], t)
    }

    /// Each operator, the function it is, and whether its operands are swapped.
    const OPERATORS: [(&'static str, &'static str, bool); 7] = [
        ("-", "Nat::sub", false),
        ("<", "Nat::lt", false),
        ("<=", "Nat::le", false),
        (">", "Nat::lt", true),
        (">=", "Nat::le", true),
        ("&&", "Bool::and", false),
        ("||", "Bool::or", false),
    ];

    /// The function a binary operator is, with its operands swapped or not,
    /// when that function is declared.
    fn operator(&self, op: &str) -> Option<(&'static str, bool)> {
        Self::OPERATORS
            .iter()
            .find(|(o, f, _)| *o == op && self.ops.contains(f))
            .map(|&(_, f, swap)| (f, swap))
    }

    /// `t` in the place of a type. The unit type is written `Unit`; `#()` is only the value
    /// and the pattern, so in the place of a type it reads as the name `#()`, which nothing
    /// defines, and the diagnostic points to `Unit`.
    fn ty(&self, t: &T) -> T {
        match &*t.kind {
            TermKind::App {
                function,
                arguments,
            } if arguments.is_empty()
                && matches!(&*function.kind, TermKind::Var(f) if f == "Tuple") =>
            {
                T::var("#()", t.span)
            }
            _ => self.term(t),
        }
    }

    fn term(&self, t: &T) -> T {
        let sp = t.span;
        let kind = match &*t.kind {
            TermKind::Text(s) if let Some(ctor) = &self.text => return self.literal(ctor, s, t),
            TermKind::Bool(b) if self.bools => TermKind::Var(b.to_string()),
            // `#(a, b)` is the product `prod_mk(a, b)` where it is elaborated, never a `Pair`
            // written by its name; extraction keeps the product.
            TermKind::Tuple(_) if self.bools => {
                return self.term(&crate::surface::qualify::tuple_as_products(t));
            }
            // `#()` where a value stands is `Star`; in the place of a type, `ty` rejects it.
            TermKind::App {
                function,
                arguments,
            } if self.bools
                && arguments.is_empty()
                && matches!(&*function.kind, TermKind::Var(f) if f == "Tuple") =>
            {
                TermKind::Var("Star".into())
            }
            TermKind::Float(s)
                if let Some(f) = &self.float
                    && let Some(x) = s.parse::<f64>().ok().filter(|x| x.is_finite()) =>
            {
                return app(
                    f,
                    vec![T::new(TermKind::Nat(x.to_bits().to_string()), sp)],
                    t,
                );
            }
            // `-1.5` is the literal of a negative `Float`.
            TermKind::App {
                function,
                arguments,
            } if self.float.is_some()
                && matches!(&*function.kind, TermKind::Var(op) if op == "-")
                && let [x] = arguments.as_slice()
                && let TermKind::Float(s) = &*x.kind =>
            {
                return self.term(&T::new(TermKind::Float(format!("-{s}")), sp));
            }
            TermKind::App {
                function,
                arguments,
            } => {
                let mut arguments: Vec<T> = arguments.iter().map(|a| self.term(a)).collect();
                if arguments.len() == 2
                    && let TermKind::Var(op) = &*function.kind
                    && let Some((f, swap)) = self.operator(op)
                {
                    if swap {
                        arguments.reverse();
                    }
                    return app(f, arguments, t);
                }
                TermKind::App {
                    function: Box::new(self.term(function)),
                    arguments,
                }
            }
            // `A × B × C` is `Prod(A, Prod(B, C))`, the type `#(a, b, c)` makes, which the
            // kernel unfolds to `Pair(A, Pair(B, C))`. The members
            // stand in the order they are written: `A × B` and `B × A` are two types. The names are read after the program's names are
            // told apart: `Pair` and `Unit` are then the prelude's, as a file's own
            // declaration of either has its full name.
            // A member that is itself a product gives its members, and a member `Unit` gives
            // none: `(A × B) × C` is `A × B × C`, `A × Unit` is `A`, and a product left with
            // no member is `Unit`.
            TermKind::Product(items) => {
                let mut items = crate::surface::qualify::product_type_members(items);
                if items.len() < 2 {
                    return match items.pop() {
                        Some(one) => self.ty(&one),
                        None => T::var("Unit", sp),
                    };
                }
                let mut items: Vec<T> = items.iter().map(|i| self.ty(i)).collect();
                let last = items.pop().expect("two or more");
                return items.into_iter().rev().fold(last, |snd, fst| {
                    let cell = T::new(TermKind::Var("Prod".into()), fst.span);
                    T::new(
                        TermKind::App {
                            function: Box::new(cell),
                            arguments: vec![fst, snd],
                        },
                        sp,
                    )
                });
            }
            // `@a e` is `@label.a(e)`. What it holds is read as a term: whether it is the type
            // `@a T` or the value `@a e` is told by its type, when it is elaborated
            // (`matching.rs`), so `@a #()` is the unit labelled.
            // Labels are a set: a chain `@b @a e` stands in the order of its labels, the
            // same as `@a @b e`, so the two are one type and one value.
            TermKind::Tagged { .. } if let Some(labels) = &self.labels => {
                let mut tags = Vec::new();
                let mut inner = t;
                while let TermKind::Tagged { tag, term } = &*inner.kind {
                    tags.push(tag.clone());
                    inner = term;
                }
                tags.sort();
                tags.dedup();
                let mut out = self.term(inner);
                for tag in tags.iter().rev() {
                    labels.borrow_mut().insert(tag.clone());
                    out = app(&label_family(tag), vec![out], t);
                }
                return out;
            }
            // `#(@b y, @a x)` and `#(#(a, b), c)` are put in the order of their type's members
            // where the tuple is read (`tuple_as_pairs`); a `Pair { fst, snd }` written by its
            // name is the inductive `Pair` and stands as it is written.
            TermKind::Record { name, fields, .. } => match self.records.get(name) {
                Some((ctor, names)) => {
                    let mut args = Vec::new();
                    for n in names {
                        match fields.iter().find(|(f, _)| f == n) {
                            Some((_, e)) => args.push(self.term(e)),
                            // A missing field is left for the kernel to
                            // report: an unbound name.
                            None => args.push(T::var(&format!("{name}::{n}"), sp)),
                        }
                    }
                    return app(ctor, args, t);
                }
                None => (*t.kind).clone(),
            },
            TermKind::Field { base, name } if matches!(&*base.kind, TermKind::Var(c) if self.members.contains(&format!("{c}::{name}"))) =>
            {
                let TermKind::Var(c) = &*base.kind else {
                    unreachable!()
                };
                TermKind::Var(format!("{c}::{name}"))
            }
            TermKind::Field { base, name } => TermKind::Field {
                base: Box::new(self.term(base)),
                name: name.clone(),
            },
            TermKind::Ascribe { term, ty } => TermKind::Ascribe {
                term: Box::new(self.term(term)),
                ty: Box::new(self.ty(ty)),
            },
            TermKind::Pi {
                params,
                result,
                effects,
            } => TermKind::Pi {
                params: params
                    .iter()
                    .map(|(n, d)| (n.clone(), self.ty(d)))
                    .collect(),
                result: Box::new(self.ty(result)),
                effects: effects.clone(),
            },
            TermKind::Exists {
                binder,
                domain,
                body,
            } => TermKind::Exists {
                binder: binder.clone(),
                domain: Box::new(self.term(domain)),
                body: Box::new(self.term(body)),
            },
            TermKind::Lam {
                params,
                body,
                types,
            } => TermKind::Lam {
                params: params.clone(),
                body: Box::new(self.term(body)),
                types: types
                    .iter()
                    .map(|ty| ty.as_ref().map(|ty| self.term(ty)))
                    .collect(),
            },
            // `p if g => e`: the arm of `p` is `match g { true => e false => … }`, where `…` is the
            // `match` of the arms after it (`guard_chain`).
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } if arms.iter().any(|a| a.guard.is_some()) => {
                let chain = guard_chain(scrutinee, result.as_deref(), binder.as_deref(), arms, sp);
                return self.term(&chain);
            }
            TermKind::Match {
                scrutinee,
                result,
                binder: None,
                arms,
            } if self.text.is_some()
                && let Some(chain) =
                    literal_chain(scrutinee, result.as_deref(), arms, Literal::Text, sp) =>
            {
                return self.term(&chain);
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } => TermKind::Match {
                binder: binder.clone(),
                scrutinee: Box::new(self.term(scrutinee)),
                result: result.as_ref().map(|r| Box::new(self.term(r))),
                arms: arms
                    .iter()
                    .map(|a| MatchArm {
                        goal: a.goal.as_ref().map(|g| self.term(g)),
                        pattern: self.pattern(&a.pattern),
                        guard: a.guard.as_ref().map(|g| self.term(g)),
                        body: self.term(&a.body),
                    })
                    .collect(),
            },
            TermKind::Block(stmts) => TermKind::Block(stmts.iter().map(|s| self.stmt(s)).collect()),
            // Read by extraction, which sees an `if` and a `&mut` as written.
            TermKind::If {
                condition,
                then,
                otherwise,
            } => TermKind::If {
                condition: Box::new(self.term(condition)),
                then: Box::new(self.term(then)),
                otherwise: otherwise.as_ref().map(|o| Box::new(self.term(o))),
            },
            TermKind::Borrow { mutable, term } => TermKind::Borrow {
                mutable: *mutable,
                term: Box::new(self.term(term)),
            },
            other => other.clone(),
        };
        T::new(kind, sp)
    }

    fn pattern(&self, p: &Pattern) -> Pattern {
        // `#(p, q)` is the prelude's `Pair { fst: p, snd: q }`, as the value is.
        if let Pattern::Tuple(items) = p
            && self.keep_products
        {
            return Pattern::Tuple(items.iter().map(|q| self.pattern(q)).collect());
        }
        if let Pattern::Tuple(_) = p {
            let pair = if self.records.contains_key("Pair") {
                "Pair".to_string()
            } else {
                format!(
                    "{}{}Pair",
                    crate::surface::qualify::PRELUDE_MODULE,
                    crate::surface::qualify::SEPARATOR
                )
            };
            return self.pattern(&crate::surface::qualify::tuple_pattern_as_pairs(p, &pair));
        }
        // `#(p, #())` is `p`, as the value is.
        if let Some(flat) = crate::surface::qualify::flatten_pair_pattern(p) {
            return self.pattern(&flat);
        }
        match p {
            // `#(a, b)` names the prelude's `Pair` by its full name; the
            // kernel declares it by its short one, whether or not the file
            // imports anything of the library.
            Pattern::Record { name, fields } => match self.records.get(name).or_else(|| {
                let short = name
                    .strip_prefix(crate::surface::qualify::PRELUDE_MODULE)?
                    .strip_prefix(crate::surface::qualify::SEPARATOR)?;
                self.records.get(short)
            }) {
                Some((ctor, names)) => Pattern::Ctor {
                    name: ctor.clone(),
                    args: names
                        .iter()
                        .map(|n| match fields.iter().find(|(f, _)| f == n) {
                            Some((_, q)) => self.pattern(q),
                            None => Pattern::Wild,
                        })
                        .collect(),
                },
                // `C<n: m>(…)`'s implicit arguments, which `full_fields` places.
                None => Pattern::Record {
                    name: name.clone(),
                    fields: fields
                        .iter()
                        .map(|(f, q)| (f.clone(), self.pattern(q)))
                        .collect(),
                },
            },
            // `@a p` is `@label.a.Mk(p)`: `p` on the value the label wraps.
            // A chain of labels `@b @a p` stands in the order of its labels, as the type does.
            Pattern::Ctor { .. }
                if p.label().is_some()
                    && let Some(labels) = &self.labels =>
            {
                let mut tags = Vec::new();
                let mut inner = p;
                while let Some((tag, q)) = inner.label() {
                    tags.push(tag.to_string());
                    inner = q;
                }
                tags.sort();
                tags.dedup();
                let mut out = self.pattern(inner);
                for tag in tags.iter().rev() {
                    labels.borrow_mut().insert(tag.clone());
                    out = Pattern::Ctor {
                        name: format!("{}::Mk", label_family(tag)),
                        args: vec![out],
                    };
                }
                out
            }
            Pattern::Ctor { name, args } => Pattern::Ctor {
                name: name.clone(),
                args: args.iter().map(|a| self.pattern(a)).collect(),
            },
            Pattern::Bool(b) if self.bools => Pattern::Bind(b.to_string()),
            other => other.clone(),
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
pub(super) enum Literal {
    Text,
    Int,
}

/// `match e: G { "a" => x  "b" => y  other => z }` as the branches on `==` it
/// stands for: `match e == "a": G { true => x  false => match e == "b": G { true => y
/// false => { let other := e  z } } }`. Each arm but the last is a literal of the
/// kind given (`Text`, or a numeral of an `Int`, `-3` among them), and the last is the
/// arm of the other values, named (or `_`); any other `match` is left as written.
pub(super) fn literal_chain(
    scrutinee: &T,
    result: Option<&T>,
    arms: &[MatchArm],
    kind: Literal,
    sp: tauto_parol::Span,
) -> Option<T> {
    let (last, literals) = arms.split_last()?;
    if literals.is_empty()
        || arms.iter().any(|a| a.guard.is_some() || a.goal.is_some())
        || !literals.iter().all(|a| {
            matches!(
                (&a.pattern, kind),
                (Pattern::Text(_), Literal::Text) | (Pattern::Int(_), Literal::Int)
            )
        })
    {
        return None;
    }
    let mut chain = match &last.pattern {
        Pattern::Wild => last.body.clone(),
        Pattern::Bind(other) => T::new(
            TermKind::Block(vec![
                Stmt::Let {
                    name: other.clone(),
                    ty: None,
                    value: scrutinee.clone(),
                    borrow: false,
                    borrow_mut: false,
                },
                Stmt::Expr(last.body.clone()),
            ]),
            last.body.span,
        ),
        _ => return None,
    };
    let arm = |name: &str, body: T| MatchArm {
        goal: None,
        pattern: Pattern::Bind(name.into()),
        guard: None,
        body,
    };
    for a in literals.iter().rev() {
        let at = a.body.span;
        let literal = match &a.pattern {
            Pattern::Text(text) => T::new(TermKind::Text(text.clone()), at),
            Pattern::Int(n) => {
                let numeral = T::new(TermKind::Nat(n.unsigned_abs().to_string()), at);
                if *n < 0 {
                    app("-", vec![numeral], scrutinee)
                } else {
                    numeral
                }
            }
            _ => unreachable!(),
        };
        let test = app("==", vec![scrutinee.clone(), literal], scrutinee);
        chain = T::new(
            TermKind::Match {
                scrutinee: Box::new(test),
                result: result.map(|r| Box::new(r.clone())),
                binder: None,
                arms: vec![arm("true", a.body.clone()), arm("false", chain)],
            },
            sp,
        );
    }
    Some(chain)
}

/// A `match` with guards as the `match`es it stands for. The first arm with a guard,
/// `p if g => e`, becomes `p => match g { true => e false => match s { rest } }`, `rest` being the arms
/// after it; the arms after it stay too, but for those `p` takes every value of (all of them
/// when `p` is a name or `_`, those of its constructor when its fields are names or `_`).
/// `rest` is read again in the same way, so each guard is one `match` on a `Bool`.
pub fn guard_chain(
    scrutinee: &T,
    result: Option<&T>,
    binder: Option<&str>,
    arms: &[MatchArm],
    sp: tauto_parol::Span,
) -> T {
    let Some(at) = arms.iter().position(|a| a.guard.is_some()) else {
        return T::new(
            TermKind::Match {
                scrutinee: Box::new(scrutinee.clone()),
                result: result.map(|r| Box::new(r.clone())),
                binder: binder.map(str::to_string),
                arms: arms.to_vec(),
            },
            sp,
        );
    };
    let guarded = &arms[at];
    let rest = &arms[at + 1..];
    let otherwise = guard_chain(scrutinee, result, None, rest, sp);
    let branch = |name: &str, body: T| MatchArm {
        goal: None,
        pattern: Pattern::Bind(name.into()),
        guard: None,
        body,
    };
    let body = T::new(
        TermKind::Match {
            scrutinee: Box::new(guarded.guard.clone().expect("a guard")),
            result: result.map(|r| Box::new(r.clone())),
            binder: None,
            arms: vec![
                branch("true", guarded.body.clone()),
                branch("false", otherwise),
            ],
        },
        guarded.body.span,
    );
    let mut out: Vec<MatchArm> = arms[..at].to_vec();
    out.push(MatchArm {
        pattern: guarded.pattern.clone(),
        guard: None,
        goal: guarded.goal.clone(),
        body,
    });
    let simple = |p: &Pattern| matches!(p, Pattern::Wild | Pattern::Bind(_));
    for arm in rest {
        let taken = match (&guarded.pattern, &arm.pattern) {
            (Pattern::Wild | Pattern::Bind(_), _) => true,
            (Pattern::Ctor { name, args }, Pattern::Ctor { name: other, .. }) => {
                name == other && args.iter().all(simple)
            }
            _ => false,
        };
        if !taken {
            out.push(arm.clone());
        }
    }
    guard_chain(scrutinee, result, binder, &out, sp)
}

fn app(f: &str, args: Vec<T>, at: &T) -> T {
    T::new(
        TermKind::App {
            function: Box::new(T::var(f, at.span)),
            arguments: args,
        },
        at.span,
    )
}

#[cfg(test)]
mod tests {
    use super::label_of;

    #[test]
    fn label_of_accepts_only_label_families() {
        assert_eq!(label_of("@label.a"), Some("a"));
        for name in ["@label.a::Mk", "@label.a::ind", "@label.", "@other.a"] {
            assert_eq!(label_of(name), None, "{name}");
        }
    }
}
