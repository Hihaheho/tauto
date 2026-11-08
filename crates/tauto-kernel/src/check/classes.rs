//! Classes in the proof language, read before a
//! declaration is checked. A class is a record the kernel already has, and
//! nothing here is a new rule:
//!
//! * `class C(A: Type) { fn m(…): R  theorem l<g>(…): P }` is `inductive C(A: Type)`
//!   with one constructor `C::Mk` whose fields are the methods. Its laws form
//!   a separate record `C::laws(A, methods)` and may mention those methods.
//!   A method projection takes the methods record; a law projection takes
//!   its own generics, the methods record and the laws record.
//! * `instance<G> C(H(G)) where D(G) { … }` is the function `C::inst@H` from
//!   the records of its `where` to the record of `C(H(G))`; each method is a
//!   function `C::m@H` and each law a theorem `C::l@H`, so that a recursive
//!   method is an ordinary structural recursion. A law the instance does not
//!   prove leaves a hole in its laws record; the methods record remains usable.
//! * `where C(T)` is a parameter `inst@C0: C(T)` after the generics. Proofs
//!   that use its laws also take `inst@C0@laws: C::laws(T, inst@C0)`.
//!
//! Which record a call needs is found in `implicit.rs`, which writes it out;
//! the kernel and the independent core see only the terms.

use crate::surface::Name;
use std::collections::{HashMap, HashSet};

use tauto_message::{Message, msg};
use tauto_parol::Span;

use super::{Diagnostic, Entry, Kernel, T, Verdict, pi};
use crate::surface::{
    ClassDecl, Constraint, Constructor, DICT, FnDecl, InductiveDecl, InstanceDecl, MatchArm,
    Pattern, Stmt, TermKind, TheoremDecl, dictionary_name,
};

pub(super) fn is_dict(name: &Name) -> bool {
    name.starts_with(DICT)
}

#[derive(Default, Clone)]
pub(super) struct Registry {
    classes: HashMap<Name, Class>,
    constructor_shapes: HashMap<Name, (usize, usize)>,
    pub(super) law_owners: HashMap<Name, Name>,
    pub(super) law_records: HashMap<Name, Name>,
    pub(super) member_owners: HashMap<Name, Name>,
    pub(super) member_labels: HashMap<Name, String>,
    pub(super) direct_members: HashMap<(Name, Name), Name>,
    pub(super) direct_origins: HashMap<Name, (Name, Name)>,
    /// `C::m` for every method and law of a class: the names a program may
    /// write as `C::m(…)`.
    members: HashSet<Name>,
    methods: HashSet<Name>,
    /// For each law `C::l`, how many generics it has of its own.
    laws: HashMap<Name, usize>,
    /// Where each law an instance proves is written, and what is wrong if
    /// the record of the laws does not take it.
    law_spans: Vec<(Span, Message)>,
    pub(super) instances: HashMap<(Name, Name), Instance>,
    /// An instance's function, by name: the class and the head it is for.
    pub(super) globals: HashMap<Name, (Name, Name)>,
}

fn member_name(class: &Name, descriptor: &Class, label: &str) -> Name {
    let (index, law) = if let Some(index) = descriptor.methods.iter().position(|m| m.name == label)
    {
        (index, false)
    } else {
        (
            descriptor
                .laws
                .iter()
                .position(|l| l.name == label)
                .expect("declared class member"),
            true,
        )
    };
    match class.as_global() {
        Some(owner) => owner.class_member(index, law, label).into(),
        None => format!("{class}::{label}").into(),
    }
}

fn laws_name(class: &Name) -> Name {
    match class.as_global() {
        Some(owner) => owner
            .generated(tauto_surface::identity::Generation::ClassLaws)
            .into(),
        None => format!("{class}::laws").into(),
    }
}

fn instance_name(member: &Name, head: &Name) -> Name {
    match (member.as_global(), head.as_global()) {
        (Some(member), Some(head)) => member
            .specialize(&format!("head:{:?}", head.id()), format!("{member}@{head}"))
            .into(),
        _ => format!("{member}@{head}").into(),
    }
}

fn constructor_name(family: &Name) -> Name {
    match family.as_global() {
        Some(owner) => owner.constructor(0, "Mk").into(),
        None => format!("{family}::Mk").into(),
    }
}

impl Registry {
    pub(super) fn resolve(&mut self, resolver: &mut tauto_surface::resolve::Resolver) {
        self.constructor_shapes = self
            .constructor_shapes
            .drain()
            .map(|(n, shape)| (resolver.global(&n), shape))
            .collect();
        for (class, descriptor) in &self.classes {
            let class_ref = resolver.global(class);
            for label in descriptor
                .methods
                .iter()
                .map(|m| &m.name)
                .chain(descriptor.laws.iter().map(|l| &l.name))
            {
                let member = resolver.global(&member_name(&class_ref, descriptor, label));
                self.member_owners.insert(member.clone(), class_ref.clone());
                self.member_labels.insert(member.clone(), label.to_string());
                for ((owner, head), instance) in &self.instances {
                    if owner != class {
                        continue;
                    }
                    if descriptor.laws.iter().any(|l| l.name == *label)
                        && !instance.proved.contains(label)
                    {
                        continue;
                    }
                    let head = resolver.global(head);
                    let direct = resolver.global(&instance_name(&member, &head));
                    self.direct_members
                        .insert((member.clone(), head.clone()), direct.clone());
                    self.direct_origins.insert(direct, (member.clone(), head));
                }
            }
        }
        self.members = self.members.drain().map(|n| resolver.global(&n)).collect();
        self.methods = self.methods.drain().map(|n| resolver.global(&n)).collect();
        self.laws = self
            .laws
            .drain()
            .map(|(n, v)| (resolver.global(&n), v))
            .collect();
        self.classes = self
            .classes
            .drain()
            .map(|(n, c)| {
                let law = resolver.global(&laws_name(&n));
                let n = resolver.global(&n);
                self.law_records.insert(n.clone(), law.clone());
                self.law_owners.insert(law, n.clone());
                (n, c)
            })
            .collect();
        self.globals = self
            .globals
            .drain()
            .map(|(n, (c, h))| {
                (
                    resolver.global(&n),
                    (resolver.global(&c), resolver.global(&h)),
                )
            })
            .collect();
        self.instances = self
            .instances
            .drain()
            .map(|((c, h), mut instance)| {
                instance.global = resolver.global(&instance.global);
                instance.laws_global = instance.laws_global.as_ref().map(|n| resolver.global(n));
                let mut terms = vec![instance.head.clone()];
                terms.extend(instance.arguments.iter().cloned());
                terms.extend(instance.wheres.iter().flat_map(|(_, t)| t.iter().cloned()));
                resolver.abstract_terms(&instance.global, &mut instance.generics, &mut terms);
                instance.head = terms.remove(0);
                let mut terms = terms.into_iter();
                for arg in &mut instance.arguments {
                    *arg = terms.next().expect("instance argument");
                }
                for (class, args) in &mut instance.wheres {
                    *class = resolver.global(class);
                    for arg in args {
                        *arg = terms.next().expect("constraint argument");
                    }
                }
                ((resolver.global(&c), resolver.global(&h)), instance)
            })
            .collect();
    }

    pub(super) fn member_bindings(&self) -> HashMap<(Name, String), Name> {
        self.members
            .iter()
            .filter_map(|member| {
                let (owner, label) = match member {
                    Name::Spelled(text) => {
                        let (owner, label) = text.rsplit_once("::")?;
                        (Name::from(owner), label.to_string())
                    }
                    _ => (
                        self.member_owners.get(member)?.clone(),
                        self.member_labels.get(member)?.clone(),
                    ),
                };
                Some(((owner, label), member.clone()))
            })
            .collect()
    }

    /// A failure of a record of laws at a law the instance wrote: that law
    /// states another proposition than the class's.
    pub(super) fn explain(&self, verdict: Verdict) -> Verdict {
        let Verdict::Failed(d) = &verdict else {
            return verdict;
        };
        let Some(at) = d.span else {
            return verdict;
        };
        match self.law_spans.iter().find(|(s, _)| *s == at) {
            Some((_, message)) if super::says(&d.message, super::TYPE_MISMATCH) => {
                Verdict::Failed(Diagnostic::new(message.clone(), d.span))
            }
            _ => verdict,
        }
    }

    /// The classes of the proof language declared so far.
    pub(super) fn class_names(&self) -> HashSet<Name> {
        self.classes.keys().cloned().collect()
    }

    pub(super) fn is_method(&self, name: &Name) -> bool {
        self.methods.contains(name)
    }

    /// The method-local binders preceding its dictionary argument.
    pub(super) fn method_generics(&self, name: &Name) -> usize {
        self.member_owners
            .get(name)
            .and_then(|owner| self.classes.get(owner))
            .and_then(|class| {
                self.member_labels
                    .get(name)
                    .and_then(|label| class.methods.iter().find(|m| &m.name == label))
            })
            .map_or(0, |method| method.generics.len())
    }

    /// The generics of the law `C::l` of its own, if it is one.
    pub(super) fn law_generics(&self, name: &Name) -> Option<usize> {
        self.laws.get(name).copied()
    }
}

impl Registry {
    pub(super) fn dictionary_family(&self, name: &Name) -> bool {
        self.classes.contains_key(name) || self.law_owners.contains_key(name)
    }

    pub(super) fn arity(&self, class: &Name) -> usize {
        self.classes.get(class).map_or(1, |c| c.parameters.len())
    }
    pub(super) fn has_laws(&self, class: &Name) -> bool {
        self.classes.get(class).is_some_and(|c| !c.laws.is_empty())
    }
}

#[derive(Clone)]
struct Class {
    parameters: Vec<(Name, T)>,
    methods: Vec<Method>,
    laws: Vec<Law>,
}

// `bounds` also retains ordinary typed-binder spellings such as `Nat`.
// Only ownership kinds belong to the metadata this pure path cannot preserve.
fn method_has_ownership_bounds(method: &FnDecl) -> bool {
    method.bounds.iter().flatten().any(|bound| {
        bound
            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
            .any(|word| matches!(word, "copy" | "shared" | "affine" | "linear"))
    })
}

#[derive(Clone)]
struct Method {
    name: String,
    generics: Vec<(Name, T)>,
    params: Vec<(Name, T)>,
    result: T,
}

#[derive(Clone)]
struct Law {
    name: String,
    /// The generics and the parameters: the type of the field is `∀` over all
    /// of them.
    params: Vec<(Name, T)>,
    implicit: usize,
    ty: T,
}

#[derive(Clone)]
pub(super) struct Instance {
    pub(super) generics: Vec<Name>,
    pub(super) head: T,
    pub(super) arguments: Vec<T>,
    pub(super) type_heads: Vec<bool>,
    /// The classes of the `where` and the types they are for.
    pub(super) wheres: Vec<(Name, Vec<T>)>,
    pub(super) global: Name,
    /// The record of its laws, when the class has any.
    pub(super) laws_global: Option<Name>,
    /// The laws it proves: the others are holes of its record.
    pub(super) proved: HashSet<String>,
}

/// A structural discriminator for first-order instance selection. Display text
/// and source spans are deliberately absent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum HeadKey {
    Any,
    Unknown,
    Name(Name),
    Nat(String),
    Text(String),
    Bool(bool),
    App(Box<HeadKey>, Vec<HeadKey>),
}
impl HeadKey {
    pub(super) fn overlaps(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Any, _) | (_, Self::Any) => true,
            (Self::Unknown, _) | (_, Self::Unknown) => false,
            (Self::Nat(n), Self::App(f, args)) | (Self::App(f, args), Self::Nat(n))
                if matches!(&**f, Self::Name(name) if tauto_surface::bindings::is_library(name, "Succ"))
                    && args.len() == 1 =>
            {
                if n == "0" {
                    return false;
                }
                let mut digits = n.as_bytes().to_vec();
                for digit in digits.iter_mut().rev() {
                    if *digit == b'0' {
                        *digit = b'9';
                    } else {
                        *digit -= 1;
                        break;
                    }
                }
                args[0].overlaps(&Self::Nat(nat_key(
                    std::str::from_utf8(&digits).expect("decimal digits"),
                )))
            }
            (Self::App(f, a), Self::App(g, b)) => {
                a.len() == b.len() && f.overlaps(g) && a.iter().zip(b).all(|(x, y)| x.overlaps(y))
            }
            _ => self == other,
        }
    }
}
fn nat_key(s: &str) -> String {
    let s = s.trim_start_matches('0');
    if s.is_empty() { "0".into() } else { s.into() }
}
/// A fully expanded text literal, including both explicit and implicit list
/// element types, has the same discriminator as its source spelling.
fn literal_text(t: &T, text_ctor: Option<&Name>) -> Option<String> {
    if let TermKind::Text(text) = &*t.kind {
        return Some(text.clone());
    }
    let TermKind::App {
        function,
        arguments,
    } = &*t.kind
    else {
        return None;
    };
    let TermKind::Var(name) = &*function.kind else {
        return None;
    };
    if text_ctor != Some(name) || arguments.len() != 1 {
        return None;
    }
    let mut list = &arguments[0];
    let mut out = Vec::new();
    loop {
        let (name, args) = match &*list.kind {
            TermKind::Var(name) => (name, &[][..]),
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(name) => (name, arguments.as_slice()),
                _ => return None,
            },
            _ => return None,
        };
        if tauto_surface::bindings::is_library(name, "Nil") && args.len() <= 1 {
            return String::from_utf8(out).ok();
        }
        if !tauto_surface::bindings::is_library(name, "Cons") || !(2..=3).contains(&args.len()) {
            return None;
        }
        let TermKind::Nat(n) = &*args[args.len() - 2].kind else {
            return None;
        };
        out.push(n.parse::<u8>().ok()?);
        list = &args[args.len() - 1];
    }
}
fn argument_key(
    t: &T,
    generics: &[Name],
    type_head: bool,
    text_ctor: Option<&Name>,
    shapes: &impl Fn(&Name) -> Option<(usize, usize)>,
    allow_unknown: bool,
) -> Option<HeadKey> {
    if let Some(text) = literal_text(t, text_ctor) {
        return Some(HeadKey::Text(text));
    }
    let constructor = |name: &Name, arguments: &[T]| {
        if tauto_surface::bindings::is_library(name, "Zero") && arguments.is_empty() {
            return Some(HeadKey::Nat("0".into()));
        }
        if tauto_surface::bindings::is_library(name, "Succ")
            && arguments.len() == 1
            && let Some(HeadKey::Nat(n)) = argument_key(
                &arguments[0],
                generics,
                false,
                text_ctor,
                shapes,
                allow_unknown,
            )
        {
            let mut digits = n.into_bytes();
            let mut carry = true;
            for digit in digits.iter_mut().rev() {
                if *digit == b'9' {
                    *digit = b'0';
                } else {
                    *digit += 1;
                    carry = false;
                    break;
                }
            }
            if carry {
                digits.insert(0, b'1');
            }
            return Some(HeadKey::Nat(
                String::from_utf8(digits).expect("decimal digits"),
            ));
        }
        if tauto_surface::bindings::is_library(name, "true") && arguments.is_empty() {
            return Some(HeadKey::Bool(true));
        }
        if tauto_surface::bindings::is_library(name, "false") && arguments.is_empty() {
            return Some(HeadKey::Bool(false));
        }
        let (implicit, total) = shapes(name)?;
        let arguments = if arguments.len() == total {
            &arguments[implicit..]
        } else if arguments.len() + implicit == total {
            arguments
        } else {
            return None;
        };
        Some(HeadKey::App(
            Box::new(HeadKey::Name(name.clone())),
            arguments
                .iter()
                .map(|a| argument_key(a, generics, false, text_ctor, shapes, allow_unknown))
                .collect::<Option<Vec<_>>>()?,
        ))
    };
    match &*t.kind {
        TermKind::Var(name) if generics.contains(name) => Some(HeadKey::Any),
        TermKind::Var(name) if type_head => Some(HeadKey::Name(name.clone())),
        TermKind::Var(name) => constructor(name, &[]),
        TermKind::Nat(n) => Some(HeadKey::Nat(nat_key(n))),
        TermKind::Bool(b) => Some(HeadKey::Bool(*b)),
        TermKind::App { function, .. } if type_head => {
            argument_key(function, generics, true, text_ctor, shapes, allow_unknown)
        }
        TermKind::App {
            function,
            arguments,
        } => match &*function.kind {
            TermKind::Var(name) => constructor(name, arguments),
            _ => None,
        },
        _ => None,
    }
    .or_else(|| allow_unknown.then_some(HeadKey::Unknown))
}

pub(super) fn head_name(head: &T) -> Option<Name> {
    match &*head.kind {
        TermKind::Var(n) => Some(n.clone()),
        TermKind::App { function, .. } => head_name(function),
        _ => None,
    }
}

/// An instance's head with a product `A × B × C` in it as `Prod(A, Prod(B, C))`, the
/// type the checker reads it as: the instance is keyed by `Prod`, never by `Pair`.
fn product_head(head: &T) -> T {
    let TermKind::Product(items) = &*head.kind else {
        return head.clone();
    };
    let mut items = tauto_surface::surface::qualify::product_type_members(items);
    let Some(last) = items.pop() else {
        return T::var(&tauto_surface::bindings::library_name("Unit"), head.span);
    };
    items
        .into_iter()
        .rev()
        .fold(product_head(&last), |snd, fst| {
            T::app(
                &tauto_surface::bindings::library_name("Prod"),
                vec![product_head(&fst), snd],
                head.span,
            )
        })
}

pub(super) fn call(f: impl Into<Name>, args: Vec<T>, sp: Span) -> T {
    let f = f.into();
    if args.is_empty() {
        T::var(&f, sp)
    } else {
        T::app(&f, args, sp)
    }
}

fn pis(params: &[(Name, T)], result: T) -> T {
    params
        .iter()
        .rev()
        .fold(result, |acc, (n, d)| pi(n, d.clone(), acc))
}

fn failed(message: Message, span: Span) -> Verdict {
    Verdict::Failed(Diagnostic::new(message, Some(span)))
}

impl Kernel {
    /// Generated dictionaries choose the universe required by their fields,
    /// using the existing kernel type checker, once dependencies are declared.
    /// User-written inductives retain their explicitly written universe.
    pub(super) fn dictionary_universe(
        &mut self,
        decl: &InductiveDecl,
    ) -> Result<InductiveDecl, Diagnostic> {
        // The ordinary inductive check records the applications exactly once.
        let record_sites = self.record_sites;
        self.record_sites = false;
        let result = self.dictionary_universe_inner(decl);
        self.record_sites = record_sites;
        result
    }

    fn dictionary_universe_inner(
        &mut self,
        decl: &InductiveDecl,
    ) -> Result<InductiveDecl, Diagnostic> {
        let mut context = Vec::new();
        for (name, domain) in &decl.params {
            let domain = self.shape(domain)?;
            let domain = self.elab(&context, &domain, None)?;
            self.expect_type(&context, &domain)?;
            context.push((name.clone(), domain));
        }
        let mut universe = super::Sort::ty(0);
        for constructor in &decl.constructors {
            let mut inner = context.clone();
            for (name, domain) in &constructor.params {
                let domain = self.shape(domain)?;
                let domain = self.elab(&inner, &domain, None)?;
                let field_sort = self.expect_type(&inner, &domain)?;
                universe = field_sort.pi(&universe);
                inner.push((name.clone(), domain));
            }
        }
        let mut decl = decl.clone();
        decl.sort = super::sort_term(&universe, decl.span);
        for (_, expanded) in &mut self.class_expansions {
            for statement in expanded {
                if let Stmt::Inductive(saved) = statement
                    && saved.name == decl.name
                {
                    saved.sort = decl.sort.clone();
                }
            }
        }
        Ok(decl)
    }

    pub(super) fn instance_constructor_shape(&self, name: &Name) -> Option<(usize, usize)> {
        self.classes
            .constructor_shapes
            .get(name)
            .copied()
            .or_else(|| {
                let (family, index) = self.ctors.get(name)?;
                let ind = self.inds.get(family)?;
                let ctor = ind.ctors.get(*index)?;
                Some((
                    ind.params.len() + ctor.implicit,
                    ind.params.len() + ctor.args.len(),
                ))
            })
    }

    pub(super) fn instance_argument_key(
        &self,
        term: &T,
        generics: &[Name],
        type_head: bool,
        allow_unknown: bool,
    ) -> Option<HeadKey> {
        let text = self
            .resolver
            .source_reference("Text")
            .as_ref()
            .and_then(|reference| self.inds.get(reference))
            .and_then(|ind| match ind.ctors.as_slice() {
                [ctor] => Some(&ctor.name),
                _ => None,
            });
        argument_key(
            term,
            generics,
            type_head,
            text,
            &|name| self.instance_constructor_shape(name),
            allow_unknown,
        )
    }

    /// The parameters a `where` makes: `inst@C0: C(T)`, … and, for the proofs
    /// that use laws, after each the record of the laws
    /// `inst@C0@laws: C::laws(T, inst@C0)` (a class without laws has none).
    fn dictionaries(&self, wheres: &[(Name, Vec<T>)], laws: bool, sp: Span) -> Vec<(Name, T)> {
        let mut out = Vec::new();
        for (i, (class, ty)) in wheres.iter().enumerate() {
            let name = Name::from(dictionary_name(class, i));
            out.push((name.clone(), T::app(class, ty.clone(), sp)));
            if laws && self.classes.has_laws(class) {
                out.push((
                    Name::from(format!("{name}@laws")),
                    T::app(
                        &laws_name(class),
                        ty.iter()
                            .cloned()
                            .chain(std::iter::once(T::var(&name, sp)))
                            .collect(),
                        sp,
                    ),
                ));
            }
        }
        out
    }

    /// `stmts` with each class, instance and `where` read; what goes wrong
    /// reading one is an entry of its own.
    pub(super) fn class_pass(&mut self, stmts: &[Stmt], entries: &mut Vec<Entry>) -> Vec<Stmt> {
        // The prepass also sees constructors declared in this unit, before
        // checking has populated `ctors`. Implicit constructor parameters do
        // not discriminate instances: both source and elaborated applications
        // are compared by constructor identity and explicit fields.
        for stmt in stmts {
            if let Stmt::Inductive(ind) = stmt {
                for ctor in &ind.constructors {
                    self.classes.constructor_shapes.insert(
                        ctor.name.clone(),
                        (
                            ind.params.len() + ctor.implicit,
                            ind.params.len() + ctor.params.len(),
                        ),
                    );
                }
            }
        }
        let mut out = Vec::new();
        for stmt in stmts {
            let start = out.len();
            match stmt {
                Stmt::Class(c) => match self.class_decl(c) {
                    Ok(made) => out.extend(made),
                    Err(verdict) => entries.push(Entry {
                        name: c.name.clone(),
                        verdict,
                    }),
                },
                Stmt::Instance(i) => match self.instance_decl(i) {
                    Ok(made) => out.extend(made),
                    Err(verdict) => entries.push(Entry {
                        name: format!(
                            "{}({})",
                            i.class,
                            std::iter::once(&i.head)
                                .chain(&i.arguments)
                                .map(crate::check::describe)
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                        .into(),
                        verdict,
                    }),
                },
                Stmt::Fn(f) => out.push(Stmt::Fn(self.where_fn(f))),
                Stmt::Theorem(t) => out.push(Stmt::Theorem(self.where_theorem(t))),
                Stmt::Mutual { items, span } => out.push(Stmt::Mutual {
                    items: self.class_pass(items, entries),
                    span: *span,
                }),
                other => out.push(other.clone()),
            }
            if self.record_sites && matches!(stmt, Stmt::Class(_) | Stmt::Instance(_))
                || self.record_sites && matches!(stmt, Stmt::Fn(f) if !f.where_.is_empty())
            {
                self.class_expansions
                    .push((stmt.clone(), out[start..].to_vec()));
            }
        }
        out
    }

    /// The constraints of a function's `where` as parameters, when every
    /// class is one the proof language has.
    fn where_fn(&self, f: &FnDecl) -> FnDecl {
        let Some(wheres) = self.constraints(&f.where_) else {
            return f.clone();
        };
        let dicts = self.dictionaries(&wheres, false, f.span);
        let mut f = f.clone();
        f.where_ = Vec::new();
        let mut params: Vec<Name> = dicts.iter().map(|(n, _)| n.clone()).collect();
        params.extend(f.params);
        f.params = params;
        f.borrows = std::iter::repeat_n(None, dicts.len())
            .chain(f.borrows)
            .collect();
        f.param_types = dicts
            .into_iter()
            .map(|(_, t)| Some(t))
            .chain(f.param_types)
            .collect();
        f
    }

    /// A theorem's `where` (already parameters, from the parser) with the
    /// records of the laws after them.
    fn where_theorem(&self, t: &TheoremDecl) -> TheoremDecl {
        let at = t.implicit.min(t.params.len());
        let records = t.params[at..]
            .iter()
            .take_while(|(n, _)| n.starts_with(DICT))
            .count();
        let mut wheres = Vec::new();
        for (_, ty) in &t.params[at..at + records] {
            let TermKind::App {
                function,
                arguments,
            } = &*ty.kind
            else {
                return t.clone();
            };
            let TermKind::Var(class) = &*function.kind else {
                return t.clone();
            };
            if !self.classes.classes.contains_key(class) {
                return t.clone();
            }
            wheres.push((class.clone(), arguments.clone()));
        }
        if wheres.is_empty() {
            return t.clone();
        }
        let mut t = t.clone();
        let dicts = self.dictionaries(&wheres, true, t.span);
        t.params.splice(at..at + records, dicts);
        t
    }

    fn constraints(&self, wheres: &[Constraint]) -> Option<Vec<(Name, Vec<T>)>> {
        if wheres.is_empty()
            || wheres
                .iter()
                .any(|c| !self.classes.classes.contains_key(&c.class))
        {
            return None;
        }
        Some(
            wheres
                .iter()
                .map(|c| {
                    (
                        c.class.clone(),
                        std::iter::once(c.ty.clone())
                            .chain(c.arguments.clone())
                            .collect(),
                    )
                })
                .collect(),
        )
    }

    fn sugared(&self, stmt: &Stmt) -> Stmt {
        self.program_sugar(stmt)
    }

    fn class_decl(&mut self, c: &ClassDecl) -> Result<Vec<Stmt>, Verdict> {
        let sp = c.span;
        let skip =
            |why: Message| Verdict::Skipped(msg!("kernel-class-skipped", why = why));
        if !c.over_types() {
            return Err(skip(msg!("kernel-class-one-param")));
        }
        if self.classes.classes.contains_key(&c.name) {
            return Err(failed(
                msg!("kernel-class-defined", name = (&c.name).to_string()),
                sp,
            ));
        }
        for m in &c.methods {
            if m.effects.as_ref().is_some_and(|e| !e.is_empty()) {
                return Err(if c.laws.is_empty() {
                    skip(msg!(
                        "kernel-class-method-effects",
                        name = (&m.name).to_string()
                    ))
                } else {
                    failed(
                        msg!(
                            "kernel-class-effects-laws",
                            class = (&c.name).to_string(),
                            method = (&m.name).to_string()
                        ),
                        m.span,
                    )
                });
            }
            // The checked dictionary path supports pure typed telescopes.
            // Row, ownership and constrained methods stay on their existing
            // native path rather than silently losing signature information.
            if !m.generics.is_empty()
                && (m.rows.iter().any(|row| *row)
                    || method_has_ownership_bounds(m)
                    || !m.where_.is_empty()
                    || m.borrows.iter().any(Option::is_some))
            {
                return Err(skip(msg!(
                    "kernel-class-method-generics",
                    name = (&m.name).to_string()
                )));
            }
            if m.param_types.iter().any(|t| t.is_none()) {
                return Err(skip(msg!(
                    "kernel-class-method-untyped",
                    name = (&m.name).to_string()
                )));
            }
            // A built-in type (`i64` and the like), which the kernel declares
            // under other names, cannot be a field of the dictionary: the
            // class is left out of the proofs, as a function with such a
            // type is.
            let builtin = m
                .param_types
                .iter()
                .flatten()
                .chain(m.result.iter())
                .flat_map(super::free_vars)
                .any(|n| {
                    tauto_surface::surface::qualify::BUILTIN_TYPES
                        .iter()
                        .any(|b| tauto_surface::bindings::is_library(&n, b))
                });
            if builtin {
                return Err(skip(msg!("kernel-type-not-kernel")));
            }
        }
        // The names `C::m` before the terms are read, so that the laws can
        // mention the methods.
        let member = |index: usize, law: bool, label: &str| -> Name {
            match c.name.as_global() {
                Some(owner) => owner.class_member(index, law, label).into(),
                None => format!("{}::{label}", c.name).into(),
            }
        };
        let names: Vec<Name> = c
            .methods
            .iter()
            .enumerate()
            .map(|(index, m)| member(index, false, &m.name))
            .chain(
                c.laws
                    .iter()
                    .enumerate()
                    .map(|(index, l)| member(index, true, &l.name)),
            )
            .collect();
        self.classes.members.extend(names.iter().cloned());
        let unit = T::var(&tauto_surface::bindings::library_name("Unit"), sp);
        let methods: Vec<Method> = c
            .methods
            .iter()
            .map(|m| {
                let Stmt::Fn(m) = self.sugared(&Stmt::Fn(FnDecl {
                    body: T::var("()", sp),
                    ..m.clone()
                })) else {
                    unreachable!()
                };
                Method {
                    name: m.name.to_string(),
                    generics: m.generic_parameters(),
                    params: m
                        .params
                        .iter()
                        .cloned()
                        .zip(m.param_types.iter().flatten().cloned())
                        .collect(),
                    result: m.result.clone().unwrap_or_else(|| unit.clone()),
                }
            })
            .collect();
        let laws: Vec<Law> = c
            .laws
            .iter()
            .map(|l| {
                let Stmt::Theorem(t) = self.sugared(&Stmt::Theorem(l.theorem.clone())) else {
                    unreachable!()
                };
                Law {
                    name: l.name.to_string(),
                    params: t.params,
                    implicit: t.implicit,
                    ty: t.ty,
                }
            })
            .collect();
        self.classes.methods.extend(
            c.methods
                .iter()
                .enumerate()
                .map(|(index, m)| member(index, false, &m.name)),
        );
        for (index, l) in laws.iter().enumerate() {
            self.classes
                .laws
                .insert(member(index, true, &l.name), l.implicit);
        }
        let class = Class {
            parameters: c.parameters.clone(),
            methods,
            laws,
        };

        let class_args: Vec<T> = c.parameters.iter().map(|(n, _)| T::var(n, sp)).collect();
        let dict_ty = T::app(&c.name, class_args.clone(), sp);
        let dict = format!("{DICT}{}", c.name);
        let mk = constructor_name(&c.name);
        let fields: Vec<(Name, T)> = class
            .methods
            .iter()
            .map(|m| {
                (
                    Name::from(format!("{}::{}", c.name, m.name)),
                    pis(&m.generics, pis(&m.params, m.result.clone())),
                )
            })
            .collect();
        let mut out = vec![Stmt::Inductive(InductiveDecl {
            vis: Default::default(),
            generates: Default::default(),
            name: c.name.clone(),
            params: c.parameters.clone(),
            sort: T::var(&tauto_surface::bindings::library_name("Type"), sp),
            constructors: vec![Constructor {
                name: mk.clone(),
                implicit: 0,
                params: fields.clone(),
                result: dict_ty.clone(),
            }],
            span: sp,
        })];
        // `match record: result { mk(f@0, …) => f@i(args) }`.
        let project = |scrutinee: &str, mk: &Name, fields: usize, result: &T, body: T| {
            T::new(
                TermKind::Match {
                    binder: None,
                    scrutinee: Box::new(T::var(scrutinee, sp)),
                    result: Some(Box::new(result.clone())),
                    arms: vec![MatchArm {
                        goal: None,
                        pattern: Pattern::Ctor {
                            name: mk.clone(),
                            args: (0..fields)
                                .map(|i| Pattern::Bind(format!("f@{i}").into()))
                                .collect(),
                        },
                        guard: None,
                        body,
                    }],
                },
                sp,
            )
        };
        for (i, m) in class.methods.iter().enumerate() {
            let args: Vec<T> = m
                .generics
                .iter()
                .chain(&m.params)
                .map(|(n, _)| T::var(n, sp))
                .collect();
            let body = project(
                &dict,
                &mk,
                fields.len(),
                &m.result,
                call(&format!("f@{i}"), args, sp),
            );
            let mut params = vec![Name::from(&dict)];
            params.extend(m.params.iter().map(|(n, _)| n.clone()));
            let mut types = vec![Some(dict_ty.clone())];
            types.extend(m.params.iter().map(|(_, t)| Some(t.clone())));
            out.push(Stmt::Fn(FnDecl {
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                decreasing_by: None,
                name: member_name(&c.name, &class, &m.name),
                generic_types: c
                    .parameters
                    .iter()
                    .chain(&m.generics)
                    .map(|(_, t)| t.clone())
                    .collect(),
                generics: c
                    .parameters
                    .iter()
                    .chain(&m.generics)
                    .map(|(n, _)| n.clone())
                    .collect(),
                rows: vec![false; c.parameters.len() + m.generics.len()],
                bounds: vec![None; c.parameters.len() + m.generics.len()],
                bound_spans: Vec::new(),
                borrows: vec![None; params.len()],
                params,
                param_types: types,
                result: Some(m.result.clone()),
                effects: None,
                where_: Vec::new(),
                span: sp,
                body,
            }));
        }
        if !class.laws.is_empty() {
            // The laws are a record of their own, over the record of the
            // methods: an instance missing a law is incomplete only there.
            let laws_name = laws_name(&c.name);
            let laws_mk = constructor_name(&laws_name);
            let laws_ty = T::app(
                &laws_name,
                class_args
                    .iter()
                    .cloned()
                    .chain(std::iter::once(T::var(&dict, sp)))
                    .collect(),
                sp,
            );
            let laws_dict = format!("{dict}@laws");
            let law_fields: Vec<(Name, T)> = class
                .laws
                .iter()
                .map(|l| {
                    (
                        Name::from(format!("{}::{}", c.name, l.name)),
                        pis(&l.params, l.ty.clone()),
                    )
                })
                .collect();
            out.push(Stmt::Inductive(InductiveDecl {
                vis: Default::default(),
                generates: Default::default(),
                name: laws_name.clone(),
                params: c
                    .parameters
                    .iter()
                    .cloned()
                    .chain(std::iter::once((Name::from(dict.clone()), dict_ty.clone())))
                    .collect(),
                sort: T::var(&tauto_surface::bindings::library_name("Type"), sp),
                constructors: vec![Constructor {
                    name: laws_mk.clone(),
                    implicit: 0,
                    params: law_fields.clone(),
                    result: laws_ty.clone(),
                }],
                span: sp,
            }));
            for (j, l) in class.laws.iter().enumerate() {
                // The generics of the law, then the records, then the rest.
                let (gens, rest) = l.params.split_at(l.implicit);
                let args: Vec<T> = l.params.iter().map(|(n, _)| T::var(n, sp)).collect();
                let body = project(
                    &laws_dict,
                    &laws_mk,
                    law_fields.len(),
                    &l.ty,
                    call(&format!("f@{j}"), args, sp),
                );
                let mut params = c.parameters.clone();
                params.extend(gens.iter().cloned());
                params.push((crate::surface::Name::Spelled(dict.clone()), dict_ty.clone()));
                params.push((
                    crate::surface::Name::Spelled(laws_dict.clone()),
                    laws_ty.clone(),
                ));
                params.extend(rest.iter().cloned());
                out.push(Stmt::Theorem(TheoremDecl {
                    budget: None,
                    vis: Default::default(),
                    decreasing_by: None,
                    name: member_name(&c.name, &class, &l.name),
                    implicit: c.parameters.len() + l.implicit,
                    params,
                    ty: l.ty.clone(),
                    body: Some(body),
                    span: sp,
                }));
            }
        }
        self.classes.classes.insert(c.name.clone(), class);
        Ok(out)
    }

    fn class_substitute(
        &mut self,
        term: &T,
        parameters: &[(Name, T)],
        instance: &InstanceDecl,
    ) -> T {
        let args = std::iter::once(&instance.head).chain(&instance.arguments);
        parameters
            .iter()
            .zip(args)
            .fold(term.clone(), |term, ((name, _), arg)| {
                self.subst(&term, name, arg)
            })
    }

    fn instance_decl(&mut self, i: &InstanceDecl) -> Result<Vec<Stmt>, Verdict> {
        let i = &InstanceDecl {
            head: product_head(&i.head),
            arguments: i.arguments.iter().map(product_head).collect(),
            ..i.clone()
        };
        let sp = i.span;
        let Some(class) = self.classes.classes.get(&i.class).cloned() else {
            return Err(Verdict::Skipped(
                msg!(
                    "kernel-instance-not-class-skipped",
                    name = (&i.class).to_string()
                ),
            ));
        };
        let head = head_name(&i.head).unwrap_or_else(|| Name::from("value"));
        let all_args: Vec<T> = std::iter::once(i.head.clone())
            .chain(i.arguments.clone())
            .collect();
        if all_args.len() != class.parameters.len() {
            return Err(failed(msg!("kernel-class-argument-arity"), sp));
        }
        let type_heads: Vec<bool> = class
            .parameters
            .iter()
            .map(|(_, ty)| matches!(super::sort_of(ty), Some(super::Sort::Type(_))))
            .collect();
        let keys: Option<Vec<_>> = all_args
            .iter()
            .zip(&type_heads)
            .map(|(a, ty)| self.instance_argument_key(a, &i.generics, *ty, false))
            .collect();
        let Some(keys) = keys else {
            return Err(failed(msg!("kernel-instance-first-order"), sp));
        };
        let overlapping = self.classes.instances.iter().any(|((owner, _), other)| {
            owner == &i.class
                && std::iter::once(&other.head)
                    .chain(&other.arguments)
                    .zip(&other.type_heads)
                    .map(|(a, ty)| self.instance_argument_key(a, &other.generics, *ty, false))
                    .collect::<Option<Vec<_>>>()
                    .is_some_and(|old| {
                        old.len() == keys.len() && old.iter().zip(&keys).all(|(a, b)| a.overlaps(b))
                    })
        });
        let head = if class.parameters.len() == 1 && type_heads[0] {
            head
        } else {
            let label = format!("{}@instance{}", head, self.classes.instances.len());
            match i.class.as_global() {
                Some(owner) => owner
                    .specialize(
                        &format!("instance-head:{}", self.classes.instances.len()),
                        label,
                    )
                    .into(),
                None => Name::from(label),
            }
        };
        let key = (i.class.clone(), head.clone());
        let shown = format!(
            "{}({})",
            i.class,
            std::iter::once(&i.head)
                .chain(&i.arguments)
                .map(crate::check::describe)
                .collect::<Vec<_>>()
                .join(", ")
        );
        if overlapping {
            return Err(failed(
                msg!("kernel-instance-defined", instance = &shown),
                sp,
            ));
        }
        let mut wheres = Vec::new();
        for c in &i.where_ {
            if !self.classes.classes.contains_key(&c.class) {
                return Err(failed(
                    msg!("kernel-instance-not-class", name = (&c.class).to_string()),
                    c.span,
                ));
            }
            wheres.push((
                c.class.clone(),
                std::iter::once(c.ty.clone())
                    .chain(c.arguments.clone())
                    .collect(),
            ));
        }
        // The records of the `where`: of the methods for the functions, with
        // the laws for the proofs.
        let methods_only = self.dictionaries(&wheres, false, sp);
        let with_laws = self.dictionaries(&wheres, true, sp);
        let names =
            |dicts: &[(Name, T)]| -> Vec<Name> { dicts.iter().map(|(n, _)| n.clone()).collect() };
        let vars = |names: &[Name]| -> Vec<T> { names.iter().map(|n| T::var(n, sp)).collect() };
        let generics: Vec<(Name, T)> = i
            .generics
            .iter()
            .enumerate()
            .map(|(index, g)| {
                (
                    g.clone(),
                    i.generic_types.get(index).cloned().unwrap_or_else(|| {
                        T::var(&tauto_surface::bindings::library_name("Type"), sp)
                    }),
                )
            })
            .collect();
        let generic_vars: Vec<T> = i.generics.iter().map(|g| T::var(g, sp)).collect();
        let name = |member: &str| instance_name(&member_name(&i.class, &class, member), &head);
        let global = match i.class.as_global() {
            Some(owner) => owner
                .specialize(
                    &format!("dictionary:{head:?}"),
                    format!("{}::inst@{head}", i.class),
                )
                .into(),
            None => Name::from(format!("{}::inst@{head}", i.class)),
        };
        let laws_global = instance_name(&laws_name(&i.class), &head);

        let mut out = Vec::new();
        let mut methods: Vec<T> = Vec::new();
        let mut laws: Vec<T> = Vec::new();
        let mut proved = HashSet::new();
        for m in &class.methods {
            let Some(written) = i.methods.iter().find(|w| w.name.as_str() == m.name) else {
                return Err(failed(
                    msg!(
                        "kernel-instance-lacks",
                        instance = &shown,
                        method = (&m.name).to_string()
                    ),
                    sp,
                ));
            };
            if written.generics.len() != m.generics.len() {
                return Err(failed(
                    msg!(
                        "kernel-instance-method-params",
                        method = (&m.name).to_string(),
                        instance = &shown,
                        written = written.generics.len(),
                        class = m.generics.len()
                    ),
                    written.span,
                ));
            }
            if !m.generics.is_empty()
                && (written.rows.iter().any(|row| *row)
                    || method_has_ownership_bounds(written)
                    || !written.where_.is_empty()
                    || written.borrows.iter().any(Option::is_some)
                    || written
                        .effects
                        .as_ref()
                        .is_some_and(|effects| !effects.is_empty()))
            {
                return Err(failed(
                    msg!(
                        "kernel-class-method-generics",
                        name = (&written.name).to_string()
                    ),
                    written.span,
                ));
            }
            let method_generics = written.generic_parameters();
            if written.params.len() != m.params.len() {
                return Err(failed(
                    msg!(
                        "kernel-instance-method-params",
                        method = (&m.name).to_string(),
                        instance = &shown,
                        written = written.params.len(),
                        class = m.params.len()
                    ),
                    written.span,
                ));
            }
            // Rename simultaneously, including omitted annotations whose
            // earlier binders have different names in the instance.
            let renames: Vec<_> = m
                .generics
                .iter()
                .map(|(name, _)| name)
                .chain(m.params.iter().map(|(name, _)| name))
                .zip(
                    method_generics
                        .iter()
                        .map(|(name, _)| name)
                        .chain(&written.params),
                )
                .filter(|_| !m.generics.is_empty())
                .map(|(declared, actual)| {
                    (declared.clone(), actual.clone(), self.fresh_name(declared))
                })
                .collect();
            let mut inherit_type = |ty: &T| {
                let mut ty = self.class_substitute(ty, &class.parameters, i);
                for (declared, _, fresh) in &renames {
                    ty = self.subst(&ty, declared, &T::var(fresh, written.span));
                }
                for (_, actual, fresh) in &renames {
                    ty = self.subst(&ty, fresh, &T::var(actual, written.span));
                }
                ty
            };
            let params: Vec<(Name, T)> = written
                .params
                .iter()
                .zip(&written.param_types)
                .zip(&m.params)
                .map(|((n, t), (_, class_ty))| {
                    let t = t.clone().unwrap_or_else(|| inherit_type(class_ty));
                    (n.clone(), t)
                })
                .collect();
            let result = written
                .result
                .clone()
                .unwrap_or_else(|| inherit_type(&m.result));
            let fname = name(&m.name);
            let mut all_params = names(&methods_only);
            all_params.extend(method_generics.iter().map(|(n, _)| n.clone()));
            all_params.extend(params.iter().map(|(n, _)| n.clone()));
            let mut types: Vec<Option<T>> =
                methods_only.iter().map(|(_, t)| Some(t.clone())).collect();
            types.extend(method_generics.iter().map(|(_, t)| Some(t.clone())));
            types.extend(params.iter().map(|(_, t)| Some(t.clone())));
            out.push(Stmt::Fn(FnDecl {
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                decreasing_by: None,
                name: fname.clone(),
                generic_types: i.generic_types.clone(),
                generics: i.generics.clone(),
                rows: vec![false; i.generics.len()],
                bounds: vec![None; i.generics.len()],
                bound_spans: Vec::new(),
                borrows: vec![None; all_params.len()],
                params: all_params,
                param_types: types,
                result: Some(result),
                effects: None,
                where_: Vec::new(),
                span: written.span,
                body: written.body.clone(),
            }));
            let mut args = generic_vars.clone();
            args.extend(vars(&names(&methods_only)));
            args.extend(method_generics.iter().map(|(n, _)| T::var(n, written.span)));
            args.extend(params.iter().map(|(n, _)| T::var(n, written.span)));
            let applied = T::app(&fname, args, written.span);
            methods.push(if method_generics.is_empty() && params.is_empty() {
                applied
            } else {
                T::new(
                    TermKind::Lam {
                        params: method_generics
                            .iter()
                            .chain(&params)
                            .map(|(n, _)| n.clone())
                            .collect(),
                        body: Box::new(applied),
                        types: Vec::new(),
                    },
                    written.span,
                )
            });
        }
        for w in &i.methods {
            if !class.methods.iter().any(|m| m.name == w.name.as_str()) {
                return Err(failed(
                    msg!(
                        "kernel-instance-not-method",
                        name = (&w.name).to_string(),
                        class = (&i.class).to_string()
                    ),
                    w.span,
                ));
            }
        }
        for w in &i.laws {
            if !class.laws.iter().any(|l| l.name == w.name.as_str()) {
                return Err(failed(
                    msg!(
                        "kernel-instance-not-law",
                        name = (&w.name).to_string(),
                        class = (&i.class).to_string()
                    ),
                    w.span,
                ));
            }
        }
        for l in &class.laws {
            let missing = |at: Span| T::new(TermKind::Hole(format!("law:{shown}::{}", l.name)), at);
            let Some(written) = i.laws.iter().find(|w| w.name.as_str() == l.name) else {
                // Not proved: a hole, and the record of the laws is incomplete.
                laws.push(missing(sp));
                continue;
            };
            let t = &written.theorem;
            if t.params.len() != l.params.len() || t.implicit != l.implicit {
                return Err(failed(
                    msg!(
                        "kernel-instance-law-params",
                        law = (&l.name).to_string(),
                        instance = &shown
                    ),
                    written.span,
                ));
            }
            let Some(body) = &t.body else {
                laws.push(missing(written.span));
                continue;
            };
            // The generics of the instance, the records, then the law's own
            // generics, which a recursive use (`C::l(smaller, …)`) writes.
            let (gens, rest) = t.params.split_at(t.implicit);
            let mut params = generics.clone();
            params.extend(with_laws.iter().cloned());
            params.extend(gens.iter().cloned());
            params.extend(rest.iter().cloned());
            let tname = name(&l.name);
            proved.insert(l.name.clone());
            out.push(Stmt::Theorem(TheoremDecl {
                budget: None,
                vis: Default::default(),
                decreasing_by: None,
                name: tname.clone(),
                implicit: generics.len(),
                params,
                ty: t.ty.clone(),
                body: Some(body.clone()),
                span: written.span,
            }));
            let mut args = generic_vars.clone();
            args.extend(vars(&names(&with_laws)));
            args.extend(gens.iter().map(|(n, _)| T::var(n, written.span)));
            args.extend(rest.iter().map(|(n, _)| T::var(n, written.span)));
            let applied = T::app(&tname, args, written.span);
            self.classes.law_spans.push((
                written.span,
                msg!(
                    "kernel-instance-law-differs",
                    law = (&l.name).to_string(),
                    instance = &shown
                ),
            ));
            laws.push(T::new(
                TermKind::Lam {
                    params: t.params.iter().map(|(n, _)| n.clone()).collect(),
                    body: Box::new(applied),
                    types: Vec::new(),
                },
                written.span,
            ));
        }
        let instance_args: Vec<T> = std::iter::once(i.head.clone())
            .chain(i.arguments.clone())
            .collect();
        let head_ty = T::app(&i.class, instance_args.clone(), sp);
        let method_names = names(&methods_only);
        out.push(Stmt::Fn(FnDecl {
            budget: None,
            vis: Default::default(),
            generates: None,
            opaque: false,
            decreasing_by: None,
            name: global.clone(),
            generic_types: i.generic_types.clone(),
            generics: i.generics.clone(),
            rows: vec![false; i.generics.len()],
            bounds: vec![None; i.generics.len()],
            bound_spans: Vec::new(),
            borrows: vec![None; method_names.len()],
            params: method_names.clone(),
            param_types: methods_only.iter().map(|(_, t)| Some(t.clone())).collect(),
            result: Some(head_ty),
            effects: None,
            where_: Vec::new(),
            span: sp,
            body: T::app(&constructor_name(&i.class), methods, sp),
        }));
        let has_laws = !class.laws.is_empty();
        if has_laws {
            let mut inst_args = generic_vars.clone();
            inst_args.extend(vars(&method_names));
            let all = names(&with_laws);
            out.push(Stmt::Fn(FnDecl {
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                decreasing_by: None,
                name: laws_global.clone(),
                generic_types: i.generic_types.clone(),
                generics: i.generics.clone(),
                rows: vec![false; i.generics.len()],
                bounds: vec![None; i.generics.len()],
                bound_spans: Vec::new(),
                borrows: vec![None; all.len()],
                params: all,
                param_types: with_laws.iter().map(|(_, t)| Some(t.clone())).collect(),
                result: Some(T::app(
                    &laws_name(&i.class),
                    instance_args
                        .iter()
                        .cloned()
                        .chain(std::iter::once(call(&global, inst_args, sp)))
                        .collect(),
                    sp,
                )),
                effects: None,
                where_: Vec::new(),
                span: sp,
                body: T::app(&constructor_name(&laws_name(&i.class)), laws, sp),
            }));
            self.classes
                .globals
                .insert(laws_global.clone(), key.clone());
        }
        self.classes.instances.insert(
            key.clone(),
            Instance {
                generics: i.generics.clone(),
                head: i.head.clone(),
                arguments: i.arguments.clone(),
                type_heads,
                wheres,
                global: global.clone(),
                laws_global: has_laws.then_some(laws_global),
                proved,
            },
        );
        self.classes.globals.insert(global, key);
        Ok(out)
    }
}
