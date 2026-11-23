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

use super::{Diagnostic, Entry, Kernel, T, Verdict};
use crate::surface::{
    ClassDecl, Constraint, Constructor, DICT, FnDecl, InductiveDecl, InferCondition, InstanceDecl,
    MatchArm, Pattern, Stmt, TermKind, TheoremDecl, dictionary_name,
};

pub(super) fn is_dict(name: &Name) -> bool {
    name.starts_with(DICT)
}

#[derive(Default, Clone)]
pub(super) struct Registry {
    classes: tauto_identity::ForkedMap<Name, Class>,
    constructor_shapes: tauto_identity::ForkedMap<Name, (usize, usize)>,
    pub(super) law_owners: tauto_identity::ForkedMap<Name, Name>,
    pub(super) law_records: tauto_identity::ForkedMap<Name, Name>,
    pub(super) member_owners: tauto_identity::ForkedMap<Name, Name>,
    pub(super) member_labels: tauto_identity::ForkedMap<Name, String>,
    pub(super) direct_members: tauto_identity::ForkedMap<(Name, Name), Name>,
    pub(super) direct_origins: tauto_identity::ForkedMap<Name, (Name, Name)>,
    /// `C::m` for every method and law of a class: the names a program may
    /// write as `C::m(…)`.
    members: tauto_identity::ForkedSet<Name>,
    methods: tauto_identity::ForkedSet<Name>,
    /// For each law `C::l`, how many generics it has of its own.
    laws: tauto_identity::ForkedMap<Name, usize>,
    /// Where each law an instance proves is written, and what is wrong if
    /// the record of the laws does not take it.
    law_spans: Vec<(Span, Message)>,
    pub(super) instances: tauto_identity::ForkedMap<(Name, Name), Instance>,
    /// An instance's function, by name: the class and the head it is for.
    pub(super) globals: tauto_identity::ForkedMap<Name, (Name, Name)>,
}

impl Registry {
    pub(super) fn law_spans_len(&self) -> usize {
        self.law_spans.len()
    }

    /// Leaves in this copy only what it wrote since it was made, and of the
    /// `law_spans` it shares the first `law_spans` of, only what follows.
    pub(super) fn subtract(&mut self, since: u64, law_spans: usize) {
        self.classes.subtract(since);
        self.constructor_shapes.subtract(since);
        self.law_owners.subtract(since);
        self.law_records.subtract(since);
        self.member_owners.subtract(since);
        self.member_labels.subtract(since);
        self.direct_members.subtract(since);
        self.direct_origins.subtract(since);
        self.members.subtract(since);
        self.methods.subtract(since);
        self.laws.subtract(since);
        self.instances.subtract(since);
        self.globals.subtract(since);
        self.law_spans.drain(..law_spans.min(self.law_spans.len()));
    }

    /// Takes in what a copy of this registry wrote (`check/fork.rs`); false
    /// as [`tauto_identity::ForkedMap::absorb`] is.
    pub(super) fn absorb(&mut self, other: Registry, law_spans: usize) -> bool {
        use super::fork::add_after;
        let Registry {
            classes,
            constructor_shapes,
            law_owners,
            law_records,
            member_owners,
            member_labels,
            direct_members,
            direct_origins,
            members,
            methods,
            laws,
            law_spans: spans,
            instances,
            globals,
        } = other;
        let mut alone = true;
        alone &= self.classes.absorb_any(classes);
        alone &= self.constructor_shapes.absorb(constructor_shapes);
        alone &= self.law_owners.absorb(law_owners);
        alone &= self.law_records.absorb(law_records);
        alone &= self.member_owners.absorb(member_owners);
        alone &= self.member_labels.absorb(member_labels);
        alone &= self.direct_members.absorb(direct_members);
        alone &= self.direct_origins.absorb(direct_origins);
        alone &= self.members.absorb(members);
        alone &= self.methods.absorb(methods);
        alone &= self.laws.absorb(laws);
        add_after(&mut self.law_spans, spans, law_spans);
        alone &= self.instances.absorb_any(instances);
        alone &= self.globals.absorb(globals);
        alone
    }
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

pub(super) fn laws_name(class: &Name) -> Name {
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

pub(super) fn constructor_name(family: &Name) -> Name {
    match family.as_global() {
        Some(owner) => owner.constructor(0, "Mk").into(),
        None => format!("{family}::Mk").into(),
    }
}

impl Registry {
    pub(super) fn resolve(&mut self, resolver: &mut tauto_surface::resolve::Resolver) {
        // What is already resolved stays as it is, and is not written: a
        // copy hands back only what it changed (`tauto_identity::forked`).
        self.constructor_shapes.rename_keys(|n| resolver.global(n));
        for (class, descriptor) in &self.classes {
            let class_ref = resolver.global(class);
            for label in descriptor
                .methods
                .iter()
                .map(|m| &m.name)
                .chain(descriptor.laws.iter().map(|l| &l.name))
            {
                let member = resolver.global(&member_name(&class_ref, descriptor, label));
                self.member_owners.put(member.clone(), class_ref.clone());
                self.member_labels.put(member.clone(), label.to_string());
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
                        .put((member.clone(), head.clone()), direct.clone());
                    self.direct_origins.put(direct, (member.clone(), head));
                }
            }
        }
        self.members.rename(|n| resolver.global(n));
        self.methods.rename(|n| resolver.global(n));
        self.laws.rename_keys(|n| resolver.global(n));
        let classes: Vec<Name> = self.classes.keys().cloned().collect();
        for n in classes {
            let law = resolver.global(&laws_name(&n));
            let n = resolver.global(&n);
            self.law_records.put(n.clone(), law.clone());
            self.law_owners.put(law, n);
        }
        self.classes.rename_keys(|n| resolver.global(n));
        self.globals.rename_keys(|n| resolver.global(n));
        self.globals.change_values(|_, (c, h)| {
            let to = (resolver.global(c), resolver.global(h));
            let changed = to != (c.clone(), h.clone());
            (*c, *h) = to;
            changed
        });
        // An instance is resolved once, when its names are not yet: one
        // whose names are resolved already is left as it is, unwritten.
        let unresolved: Vec<(Name, Name)> = self
            .instances
            .iter()
            .filter(|((c, h), instance)| {
                resolver.global(c) != *c
                    || resolver.global(h) != *h
                    || resolver.global(&instance.global) != instance.global
            })
            .map(|(k, _)| k.clone())
            .collect();
        let resolved: Vec<((Name, Name), Instance)> = unresolved
            .into_iter()
            .filter_map(|k| self.instances.remove(&k).map(|v| (k, v)))
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
        for (k, v) in resolved {
            self.instances.insert(k, v);
        }
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
/// A written parameter or result as the kernel reads a passing convention:
/// an outer `&A` or `&mut A` is the value `A`. Borrows that appear inside a
/// type (the item of `FiniteStep(&mut I, …)`, `Option(&mut I)`, …) stay:
/// they are part of what the method returns or relates, and Nib still
/// checks exclusivity for those positions.
pub(super) fn without_borrows(t: &T) -> T {
    let mut t = t.clone();
    while let crate::surface::TermKind::Borrow { term, .. } = &*t.kind {
        t = (**term).clone();
    }
    t
}

/// The reader's `borrows` mark put back on a parameter type for the
/// dictionary field and its projection, so exclusive places stay places.
fn with_borrow_mark(ty: &T, mark: Option<bool>) -> T {
    match mark {
        Some(mutable) => T::new(
            TermKind::Borrow { orig: false, rc: false,
                mutable,
                term: Box::new(without_borrows(ty)),
            },
            ty.span,
        ),
        None => without_borrows(ty),
    }
}

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
    /// Outer `&` / `&mut` on each parameter of [`Self::params`], including a
    /// leading `None` for each `where` dictionary. Extraction restores those
    /// marks on the dictionary fields and projections so exclusive places are
    /// not retyped as owned values.
    borrows: Vec<Option<bool>>,
    /// `borrows(…)` after the result: projections keep this so an item-lending
    /// method is not rewritten as a Mut'k out-parameter function.
    lends: Option<Vec<String>>,
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
    pub(super) infer_from: Option<InferenceGate>,
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

#[derive(Clone)]
pub(super) enum InferenceGate {
    Slot(usize),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
}

impl InferenceGate {
    pub(super) fn holds(&self, known: &[bool]) -> bool {
        match self {
            Self::Slot(index) => known.get(*index).copied().unwrap_or(false),
            Self::And(left, right) => left.holds(known) && right.holds(known),
            Self::Or(left, right) => left.holds(known) || right.holds(known),
        }
    }
}

fn inference_gate(
    condition: &InferCondition,
    class: &Class,
    type_heads: &[bool],
) -> Option<InferenceGate> {
    Some(match condition {
        InferCondition::Parameter(name) => {
            InferenceGate::Slot(class.parameters.iter().enumerate().find_map(
                |(index, (parameter, _))| {
                    (inference_parameter_label(parameter) == name.as_str() && type_heads[index])
                        .then_some(index)
                },
            )?)
        }
        InferCondition::And(left, right) => InferenceGate::And(
            Box::new(inference_gate(left, class, type_heads)?),
            Box::new(inference_gate(right, class, type_heads)?),
        ),
        InferCondition::Or(left, right) => InferenceGate::Or(
            Box::new(inference_gate(left, class, type_heads)?),
            Box::new(inference_gate(right, class, type_heads)?),
        ),
    })
}

fn inference_parameter_label(name: &Name) -> &str {
    tauto_surface::macros::scope::split(name.as_str()).0
}

fn inference_owned(
    condition: &InferCondition,
    class: &Class,
    arguments: &[T],
    owners: &HashSet<Name>,
    generics: &[Name],
) -> bool {
    match condition {
        InferCondition::Parameter(parameter) => class
            .parameters
            .iter()
            .position(|(name, _)| inference_parameter_label(name) == parameter.as_str())
            .is_some_and(|index| {
                let argument = &arguments[index];
                !matches!(&*argument.kind, TermKind::Pi { .. })
                    && argument.product_type_members().is_none()
                    && head_name(argument)
                        .is_some_and(|head| !generics.contains(&head) && owners.contains(&head))
            }),
        InferCondition::And(left, right) => {
            inference_owned(left, class, arguments, owners, generics)
                || inference_owned(right, class, arguments, owners, generics)
        }
        InferCondition::Or(left, right) => {
            inference_owned(left, class, arguments, owners, generics)
                && inference_owned(right, class, arguments, owners, generics)
        }
    }
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
            // A type applied to numerals (`UInt(64)`, [`numeral_arguments`])
            // and the same type with its arguments not told apart.
            (n @ Self::Name(_), Self::App(f, _)) | (Self::App(f, _), n @ Self::Name(_)) => {
                **f == *n
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
/// Whether a class parameter of this kind is written by a type: `Type`, or a
/// type constructor `(Type) -> Type` (a higher-kinded class's parameter).
fn type_or_type_former(kind: &T) -> bool {
    match &*kind.kind {
        TermKind::Pi { result, .. } => type_or_type_former(result),
        _ => matches!(super::sort_of(kind), Some(super::Sort::Type(_))),
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
        // A function type is its own head, whatever it takes and gives.
        TermKind::Pi { .. } if type_head => Some(HeadKey::Name(function_head())),
        TermKind::Var(name) if generics.contains(name) => Some(HeadKey::Any),
        TermKind::Var(name) if type_head => Some(HeadKey::Name(name.clone())),
        TermKind::Var(name) => constructor(name, &[]),
        TermKind::Nat(n) => Some(HeadKey::Nat(nat_key(n))),
        TermKind::Bool(b) => Some(HeadKey::Bool(*b)),
        // A type applied to numerals is told apart by them: `UInt(8)` and
        // `UInt(64)` are two heads.
        TermKind::App {
            function,
            arguments,
        } if type_head && numeral_arguments(arguments) => Some(HeadKey::App(
            Box::new(argument_key(
                function,
                generics,
                true,
                text_ctor,
                shapes,
                allow_unknown,
            )?),
            arguments
                .iter()
                .map(|a| match &*a.kind {
                    TermKind::Nat(n) => HeadKey::Nat(nat_key(n)),
                    _ => HeadKey::Unknown,
                })
                .collect(),
        )),
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

/// Whether every argument of a type is a numeral (`UInt(64)`): such a type
/// is a head of instances of its own.
pub(super) fn numeral_arguments(arguments: &[T]) -> bool {
    !arguments.is_empty()
        && arguments
            .iter()
            .all(|a| matches!(&*a.kind, TermKind::Nat(_)))
}

/// The name the instances of a type applied to numerals are kept under
/// (`UInt@64` for `UInt(64)`): the same name each time it is asked for, so
/// that extraction finds the members of the instance by its head.
pub fn numeral_head(head: &T) -> Option<Name> {
    let TermKind::App {
        function,
        arguments,
    } = &*head.kind
    else {
        return None;
    };
    let TermKind::Var(n) = &*function.kind else {
        return None;
    };
    if !numeral_arguments(arguments) {
        return None;
    }
    let widths = arguments
        .iter()
        .map(|a| match &*a.kind {
            TermKind::Nat(w) => nat_key(w),
            _ => String::new(),
        })
        .collect::<Vec<_>>()
        .join(",");
    let label = format!("{n}@{widths}");
    Some(match n.as_global() {
        Some(owner) => owner
            .specialize(&format!("numeral-head:{widths}"), label)
            .into(),
        None => Name::from(label),
    })
}

/// The head of the instances for function types, `(A) -> R`: a spelling no
/// declaration can have.
pub(super) fn function_head() -> Name {
    Name::from("(_) -> _")
}

pub(super) fn head_name(head: &T) -> Option<Name> {
    match &*head.kind {
        TermKind::Pi { .. } => Some(function_head()),
        TermKind::Var(n) => Some(n.clone()),
        TermKind::App { function, .. } => head_name(function),
        _ => None,
    }
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
    if params.is_empty() {
        return result;
    }
    // One multi-argument Π matches a Nib call `f(a, b, c)`. Currying would
    // make the field a function of one value while projections apply all
    // method arguments at once.
    let span = result.span;
    T::new(
        TermKind::Pi {
            params: params
                .iter()
                .map(|(n, d)| (Some(n.clone()), d.clone()))
                .collect(),
            result: Box::new(result),
            effects: None,
            unused: Vec::new(),
        },
        span,
    )
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
        fn collect(stmts: &[Stmt], owners: &mut HashSet<Name>) {
            for stmt in stmts {
                match stmt {
                    Stmt::Inductive(decl) => {
                        owners.insert(decl.name.clone());
                    }
                    Stmt::Struct(decl) | Stmt::Enum(decl) => {
                        owners.insert(decl.name.clone());
                    }
                    Stmt::Mutual { items, .. } => collect(items, owners),
                    _ => {}
                }
            }
        }
        let mut owners = HashSet::new();
        collect(stmts, &mut owners);
        let owners = self.inference_owners.clone().unwrap_or(owners);
        self.class_pass_with_owners(stmts, entries, &owners)
    }

    fn class_pass_with_owners(
        &mut self,
        stmts: &[Stmt],
        entries: &mut Vec<Entry>,
        owners: &HashSet<Name>,
    ) -> Vec<Stmt> {
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
                Stmt::Instance(i) => match self.instance_decl(i, owners) {
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
                    items: self.class_pass_with_owners(items, entries, owners),
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
        let n_dicts = dicts.len();
        let mut f = f.clone();
        f.where_ = Vec::new();
        let mut params: Vec<Name> = dicts.iter().map(|(n, _)| n.clone()).collect();
        params.extend(f.params);
        f.params = params;
        f.borrows = std::iter::repeat_n(None, n_dicts)
            .chain(f.borrows)
            .collect();
        f.param_types = dicts
            .into_iter()
            .map(|(_, t)| Some(t))
            .chain(f.param_types)
            .collect();
        f.unused_params = std::iter::repeat_n(None, n_dicts)
            .chain(f.unused_params)
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
        // Only an `inductive class` is a class of the proof language; what it
        // cannot be is an error where it is declared, not a class the kernel
        // leaves to the program.
        if !c.inductive {
            return Err(Verdict::Skipped(msg!(
                "kernel-class-skipped",
                why = msg!("kernel-class-not-inductive")
            )));
        }
        let skip = |why: Message| failed(msg!("kernel-class-skipped", why = why), sp);
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
                    || !m.where_.is_empty() && self.constraints(&m.where_).is_none())
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
                        // `Bool` is the kernel's own inductive (`prelude_nat.taut`).
                        .filter(|b| **b != "Bool")
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
                // The evidence the method asks for leads its parameters, as the
                // parameters a function's `where` makes.
                let evidence = self
                    .constraints(&m.where_)
                    .map(|wheres| self.dictionaries(&wheres, false, m.span))
                    .unwrap_or_default();
                // Restore outer `&` / `&mut` on method parameters in the
                // dictionary field type. The reader splits them into
                // `borrows` + inner type; leaving the field as a bare `A`
                // made exclusive methods unify the place into the class
                // parameter (`MutIt(&mut A)` vs `MutIt(A)`) and extraction
                // then lost writes through the class path.
                let method_params: Vec<(Name, T)> = m
                    .params
                    .iter()
                    .cloned()
                    .zip(m.param_types.iter().flatten())
                    .enumerate()
                    .map(|(i, (n, ty))| {
                        (n, with_borrow_mark(ty, m.borrows.get(i).copied().flatten()))
                    })
                    .collect();
                let mut borrows = vec![None; evidence.len()];
                borrows.extend(m.borrows.iter().copied());
                if borrows.len() < evidence.len() + method_params.len() {
                    borrows.resize(evidence.len() + method_params.len(), None);
                }
                Method {
                    name: m.name.to_string(),
                    generics: m.generic_parameters(),
                    params: evidence.into_iter().chain(method_params).collect(),
                    borrows,
                    lends: m.lends.clone(),
                    result: m
                        .result
                        .as_ref()
                        .map(without_borrows)
                        .unwrap_or_else(|| unit.clone()),
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
                    binder_unused: None,
                    scrutinee: Box::new(T::var(scrutinee, sp)),
                    result: Some(Box::new(result.clone())),
                    arms: vec![MatchArm {
                        goal: None,
                        pattern: Pattern::Ctor {
                            name: mk.clone(),
                            args: (0..fields)
                                .map(|i| Pattern::Bind {
                                    name: format!("f@{i}").into(),
                                    unused: None,
                                })
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
            // Dictionary binder is never a place; method parameters keep the
            // class method's `&` / `&mut` marks for extraction.
            let mut borrows = vec![None];
            borrows.extend(m.borrows.iter().copied());
            if borrows.len() < params.len() {
                borrows.resize(params.len(), None);
            }
            out.push(Stmt::Fn(FnDecl {
                lends: m.lends.clone(),
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                ghost: false,
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
                borrows,
                params,
                param_types: types,
                result: Some(m.result.clone()),
                effects: None,
                written_effects: None,
                row_hole: None,
                where_: Vec::new(),
                span: sp,
                body,
                unused: None,
                unused_generics: Vec::new(),
                unused_params: Vec::new(),
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
                    unused: None,
                    unused_params: Vec::new(),
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

    fn instance_decl(
        &mut self,
        i: &InstanceDecl,
        owners: &HashSet<Name>,
    ) -> Result<Vec<Stmt>, Verdict> {
        let i = &InstanceDecl {
            head: i.head.clone(),
            arguments: i.arguments.clone(),
            ..i.clone()
        };
        let sp = i.span;
        let Some(class) = self.classes.classes.get(&i.class).cloned() else {
            return Err(Verdict::Skipped(msg!(
                "kernel-instance-not-class-skipped",
                name = (&i.class).to_string()
            )));
        };
        if !self.structural_instances
            && ["PartialEq", "DecEq"]
                .iter()
                .any(|c| tauto_surface::bindings::is_library(&i.class, c))
        {
            return Err(failed(
                msg!("kernel-instance-structural", name = (&i.class).to_string()),
                sp,
            ));
        }
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
            .map(|(_, ty)| type_or_type_former(ty))
            .collect();
        let infer_from = match &i.infer_from {
            Some(condition) => Some(
                inference_gate(condition, &class, &type_heads)
                    .ok_or_else(|| failed(msg!("kernel-instance-infer-condition"), sp))?,
            ),
            None => None,
        };
        if i.infer_from.as_ref().is_some_and(|condition| {
            !inference_owned(condition, &class, &all_args, owners, &i.generics)
        }) {
            return Err(failed(msg!("kernel-instance-infer-owner"), sp));
        }
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
        let inference_conflict = infer_from.as_ref().is_some_and(|new_gate| {
            self.classes
                .instances
                .iter()
                .any(|((owner, _), old_instance)| {
                    if owner != &i.class {
                        return false;
                    }
                    let Some(old_gate) = &old_instance.infer_from else {
                        return false;
                    };
                    let Some(old_keys): Option<Vec<_>> = std::iter::once(&old_instance.head)
                        .chain(&old_instance.arguments)
                        .zip(&old_instance.type_heads)
                        .map(|(argument, type_head)| {
                            self.instance_argument_key(
                                argument,
                                &old_instance.generics,
                                *type_head,
                                false,
                            )
                        })
                        .collect()
                    else {
                        return false;
                    };
                    if old_keys.len() != keys.len() {
                        return false;
                    }
                    let potentially_known: Vec<bool> = old_keys
                        .iter()
                        .zip(&keys)
                        .map(|(old, new)| old.overlaps(new))
                        .collect();
                    old_gate.holds(&potentially_known) && new_gate.holds(&potentially_known)
                })
        });
        let head = if let Some(numeral) = numeral_head(&i.head) {
            numeral
        } else if class.parameters.len() == 1 && type_heads[0] {
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
        if inference_conflict {
            return Err(failed(msg!("kernel-instance-infer-conflict"), sp));
        }
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
                    || !written.where_.is_empty() && self.constraints(&written.where_).is_none()
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
            let evidence = self
                .constraints(&written.where_)
                .map(|wheres| self.dictionaries(&wheres, false, written.span))
                .unwrap_or_default();
            let written_names: Vec<Name> = evidence
                .iter()
                .map(|(n, _)| n.clone())
                .chain(written.params.iter().cloned())
                .collect();
            if written_names.len() != m.params.len() {
                return Err(failed(
                    msg!(
                        "kernel-instance-method-params",
                        method = (&m.name).to_string(),
                        instance = &shown,
                        written = written_names.len(),
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
                        .chain(&written_names),
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
            // Keep the reader's split of `&mut T` into `borrows` + inner type.
            // Nested borrows in the result (`FiniteStep(&mut I, …)`) stay so
            // exclusive items type-check; extraction reads `borrows` to emit
            // `&mut TautoErasedValue` parameters.
            let params: Vec<(Name, T)> = evidence
                .iter()
                .cloned()
                .chain(
                    written
                        .params
                        .iter()
                        .zip(&written.param_types)
                        .map(|(n, t)| (n.clone(), t.clone()))
                        .zip(m.params.iter().skip(evidence.len()))
                        .map(|((n, t), (_, class_ty))| {
                            (
                                n,
                                t.unwrap_or_else(|| without_borrows(&inherit_type(class_ty))),
                            )
                        }),
                )
                .collect();
            // Keep borrows in the result (outer `&mut I` and nested
            // `FiniteStep(&mut I, …)`) so the mutable rewrite treats the
            // method as an item lend, not a Mut'k out-parameter function.
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
            let written_at = methods_only.len() + method_generics.len() + evidence.len();
            let mut method_borrows = vec![None; all_params.len()];
            for (i, flag) in written.borrows.iter().enumerate() {
                if let Some(slot) = method_borrows.get_mut(written_at + i) {
                    *slot = *flag;
                }
            }
            // `borrows(source)` after the result is `lends`: exclusive
            // methods that lend an item keep that clause so the mutable
            // rewrite does not turn `&mut source` into a Mut'k out.
            out.push(Stmt::Fn(FnDecl {
                lends: written.lends.clone(),
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                ghost: false,
                decreasing_by: None,
                name: fname.clone(),
                generic_types: i.generic_types.clone(),
                generics: i.generics.clone(),
                rows: vec![false; i.generics.len()],
                bounds: vec![None; i.generics.len()],
                bound_spans: Vec::new(),
                borrows: method_borrows,
                params: all_params,
                param_types: types,
                result: Some(result),
                effects: None,
                written_effects: None,
                row_hole: None,
                where_: Vec::new(),
                span: written.span,
                body: written.body.clone(),
                unused: None,
                unused_generics: Vec::new(),
                unused_params: Vec::new(),
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
                        unused_params: Vec::new(),
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
                unused: None,
                unused_params: Vec::new(),
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
                    unused_params: Vec::new(),
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
            lends: None,
            budget: None,
            vis: Default::default(),
            generates: None,
            opaque: false,
            ghost: false,
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
            written_effects: None,
            row_hole: None,
            where_: Vec::new(),
            span: sp,
            body: T::app(&constructor_name(&i.class), methods, sp),
            unused: None,
            unused_generics: Vec::new(),
            unused_params: Vec::new(),
        }));
        let has_laws = !class.laws.is_empty();
        if has_laws {
            let mut inst_args = generic_vars.clone();
            inst_args.extend(vars(&method_names));
            let all = names(&with_laws);
            out.push(Stmt::Fn(FnDecl {
                lends: None,
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                ghost: false,
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
                written_effects: None,
                row_hole: None,
                where_: Vec::new(),
                span: sp,
                body: T::app(&constructor_name(&laws_name(&i.class)), laws, sp),
                unused: None,
                unused_generics: Vec::new(),
                unused_params: Vec::new(),
            }));
            self.classes
                .globals
                .insert(laws_global.clone(), key.clone());
        }
        self.classes.instances.insert(
            key.clone(),
            Instance {
                infer_from,
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
