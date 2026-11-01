//! Classes in the proof language, read before a
//! declaration is checked. A class is a record the kernel already has, and
//! nothing here is a new rule:
//!
//! * `class C(A: Type) { fn m(…): R  law l<g>(…): P }` is `inductive C(A: Type)`
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

use std::collections::{HashMap, HashSet};

use tauto_message::{Message, msg};
use tauto_parol::Span;

use super::{Diagnostic, Entry, Kernel, T, Verdict, pi};
use crate::surface::{
    ClassDecl, Constraint, Constructor, DICT, FnDecl, InductiveDecl, InstanceDecl, MatchArm,
    Pattern, Stmt, TermKind, TheoremDecl, dictionary_name,
};

pub(super) fn is_dict(name: &str) -> bool {
    name.starts_with(DICT)
}

#[derive(Default, Clone)]
pub(super) struct Registry {
    classes: HashMap<String, Class>,
    /// `C::m` for every method and law of a class: the names a program may
    /// write as `C::m(…)`.
    members: HashSet<String>,
    methods: HashSet<String>,
    /// For each law `C::l`, how many generics it has of its own.
    laws: HashMap<String, usize>,
    /// Where each law an instance proves is written, and what is wrong if
    /// the record of the laws does not take it.
    law_spans: Vec<(Span, Message)>,
    pub(super) instances: HashMap<(String, String), Instance>,
    /// An instance's function, by name: the class and the head it is for.
    pub(super) globals: HashMap<String, (String, String)>,
}

impl Registry {
    pub(super) fn members(&self) -> &HashSet<String> {
        &self.members
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
    pub(super) fn class_names(&self) -> HashSet<String> {
        self.classes.keys().cloned().collect()
    }

    pub(super) fn is_method(&self, name: &str) -> bool {
        self.methods.contains(name)
    }

    /// The generics of the law `C::l` of its own, if it is one.
    pub(super) fn law_generics(&self, name: &str) -> Option<usize> {
        self.laws.get(name).copied()
    }
}

impl Registry {
    pub(super) fn has_laws(&self, class: &str) -> bool {
        self.classes.get(class).is_some_and(|c| !c.laws.is_empty())
    }
}

#[derive(Clone)]
struct Class {
    param: String,
    methods: Vec<Method>,
    laws: Vec<Law>,
}

#[derive(Clone)]
struct Method {
    name: String,
    params: Vec<(String, T)>,
    result: T,
}

#[derive(Clone)]
struct Law {
    name: String,
    /// The generics and the parameters: the type of the field is `∀` over all
    /// of them.
    params: Vec<(String, T)>,
    implicit: usize,
    ty: T,
}

#[derive(Clone)]
pub(super) struct Instance {
    pub(super) generics: Vec<String>,
    pub(super) head: T,
    /// The classes of the `where` and the types they are for.
    pub(super) wheres: Vec<(String, T)>,
    pub(super) global: String,
    /// The record of its laws, when the class has any.
    pub(super) laws_global: Option<String>,
    /// The laws it proves: the others are holes of its record.
    pub(super) proved: HashSet<String>,
}

pub(super) fn head_name(head: &T) -> Option<String> {
    match &*head.kind {
        TermKind::Var(n) => Some(n.clone()),
        TermKind::App { function, .. } => head_name(function),
        _ => None,
    }
}

pub(super) fn call(f: &str, args: Vec<T>, sp: Span) -> T {
    if args.is_empty() {
        T::var(f, sp)
    } else {
        T::app(f, args, sp)
    }
}

fn pis(params: &[(String, T)], result: T) -> T {
    params
        .iter()
        .rev()
        .fold(result, |acc, (n, d)| pi(n, d.clone(), acc))
}

fn failed(message: Message, span: Span) -> Verdict {
    Verdict::Failed(Diagnostic::new(message, Some(span)))
}

impl Kernel {
    /// The parameters a `where` makes: `inst@C0: C(T)`, … and, for the proofs
    /// that use laws, after each the record of the laws
    /// `inst@C0@laws: C::laws(T, inst@C0)` (a class without laws has none).
    fn dictionaries(&self, wheres: &[(String, T)], laws: bool, sp: Span) -> Vec<(String, T)> {
        let mut out = Vec::new();
        for (i, (class, ty)) in wheres.iter().enumerate() {
            let name = dictionary_name(class, i);
            out.push((name.clone(), T::app(class, vec![ty.clone()], sp)));
            if laws && self.classes.has_laws(class) {
                out.push((
                    format!("{name}@laws"),
                    T::app(
                        &format!("{class}::laws"),
                        vec![ty.clone(), T::var(&name, sp)],
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
        let mut out = Vec::new();
        for stmt in stmts {
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
                        name: format!("{}({})", i.class, crate::check::describe(&i.head)),
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
        let mut params: Vec<String> = dicts.iter().map(|(n, _)| n.clone()).collect();
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
            wheres.push((class.clone(), arguments[0].clone()));
        }
        if wheres.is_empty() {
            return t.clone();
        }
        let mut t = t.clone();
        let dicts = self.dictionaries(&wheres, true, t.span);
        t.params.splice(at..at + records, dicts);
        t
    }

    fn constraints(&self, wheres: &[Constraint]) -> Option<Vec<(String, T)>> {
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
                .map(|c| (c.class.clone(), c.ty.clone()))
                .collect(),
        )
    }

    /// `C::m` as a term of the program: a method or a law of a class.
    fn sugared(&self, stmt: &Stmt) -> Stmt {
        self.program_sugar(stmt)
    }

    fn class_decl(&mut self, c: &ClassDecl) -> Result<Vec<Stmt>, Verdict> {
        let sp = c.span;
        let skip =
            |why: Message| Verdict::Skipped(msg!("kernel-class-skipped", why = why).to_string());
        if c.arity != 1 || c.bound.as_deref().is_some_and(|b| b.contains("->")) {
            return Err(skip(msg!("kernel-class-one-param")));
        }
        if self.classes.classes.contains_key(&c.name) {
            return Err(failed(msg!("kernel-class-defined", name = &c.name), sp));
        }
        for m in &c.methods {
            if m.effects.as_ref().is_some_and(|e| !e.is_empty()) {
                return Err(if c.laws.is_empty() {
                    skip(msg!("kernel-class-method-effects", name = &m.name))
                } else {
                    failed(
                        msg!(
                            "kernel-class-effects-laws",
                            class = &c.name,
                            method = &m.name
                        ),
                        m.span,
                    )
                });
            }
            if !m.generics.is_empty() {
                return Err(skip(msg!("kernel-class-method-generics", name = &m.name)));
            }
            if m.param_types.iter().any(|t| t.is_none()) {
                return Err(skip(msg!("kernel-class-method-untyped", name = &m.name)));
            }
        }
        // The names `C::m` before the terms are read, so that the laws can
        // mention the methods.
        let names: Vec<String> = c
            .methods
            .iter()
            .map(|m| m.name.clone())
            .chain(c.laws.iter().map(|l| l.name.clone()))
            .map(|n| format!("{}::{n}", c.name))
            .collect();
        self.classes.members.extend(names.iter().cloned());
        let unit = T::var("Unit", sp);
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
                    name: m.name.clone(),
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
                    name: l.name.clone(),
                    params: t.params,
                    implicit: t.implicit,
                    ty: t.ty,
                }
            })
            .collect();
        self.classes
            .methods
            .extend(c.methods.iter().map(|m| format!("{}::{}", c.name, m.name)));
        for l in &laws {
            self.classes
                .laws
                .insert(format!("{}::{}", c.name, l.name), l.implicit);
        }
        let class = Class {
            param: c.param.clone(),
            methods,
            laws,
        };

        let dict_ty = T::app(&c.name, vec![T::var(&c.param, sp)], sp);
        let a = (c.param.clone(), T::var("Type", sp));
        let dict = format!("{DICT}{}", c.name);
        let mk = format!("{}::Mk", c.name);
        let fields: Vec<(String, T)> = class
            .methods
            .iter()
            .map(|m| {
                (
                    format!("{}::{}", c.name, m.name),
                    pis(&m.params, m.result.clone()),
                )
            })
            .collect();
        let mut out = vec![Stmt::Inductive(InductiveDecl {
            vis: Default::default(),
            generates: Default::default(),
            name: c.name.clone(),
            params: vec![a.clone()],
            sort: T::var("Type", sp),
            constructors: vec![Constructor {
                name: mk.clone(),
                implicit: 0,
                params: fields.clone(),
                result: dict_ty.clone(),
            }],
            span: sp,
        })];
        // `match record: result { mk(f@0, …) => f@i(args) }`.
        let project = |scrutinee: &str, mk: &str, fields: usize, result: &T, body: T| {
            T::new(
                TermKind::Match {
                    binder: None,
                    scrutinee: Box::new(T::var(scrutinee, sp)),
                    result: Some(Box::new(result.clone())),
                    arms: vec![MatchArm {
                        goal: None,
                        pattern: Pattern::Ctor {
                            name: mk.to_string(),
                            args: (0..fields)
                                .map(|i| Pattern::Bind(format!("f@{i}")))
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
            let args: Vec<T> = m.params.iter().map(|(n, _)| T::var(n, sp)).collect();
            let body = project(
                &dict,
                &mk,
                fields.len(),
                &m.result,
                call(&format!("f@{i}"), args, sp),
            );
            let mut params = vec![dict.clone()];
            params.extend(m.params.iter().map(|(n, _)| n.clone()));
            let mut types = vec![Some(dict_ty.clone())];
            types.extend(m.params.iter().map(|(_, t)| Some(t.clone())));
            out.push(Stmt::Fn(FnDecl {
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                decreasing_by: None,
                name: format!("{}::{}", c.name, m.name),
                generics: vec![c.param.clone()],
                rows: vec![false],
                bounds: vec![None],
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
            let laws_name = format!("{}::laws", c.name);
            let laws_mk = format!("{}::Mk", laws_name);
            let laws_ty = T::app(
                &laws_name,
                vec![T::var(&c.param, sp), T::var(&dict, sp)],
                sp,
            );
            let laws_dict = format!("{dict}@laws");
            let law_fields: Vec<(String, T)> = class
                .laws
                .iter()
                .map(|l| {
                    (
                        format!("{}::{}", c.name, l.name),
                        pis(&l.params, l.ty.clone()),
                    )
                })
                .collect();
            out.push(Stmt::Inductive(InductiveDecl {
                vis: Default::default(),
                generates: Default::default(),
                name: laws_name.clone(),
                params: vec![a.clone(), (dict.clone(), dict_ty.clone())],
                sort: T::var("Type", sp),
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
                let mut params = vec![a.clone()];
                params.extend(gens.iter().cloned());
                params.push((dict.clone(), dict_ty.clone()));
                params.push((laws_dict.clone(), laws_ty.clone()));
                params.extend(rest.iter().cloned());
                out.push(Stmt::Theorem(TheoremDecl {
                    budget: None,
                    vis: Default::default(),
                    decreasing_by: None,
                    name: format!("{}::{}", c.name, l.name),
                    implicit: 1 + l.implicit,
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

    fn instance_decl(&mut self, i: &InstanceDecl) -> Result<Vec<Stmt>, Verdict> {
        let sp = i.span;
        let Some(class) = self.classes.classes.get(&i.class).cloned() else {
            return Err(Verdict::Skipped(
                msg!("kernel-instance-not-class-skipped", name = &i.class).to_string(),
            ));
        };
        let Some(head) = head_name(&i.head) else {
            return Err(failed(msg!("kernel-instance-head", name = &i.class), sp));
        };
        let key = (i.class.clone(), head.clone());
        let shown = format!("{}({})", i.class, crate::check::describe(&i.head));
        if self.classes.instances.contains_key(&key) {
            return Err(failed(
                msg!("kernel-instance-defined", instance = &shown),
                sp,
            ));
        }
        let mut wheres = Vec::new();
        for c in &i.where_ {
            if !self.classes.classes.contains_key(&c.class) {
                return Err(failed(
                    msg!("kernel-instance-not-class", name = &c.class),
                    c.span,
                ));
            }
            wheres.push((c.class.clone(), c.ty.clone()));
        }
        // The records of the `where`: of the methods for the functions, with
        // the laws for the proofs.
        let methods_only = self.dictionaries(&wheres, false, sp);
        let with_laws = self.dictionaries(&wheres, true, sp);
        let names = |dicts: &[(String, T)]| -> Vec<String> {
            dicts.iter().map(|(n, _)| n.clone()).collect()
        };
        let vars = |names: &[String]| -> Vec<T> { names.iter().map(|n| T::var(n, sp)).collect() };
        let generics: Vec<(String, T)> = i
            .generics
            .iter()
            .map(|g| (g.clone(), T::var("Type", sp)))
            .collect();
        let generic_vars: Vec<T> = i.generics.iter().map(|g| T::var(g, sp)).collect();
        let name = |member: &str| format!("{}::{member}@{head}", i.class);
        let global = format!("{}.inst@{head}", i.class);
        let laws_global = format!("{}::laws@{head}", i.class);

        let mut out = Vec::new();
        let mut methods: Vec<T> = Vec::new();
        let mut laws: Vec<T> = Vec::new();
        let mut proved = HashSet::new();
        for m in &class.methods {
            let Some(written) = i.methods.iter().find(|w| w.name == m.name) else {
                return Err(failed(
                    msg!("kernel-instance-lacks", instance = &shown, method = &m.name),
                    sp,
                ));
            };
            if written.params.len() != m.params.len() {
                return Err(failed(
                    msg!(
                        "kernel-instance-method-params",
                        method = &m.name,
                        instance = &shown,
                        written = written.params.len(),
                        class = m.params.len()
                    ),
                    written.span,
                ));
            }
            let params: Vec<(String, T)> = written
                .params
                .iter()
                .zip(&written.param_types)
                .zip(&m.params)
                .map(|((n, t), (_, class_ty))| {
                    let t = t
                        .clone()
                        .unwrap_or_else(|| self.subst(class_ty, &class.param, &i.head));
                    (n.clone(), t)
                })
                .collect();
            let result = written
                .result
                .clone()
                .unwrap_or_else(|| self.subst(&m.result, &class.param, &i.head));
            let fname = name(&m.name);
            let mut all_params = names(&methods_only);
            all_params.extend(params.iter().map(|(n, _)| n.clone()));
            let mut types: Vec<Option<T>> =
                methods_only.iter().map(|(_, t)| Some(t.clone())).collect();
            types.extend(params.iter().map(|(_, t)| Some(t.clone())));
            out.push(Stmt::Fn(FnDecl {
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                decreasing_by: None,
                name: fname.clone(),
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
            args.extend(params.iter().map(|(n, _)| T::var(n, written.span)));
            let applied = T::app(&fname, args, written.span);
            methods.push(if params.is_empty() {
                applied
            } else {
                T::new(
                    TermKind::Lam {
                        params: params.iter().map(|(n, _)| n.clone()).collect(),
                        body: Box::new(applied),
                        types: Vec::new(),
                    },
                    written.span,
                )
            });
        }
        for w in &i.methods {
            if !class.methods.iter().any(|m| m.name == w.name) {
                return Err(failed(
                    msg!(
                        "kernel-instance-not-method",
                        name = &w.name,
                        class = &i.class
                    ),
                    w.span,
                ));
            }
        }
        for w in &i.laws {
            if !class.laws.iter().any(|l| l.name == w.name) {
                return Err(failed(
                    msg!("kernel-instance-not-law", name = &w.name, class = &i.class),
                    w.span,
                ));
            }
        }
        for l in &class.laws {
            let missing = |at: Span| T::new(TermKind::Hole(format!("law:{shown}::{}", l.name)), at);
            let Some(written) = i.laws.iter().find(|w| w.name == l.name) else {
                // Not proved: a hole, and the record of the laws is incomplete.
                laws.push(missing(sp));
                continue;
            };
            let t = &written.theorem;
            if t.params.len() != l.params.len() || t.implicit != l.implicit {
                return Err(failed(
                    msg!(
                        "kernel-instance-law-params",
                        law = &l.name,
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
                    law = &l.name,
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
        let head_ty = T::app(&i.class, vec![i.head.clone()], sp);
        let method_names = names(&methods_only);
        out.push(Stmt::Fn(FnDecl {
            budget: None,
            vis: Default::default(),
            generates: None,
            opaque: false,
            decreasing_by: None,
            name: global.clone(),
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
            body: T::app(&format!("{}::Mk", i.class), methods, sp),
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
                generics: i.generics.clone(),
                rows: vec![false; i.generics.len()],
                bounds: vec![None; i.generics.len()],
                bound_spans: Vec::new(),
                borrows: vec![None; all.len()],
                params: all,
                param_types: with_laws.iter().map(|(_, t)| Some(t.clone())).collect(),
                result: Some(T::app(
                    &format!("{}::laws", i.class),
                    vec![i.head.clone(), call(&global, inst_args, sp)],
                    sp,
                )),
                effects: None,
                where_: Vec::new(),
                span: sp,
                body: T::app(&format!("{}::laws::Mk", i.class), laws, sp),
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
