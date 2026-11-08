//! Inductive families: the declaration is checked, and its eliminators are
//! *generated* from it, never assumed.
//!
//! `inductive I(p⃗: P⃗): (i⃗: Ī) -> S { c(x⃗: X⃗): I<p⃗, t⃗> … }` gives
//!
//! * `c : ∀ p⃗ x⃗. I<p⃗, t⃗>` for each constructor;
//! * `I::ind`, the eliminator into `Prop`, and `I::rec`, the eliminator into
//!   `Type`, each
//!   `∀ p⃗ (M: ∀ i⃗ (t: I<p⃗, i⃗>). S') (minor_c…) i⃗ (t: I<p⃗, i⃗>). M i⃗ t`
//!   where `minor_c : ∀ x⃗ (ih…). M t⃗ (c p⃗ x⃗)` has an induction hypothesis for
//!   every argument whose type is `I` (under binders);
//! * the iota rule `I::rec p⃗ M m⃗ i⃗ (c p⃗ a⃗) ⟶ m_c a⃗ ih⃗`.
//!
//! A `mutual { inductive … inductive … }` group shares its parameters; each
//! family gets an eliminator whose motives and minor premises cover the whole
//! group (`I::rec p⃗ M₁…Mₙ m⃗ i⃗ t`), so recursion may pass from one family to
//! another.
//!
//! The declaration must be strictly positive and its constructors must fit
//! the family's sort. A family in `Prop` may eliminate into `Type` only when
//! it has no constructor, or one whose arguments are all proofs or appear in
//! its indices (`Eq`, `And`, `True`, `False`, but not `Or`).

use crate::surface::Name;
use std::collections::BTreeSet;
use std::collections::HashMap;
use tauto_surface::identity::Generation;

use tauto_message::msg;
use tauto_parol::Span;

use super::{Ctx, Diagnostic, Kernel, Sort, T, Verdict, describe, err, occurs, pi, sort_of};
use crate::surface::{InductiveDecl, Stmt, TermKind};

#[derive(Debug, Clone)]
pub(super) struct Ind {
    pub params: Vec<(Name, T)>,
    pub indices: usize,
    pub ctors: Vec<Ctor>,
    /// The families declared together (just this one unless `mutual`), in
    /// order, and this family's place among them.
    pub group: Vec<Name>,
    pub pos: usize,
    /// The binders of the family's indices (they may mention the parameters
    /// and earlier indices).
    pub index_tys: Vec<(Name, T)>,
    /// For a nested occurrence `J<args>` of an existing type inside the
    /// group: the type and its arguments. The member is `J<args>` itself,
    /// its constructors `J`'s with the parameters instantiated.
    pub alias: Option<(Name, Vec<T>)>,
}

#[derive(Debug, Clone)]
pub(super) struct Ctor {
    pub name: Name,
    pub args: Vec<(Name, T)>,
    /// The names the declaration gave `args`, one for each: an argument
    /// named like something in scope is renamed in `args`, but a record's
    /// field keeps the name it was written with.
    pub fields: Vec<Name>,
    /// How many leading `args` are generics, which a call or a pattern may
    /// leave out.
    pub implicit: usize,
    /// Recursive arguments: which, the binders `ys` they abstract, the
    /// family of the group they land in, and its indices.
    pub recs: Vec<Rec>,
    pub idx: Vec<T>,
    /// The arguments whose equality `no-confusion` yields (those whose type
    /// mentions no earlier argument); set once `I::noconf` exists.
    pub inj: Vec<usize>,
}

#[derive(Debug, Clone)]
pub(super) struct Rec {
    pub arg: usize,
    pub ys: Vec<(Name, T)>,
    pub fam: usize,
    pub idx: Vec<T>,
}

type RecShape = (usize, Vec<(Name, T)>, Vec<T>);

struct Fam {
    name: Name,
    ind: Ind,
    indices: Vec<(Name, T)>,
    result_idx: Vec<Vec<T>>,
    /// The type of the member's values when it is not `name` applied to the
    /// parameters (a nested occurrence).
    head: Option<T>,
}

struct Nested {
    names: Vec<Name>,
    /// (member name, the type `J`, its arguments)
    aux: Vec<(Name, Name, Vec<T>)>,
    nparams: usize,
}

pub(super) fn var(n: impl Into<Name>) -> T {
    T::var(&n.into(), Span::new(0, 0))
}

pub(super) fn app(f: T, args: Vec<T>) -> T {
    if args.is_empty() {
        return f;
    }
    let span = f.span;
    T::new(
        TermKind::App {
            function: Box::new(f),
            arguments: args,
        },
        span,
    )
}

pub(super) fn pi_all(binders: &[(Name, T)], result: T) -> T {
    binders
        .iter()
        .rev()
        .fold(result, |acc, (n, d)| pi(n, d.clone(), acc))
}

/// `∀ ys. J(p⃗, …)` applies `J` to the parameters `p⃗` themselves.
fn uniform(d: &T, params: &[(Name, T)]) -> bool {
    let mut walk = d;
    while let TermKind::Pi {
        params: binders,
        result,
        ..
    } = &*walk.kind
    {
        if params
            .iter()
            .any(|(p, _)| binders[0].0.as_deref() == Some(p.as_str()))
        {
            // A binder hides a parameter.
            return false;
        }
        walk = result;
    }
    let arguments = match &*walk.kind {
        TermKind::App { arguments, .. } => arguments.as_slice(),
        _ => &[],
    };
    arguments.len() >= params.len()
        && arguments
            .iter()
            .zip(params)
            .all(|(a, (p, _))| matches!(&*a.kind, TermKind::Var(n) if n == p))
}

impl Kernel {
    pub(super) fn inductive(&mut self, i: &InductiveDecl) -> Verdict {
        if self.classes.dictionary_family(&i.name) {
            return match self.dictionary_universe(i) {
                Ok(dictionary) => self.inductive_group(&[&dictionary]),
                Err(diagnostic) => Verdict::Failed(diagnostic),
            };
        }
        self.inductive_group(&[i])
    }

    pub(super) fn inductive_group(&mut self, decls: &[&InductiveDecl]) -> Verdict {
        let fresh: Vec<Name> = decls
            .iter()
            .filter(|d| !self.globals.contains_key(&d.name))
            .map(|d| d.name.clone())
            .collect();
        match self.inductive_inner(decls) {
            Ok(()) => Verdict::Checked { axioms: vec![] },
            Err(d) => {
                // A family registered before the error stays only for the
                // messages of later declarations, which fail if they use it.
                for n in fresh {
                    if let Some(g) = self.globals.get_mut(&n) {
                        g.failed = true;
                    }
                }
                Verdict::Failed(d)
            }
        }
    }

    fn inductive_inner(&mut self, decls: &[&InductiveDecl]) -> Result<(), Diagnostic> {
        // The group's common telescope has one set of local references.
        // Each source declaration supplies its own binders at the same positions.
        let mut aligned = Vec::new();
        if let Some(first) = decls.first() {
            for declaration in decls {
                if declaration.params.len() != first.params.len()
                    || declaration
                        .params
                        .iter()
                        .zip(&first.params)
                        .any(|((name, _), (common, _))| name.as_str() != common.as_str())
                {
                    return err(msg!("kernel-ind-group-share"), declaration.span);
                }
                let substitutions: HashMap<_, _> = declaration
                    .params
                    .iter()
                    .zip(&first.params)
                    .map(|((name, _), (common, _))| (name.clone(), common.clone()))
                    .collect();
                let mut statement = Stmt::Inductive((*declaration).clone());
                crate::surface::references::statement(&mut statement, &mut |name| {
                    if let Some(common) = substitutions.get(name) {
                        *name = common.clone();
                    }
                });
                let Stmt::Inductive(declaration) = statement else {
                    unreachable!()
                };
                aligned.push(declaration);
            }
        }
        let decls: Vec<_> = aligned.iter().collect();
        let decls = decls.as_slice();
        let names: Vec<Name> = decls.iter().map(|d| d.name.clone()).collect();
        let mut ctor_names: Vec<Name> = Vec::new();
        for d in decls {
            for c in &d.constructors {
                if super::is_reserved(&c.name) {
                    return err(
                        msg!("kernel-reserved", name = (&c.name).to_string()),
                        d.span,
                    );
                }
                let leaf = c.name.rsplit("::").next().unwrap_or(&c.name);
                let written = match d.name.rsplit_once("::") {
                    Some((module, _)) => format!("{module}::{leaf}"),
                    None => leaf.to_string(),
                };
                if names.iter().any(|name| name.as_str() == written) {
                    // Types and constructors share one namespace: `Region`
                    // cannot be both the type and a term of it.
                    return err(
                        msg!("kernel-ctor-type-name", name = leaf.to_string()),
                        d.span,
                    );
                }
                if self.globals.contains_key(&c.name)
                    || ctor_names
                        .iter()
                        .any(|name| name == &c.name || name.as_str() == c.name.as_str())
                {
                    return err(
                        msg!("kernel-already-defined", name = (&c.name).to_string()),
                        d.span,
                    );
                }
                ctor_names.push(c.name.clone());
            }
            for kind in [Generation::Induction, Generation::Recursion] {
                let g = self.resolver.generated(&d.name, kind);
                if self.globals.contains_key(&g) || ctor_names.contains(&g) {
                    return err(
                        msg!("kernel-already-defined", name = (g).to_string()),
                        d.span,
                    );
                }
            }
        }
        // A name the declaration binds must not stand for anything else in
        // the types it is used in, nor be a sort.
        let taken = |k: &Kernel, n: &Name| {
            k.globals.contains_key(n)
                || names.iter().any(|m| m == n)
                || ctor_names.iter().any(|m| m == n)
        };
        // Phase A: each family's arity, registered before any constructor is
        // read so siblings can mention each other.
        struct Head {
            params: Vec<(Name, T)>,
            indices: Vec<(Name, T)>,
            out: Sort,
        }
        let mut heads: Vec<Head> = Vec::new();
        let mut family_tys: Vec<T> = Vec::new();
        for i in decls {
            let mut params = Vec::new();
            for (n, d) in &i.params {
                if super::is_reserved(n)
                    || taken(self, n)
                    || params.iter().any(|(m, _): &(Name, T)| m == n)
                {
                    return err(
                        msg!(
                            "kernel-ind-param-name",
                            name = (n).to_string(),
                            family = (&i.name).to_string()
                        ),
                        i.span,
                    );
                }
                params.push((n.clone(), self.shape(d)?));
            }
            let sort = self.shape(&i.sort)?;
            let mut indices = Vec::new();
            let mut walk = sort.clone();
            while let TermKind::Pi { params, result, .. } = &*walk.kind {
                if let Some(n) = &params[0].0
                    && sort_of(&var(n)).is_some()
                {
                    return err(
                        msg!("kernel-ind-sort-index", name = (n).to_string()),
                        i.span,
                    );
                }
                let name = Name::from(format!("i'{}", indices.len()));
                indices.push((name.clone(), params[0].1.clone()));
                let next = match &params[0].0 {
                    Some(n) => self.subst(result, n, &var(&name)),
                    None => (**result).clone(),
                };
                walk = next;
            }
            let Some(out) = sort_of(&walk) else {
                return err(msg!("kernel-ind-ends-sort"), walk.span);
            };
            if let Some(first) = heads.first() {
                let same = first.params.len() == params.len()
                    && first.params.iter().zip(&params).enumerate().all(
                        |(position, ((n1, t1), (n2, t2)))| {
                            n1 == n2 && self.conv(&first.params[..position].to_vec(), t1, t2)
                        },
                    );
                if !same || first.out != out {
                    return err(msg!("kernel-ind-group-share"), i.span);
                }
            }
            let family = pi_all(&params, sort.clone());
            self.expect_type(&Vec::new(), &family)?;
            family_tys.push(family.clone());
            self.add(&i.name, family, None, BTreeSet::new());
            heads.push(Head {
                params,
                indices,
                out,
            });
        }
        let out = heads[0].out.clone();
        let mut nest = Nested {
            names: names.clone(),
            aux: Vec::new(),
            nparams: heads[0].params.len(),
        };

        let mut fams: Vec<Fam> = Vec::new();
        let mut types = Vec::new();
        for (pos, i) in decls.iter().enumerate() {
            let head = &heads[pos];
            let params = &head.params;
            let ctx: Ctx = params.clone();
            let mut ctors = Vec::new();
            let mut result_idx: Vec<Vec<T>> = Vec::new();
            for c in &i.constructors {
                let mut args = Vec::new();
                let mut internals: Vec<T> = Vec::new();
                let mut inner = ctx.clone();
                // Fields named like something already in scope are renamed
                // (later fields and the result follow): a field must not
                // capture a parameter, a constructor or a global in the
                // eliminator built from it.
                let mut renames: Vec<(Name, Name)> = Vec::new();
                let fields: Vec<Name> = c.params.iter().map(|(n, _)| n.clone()).collect();
                for (n, d) in &c.params {
                    if sort_of(&var(n)).is_some() {
                        return err(
                            msg!("kernel-ind-sort-field", name = (n).to_string()),
                            i.span,
                        );
                    }
                    let mut d = self.shape(d)?;
                    for (from, to) in &renames {
                        d = self.subst(&d, from, &var(to));
                    }
                    let n = &if n.spelling() == Some("_")
                        || taken(self, n)
                        || inner.iter().any(|(m, _)| m == n)
                    {
                        let fresh = self.fresh_name(n);
                        renames.push((n.clone(), fresh.clone()));
                        fresh
                    } else {
                        n.clone()
                    };
                    let d = self.elab(&inner, &d, None)?;
                    let s = self.expect_type(&inner, &d)?;
                    if out != Sort::Prop && !s.le(&out) {
                        return err(
                            msg!(
                                "kernel-ind-arg-universe",
                                name = (n).to_string(),
                                ctor = tauto_surface::surface::qualify::short(&c.name),
                                family = (&i.name).to_string()
                            ),
                            d.span,
                        );
                    }
                    // Positivity and nesting read the type as the kernel does, a product
                    // as its `Pair`; the field itself keeps the product as it is written.
                    let lowered = self.kernel_products(&d);
                    let internal = self.nest_type(&lowered, &mut nest)?;
                    self.positive(&nest.names, &internal)?;
                    inner.push((n.clone(), d.clone()));
                    args.push((n.clone(), d));
                    internals.push(internal);
                }
                let mut result = self.shape(&c.result)?;
                for (from, to) in &renames {
                    result = self.subst(&result, from, &var(to));
                }
                let result = self.elab(&inner, &result, None)?;
                let (function, arguments): (T, Vec<T>) = match &*result.kind {
                    TermKind::App {
                        function,
                        arguments,
                    } => ((**function).clone(), arguments.clone()),
                    _ => (result.clone(), vec![]),
                };
                if !matches!(&*function.kind, TermKind::Var(n) if *n == i.name)
                    || arguments.len() != params.len() + head.indices.len()
                    || arguments
                        .iter()
                        .zip(params)
                        .any(|(a, (p, _))| !matches!(&*a.kind, TermKind::Var(n) if n == p))
                {
                    return err(
                        msg!(
                            "kernel-ind-ctor-return",
                            ctor = tauto_surface::surface::qualify::short(&c.name),
                            family = (&i.name).to_string()
                        ),
                        result.span,
                    );
                }
                let idx: Vec<T> = arguments[params.len()..].to_vec();
                let mut recs = Vec::new();
                for (k, d) in internals.iter().enumerate() {
                    if let Some((fam, ys, rec_idx)) =
                        self.recursive_arg(&nest.names, params.len(), d)
                    {
                        // The eliminator's motive is for the declared
                        // parameters, so a recursive occurrence must use them.
                        if !uniform(d, params) {
                            return err(
                                msg!(
                                    "kernel-ind-rec-params",
                                    family = (&nest.names[fam]).to_string(),
                                    params = params
                                        .iter()
                                        .map(|(n, _)| n.as_str())
                                        .collect::<Vec<_>>()
                                        .join(", "),
                                    argument = (&args[k].0).to_string(),
                                    ctor = tauto_surface::surface::qualify::short(&c.name)
                                ),
                                i.span,
                            );
                        }
                        recs.push(Rec {
                            arg: k,
                            ys,
                            fam,
                            idx: rec_idx,
                        });
                    }
                }
                let ty = pi_all(params, pi_all(&args, result.clone()));
                self.expect_type(&Vec::new(), &ty)?;
                types.push((c.name.clone(), ty, i.name.clone(), ctors.len(), c.implicit));
                result_idx.push(idx.clone());
                ctors.push(Ctor {
                    name: c.name.clone(),
                    args,
                    fields,
                    implicit: c.implicit,
                    recs,
                    idx,
                    inj: Vec::new(),
                });
            }
            fams.push(Fam {
                name: i.name.clone(),
                ind: Ind {
                    params: params.clone(),
                    indices: head.indices.len(),
                    ctors,
                    group: names.clone(),
                    pos,
                    index_tys: head.indices.clone(),
                    alias: None,
                },
                indices: head.indices.clone(),
                result_idx,
                head: None,
            });
        }
        // Nested occurrences became members of the group; their constructors
        // are those of the type they stand for.
        let mut at = 0;
        while at < nest.aux.len() {
            let (member, j, jargs) = nest.aux[at].clone();
            at += 1;
            let jind = self.inds[&j].clone();
            let jnames: Vec<Name> = jind.params.iter().map(|(n, _)| n.clone()).collect();
            let mut ctors = Vec::new();
            for c in &jind.ctors {
                let mut args = Vec::new();
                let mut internals = Vec::new();
                // The fields get names of their own, so that none captures
                // a member of this group in the eliminator.
                let mut renames: Vec<(Name, Name)> = Vec::new();
                for (n, d) in &c.args {
                    let mut d = self.instantiate(d, &jnames, &jargs);
                    for (from, to) in &renames {
                        d = self.subst(&d, from, &var(to));
                    }
                    let fresh = self.fresh_name(n);
                    renames.push((n.clone(), fresh.clone()));
                    let lowered = self.kernel_products(&d);
                    let internal = self.nest_type(&lowered, &mut nest)?;
                    self.positive(&nest.names, &internal)?;
                    args.push((fresh, d));
                    internals.push(internal);
                }
                let mut recs = Vec::new();
                for (k, d) in internals.iter().enumerate() {
                    if let Some((fam, ys, rec_idx)) = self.recursive_arg(&nest.names, 0, d) {
                        recs.push(Rec {
                            arg: k,
                            ys,
                            fam,
                            idx: rec_idx,
                        });
                    }
                }
                ctors.push(Ctor {
                    name: c.name.clone(),
                    args,
                    fields: c.fields.clone(),
                    implicit: c.implicit,
                    recs,
                    idx: Vec::new(),
                    inj: Vec::new(),
                });
            }
            let pos = nest.names.iter().position(|n| *n == member).unwrap();
            fams.push(Fam {
                name: member.clone(),
                ind: Ind {
                    params: Vec::new(),
                    indices: 0,
                    ctors,
                    group: Vec::new(),
                    pos,
                    index_tys: Vec::new(),
                    alias: Some((j.clone(), jargs.clone())),
                },
                indices: Vec::new(),
                result_idx: vec![Vec::new(); jind.ctors.len()],
                head: Some(app(var(&j), jargs.clone())),
            });
        }
        if !nest.aux.is_empty() && out == Sort::Prop {
            return err(msg!("kernel-ind-nested-type"), decls[0].span);
        }
        for f in &mut fams {
            f.ind.group = nest.names.clone();
        }
        let large = out != Sort::Prop
            || match fams.as_slice() {
                [only] => self.large_elimination(&only.ind, &only.result_idx)?,
                _ => false,
            };

        // Phase C: register constructors and eliminators, under names that
        // are still free (a nested member is named after its parts).
        for f in &fams {
            for kind in [Generation::Induction, Generation::Recursion] {
                let g = self.resolver.generated(&f.name, kind);
                if self.globals.contains_key(&g) {
                    return err(
                        msg!("kernel-already-defined", name = (g).to_string()),
                        decls[0].span,
                    );
                }
            }
        }
        // The core kernel reads the declaration again on its own.
        let specs: Vec<super::core::FamSpec> = decls
            .iter()
            .zip(&family_tys)
            .map(|(d, ty)| super::core::FamSpec {
                name: d.name.clone(),
                ty: self.kernel_products(ty),
                ctors: types
                    .iter()
                    .filter(|(_, _, f, _, _)| *f == d.name)
                    .map(|(c, t, ..)| (c.clone(), self.kernel_products(t)))
                    .collect(),
            })
            .collect();
        if let Err(m) = self
            .core
            .add_inductive(&specs, heads[0].params.len(), out.clone())
        {
            return Err(super::core_rejects(&decls[0].name, m, decls[0].span));
        }

        for (name, ty, family, j, implicit) in types {
            self.add(&name, ty, None, BTreeSet::new());
            self.set_implicit(&name, fams[0].ind.params.len() + implicit);
            self.ctors.insert(name, (family, j));
        }
        for k in 0..fams.len() {
            let ind_ty = self.eliminator_type(
                &fams,
                k,
                var(&tauto_surface::bindings::library_name("Prop")),
            );
            let name = self
                .resolver
                .generated(&fams[k].name, Generation::Induction);
            self.add(&name, ind_ty, None, BTreeSet::new());
            self.set_implicit(&name, fams[k].ind.params.len());
            self.recs.insert(name, fams[k].name.clone());
            if large {
                let rec_ty = self.eliminator_type(
                    &fams,
                    k,
                    var(&tauto_surface::bindings::library_name("Type1")),
                );
                let name = self
                    .resolver
                    .generated(&fams[k].name, Generation::Recursion);
                self.add(&name, rec_ty, None, BTreeSet::new());
                self.set_implicit(&name, fams[k].ind.params.len());
                self.recs.insert(name, fams[k].name.clone());
            }
        }
        let eligible: Vec<Name> = if out != Sort::Prop {
            fams.iter()
                .filter(|f| f.ind.alias.is_none() && f.ind.indices == 0)
                .map(|f| f.name.clone())
                .collect()
        } else {
            Vec::new()
        };
        for f in fams {
            self.inds.insert(f.name, f.ind);
        }
        for family in eligible {
            self.no_confusion(&family);
        }
        // Types declared before `Eq` get theirs once it exists.
        if names.len() == 1 && tauto_surface::bindings::is_library(&names[0], "Eq") {
            let earlier: Vec<Name> = self
                .inds
                .iter()
                .filter(|(n, i)| {
                    i.indices == 0
                        && i.group.len() == 1
                        && !tauto_surface::bindings::is_library(n, "Eq")
                })
                .map(|(n, _)| n.clone())
                .collect();
            for n in earlier {
                self.no_confusion(&n);
            }
        }
        Ok(())
    }

    /// `∀ ys. J<params, idx>` for a family `J` of the group → its place in
    /// the group, the binders and the indices.
    fn recursive_arg(&mut self, families: &[Name], nparams: usize, d: &T) -> Option<RecShape> {
        // The binders get names of their own: the induction hypothesis
        // applies the field to them, under the field's name.
        let mut ys = Vec::new();
        let mut walk = d.clone();
        while let TermKind::Pi { params, result, .. } = (*walk.kind).clone() {
            let y = Name::from(format!("y'{}", ys.len()));
            ys.push((y.clone(), params[0].1.clone()));
            walk = match &params[0].0 {
                Some(n) => self.subst(&result, n, &var(&y)),
                None => *result,
            };
        }
        match &*walk.kind {
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(n) => families
                    .iter()
                    .position(|f| f == n)
                    .map(|k| (k, ys, arguments[nparams.min(arguments.len())..].to_vec())),
                _ => None,
            },
            TermKind::Var(n) => families
                .iter()
                .position(|f| f == n)
                .map(|k| (k, ys, vec![])),
            _ => None,
        }
    }

    /// `d` with the nested occurrences `J<…G…>` of a type `J` outside the
    /// group, whose arguments mention the group, replaced by members of the
    /// group standing for them (created on first use).
    fn nest_type(&mut self, d: &T, nest: &mut Nested) -> Result<T, Diagnostic> {
        let sp = d.span;
        match &*d.kind {
            TermKind::Pi { params, result, .. } => {
                let name = params[0].0.clone().unwrap_or_else(|| "_".into());
                let result = self.nest_type(result, nest)?;
                let mut out = pi(&name, params[0].1.clone(), result);
                out.span = sp;
                Ok(out)
            }
            TermKind::App {
                function,
                arguments,
            } => {
                let TermKind::Var(j) = &*function.kind else {
                    return Ok(d.clone());
                };
                let mentions = arguments
                    .iter()
                    .any(|a| nest.names.iter().any(|n| occurs(a, n)));
                if nest.names.contains(j) || !mentions || !self.inds.contains_key(j) {
                    return Ok(d.clone());
                }
                let jind = &self.inds[j];
                if nest.nparams > 0 {
                    return err(msg!("kernel-core-nested-no-params"), sp);
                }
                if jind.indices > 0 || jind.group.len() > 1 || arguments.len() != jind.params.len()
                {
                    return err(msg!("kernel-core-cannot-nest", name = (j).to_string()), sp);
                }
                let found = nest.aux.iter().find(|(_, j2, a2)| {
                    j2 == j
                        && a2.len() == arguments.len()
                        && a2
                            .iter()
                            .zip(arguments)
                            .all(|(left, right)| crate::surface::same_term_structure(left, right))
                });
                if let Some((member, _, _)) = found {
                    return Ok(var(member));
                }
                let member = self
                    .resolver
                    .generated(&nest.names[0], Generation::Nested(nest.aux.len()));
                nest.names.push(member.clone());
                nest.aux
                    .push((member.clone(), j.clone(), arguments.clone()));
                Ok(var(&member))
            }
            _ => Ok(d.clone()),
        }
    }

    pub(super) fn positive(&self, families: &[Name], d: &T) -> Result<(), Diagnostic> {
        let mentions = |t: &T| families.iter().any(|f| occurs(t, f));
        if !mentions(d) {
            return Ok(());
        }
        match &*d.kind {
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(n) if families.contains(n))
                && !arguments.iter().any(mentions) =>
            {
                Ok(())
            }
            TermKind::Var(n) if families.contains(n) => Ok(()),
            TermKind::Pi { params, result, .. } if !mentions(&params[0].1) => {
                self.positive(families, result)
            }
            _ => err(
                msg!(
                    "kernel-ind-negative",
                    families = families
                        .iter()
                        .map(Name::as_str)
                        .collect::<Vec<_>>()
                        .join("`/`"),
                    term = describe(d)
                ),
                d.span,
            ),
        }
    }

    /// Large elimination from `Prop`: no constructor, or one constructor
    /// whose every argument is a proof or occurs in the result's indices.
    fn large_elimination(&mut self, ind: &Ind, result_idx: &[Vec<T>]) -> Result<bool, Diagnostic> {
        match ind.ctors.as_slice() {
            [] => Ok(true),
            [c] => {
                let mut ctx: Ctx = ind.params.clone();
                for (n, d) in &c.args {
                    let proof = self.expect_type(&ctx, d)? == Sort::Prop;
                    let in_indices = result_idx[0]
                        .iter()
                        .any(|t| matches!(&*t.kind, TermKind::Var(v) if v == n));
                    if !proof && !in_indices {
                        return Ok(false);
                    }
                    ctx.push((n.clone(), d.clone()));
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// The type of `J::ind` (motive sort `Prop`) or `J::rec` (`Type1`) for the
    /// `k`-th family of its group: one motive per family, one minor premise
    /// per constructor of the group.
    fn eliminator_type(&mut self, fams: &[Fam], k: usize, motive_sort: T) -> T {
        let first = &fams[0].ind;
        let pvars: Vec<T> = first.params.iter().map(|(n, _)| var(n)).collect();
        let motive = |f: usize| Name::from(format!("M'{f}"));
        let mut motives = Vec::new();
        for (f, fam) in fams.iter().enumerate() {
            let ivars: Vec<T> = fam.indices.iter().map(|(n, _)| var(n)).collect();
            let major_ty = fam
                .head
                .clone()
                .unwrap_or_else(|| app(var(&fam.name), [pvars.clone(), ivars].concat()));
            motives.push((
                motive(f),
                pi_all(&fam.indices, pi("t'", major_ty, motive_sort.clone())),
            ));
        }
        let mut minors = Vec::new();
        for fam in fams {
            for (j, c) in fam.ind.ctors.iter().enumerate() {
                let avars: Vec<T> = c.args.iter().map(|(n, _)| var(n)).collect();
                let cparams = match &fam.ind.alias {
                    Some((_, a)) => a.clone(),
                    None => pvars.clone(),
                };
                let built = app(var(&c.name), [cparams, avars].concat());
                let mut ihs = Vec::new();
                for r in &c.recs {
                    let (name, _) = &c.args[r.arg];
                    let yvars: Vec<T> = r.ys.iter().map(|(n, _)| var(n)).collect();
                    let goal = app(
                        var(&motive(r.fam)),
                        [r.idx.clone(), vec![app(var(name), yvars)]].concat(),
                    );
                    ihs.push((Name::from("_"), pi_all(&r.ys, goal)));
                }
                let goal = app(
                    var(&motive(fam.ind.pos)),
                    [fam.result_idx[j].clone(), vec![built]].concat(),
                );
                minors.push((Name::from("_"), pi_all(&c.args, pi_all(&ihs, goal))));
            }
        }
        let fam = &fams[k];
        let ivars: Vec<T> = fam.indices.iter().map(|(n, _)| var(n)).collect();
        let major_ty = fam
            .head
            .clone()
            .unwrap_or_else(|| app(var(&fam.name), [pvars, ivars.clone()].concat()));
        let concl = app(var(&motive(k)), [ivars, vec![var("t'")]].concat());
        let tail = pi_all(&fam.indices, pi("t'", major_ty, concl));
        pi_all(&first.params, pi_all(&motives, pi_all(&minors, tail)))
    }

    pub(super) fn family_is_prop(&self, family: &Name) -> bool {
        let Some(g) = self.globals.get(family) else {
            return false;
        };
        let mut walk = g.ty.clone();
        while let TermKind::Pi { result, .. } = (*walk.kind).clone() {
            walk = *result;
        }
        sort_of(&walk) == Some(Sort::Prop)
    }

    /// Simultaneous substitution of `names` by `actual`.
    pub(super) fn instantiate(&mut self, t: &T, names: &[Name], actual: &[T]) -> T {
        let fresh: Vec<Name> = names.iter().map(|n| self.fresh_name(n)).collect();
        let mut out = t.clone();
        for (n, f) in names.iter().zip(&fresh) {
            out = self.subst(&out, n, &var(f));
        }
        for (f, a) in fresh.iter().zip(actual) {
            out = self.subst(&out, f, a);
        }
        out
    }
}
