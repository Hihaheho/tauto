//! Implicit arguments: the generics of a `theorem<A>`, the parameters of an
//! inductive type in its constructors and eliminators. A call that leaves
//! them out has them inferred by matching parameter types against the types
//! of explicit arguments, then the result against the expected type; when the
//! result does not depend on the explicit arguments, the expected type is
//! matched first (`implicit_call`). Matching
//! also solves an unknown applied to distinct variables by abstracting those
//! variables from the actual term. Class records are resolved from their
//! constraints. The elaborated term has every argument written, so the kernel
//! never sees an implicit one.

use super::SharedElab;
use super::classes::{call, head_name, is_dict};
use super::core::Ask;
use super::{
    Ctx, Diagnostic, Kernel, T, describe, err, expand_numeral, kernel_binders, lam, occurs, pi,
};
use crate::surface::Name;
use crate::surface::TermKind;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tauto_message::{Message, msg};
use tauto_parol::Span;

fn is_meta(n: &str) -> bool {
    n.starts_with('?')
}

/// The names of `ctx` that `t` mentions, with their types there.
fn mentioned_in(t: &T, ctx: &Ctx) -> Vec<(Name, T)> {
    super::free_vars(t)
        .into_iter()
        .filter_map(|n| {
            ctx.iter()
                .rev()
                .find(|(c, _)| *c == n)
                .map(|(_, ty)| (n, ty.clone()))
        })
        .collect()
}

/// Whether `t` mentions an unsolved unknown. A walk with a stack of its own: a
/// list literal is as deep as it is long, and recursing once per element ran
/// a small thread out of stack.
pub(super) fn has_meta(t: &T) -> bool {
    let mut todo = vec![t];
    while let Some(t) = todo.pop() {
        match &*t.kind {
            TermKind::Var(n) if is_meta(n) => return true,
            TermKind::App {
                function,
                arguments,
            } => {
                todo.push(function);
                todo.extend(arguments);
            }
            TermKind::Pi { params, result, .. } => {
                todo.push(&params[0].1);
                todo.push(result);
            }
            TermKind::Lam { body, .. } => todo.push(body),
            _ => {}
        }
    }
    false
}

/// What was found of terms by walking them, kept by the term (its `Arc`,
/// held so that the address is not reused) for the declaration being
/// checked. A call's elaborated arguments are the parts of the call it is
/// elaborated to, so a walk of the call meets what the walks of its
/// arguments found and reads it instead of walking those parts again: a
/// list literal is a call per element, and walking each call whole went
/// over the rest of the list once per element.
#[derive(Clone, Default)]
pub(super) struct TermFacts {
    /// Terms that mention no unsolved unknown.
    meta_free: HashMap<usize, T>,
    /// Terms with no hole `?h` in them.
    hole_free: HashMap<usize, T>,
    /// Calls and whether [`super::matching::has_match`] holds of them.
    matches: HashMap<usize, (T, bool)>,
    /// The free names of terms.
    free: HashMap<usize, (T, std::sync::Arc<HashSet<Name>>)>,
}

fn term_key(t: &T) -> usize {
    std::sync::Arc::as_ptr(&t.kind) as *const () as usize
}

impl TermFacts {
    /// [`has_meta`], passing over the parts found before to mention none.
    /// Only that a term mentions none is kept: a mention is found where
    /// the walk meets it.
    pub(super) fn has_meta(&mut self, t: &T) -> bool {
        let mut todo = vec![t];
        while let Some(t) = todo.pop() {
            match &*t.kind {
                TermKind::Var(n) if is_meta(n) => return true,
                TermKind::App { .. } | TermKind::Pi { .. } | TermKind::Lam { .. }
                    if self
                        .meta_free
                        .get(&term_key(t))
                        .is_some_and(|was| std::sync::Arc::ptr_eq(&was.kind, &t.kind)) => {}
                TermKind::App {
                    function,
                    arguments,
                } => {
                    todo.push(function);
                    todo.extend(arguments);
                }
                TermKind::Pi { params, result, .. } => {
                    todo.push(&params[0].1);
                    todo.push(result);
                }
                TermKind::Lam { body, .. } => todo.push(body),
                _ => {}
            }
        }
        if matches!(
            &*t.kind,
            TermKind::App { .. } | TermKind::Pi { .. } | TermKind::Lam { .. }
        ) {
            self.meta_free.insert(term_key(t), t.clone());
        }
        false
    }

    /// [`super::has_hole`], passing over the parts found before to have
    /// none.
    pub(super) fn has_hole(&mut self, t: &T) -> bool {
        let mut todo = vec![t];
        while let Some(s) = todo.pop() {
            if let TermKind::Hole(_) = &*s.kind {
                return true;
            }
            if self
                .hole_free
                .get(&term_key(s))
                .is_some_and(|was| std::sync::Arc::ptr_eq(&was.kind, &s.kind))
            {
                continue;
            }
            crate::surface::walk::visit_children(s, &mut |c| todo.push(c));
        }
        self.hole_free.insert(term_key(t), t.clone());
        false
    }

    /// [`super::matching::has_match`], a call found before read as what
    /// was found of it.
    pub(super) fn has_match(&mut self, t: &T) -> bool {
        match &*t.kind {
            // Along the spine of last arguments in a loop, as
            // `any_in_applications` goes, each call of it kept: a list
            // literal is a call per element, and the next walk of a call of
            // it stops where this one went.
            TermKind::App { .. } => {
                let mut seen = Vec::new();
                let mut found = false;
                let mut next = Some(t);
                while let Some(app) = next.take() {
                    if let Some((was, f)) = self.matches.get(&term_key(app))
                        && std::sync::Arc::ptr_eq(&was.kind, &app.kind)
                    {
                        found = *f;
                        break;
                    }
                    let TermKind::App {
                        function,
                        arguments,
                    } = &*app.kind
                    else {
                        found = self.has_match(app);
                        break;
                    };
                    seen.push(app);
                    next = arguments.last();
                    let equality = matches!(&*function.kind, TermKind::Var(op)
                        if tauto_surface::bindings::is_library(op, "==")
                            || tauto_surface::bindings::is_library(op, "!="));
                    if equality
                        || self.has_match(function)
                        || arguments[..arguments.len().saturating_sub(1)]
                            .iter()
                            .any(|a| self.has_match(a))
                    {
                        found = true;
                        break;
                    }
                }
                for app in seen {
                    self.matches.insert(term_key(app), (app.clone(), found));
                }
                found
            }
            TermKind::Lam { body, .. } => self.has_match(body),
            TermKind::Pi { params, result, .. } => {
                params.iter().any(|(_, d)| self.has_match(d)) || self.has_match(result)
            }
            _ => super::matching::has_match(t),
        }
    }

    /// The free names of `t` ([`super::free_names`]), reading those of the
    /// parts found before.
    pub(super) fn free_names(&mut self, t: &T) -> HashSet<Name> {
        let mut out = HashSet::new();
        self.free_names_in(t, &mut Vec::new(), &mut out);
        if let TermKind::App { .. } = &*t.kind {
            self.free
                .insert(term_key(t), (t.clone(), std::sync::Arc::new(out.clone())));
        }
        out
    }

    /// [`super::free_names`], a call found before read as the names found.
    /// The last argument of a call is read in a loop, not a recursion: a
    /// text literal is a `Cons` as deep as it is long.
    fn free_names_in(&self, t: &T, bound: &mut Vec<Name>, out: &mut HashSet<Name>) {
        let mut t = t;
        while let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        {
            if let Some((was, names)) = self.free.get(&term_key(t))
                && std::sync::Arc::ptr_eq(&was.kind, &t.kind)
            {
                out.extend(names.iter().filter(|n| !bound.contains(n)).cloned());
                return;
            }
            self.free_names_in(function, bound, out);
            let Some((last, rest)) = arguments.split_last() else {
                return;
            };
            for a in rest {
                self.free_names_in(a, bound, out);
            }
            t = last;
        }
        match &*t.kind {
            TermKind::App { .. } => unreachable!("read by the loop above"),
            TermKind::Pi { params, result, .. } => {
                let depth = bound.len();
                for (name, domain) in params {
                    self.free_names_in(domain, bound, out);
                    if let Some(name) = name {
                        bound.push(name.clone());
                    }
                }
                self.free_names_in(result, bound, out);
                bound.truncate(depth);
            }
            TermKind::Lam { params, body, .. } => {
                let depth = bound.len();
                bound.extend(params.iter().cloned());
                self.free_names_in(body, bound, out);
                bound.truncate(depth);
            }
            TermKind::Field { base, .. } => self.free_names_in(base, bound, out),
            TermKind::Ascribe { term, ty } => {
                self.free_names_in(term, bound, out);
                self.free_names_in(ty, bound, out);
            }
            _ => super::free_names(t, bound, out),
        }
    }
}

impl Kernel {
    /// Writes out the implicit arguments of every call in `t`. Where a type is expected (a
    /// function's argument, a `let` with its type written, a declaration's result) and `t` has
    /// it only as a subtype of products, `t` is taken to it as `(t: T)` takes it (`ascribe`):
    /// the members it asks for, a label put on or taken off. The two sides of `a = b` are not
    /// held so (`equation`): their type is the one found, not one expected.
    pub(super) fn elab(&mut self, ctx: &Ctx, t: &T, expected: Option<&T>) -> Result<T, Diagnostic> {
        let Some(shared) = self.group_shared.clone() else {
            return self.elab_node(ctx, t, expected);
        };
        // A part every member of a mutual group shares (`GroupShared`)
        // elaborates to the same term wherever it is met against the same
        // type, with the names of the context it mentions of the same types.
        let key = Arc::as_ptr(&t.kind) as *const () as usize;
        let met = {
            let s = shared.lock().unwrap();
            s.from_shape.contains(&key) || s.elaborated.contains_key(&key)
        };
        if !met || super::has_hole(t) || has_meta(t) || expected.is_some_and(has_meta) {
            return self.elab_node(ctx, t, expected);
        }
        let mentioned = mentioned_in(t, ctx);
        if mentioned.iter().any(|(_, ty)| has_meta(ty)) {
            return self.elab_node(ctx, t, expected);
        }
        let same = |e: &SharedElab| {
            let expected_same = match (&e.expected, expected) {
                (None, None) => true,
                (Some(a), Some(b)) => super::matching::same_up_to_binders(a, b),
                _ => false,
            };
            expected_same
                && e.mentioned.len() == mentioned.len()
                && e.mentioned
                    .iter()
                    .zip(&mentioned)
                    .all(|((m, a), (n, b))| m == n && super::matching::same_up_to_binders(a, b))
        };
        let found = shared.lock().unwrap().elaborated.get(&key).and_then(|es| {
            es.iter().find(|e| same(e)).map(|e| {
                (
                    e.value.clone(),
                    e.ctor_sites.clone(),
                    e.application_sites.clone(),
                )
            })
        });
        if let Some((value, ctor_sites, application_sites)) = found {
            self.ctor_sites.extend(ctor_sites);
            self.application_sites.extend(application_sites);
            return Ok(value);
        }
        let (holes, ctor_mark, app_mark) = (
            self.holes.len(),
            self.ctor_sites.len(),
            self.application_sites.len(),
        );
        let value = self.elab_node(ctx, t, expected)?;
        if self.holes.len() == holes && !has_meta(&value) {
            let entry = SharedElab {
                expected: expected.cloned(),
                mentioned,
                value: value.clone(),
                ctor_sites: self.ctor_sites[ctor_mark..].to_vec(),
                application_sites: self.application_sites[app_mark..].to_vec(),
            };
            shared
                .lock()
                .unwrap()
                .elaborated
                .entry(key)
                .or_default()
                .push(entry);
        }
        Ok(value)
    }

    fn elab_node(&mut self, ctx: &Ctx, t: &T, expected: Option<&T>) -> Result<T, Diagnostic> {
        // `@a e` for a value `e` (the family `@label.a` applied to something that is not a
        // type): the value wrapped, one application of the constructor `@label.a::Mk` with
        // the type of `e` written out.
        if let TermKind::App {
            function,
            arguments,
        } = &*t.kind
            && let TermKind::Var(f) = &*function.kind
            && super::sugar::label_of(f).is_some()
            && let [inner] = arguments.as_slice()
        {
            let saved = self.metas.clone();
            let inner_e = self.elab(ctx, inner, None);
            let inner_ty = inner_e.as_ref().ok().and_then(|i| self.infer(ctx, i).ok());
            match (inner_e, inner_ty) {
                (Ok(inner_e), Some(ty)) if super::sort_of(&self.whnf(ctx, &ty)).is_none() => {
                    let mk = T::new(TermKind::Var(super::sugar::label_constructor(f)), t.span);
                    let built = T::new(
                        TermKind::App {
                            function: Box::new(mk),
                            arguments: vec![ty, inner_e],
                        },
                        t.span,
                    );
                    return self.elab(ctx, &built, expected);
                }
                _ => self.metas = saved,
            }
        }
        let e = self.elab_inner(ctx, t, expected)?;
        let Some(want) = expected else {
            return Ok(e);
        };
        if matches!(&*e.kind, TermKind::Lam { .. } | TermKind::Pi { .. })
            || self.term_facts.has_meta(&e)
        {
            return Ok(e);
        }
        // Where the expected type alone rules an ascription out, the type
        // of `e` is not asked for: `needs_ascription` would answer no
        // whatever it is, and asking the core types the whole of `e` again
        // at each level of a nested term.
        let Some(wn) = self.ascription_ruled_out(ctx, want) else {
            return Ok(e);
        };
        let saved = self.metas.clone();
        let have = self.infer_known(ctx, &e);
        self.metas = saved;
        match have {
            Ok(have) if self.needs_ascription_at(ctx, &have, want, &wn) => {
                let taken = self.ascribe_at(None, &e, want, ctx, e.span)?;
                let taken = self.shape(&taken)?;
                // The members are taken out of the value as the `Pair` it is unfolded to.
                self.projecting += 1;
                let taken = self.elab_inner(ctx, &taken, Some(want));
                self.projecting -= 1;
                taken
            }
            _ => Ok(e),
        }
    }

    fn elab_inner(&mut self, ctx: &Ctx, t: &T, expected: Option<&T>) -> Result<T, Diagnostic> {
        let sp = t.span;
        let head = match &*t.kind {
            TermKind::App { function, .. } => function.as_ref(),
            _ => t,
        };
        if let TermKind::Var(Name::Selection(selection)) = &*head.kind {
            let wanted = expected.map(|ty| self.whnf(ctx, ty));
            let mut wanted = wanted.as_ref();
            while let Some(TermKind::Pi { result, .. }) = wanted.map(|ty| &*ty.kind) {
                wanted = Some(result);
            }
            let family = wanted.and_then(head_name);
            let candidates: Vec<Name> = selection
                .candidates()
                .iter()
                .map(|reference| Name::Global(reference.clone()))
                .filter(|reference| {
                    self.ctors.get(reference).is_some_and(|(owner, _)| {
                        family.as_ref().is_none_or(|family| owner == family)
                    })
                })
                .collect();
            if let [reference] = candidates.as_slice() {
                let kind = match &*t.kind {
                    TermKind::App {
                        function,
                        arguments,
                    } => TermKind::App {
                        function: Box::new(
                            function.with_kind(TermKind::Var(reference.clone()), function.span),
                        ),
                        arguments: arguments.clone(),
                    },
                    _ => TermKind::Var(reference.clone()),
                };
                let result = self.elab_inner(ctx, &t.with_kind(kind, sp), expected)?;
                if self.record_sites {
                    let occurrences = self
                        .ctor_site_origins
                        .get(&head.id())
                        .cloned()
                        .unwrap_or_else(|| vec![head.id()]);
                    for occurrence in occurrences {
                        self.ctor_sites.push(super::CtorSite {
                            expression: true,
                            occurrence,
                            span: head.span,
                            written: Name::Selection(selection.clone()),
                            resolved: reference.clone(),
                        });
                    }
                }
                return Ok(result);
            }
        }
        // A sort over level variables is not a call: its level is not elaborated.
        if self.core.level_sort(t).is_some() {
            return Ok(t.clone());
        }
        match &*t.kind {
            TermKind::Lam { .. } => {
                let Some(expected) = expected else {
                    return Ok(t.clone());
                };
                let expected = self.whnf(ctx, expected);
                let TermKind::Pi { .. } = &*expected.kind else {
                    return Ok(t.clone());
                };
                // A run of λs against a run of products takes the names of
                // the λs for those of the products all at once, in one walk
                // of the innermost result, not one walk of it for each λ.
                let mut inner = ctx.clone();
                let mut renames: Vec<(Name, T)> = Vec::new();
                let mut binders: Vec<(Name, Span)> = Vec::new();
                let mut here = t.clone();
                let mut want = expected.clone();
                let body = loop {
                    let (
                        TermKind::Lam {
                            params,
                            body,
                            types,
                            ..
                        },
                        TermKind::Pi {
                            params: pp, result, ..
                        },
                    ) = (&*here.kind, &*want.kind)
                    else {
                        unreachable!("a λ against a product")
                    };
                    let domain = self.subst_all(&pp[0].1, renames.clone());
                    if let Some(Some(written)) = types.first() {
                        let written = self.elab(&inner, written, None)?;
                        self.check_param_type(&params[0], &written, &domain, &inner)?;
                    }
                    let name = pp[0].0.clone().unwrap_or_else(|| "_".into());
                    // Whether the λ's name clashes is asked of the result with
                    // the names put in, so where it is one they replace, they are.
                    let put: T;
                    let result = if renames.iter().any(|(n, _)| n == &params[0]) {
                        put = self.subst_all(result, std::mem::take(&mut renames));
                        &put
                    } else {
                        &**result
                    };
                    let (x, b) = self.enter_lam(&inner, &params[0], body, &name, &domain, result);
                    inner.push((x.clone(), domain));
                    binders.push((x.clone(), here.span));
                    // Put in at once, the names must be what putting them in
                    // one after another gives: none put in is replaced later,
                    // and none replaced is put in again.
                    let apart = renames
                        .iter()
                        .all(|(n, v)| n != &name && n != &x && !occurs(v, &name));
                    let result: T = if apart {
                        if x != name {
                            renames.push((name.clone(), T::var(&x, sp)));
                        }
                        T::clone(result)
                    } else {
                        let r = self.subst_all(result, std::mem::take(&mut renames));
                        self.subst(&r, &name, &T::var(&x, sp))
                    };
                    let next = matches!(
                        (&*b.kind, &*result.kind),
                        (TermKind::Lam { params: p2, .. }, TermKind::Pi { params: q2, .. })
                            if p2.len() == 1 && q2.len() == 1
                    );
                    if next {
                        here = b;
                        want = result;
                    } else {
                        let result = self.subst_all(&result, renames.clone());
                        break self.elab(&inner, &b, Some(&result))?;
                    }
                };
                let mut out = body;
                for (x, span) in binders.into_iter().rev() {
                    out = lam(&x, out);
                    out.span = span;
                }
                Ok(out)
            }
            TermKind::Pi { params, result, .. } => {
                let name = params[0].0.clone().unwrap_or_else(|| "_".into());
                let domain = self.elab(ctx, &params[0].1, None)?;
                let (name, result) = self.enter_binder(ctx, &name, result, &[]);
                let mut inner = ctx.clone();
                inner.push((name.clone(), domain.clone()));
                let result = self.elab(&inner, &result, None)?;
                let mut out = pi(&name, domain, result);
                out.span = sp;
                Ok(out)
            }
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(op) if tauto_surface::bindings::is_library(&op, "="))
                && arguments.len() == 2
                && !ctx
                    .iter()
                    .any(|(n, _)| tauto_surface::bindings::is_library(&n, "=")) =>
            {
                self.equation(ctx, &arguments[0], &arguments[1], sp)
            }
            TermKind::Nat(_) | TermKind::App { .. }
                if let Some(expected) = expected
                    && let Some(mk) = self.machine_literal(ctx, t, expected) =>
            {
                self.elab(ctx, &mk, Some(expected))
            }
            TermKind::Nat(_) | TermKind::App { .. }
                if let Some(expected) = expected
                    && let Some(int) = self.int_literal(ctx, t, expected) =>
            {
                Ok(int)
            }
            TermKind::App { .. } if let Some(list) = self.numeral_list(ctx, t) => Ok(list),
            TermKind::App {
                function,
                arguments,
            } => self.elab_app(ctx, t, function, arguments, expected),
            // A function with no parameters of its own is called with `()`,
            // as its programs are run: the bare name is not a second
            // spelling of the call.
            TermKind::Var(g) if self.nullary_fn(ctx, g) => Err(Diagnostic::new(
                msg!("kernel-implicit-nullary", name = (g).to_string()),
                Some(sp),
            )),
            // A constructor with nothing but implicit parameters, written bare.
            TermKind::Var(g)
                if !ctx.iter().any(|(n, _)| n == g)
                    && self.globals.get(g).is_some_and(|x| {
                        let k = x.implicit + dict_count(&x.ty, x.implicit);
                        k > 0 && pi_arity(&x.ty) == k
                    }) =>
            {
                self.implicit_call(ctx, g, t, &[], &[], expected, t)
            }
            // A generic function passed as a value where a function type is
            // expected: its generics are what make its type that one
            // (`Eq::congr(list_length, e)` is `Eq::congr(list_length(A), e)`).
            // When they do not (the expected type is itself generic), it
            // stays as written.
            TermKind::Var(g) if expected.is_some() && self.bare_generic(ctx, t) => {
                let expected = self.whnf(ctx, expected.unwrap());
                if !matches!(&*expected.kind, TermKind::Pi { .. }) {
                    return Ok(t.clone());
                }
                let saved = self.metas.clone();
                let mark = self.application_sites.len();
                match self.implicit_call(ctx, g, t, &[], &[], Some(&expected), t) {
                    Ok(e) => match self.infer(ctx, &e) {
                        Ok(actual) if self.unify(ctx, &expected, &actual) => Ok(e),
                        _ => {
                            self.application_sites.truncate(mark);
                            self.metas = saved;
                            Ok(t.clone())
                        }
                    },
                    Err(_) => {
                        self.application_sites.truncate(mark);
                        self.metas = saved;
                        Ok(t.clone())
                    }
                }
            }
            _ => Ok(t.clone()),
        }
    }

    /// Whether the form of `t` leaves its type open: a numeric literal, a hole, a λ, and a
    /// constructor of a type with parameters written without arguments (`Nil`, `None`).
    pub(super) fn type_open(&self, ctx: &Ctx, t: &T) -> bool {
        match &*t.kind {
            TermKind::Nat(_) | TermKind::Float(_) | TermKind::Hole(_) | TermKind::Lam { .. } => {
                true
            }
            TermKind::Var(n) if !ctx.iter().any(|(x, _)| x == n) => {
                let open = |(family, at): &(Name, usize)| {
                    let ind = &self.inds[family];
                    let c = &ind.ctors[*at];
                    (!ind.params.is_empty() || c.implicit > 0) && c.args.len() == c.implicit
                };
                match n {
                    Name::Selection(selection) => selection.candidates().iter().any(|reference| {
                        self.ctors
                            .get(&Name::Global(reference.clone()))
                            .is_some_and(open)
                    }),
                    _ => self.ctors.get(n).is_some_and(open),
                }
            }
            // `#(a, b)` has the type `A × B` made from its components' types, so it is open
            // when one of them is.
            TermKind::App {
                function,
                arguments,
            } if arguments.len() == 2
                && matches!(&*function.kind, TermKind::Var(n)
                if !ctx.iter().any(|(x, _)| x == n)
                    && self.ctors.get(n).is_some_and(|(family, _)| {
                        tauto_surface::bindings::is_library(family, "Pair")
                    })) =>
            {
                arguments.iter().any(|x| self.type_open(ctx, x))
            }
            _ => false,
        }
    }

    /// `a = b` is `Eq(T, a, b)`, with `T` the type of `a`, or of `b` when the form of `a` leaves
    /// its type open or `a` has none to find. The other side is held to `T` by `Eq`, with no
    /// conversion between types.
    fn equation(&mut self, ctx: &Ctx, a: &T, b: &T, sp: Span) -> Result<T, Diagnostic> {
        let side = |this: &mut Self, x: &T| -> Result<(T, T), Diagnostic> {
            let x = this.elab(ctx, x, None)?;
            let ty = this.infer(ctx, &x)?;
            Ok((this.resolve(&ty), x))
        };
        let saved = self.metas.clone();
        let found = if self.type_open(ctx, a) {
            if self.type_open(ctx, b) {
                return Err(Diagnostic::new(msg!("kernel-eq-type-open"), Some(sp)));
            }
            let (ty, other) = side(self, b)?;
            (ty, a, other, true)
        } else {
            match side(self, a) {
                Ok((ty, x)) => (ty, b, x, false),
                Err(e) if self.type_open(ctx, b) => return Err(e),
                Err(e) => {
                    self.metas = saved;
                    match side(self, b) {
                        Ok((ty, x)) => (ty, a, x, true),
                        Err(_) => return Err(e),
                    }
                }
            }
        };
        let (ty, rest, done, flipped) = found;
        let rest = self.elab_inner(ctx, rest, Some(&ty))?;
        let (lhs, rhs) = if flipped { (rest, done) } else { (done, rest) };
        Ok(call(
            &tauto_surface::bindings::library_name("Eq"),
            vec![ty, lhs, rhs],
            sp,
        ))
    }

    /// A numeral where std's `Int` is expected, as its constructors write it: `3` is
    /// `IntOfNat(3)`, `-3` is `IntNegSucc(2)` (`-(n + 1)` is `IntNegSucc(n)`), and `-0` is
    /// `IntOfNat(0)`. The kernel gets the constructors and has no integers of its own.
    fn int_literal(&mut self, ctx: &Ctx, t: &T, expected: &T) -> Option<T> {
        let (negative, n) = match &*t.kind {
            TermKind::Nat(n) => (false, n),
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(op) if tauto_surface::bindings::is_library(&op, "-"))
                && let [x] = arguments.as_slice()
                && let TermKind::Nat(n) = &*x.kind =>
            {
                (true, n)
            }
            _ => return None,
        };
        let n = super::num::Num::parse(n)?;
        let ty = self.whnf(ctx, expected);
        let TermKind::Var(family) = &*ty.kind else {
            return None;
        };
        if self.resolver.source_reference("Int").as_ref() != Some(family) {
            return None;
        }
        let ind = self.inds.get(family)?;
        let ctor = |name: &str| {
            let reference = self.resolver.source_reference(name)?;
            ind.ctors
                .iter()
                .find(|c| c.name == reference)
                .filter(|c| c.args.len() == 1)
                .map(|c| c.name.clone())
        };
        let (of_nat, neg_succ) = (ctor("IntOfNat")?, ctor("IntNegSucc")?);
        if ind.ctors.len() != 2 || !ind.params.is_empty() {
            return None;
        }
        let sp = t.span;
        let (c, k) = if negative && !n.is_zero() {
            (neg_succ, n - super::num::Num::ONE)
        } else {
            (of_nat, n)
        };
        Some(call(&c, vec![T::new(TermKind::Nat(k.to_string()), sp)], sp))
    }

    /// A list of numerals ending in `Nil(Nat)`, as a text literal's bytes are
    /// written (`check/sugar.rs`), with `Nat` written out in each `Cons`.
    /// Elaborating it a `Cons` at a time types each tail again, which takes
    /// time and memory growing with the square of the length; its type is
    /// known from the end, so it is written out in one pass. The kernel gets
    /// the term elaboration would make and types it once.
    fn numeral_list(&self, ctx: &Ctx, t: &T) -> Option<T> {
        let global = |n: &Name| !ctx.iter().any(|(m, _)| m == n);
        let ctor = |n: &Name, arity: usize| {
            global(n)
                && self
                    .globals
                    .get(n)
                    .is_some_and(|g| g.implicit == 1 && pi_arity(&g.ty) == arity)
        };
        if !(global(&tauto_surface::bindings::library_name("Nat"))
            && ctor(&tauto_surface::bindings::library_name("Cons"), 3)
            && ctor(&tauto_surface::bindings::library_name("Nil"), 1))
        {
            return None;
        }
        let mut heads = Vec::new();
        let mut at = t;
        loop {
            let TermKind::App {
                function,
                arguments,
            } = &*at.kind
            else {
                return None;
            };
            match (&*function.kind, arguments.as_slice()) {
                (TermKind::Var(c), [head, tail])
                    if tauto_surface::bindings::is_library(&c, "Cons")
                        && matches!(&*head.kind, TermKind::Nat(_)) =>
                {
                    heads.push((at, function, head));
                    at = tail;
                }
                (TermKind::Var(c), [ty])
                    if tauto_surface::bindings::is_library(&c, "Nil")
                        && matches!(&*ty.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(&n, "Nat")) =>
                {
                    break;
                }
                _ => return None,
            }
        }
        if heads.is_empty() {
            return None;
        }
        let mut list = at.clone();
        for (node, function, head) in heads.into_iter().rev() {
            list = T::new(
                TermKind::App {
                    function: function.clone(),
                    arguments: vec![
                        T::var(&tauto_surface::bindings::library_name("Nat"), node.span),
                        head.clone(),
                        list,
                    ],
                },
                node.span,
            );
        }
        Some(list)
    }

    /// `t` is the bare name of a global with generics or class records
    /// before parameters of its own.
    fn bare_generic(&self, ctx: &Ctx, t: &T) -> bool {
        let TermKind::Var(g) = &*t.kind else {
            return false;
        };
        !ctx.iter().any(|(n, _)| n == g)
            && self.globals.get(g).is_some_and(|x| {
                let k = x.implicit + dict_count(&x.ty, x.implicit);
                k > 0 && pi_arity(&x.ty) > k
            })
    }

    /// The type of `g` and how many of its leading parameters are implicit:
    /// a global, or a function being defined (typed as a variable in `ctx`),
    /// whose recursive calls leave the generics out like any other call.
    fn implicit_sig(&self, ctx: &Ctx, g: &Name) -> Option<(T, usize)> {
        if let Some((_, ty)) = ctx.iter().rev().find(|(n, _)| n == g) {
            let k = self.defining_implicit.iter().find(|(n, _)| n == g)?.1;
            return self
                .defining
                .iter()
                .any(|(n, t)| n == g && t == ty)
                .then(|| (ty.clone(), k));
        }
        self.globals.get(g).map(|x| (x.ty.clone(), x.implicit))
    }

    fn note_application(&mut self, source: &T, written: usize, arguments: &[T], callee: &Name) {
        if self.record_sites {
            let occurrences = self
                .ctor_site_origins
                .get(&source.id())
                .cloned()
                .unwrap_or_else(|| vec![source.id()]);
            let arguments: Vec<_> = arguments
                .iter()
                .map(|t| as_written(self.resolve(t)))
                .collect();
            for occurrence in occurrences {
                self.application_sites.push(super::ApplicationSite {
                    span: source.span,
                    occurrence,
                    callee: match self.application_heads.get(&occurrence) {
                        Some(name @ Name::Local(_)) => name.clone(),
                        _ => callee.clone(),
                    },
                    written,
                    omitted: arguments.len(),
                    arguments: arguments.clone(),
                });
            }
        }
    }

    fn elab_app(
        &mut self,
        ctx: &Ctx,
        whole: &T,
        function: &T,
        arguments: &[T],
        expected: Option<&T>,
    ) -> Result<T, Diagnostic> {
        let out = self.elab_app_inner(ctx, whole, function, arguments, expected)?;
        if self.record_sites {
            let mut head = &out;
            let mut spine = Vec::new();
            while let TermKind::App {
                function,
                arguments,
            } = &*head.kind
            {
                spine.push(arguments.as_slice());
                head = function;
            }
            let arguments_out: Vec<_> = spine.into_iter().rev().flatten().cloned().collect();
            if let (TermKind::Var(a), TermKind::Var(b)) = (&*function.kind, &*head.kind)
                && a == b
                && !matches!(arguments.first().map(|t| &*t.kind), Some(TermKind::Record { name, .. })
                    if name.spelling() == Some(tauto_surface::IMPLICITS))
                && let Some(omitted) = arguments_out.len().checked_sub(arguments.len())
            {
                self.note_application(whole, arguments.len(), &arguments_out[..omitted], a);
            }
        }
        Ok(out)
    }

    fn elab_app_inner(
        &mut self,
        ctx: &Ctx,
        whole: &T,
        function: &T,
        arguments: &[T],
        expected: Option<&T>,
    ) -> Result<T, Diagnostic> {
        let sp = whole.span;
        // `f(<x: v>, h)`: the implicit arguments named are carried first, as a
        // record of the internal name `IMPLICITS`.
        let (named, explicit) = match arguments.split_first() {
            Some((first, rest)) => match &*first.kind {
                TermKind::Record { name, fields, .. }
                    if name.spelling() == Some(tauto_surface::IMPLICITS) =>
                {
                    (Some((first, fields.as_slice())), rest)
                }
                _ => (None, arguments),
            },
            None => (None, arguments),
        };
        // A constructor without fields is written without `()`, as `Nil` is.
        if arguments.is_empty()
            && let TermKind::Var(g) = &*function.kind
            && !ctx.iter().any(|(n, _)| n == g)
            && !g.contains(['@', '\''])
            && self.ctors.contains_key(g)
        {
            return Err(Diagnostic::new(
                format!("`{g}` is a constructor without fields: write `{g}`, without `()`"),
                Some(sp),
            ));
        }
        if let TermKind::Var(g) = &*function.kind
            && let Some((ty, implicit)) = self.implicit_sig(ctx, g)
            && implicit + dict_count(&ty, implicit) > 0
        {
            let arity = match self.globals.get(g) {
                Some(global) if !ctx.iter().any(|(n, _)| n == g) => {
                    global.params.unwrap_or_else(|| pi_arity(&ty))
                }
                _ => pi_arity(&ty),
            };
            let k = implicit + dict_count(&ty, implicit);
            if explicit.len() + k == arity {
                // A function value with its hidden arguments already filled
                // may have the same arity as a source call with those
                // arguments omitted. Retain the checked function value.
                if explicit.len() == k
                    && named.is_none()
                    && !whole.is_written_call()
                    && let Some(want) = expected
                    && matches!(&*self.whnf(ctx, want).kind, TermKind::Pi { .. })
                    && let Ok(actual) = self.infer_known(ctx, whole)
                    && self.conv(ctx, &actual, want)
                {
                    return Ok(whole.clone());
                }
                let fields = named.map_or(&[][..], |(_, fields)| fields);
                return self.implicit_call(ctx, g, function, explicit, fields, expected, whole);
            }
            // Arguments past the declared ones apply the call's result:
            // `f(a, h)` is `f(a)(h)`. The source writes implicit arguments
            // only by name (`f(<x: v>, a)`); a term the checker builds writes
            // every argument out, `f(u, A, m, x)` being `f(u, A, m)(x)`, and
            // that reading is tried first for it.
            if arity >= k && explicit.len() + k > arity {
                let applied_at = |at: usize| {
                    let (first, rest) = explicit.split_at(at);
                    let call = T::new(
                        TermKind::App {
                            function: Box::new(function.clone()),
                            arguments: named
                                .map(|(r, _)| r.clone())
                                .into_iter()
                                .chain(first.iter().cloned())
                                .collect(),
                        },
                        sp,
                    );
                    T::new(
                        TermKind::App {
                            function: Box::new(call),
                            arguments: rest.to_vec(),
                        },
                        sp,
                    )
                };
                let applied = applied_at(arity - k);
                // A call the source wrote, in a file or in a macro's quote; a term
                // the checker or the class expansion builds is not marked as one,
                // and may still write every argument out.
                let written = whole.is_written_call();
                if written && named.is_none() && arguments.len() >= arity {
                    let saved = self.metas.clone();
                    let app_mark = self.application_sites.len();
                    // Past the declared arguments, the rest apply the result: when
                    // that reading fails, the arguments read as implicit ones
                    // passed by position, which is never accepted, and what is
                    // wrong with the call under that reading is said with it.
                    if let Ok(t) = self.elab(ctx, &applied, expected) {
                        return Ok(t);
                    }
                    self.application_sites.truncate(app_mark);
                    self.metas = saved.clone();
                    let mut d = Diagnostic::new(
                        msg!("kernel-implicit-positional", name = (g).to_string()),
                        Some(sp),
                    );
                    let read = if arguments.len() == arity {
                        self.plain_app(ctx, whole, function, arguments, expected)
                    } else {
                        self.elab(ctx, &applied_at(arity), expected)
                    };
                    match read.and_then(|t| self.infer(ctx, &t)) {
                        Err(e) => d.also.push(e),
                        Ok(found) => {
                            if let Some(want) = expected
                                && !self.conv(ctx, &found, want)
                            {
                                let m = self.mismatch_diag(ctx, want, &found, sp);
                                d.also.push(m);
                            }
                        }
                    }
                    self.application_sites.truncate(app_mark);
                    self.metas = saved;
                    return Err(d);
                }
                if named.is_some() || written || arguments.len() < arity {
                    return self.elab(ctx, &applied, expected);
                }
                let saved = self.metas.clone();
                let app_mark = self.application_sites.len();
                let written_out = if arguments.len() == arity {
                    self.plain_app(ctx, whole, function, arguments, expected)
                } else {
                    self.elab(ctx, &applied_at(arity), expected)
                };
                // Typed as a part the terms around it read as an atom of the
                // type found (`infer_known`), so they do not type it again.
                match written_out.and_then(|t| self.infer_known(ctx, &t).map(|_| t)) {
                    Ok(t) => return Ok(t),
                    Err(e) => {
                        self.application_sites.truncate(app_mark);
                        self.metas = saved.clone();
                        return self.elab(ctx, &applied, expected).map_err(|_| {
                            self.metas = saved;
                            e
                        });
                    }
                }
            }
            if named.is_some() {
                return err(
                    msg!(
                        "kernel-implicit-named-partial",
                        name = (g).to_string(),
                        count = arity.saturating_sub(k)
                    ),
                    sp,
                );
            }
        }
        if let Some((_, fields)) = named {
            // A recursive call under a match goes through the induction
            // hypothesis, whose leading parameters are the function's
            // implicit ones under their names: the values are put in that order.
            if let TermKind::Var(g) = &*function.kind
                && let Some((_, ty)) = ctx.iter().rev().find(|(n, _)| n == g)
            {
                let mut order: Vec<String> = Vec::new();
                let ty = ty.clone();
                let mut t = self.whnf(ctx, &ty);
                while order.len() < fields.len() {
                    let TermKind::Pi {
                        params,
                        result,
                        effects,
                        ..
                    } = (*t.kind).clone()
                    else {
                        break;
                    };
                    let Some(n) = params[0].0.clone() else { break };
                    // A renamed binder reads `R'12`: the name written is before the `'`.
                    let shown = n.to_string();
                    let base = match shown.rsplit_once('\'') {
                        Some((base, n)) if n.chars().all(|c| c.is_ascii_digit()) => {
                            base.to_string()
                        }
                        _ => shown,
                    };
                    order.push(base);
                    t = if params.len() > 1 {
                        T::new(
                            TermKind::Pi {
                                params: params[1..].to_vec(),
                                result,
                                effects,
                                unused: Vec::new(),
                            },
                            t.span,
                        )
                    } else {
                        (*result).clone()
                    };
                }
                let values: Option<Vec<T>> = order
                    .iter()
                    .map(|n| {
                        fields
                            .iter()
                            .find(|(f, _)| f.as_str() == n.as_str())
                            .map(|(_, v)| v.clone())
                    })
                    .collect();
                if let Some(values) = values
                    && values.len() == fields.len()
                {
                    let all: Vec<T> = values.into_iter().chain(explicit.iter().cloned()).collect();
                    return self.plain_app(ctx, whole, function, &all, expected);
                }
            }
            return err(msg!("kernel-implicit-named-none"), sp);
        }
        self.plain_app(ctx, whole, function, arguments, expected)
    }

    /// `t` with the values of `pending` for their names at once
    /// ([`Kernel::subst_all`]), the free names of the values (which a binder of
    /// `t` would capture) taken from `pending` rather than found again.
    fn subst_pending(&mut self, t: &T, pending: &super::Subs) -> T {
        self.subst_with(t, pending)
    }

    /// [`Self::infer_head`], the parts of `t` the core has typed before read
    /// as atoms of the values and types it gave them, and `t`'s own type kept for the
    /// terms around it. Where reading so does not type, `t` is typed whole.
    fn infer_known(&mut self, ctx: &Ctx, t: &T) -> Result<T, Diagnostic> {
        if matches!(&*t.kind, TermKind::Var(_))
            || self.term_facts.has_hole(t)
            || self.term_facts.has_meta(t)
        {
            return self.infer_head(ctx, t);
        }
        // Typed before in the same context (a call is typed where it is
        // written out, and again where it is an argument): the type found.
        let key = std::sync::Arc::as_ptr(&t.kind) as *const () as usize;
        if let Some((was, at, ty)) = self.core.known.get(&key)
            && std::sync::Arc::ptr_eq(&was.kind, &t.kind)
            && at.len() == ctx.len()
            && at.iter().copied().eq(super::core::ctx_addresses(ctx))
        {
            return Ok(ty.clone());
        }
        let fast = self.infer_quiet(ctx, t);
        let ty = match fast {
            Some(ty) => ty,
            None => self.infer_head(ctx, t)?,
        };
        if !self.term_facts.has_meta(&ty) {
            // Parts typed one after another in the same context share its
            // addresses (`Core::known_at`).
            let at = match &self.core.known_at {
                Some(at) if at.iter().copied().eq(super::core::ctx_addresses(ctx)) => at.clone(),
                _ => {
                    let at: std::sync::Arc<[usize]> = super::core::ctx_addresses(ctx).collect();
                    self.core.known_at = Some(at.clone());
                    at
                }
            };
            let key = std::sync::Arc::as_ptr(&t.kind) as *const () as usize;
            self.core.known.insert(key, (t.clone(), at, ty.clone()));
        }
        Ok(ty)
    }

    /// The type of `t` with its known parts read as atoms, or nothing where
    /// it does not type so read (no diagnostic is made: `t` is then typed
    /// whole).
    fn infer_quiet(&mut self, ctx: &Ctx, t: &T) -> Option<T> {
        kernel_binders(t, &mut self.core.binders_checked).ok()?;
        let current = self.current.clone();
        let avoid: Vec<&str> = current.as_deref().into_iter().collect();
        let globals = &self.globals;
        let declared = |n: &Name| globals.get(n).map(|g| g.ty.clone());
        self.core.use_known = true;
        let typed = self.core.type_in(ctx, t, Ask::Infer, &declared, &avoid);
        self.core.use_known = false;
        typed.ok().and_then(|typed| typed.ty)
    }

    /// The type of `t`, as `infer` gives it. A global's type is asked once
    /// while it stays the same: it has no local variable in it, so it does
    /// not depend on the context it is asked in, and the entry is kept with
    /// the global's own type it was found for.
    fn infer_head(&mut self, ctx: &Ctx, t: &T) -> Result<T, Diagnostic> {
        let TermKind::Var(g) = &*t.kind else {
            return self.infer(ctx, t);
        };
        if ctx.iter().any(|(n, _)| n == g) {
            return self.infer(ctx, t);
        }
        let Some(declared) = self.globals.get(g).map(|d| d.ty.clone()) else {
            return self.infer(ctx, t);
        };
        if let Some((was, ty)) = self.head_types.get(g)
            && std::sync::Arc::ptr_eq(&was.kind, &declared.kind)
        {
            return Ok(ty.clone());
        }
        let ty = self.infer(ctx, t)?;
        self.head_types.insert(g.clone(), (declared, ty.clone()));
        Ok(ty)
    }

    fn plain_app(
        &mut self,
        ctx: &Ctx,
        whole: &T,
        function: &T,
        arguments: &[T],
        expected: Option<&T>,
    ) -> Result<T, Diagnostic> {
        let sp = whole.span;
        // `(x => b)(a, …)`, as the type of an eliminator's value has it
        // (its motive applied): `b` with `a` for `x`.
        if let TermKind::Lam {
            params,
            body,
            types,
            ..
        } = &*function.kind
            && let Some((a, rest)) = arguments.split_first()
        {
            // A chain of them, `(x => (y => c)(e))(a)` as a `let` after
            // another has it, is taken one redex at a time, each argument
            // checked as it is met (with the values before it put in), and
            // the values wait (`pending`) to be put into the body once, where
            // the chain ends: putting each into the whole rest of the chain
            // walks it once per `let`.
            let mut pending = super::Subs::waiting();
            let (mut params, mut body, mut types, mut a, mut rest, mut fspan, mut sp) =
                (params, body, types, a, rest, function.span, sp);
            loop {
                let mut a_in = self.subst_pending(a, &pending);
                // The argument is checked before it is put in: if `x` does not occur
                // in `b`, the substitution drops `a`, and `a` would not be checked at all.
                let domain = types
                    .first()
                    .cloned()
                    .flatten()
                    .map(|d| self.subst_pending(&d, &pending));
                // The written argument is what is put in (the result is elaborated as a
                // whole); its elaboration here is only the check.
                let saved = self.metas.clone();
                let checked = self.elab(ctx, &a_in, domain.as_ref()).and_then(|e| {
                    if matches!(&*e.kind, TermKind::Lam { .. } | TermKind::Hole(_))
                        || self.term_facts.has_meta(&e)
                    {
                        Ok(())
                    } else {
                        self.infer(ctx, &e).map(|_| ())
                    }
                });
                self.metas = saved;
                checked?;
                let mut free = self.term_facts.free_names(&a_in);
                // The next redex of the chain is taken with this value
                // waiting only when nothing else is in between and its
                // binder captures none of the values.
                if params.len() == 1
                    && rest.is_empty()
                    && pending.defers_under(Some(&params[0]))
                    && let TermKind::App {
                        function: f2,
                        arguments: args2,
                    } = &*body.kind
                    && let TermKind::Lam {
                        params: p2,
                        body: b2,
                        types: t2,
                        ..
                    } = &*f2.kind
                    && p2.len() == 1
                    && let Some((a2, r2)) = args2.split_first()
                    // With this value waiting too: `p2` is not its name and
                    // captures none of its free names.
                    && pending.defers_under(Some(&p2[0]))
                    && params[0] != p2[0]
                    && !free.contains(&p2[0])
                {
                    pending.push(params[0].clone(), a_in, &free);
                    (params, body, types, a, rest, fspan, sp) =
                        (p2, b2, t2, a2, r2, f2.span, body.span);
                    continue;
                }
                let rest: Vec<T> = rest
                    .iter()
                    .map(|r| self.subst_pending(r, &pending))
                    .collect();
                pending.push(params[0].clone(), a_in, &free);
                let mut inner = self.subst_pending(body, &pending);
                if params.len() > 1 {
                    inner = T::new(
                        TermKind::Lam {
                            params: params[1..].to_vec(),
                            body: Box::new(inner),
                            types: types.get(1..).map(<[_]>::to_vec).unwrap_or_default(),
                            unused_params: Vec::new(),
                        },
                        fspan,
                    );
                }
                if !rest.is_empty() {
                    inner = T::new(
                        TermKind::App {
                            function: Box::new(inner),
                            arguments: rest,
                        },
                        sp,
                    );
                }
                return self.elab(ctx, &inner, expected);
            }
        }
        let function = match &*function.kind {
            TermKind::Var(_) => function.clone(),
            _ => self.elab(ctx, function, None)?,
        };
        let mut ty = self.infer_head(ctx, &function)?;
        let mut out = Vec::new();
        // The arguments wait to be put into the rest of the type, which is
        // then walked once for all of them, not once for each: only the
        // domain of the next parameter is read before that.
        let mut pending = super::Subs::waiting();
        for arg in arguments {
            let deferred = match &*ty.kind {
                TermKind::Pi { params, result, .. }
                    if params.len() == 1 && pending.defers_under(params[0].0.as_ref()) =>
                {
                    Some((params[0].clone(), (**result).clone()))
                }
                _ => None,
            };
            if let Some(((name, domain), result)) = deferred {
                let domain = self.subst_pending(&domain, &pending);
                let arg = self.elab(ctx, arg, Some(&domain))?;
                let free = self.term_facts.free_names(&arg);
                pending.push(name.unwrap_or_else(|| "_".into()), arg.clone(), &free);
                ty = result;
                out.push(arg);
                continue;
            }
            ty = self.subst_pending(&ty, &pending);
            pending = super::Subs::waiting();
            let whnf = self.whnf(ctx, &ty);
            match &*whnf.kind {
                TermKind::Pi { params, result, .. } => {
                    let name = params[0].0.clone().unwrap_or_else(|| "_".into());
                    let arg = self.elab(ctx, arg, Some(&params[0].1))?;
                    ty = self.subst(result, &name, &arg);
                    out.push(arg);
                }
                _ => out.push(self.elab(ctx, arg, None)?),
            }
        }
        Ok(T::new(
            TermKind::App {
                function: Box::new(function),
                arguments: out,
            },
            sp,
        ))
    }

    fn implicit_call(
        &mut self,
        ctx: &Ctx,
        g: &Name,
        function: &T,
        arguments: &[T],
        named: &[(String, T)],
        expected: Option<&T>,
        whole: &T,
    ) -> Result<T, Diagnostic> {
        let sp = function.span;
        let Some((mut ty, implicit)) = self.implicit_sig(ctx, g) else {
            return err(
                msg!("kernel-implicit-not-defined", name = (g).to_string()),
                sp,
            );
        };
        let k = implicit + dict_count(&ty, implicit);
        let mut metas = Vec::new();
        let mut names: Vec<Name> = Vec::new();
        // The records of the classes a call needs (`check/classes.rs`): not
        // matched against an argument but found once the types are known.
        let mut dicts: Vec<(Name, T)> = Vec::new();
        let mut params_of: Vec<T> = Vec::new();
        for i in 0..k {
            let TermKind::Pi { params, result, .. } = (*ty.kind).clone() else {
                return err(
                    msg!("kernel-implicit-fewer-params", name = (g).to_string()),
                    sp,
                );
            };
            let name = params[0].0.clone().unwrap_or_else(|| "_".into());
            let m = self.fresh_name("?");
            self.metas.insert(m.clone(), None);
            if i >= implicit {
                dicts.push((m.clone(), params[0].1.clone()));
            }
            if i < implicit {
                params_of.push(params[0].1.clone());
            }
            ty = self.subst(&result, &name, &T::var(&m, sp));
            names.push(name);
            metas.push(m);
        }
        // The implicit arguments written by name fix their metavariables
        // before anything is inferred.
        // `C(T)::m(…)`: the class's arguments, by their places, lead the
        // generics of its methods and laws.
        let class_arity = self
            .classes
            .member_owners
            .get(g)
            .map(|class| self.classes.arity(class));
        let given = named
            .iter()
            .filter(|(f, _)| tauto_surface::class_argument_index(f).is_some())
            .count();
        if given > 0 && class_arity != Some(given) {
            return err(
                match class_arity {
                    None => msg!("kernel-class-member-not-method", name = g.to_string()),
                    Some(arity) => msg!(
                        "kernel-class-member-argument-count",
                        name = g.to_string(),
                        expected = arity.to_string(),
                        given = given.to_string()
                    ),
                },
                sp,
            );
        }
        for (field, value) in named {
            let place = match tauto_surface::class_argument_index(field) {
                Some(i) => Some(i).filter(|i| *i < implicit),
                None => names[..implicit]
                    .iter()
                    .position(|n| n.as_str() == field.as_str()),
            };
            let Some(i) = place else {
                return err(
                    msg!(
                        "kernel-implicit-named-unknown",
                        name = (g).to_string(),
                        field = field.clone()
                    ),
                    value.span,
                );
            };
            if named.iter().filter(|(f, _)| f == field).count() > 1 {
                return err(
                    msg!("kernel-implicit-named-twice", field = field.clone()),
                    value.span,
                );
            }
            let want = self.resolve(&params_of[i]);
            let value = self.elab(ctx, value, Some(&want))?;
            if !self.unify(ctx, &T::var(&metas[i], sp), &value) {
                return err(
                    msg!(
                        "kernel-implicit-named-mismatch",
                        name = (g).to_string(),
                        field = field.clone()
                    ),
                    value.span,
                );
            }
        }
        let base = ty.clone();
        // The expected type is matched first when the result does not depend
        // on the explicit arguments: an argument whose type is only
        // definitionally equal to what the parameter wants (`walk(acc, l)`
        // against `walk(dbl(acc), t)`, which `walk(acc, Cons(a, t))` reduces
        // to) would otherwise fix the generics to the wrong terms. If the
        // arguments do not check against what the expected type fixed, the
        // generics are inferred from the arguments alone.
        let start = self.metas.clone();
        let expected_first = self.unify_result_first(ctx, &base, arguments.len(), expected);
        let attempts = 1 + usize::from(expected_first);
        let mut outcome = Ok(T::var(g, sp));
        // An argument that failed against a type with no unknowns fails the
        // same way when the generics are inferred again from the arguments:
        // the second attempt stops there with the first error. Without this,
        // every call of a chain such as `Cons(a, Cons(b, …))` above an
        // ill-typed argument tries its tail twice, which doubles the work at
        // each level.
        let mut failed: Option<(usize, T, Diagnostic)> = None;
        for attempt in 0..attempts {
            let application_mark = self.application_sites.len();
            if attempt == 1 {
                self.metas = start.clone();
            }
            let mut out: Vec<T> = Vec::new();
            outcome = self
                .implicit_arguments(
                    ctx,
                    (g, sp, whole.span),
                    arguments,
                    expected,
                    Unknowns {
                        metas: &metas,
                        names: &names,
                        dicts: &dicts,
                        implicit,
                    },
                    &base,
                    &mut out,
                    &mut failed,
                )
                .map(|mut args| {
                    self.note_application(whole, arguments.len(), &args, g);
                    args.extend(out);
                    self.direct_member(g, &args, sp).unwrap_or_else(|| {
                        // The call as written, so that an error in it can
                        // point at all of it.
                        T::new(
                            TermKind::App {
                                function: Box::new(function.clone()),
                                arguments: args,
                            },
                            whole.span,
                        )
                    })
                });
            // What the expected type fixed has to be what the arguments
            // have: the call is checked before it is kept.
            let last = attempt + 1 == attempts;
            match &outcome {
                Ok(call) if !last => {
                    let call = call.clone();
                    if self.infer(ctx, &call).is_ok() {
                        break;
                    }
                }
                Ok(_) => break,
                Err(_) => {}
            }
            self.application_sites.truncate(application_mark);
        }
        for m in &metas {
            self.metas.remove(m);
        }
        outcome
    }

    /// Unifies the result of a call's type (`ty`, its implicit parameters
    /// already metavariables) with `expected`, when that result does not
    /// mention the `explicit` parameters. Leaves the metavariables as they
    /// were and says false when it does not apply or does not unify.
    fn unify_result_first(
        &mut self,
        ctx: &Ctx,
        ty: &T,
        explicit: usize,
        expected: Option<&T>,
    ) -> bool {
        let Some(expected) = expected else {
            return false;
        };
        if has_meta(expected) {
            return false;
        }
        let mut result = ty;
        let mut bound = Vec::new();
        for _ in 0..explicit {
            let TermKind::Pi {
                params, result: r, ..
            } = &*result.kind
            else {
                return false;
            };
            if let Some(n) = &params[0].0 {
                bound.push(n.clone());
            }
            result = r;
        }
        if !has_meta(result) || bound.iter().any(|n| occurs(result, n)) {
            return false;
        }
        let result = result.clone();
        // The expected type of a match arm is the motive applied to the
        // pattern (`(t => A)(Succ(k))`): applied, so a generic filled in from
        // it is `A` itself, which a recursive call has to pass unchanged.
        let expected = match &*expected.kind {
            TermKind::App { function, .. } if matches!(&*function.kind, TermKind::Lam { .. }) => {
                self.beta(expected)
            }
            _ => expected.clone(),
        };
        let saved = self.metas.clone();
        if self.unify(ctx, &result, &expected) {
            return true;
        }
        self.metas = saved;
        false
    }

    /// Unifies the result of a call's type, its explicit arguments `out`
    /// substituted, with `expected`. An argument still `deferred` is not
    /// elaborated yet (a λ whose type waits): as written it lacks the
    /// generics its body's calls take, so no conversion can equate it, and
    /// trying unfolds both sides as far as they go. It stands as an unknown
    /// here instead, and what the expected type fixes in terms of it is
    /// dropped.
    fn unify_expected(
        &mut self,
        ctx: &Ctx,
        base: &T,
        out: &[T],
        deferred: &[(usize, T, T)],
        expected: &T,
        sp: Span,
    ) {
        let mut ty = base.clone();
        let mut standins = Vec::new();
        for (i, arg) in out.iter().enumerate() {
            let whnf = self.whnf(ctx, &ty);
            let TermKind::Pi { params, result, .. } = &*whnf.kind else {
                return;
            };
            let name = params[0].0.clone().unwrap_or_else(|| "_".into());
            let arg = if deferred.iter().any(|(at, _, _)| *at == i) {
                let m = self.fresh_name("?");
                self.metas.insert(m.clone(), None);
                standins.push(m.clone());
                T::var(&m, sp)
            } else {
                arg.clone()
            };
            ty = self.subst(result, &name, &arg);
        }
        let ty = self.resolve(&ty);
        if has_meta(&ty) {
            let saved = self.metas.clone();
            self.unify(ctx, &ty, expected);
            let leaked = self.metas.iter().any(|(m, v)| {
                !standins.contains(m)
                    && v.as_ref()
                        .is_some_and(|v| standins.iter().any(|s| occurs(&self.resolve(v), s)))
            });
            if leaked {
                self.metas = saved;
            }
        }
        for m in &standins {
            self.metas.remove(m);
        }
    }

    /// The explicit arguments of a call to `g` elaborated into `out`, and the
    /// values of its implicit ones.
    #[allow(clippy::too_many_arguments)]
    fn implicit_arguments(
        &mut self,
        ctx: &Ctx,
        (g, sp, call): (&Name, Span, Span),
        arguments: &[T],
        expected: Option<&T>,
        Unknowns {
            metas,
            names,
            dicts,
            implicit,
        }: Unknowns,
        base: &T,
        out: &mut Vec<T>,
        failed: &mut Option<(usize, T, Diagnostic)>,
    ) -> Result<Vec<T>, Diagnostic> {
        let mut ty = base.clone();
        let mut deferred: Vec<(usize, T, T)> = Vec::new();
        for (index, arg) in arguments.iter().enumerate() {
            // A function that waited for its type gets it once the
            // arguments so far fix it, and the types of the later ones
            // see it elaborated (a motive applied to a bare `None`).
            let mut settled = false;
            let mut i = 0;
            while i < deferred.len() {
                let dom = self.resolve(&deferred[i].1);
                if !has_meta(&dom)
                    && (matches!(&*deferred[i].2.kind, TermKind::Lam { .. })
                        || self.bare_generic(ctx, &deferred[i].2))
                {
                    let (at, _, arg) = deferred.remove(i);
                    out[at] = self.elab(ctx, &arg, Some(&dom))?;
                    settled = true;
                } else {
                    i += 1;
                }
            }
            if settled {
                ty = base.clone();
                for a in out.iter() {
                    let whnf = self.whnf(ctx, &ty);
                    let TermKind::Pi { params, result, .. } = &*whnf.kind else {
                        break;
                    };
                    let name = params[0].0.clone().unwrap_or_else(|| "_".into());
                    ty = self.subst(result, &name, a);
                }
            }
            let whnf = self.whnf(ctx, &ty);
            let TermKind::Pi { params, result, .. } = &*whnf.kind else {
                return err(
                    msg!("kernel-too-many-arguments", name = (g).to_string()),
                    arg.span,
                );
            };
            let name = params[0].0.clone().unwrap_or_else(|| "_".into());
            let dom = self.resolve(&params[0].1);
            if has_meta(&dom)
                && (matches!(&*arg.kind, TermKind::Lam { .. } | TermKind::Hole(_))
                    || self.bare_generic(ctx, arg))
            {
                // A function needs its type first: later arguments or the
                // expected type may fix it.
                deferred.push((out.len(), dom, arg.clone()));
                ty = self.subst(result, &name, arg);
                out.push(arg.clone());
                continue;
            }
            let arg = if has_meta(&dom) {
                // An argument that cannot be elaborated yet (a bare `Nil`)
                // waits for the ones that fix its type.
                let Ok(arg) = self.elab(ctx, arg, None) else {
                    deferred.push((out.len(), dom, arg.clone()));
                    ty = self.subst(result, &name, arg);
                    out.push(arg.clone());
                    continue;
                };
                let actual = self.infer(ctx, &arg)?;
                if !self.unify(ctx, &dom, &actual) {
                    // Perhaps the expected type fixes what this cannot
                    // (`?sg(e)` against `askSig(e)`): try again then.
                    deferred.push((out.len(), dom, arg.clone()));
                    ty = self.subst(result, &name, &arg);
                    out.push(arg);
                    continue;
                }
                arg
            } else {
                if let Some((at, want, e)) = failed.as_ref()
                    && *at == index
                    && self.conv(ctx, want, &dom)
                {
                    return Err(e.clone());
                }
                match self.elab(ctx, arg, Some(&dom)) {
                    Ok(arg) => arg,
                    Err(e) => {
                        *failed = Some((index, dom, e.clone()));
                        return Err(e);
                    }
                }
            };
            ty = self.subst(result, &name, &arg);
            out.push(arg);
        }
        if let Some(expected) = expected {
            self.unify_expected(ctx, base, out, &deferred, expected, sp);
        }
        // Resolve deferred arguments that can be elaborated before this
        // call's dictionaries. A successful pass removes an argument;
        // unsuccessful trials restore all checker state.
        if self
            .classes
            .instances
            .iter()
            .any(|(_, instance)| instance.infer_from.is_some())
        {
            loop {
                let mut progress = false;
                let mut index = 0;
                while index < deferred.len() {
                    let (at, dom, arg) = &deferred[index];
                    let dom = self.resolve(dom);
                    if has_meta(&dom)
                        && matches!(&*arg.kind, TermKind::Lam { .. } | TermKind::Hole(_))
                    {
                        index += 1;
                        continue;
                    }
                    let saved = self.clone();
                    let result = self.elab(ctx, arg, Some(&dom)).and_then(|value| {
                        let actual = self.infer(ctx, &value)?;
                        if self.unify(ctx, &dom, &actual) {
                            Ok(value)
                        } else {
                            err(msg!("kernel-implicit-infer-types"), arg.span)
                        }
                    });
                    match result {
                        Ok(value) => {
                            out[*at] = value;
                            deferred.remove(index);
                            progress = true;
                        }
                        Err(_) => {
                            *self = saved;
                            index += 1;
                        }
                    }
                }
                if !progress {
                    break;
                }
            }
            self.infer_from_instances(ctx, dicts, sp)?;
        }
        // A later argument can depend on a type-valued class method. Once
        // the ordinary arguments have fixed a dictionary's complete goal,
        // resolve it before checking those deferred argument types. This
        // does not infer an unknown class parameter from instance search.
        for (meta, wanted) in dicts {
            let wanted = self.resolve(wanted);
            if !has_meta(&wanted) && has_meta(&self.resolve(&T::var(meta, sp))) {
                let dictionary = self.wanted_dictionary(ctx, &wanted, sp)?;
                self.metas.insert(meta.clone(), Some(dictionary));
            }
        }
        // Functions last: the other arguments that waited may fix their
        // types (`Eq::congr((z: L) => f(z), Eq::congr(g, e))`).
        let mut deferred = std::mem::take(&mut deferred);
        deferred.sort_by_key(|(_, _, arg)| {
            matches!(&*arg.kind, TermKind::Lam { .. }) || self.bare_generic(ctx, arg)
        });
        for (at, dom, arg) in deferred {
            let dom = self.resolve(&dom);
            if has_meta(&dom) && !matches!(&*arg.kind, TermKind::Lam { .. } | TermKind::Hole(_)) {
                // What is known of its type now may be what an argument
                // with implicit arguments of its own needed.
                let elaborated = self.elab(ctx, &arg, Some(&dom));
                if let Ok(e) = &elaborated
                    && let Ok(actual) = self.infer(ctx, e)
                    && self.unify(ctx, &dom, &actual)
                {
                    out[at] = e.clone();
                    continue;
                }
                // The argument as written, its own generics left out, is
                // not what its type is about: say why it did not elaborate.
                let actual = match (self.infer(ctx, &arg), elaborated) {
                    // A bare name whose generics nothing fixes (`Nil`):
                    // say which generic, not what its unapplied type is.
                    (_, Err(why)) if matches!(&*arg.kind, TermKind::Var(_)) => {
                        return Err(why);
                    }
                    (Ok(actual), _) => actual,
                    (Err(_), Err(why)) => return Err(why),
                    (Err(why), Ok(_)) => return Err(why),
                };
                if !self.unify(ctx, &dom, &actual) {
                    // The message is about the call to `g`. An argument
                    // that a `let` name stood for carries the span of the
                    // value it was bound to, outside this call: point at
                    // the call then, not at that earlier value.
                    let at = if call.start <= arg.span.start && arg.span.end <= call.end {
                        arg.span
                    } else {
                        call
                    };
                    return err(
                        msg!(
                            "kernel-implicit-no-match",
                            name = (g).to_string(),
                            expected = describe(&dom),
                            found = describe(&actual)
                        ),
                        at,
                    );
                }
            }
            let dom = self.resolve(&dom);
            out[at] = self.elab(ctx, &arg, Some(&dom))?;
            // A function's body may fix what its type left open
            // (`(z: L) => Cons(x, z)` for `(L) -> ?B`).
            if has_meta(&dom)
                && let TermKind::Lam { params, body, .. } = &*out[at].kind
                && let TermKind::Pi {
                    params: pp, result, ..
                } = &*self.whnf(ctx, &dom).kind
            {
                let name = pp[0].0.clone().unwrap_or_else(|| "_".into());
                let mut inner = ctx.clone();
                inner.push((params[0].clone(), pp[0].1.clone()));
                let result = self.subst(result, &name, &T::var(&params[0], arg.span));
                // Only what does not mention the parameter: an open
                // type outside the λ cannot be solved with its bound
                // name (a `match` on it infers `motive(o)`, which reads
                // as the motive's result once applied).
                if let Ok(actual) = self.infer(&inner, body) {
                    let actual = self.beta(&actual);
                    if !occurs(&actual, &params[0]) {
                        self.unify(&inner, &result, &actual);
                    }
                }
            }
        }
        for (m, wanted) in dicts {
            let wanted = self.resolve(wanted);
            let found = self.wanted_dictionary(ctx, &wanted, sp)?;
            self.metas.insert(m.clone(), Some(found));
        }
        let mut values = Vec::new();
        for (j, m) in metas.iter().enumerate() {
            let v = self.resolve(&T::var(m, sp));
            if has_meta(&v) {
                if j >= implicit {
                    return err(
                        msg!("kernel-implicit-cannot-infer", name = (g).to_string()),
                        sp,
                    );
                }
                return err(
                    msg!(
                        "kernel-implicit-generic",
                        generic = (&names[j]).to_string(),
                        name = (g).to_string(),
                        generics = names[..implicit]
                            .iter()
                            .map(|n| format!("{}: …", n.as_str()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    sp,
                );
            }
            values.push(v);
        }
        Ok(values)
    }

    /// The record `wanted` (`C(T)`, or `C::laws(T, r)` for the laws) is: an
    /// assumption of the context (a `where` of the declaration being
    /// checked) of that type, or the instance for the head of `T`, applied to
    /// the records its own `where` needs.
    fn unify_instance_pattern(&mut self, ctx: &Ctx, pattern: &T, actual: &T) -> bool {
        let pkey = self.instance_argument_key(pattern, &[], false, false);
        let akey = self.instance_argument_key(actual, &[], false, true);
        if matches!((&pkey, &akey), (Some(super::classes::HeadKey::Text(a)), Some(super::classes::HeadKey::Text(b))) if a == b)
        {
            return true;
        }
        // A function head `(A) -> R` takes the first parameter of a function
        // and the function of the rest: `(X, Y) -> Z` is `(X) -> (Y) -> Z`.
        if let (
            TermKind::Pi {
                params: pp,
                result: pr,
                ..
            },
            TermKind::Pi {
                params: ap,
                result: ar,
                effects,
                ..
            },
        ) = (&*pattern.kind, &*actual.kind)
            && let ([(_, p_domain)], Some(((a_name, a_domain), rest))) =
                (pp.as_slice(), ap.split_first())
        {
            if a_name.as_ref().is_some_and(|n| {
                rest.iter().any(|(_, t)| super::mentions(t, n)) || super::mentions(ar, n)
            }) {
                return false;
            }
            let rest = if rest.is_empty() {
                (**ar).clone()
            } else {
                T::new(
                    TermKind::Pi {
                        params: rest.to_vec(),
                        result: ar.clone(),
                        effects: effects.clone(),
                        unused: Vec::new(),
                    },
                    actual.span,
                )
            };
            return self.unify_instance_pattern(ctx, p_domain, a_domain)
                && self.unify_instance_pattern(ctx, pr, &rest);
        }
        if let (
            TermKind::App {
                function: p,
                arguments: pa,
            },
            TermKind::App {
                function: a,
                arguments: aa,
            },
        ) = (&*pattern.kind, &*actual.kind)
            && let (TermKind::Var(p), TermKind::Var(a)) = (&*p.kind, &*a.kind)
            && p == a
            && let Some((implicit, total)) = self.instance_constructor_shape(p)
        {
            let explicit = |args: &[T]| -> Option<Vec<T>> {
                if args.len() == total {
                    Some(args[implicit..].to_vec())
                } else if args.len() + implicit == total {
                    Some(args.to_vec())
                } else {
                    None
                }
            };
            if let (Some(pa), Some(aa)) = (explicit(pa), explicit(aa)) {
                return pa
                    .iter()
                    .zip(&aa)
                    .all(|(p, a)| self.unify_instance_pattern(ctx, p, a));
            }
        }
        self.unify(ctx, pattern, actual)
    }

    fn wanted_dictionary(&mut self, ctx: &Ctx, wanted: &T, sp: Span) -> Result<T, Diagnostic> {
        self.find_dictionary(ctx, wanted, sp, &mut Vec::new())
    }

    /// Select every inference rule from the same ordinary-inference snapshot.
    /// No `where` record is resolved while choosing candidates.
    fn infer_from_instances(
        &mut self,
        ctx: &Ctx,
        dicts: &[(Name, T)],
        sp: Span,
    ) -> Result<(), Diagnostic> {
        let mut selected = Vec::new();
        for (_, wanted) in dicts {
            let wanted = self.resolve(wanted);
            let TermKind::App {
                function,
                arguments,
            } = &*wanted.kind
            else {
                continue;
            };
            let TermKind::Var(class) = &*function.kind else {
                continue;
            };
            let base = self.classes.law_owners.get(class).unwrap_or(class).clone();
            let arity = self.classes.arity(&base);
            if arguments.len() < arity {
                continue;
            }
            let actual = &arguments[..arity];
            let known: Vec<bool> = actual.iter().map(|argument| !has_meta(argument)).collect();
            if known.iter().all(|yes| *yes) {
                continue;
            }
            let instances: Vec<_> = self
                .classes
                .instances
                .iter()
                .filter(|((owner, _), instance)| {
                    owner == &base
                        && instance
                            .infer_from
                            .as_ref()
                            .is_some_and(|gate| gate.holds(&known))
                })
                .map(|(_, instance)| instance.clone())
                .collect();
            let candidates: Vec<_> = instances
                .into_iter()
                .filter(|instance| {
                    self.inference_candidate_matches(ctx, instance, actual, &known, sp)
                })
                .collect();
            if candidates.len() > 1 {
                return err(msg!("kernel-instance-ambiguous"), sp);
            }
            if let Some(instance) = candidates.into_iter().next() {
                selected.push((actual.to_vec(), known, instance));
            }
        }
        for (actual, known, instance) in selected {
            let mut patterns: Vec<T> = std::iter::once(instance.head)
                .chain(instance.arguments)
                .collect();
            let mut generic_metas = Vec::new();
            for generic in &instance.generics {
                let meta = self.fresh_name("?");
                self.metas.insert(meta.clone(), None);
                for pattern in &mut patterns {
                    *pattern = self.subst(pattern, generic, &T::var(&meta, sp));
                }
                generic_metas.push(meta);
            }
            for ((pattern, value), is_known) in patterns.iter().zip(&actual).zip(&known) {
                if *is_known && !self.unify_instance_pattern(ctx, pattern, value) {
                    return err(msg!("kernel-implicit-infer-types"), sp);
                }
            }
            for (index, ((pattern, value), is_known)) in
                patterns.iter().zip(&actual).zip(&known).enumerate()
            {
                if !is_known {
                    if !instance.type_heads[index] {
                        return err(msg!("kernel-implicit-infer-types"), sp);
                    }
                    let inferred = self.resolve(pattern);
                    if has_meta(&inferred) || !self.unify(ctx, value, &inferred) {
                        return err(msg!("kernel-implicit-infer-types"), sp);
                    }
                }
            }
            for meta in generic_metas {
                self.metas.remove(&meta);
            }
        }
        Ok(())
    }

    fn inference_candidate_matches(
        &mut self,
        ctx: &Ctx,
        instance: &super::classes::Instance,
        actual: &[T],
        known: &[bool],
        sp: Span,
    ) -> bool {
        let saved = self.clone();
        let mut patterns: Vec<T> = std::iter::once(instance.head.clone())
            .chain(instance.arguments.clone())
            .collect();
        for generic in &instance.generics {
            let meta = self.fresh_name("?");
            self.metas.insert(meta.clone(), None);
            for pattern in &mut patterns {
                *pattern = self.subst(pattern, generic, &T::var(&meta, sp));
            }
        }
        let mut compatible = true;
        for ((pattern, value), is_known) in patterns.iter().zip(actual).zip(known) {
            if *is_known && !self.unify_instance_pattern(ctx, pattern, value) {
                compatible = false;
                break;
            }
        }
        *self = saved;
        compatible
    }

    fn find_dictionary(
        &mut self,
        ctx: &Ctx,
        wanted: &T,
        sp: Span,
        pending: &mut Vec<T>,
    ) -> Result<T, Diagnostic> {
        // Failure is explicit: a cycle or a growing chain must never become
        // an accepted dictionary, nor exhaust the host stack.
        if pending.len() >= 128 {
            return err(msg!("kernel-instance-resolution-depth"), sp);
        }
        let wanted = self.resolve(wanted);
        if pending.iter().any(|goal| self.conv(ctx, goal, &wanted)) {
            return err(msg!("kernel-instance-resolution-cycle"), sp);
        }
        pending.push(wanted.clone());
        let result = self.wanted_dictionary_inner(ctx, &wanted, sp, pending);
        pending.pop();
        result
    }

    fn wanted_dictionary_inner(
        &mut self,
        ctx: &Ctx,
        wanted: &T,
        sp: Span,
        pending: &mut Vec<T>,
    ) -> Result<T, Diagnostic> {
        let wanted = self.resolve(wanted);
        let TermKind::App {
            function,
            arguments,
        } = &*wanted.kind
        else {
            return err(msg!("kernel-implicit-class-needed"), sp);
        };
        let TermKind::Var(class) = &*function.kind else {
            return err(msg!("kernel-implicit-class-needed"), sp);
        };
        let mut ty = self.resolve(&arguments[0]);
        // A type written through a function that returns a type (an alias,
        // `fn Reg(T: Type): Type { KeyMap(T, …) }`) is searched under the
        // type it stands for: unfold the head while it names no instance.
        let base = self.classes.law_owners.get(class).unwrap_or(class).clone();
        while !has_meta(&ty)
            && !head_name(&ty)
                .is_some_and(|h| self.classes.instances.contains_key(&(base.clone(), h)))
        {
            let w = self.whnf(ctx, &ty);
            if w == ty {
                break;
            }
            ty = w;
        }
        let shown = |laws: bool| {
            let instance = format!("{base}({})", describe(&ty));
            if laws {
                msg!("kernel-implicit-laws-of", instance = instance)
            } else {
                Message::text(instance)
            }
        };
        if has_meta(&ty) || arguments.iter().any(has_meta) {
            return err(
                msg!("kernel-implicit-class-type", class = (class).to_string()),
                sp,
            );
        }
        let laws = self.classes.law_owners.contains_key(class);
        for (n, t) in ctx.iter().rev() {
            if is_dict(n) && self.conv(ctx, t, &wanted) {
                return Ok(T::var(n, sp));
            }
        }
        let id = match (base.as_str(), head_name(&ty).as_deref()) {
            ("Ord", Some("Nat")) => "kernel-implicit-no-instance-ord",
            _ => "kernel-implicit-no-instance",
        };
        let no_instance = || err(msg!(id, instance = shown(laws)), sp);
        let arity = self.classes.arity(&base);
        if arguments.len() < arity {
            return no_instance();
        }
        let mut wanted_args: Vec<T> = arguments[..arity]
            .iter()
            .map(|arg| self.whnf(ctx, arg))
            .collect();
        wanted_args[0] = ty.clone();
        let mut matches = self
            .classes
            .instances
            .iter()
            .filter_map(|((owner, _), instance)| {
                if owner != &base {
                    return None;
                }
                let pattern = std::iter::once(&instance.head).chain(&instance.arguments);
                let compatible = pattern.zip(&wanted_args).zip(&instance.type_heads).all(
                    |((p, a), type_head)| match (
                        self.instance_argument_key(p, &instance.generics, *type_head, false),
                        self.instance_argument_key(a, &[], *type_head, true),
                    ) {
                        (Some(p), Some(a)) => p.overlaps(&a),
                        _ => false,
                    },
                );
                compatible.then_some(instance.clone())
            });
        let Some(instance) = matches.next() else {
            drop(matches);
            return match self.partial_from_dec(ctx, &base, laws, &ty, arguments, sp, pending) {
                Some(record) => Ok(record),
                None => no_instance(),
            };
        };
        if matches.next().is_some() {
            return err(msg!("kernel-instance-ambiguous"), sp);
        }

        let global = if laws {
            let Some(g) = &instance.laws_global else {
                return no_instance();
            };
            g.clone()
        } else {
            instance.global.clone()
        };
        let mut metas = Vec::new();
        let mut patterns: Vec<T> = std::iter::once(instance.head.clone())
            .chain(instance.arguments.clone())
            .collect();
        for g in &instance.generics {
            let m = self.fresh_name("?");
            self.metas.insert(m.clone(), None);
            for pattern in &mut patterns {
                *pattern = self.subst(pattern, g, &T::var(&m, sp));
            }
            metas.push(m);
        }
        let result = (|| {
            if !patterns
                .iter()
                .zip(&wanted_args)
                .all(|(p, a)| self.unify_instance_pattern(ctx, p, a))
            {
                return no_instance();
            }
            let mut generics = Vec::new();
            for m in &metas {
                let v = self.resolve(&T::var(m, sp));
                if has_meta(&v) {
                    return err(
                        msg!("kernel-implicit-instance-types", instance = shown(laws)),
                        sp,
                    );
                }
                generics.push(v);
            }
            let mut args = generics.clone();
            for (c, t) in &instance.wheres {
                // Through the fresh names, so that a type given for one
                // generic is not read again as another (`V` given for `K`).
                let mut terms = t.clone();
                for term in &mut terms {
                    for (g, m) in instance.generics.iter().zip(&metas) {
                        *term = self.subst(term, g, &T::var(m, sp));
                    }
                    *term = self.resolve(term);
                }
                let goal = T::app(c, terms.clone(), sp);
                let record = self.find_dictionary(ctx, &goal, sp, pending)?;
                args.push(record.clone());
                if laws && self.classes.has_laws(c) {
                    let law_record = &self.classes.law_records[c];
                    let goal = T::app(
                        law_record,
                        terms.into_iter().chain(std::iter::once(record)).collect(),
                        sp,
                    );
                    args.push(self.find_dictionary(ctx, &goal, sp, pending)?);
                }
            }
            Ok(call(&global, args, sp))
        })();
        for m in &metas {
            self.metas.remove(m);
        }
        result
    }

    /// The record of `PartialEq(ty)` (or of its laws) made from that of `DecEq(ty)`, when
    /// `ty` has no instance of its own (a type variable of a `where DecEq(A)`): `DecEq(T)`
    /// gives `PartialEq(T)` by the rule of the structural predicates, not as a superclass.
    /// Its `beq` is `DecEq::beq`, and its laws are `dec_eq_symm` and `dec_eq_trans`.
    #[allow(clippy::too_many_arguments)]
    fn partial_from_dec(
        &mut self,
        ctx: &Ctx,
        base: &Name,
        laws: bool,
        ty: &T,
        arguments: &[T],
        sp: Span,
        pending: &mut Vec<T>,
    ) -> Option<T> {
        if !tauto_surface::bindings::is_library(base, "PartialEq") {
            return None;
        }
        let dec = tauto_surface::bindings::library_reference("DecEq")?;
        let goal = T::app(&dec, vec![ty.clone()], sp);
        let record = self.find_dictionary(ctx, &goal, sp, pending).ok()?;
        if !laws {
            let beq = tauto_surface::bindings::library_reference("DecEq::beq")?;
            let left = Name::from(tauto_surface::identity::LocalRef::fresh("eq_left"));
            let right = Name::from(tauto_surface::identity::LocalRef::fresh("eq_right"));
            // Elaborated as any λ is: one binder at a time, typed by the field.
            let compare = lam(
                &left,
                lam(
                    &right,
                    call(
                        &beq,
                        vec![ty.clone(), record, T::var(&left, sp), T::var(&right, sp)],
                        sp,
                    ),
                ),
            );
            return Some(call(
                &super::classes::constructor_name(base),
                vec![ty.clone(), compare],
                sp,
            ));
        }
        let goal = T::app(
            &super::classes::laws_name(&dec),
            vec![ty.clone(), record.clone()],
            sp,
        );
        let law_record = self.find_dictionary(ctx, &goal, sp, pending).ok()?;
        let law = |name: &str| {
            tauto_surface::bindings::library_reference(name)
                .map(|f| call(&f, vec![ty.clone(), record.clone(), law_record.clone()], sp))
        };
        let (symm, trans) = (law("dec_eq_symm")?, law("dec_eq_trans")?);
        Some(call(
            &super::classes::constructor_name(&super::classes::laws_name(base)),
            vec![ty.clone(), arguments.get(1)?.clone(), symm, trans],
            sp,
        ))
    }

    fn unify_method(
        &mut self,
        ctx: &Ctx,
        function: &T,
        arguments: &[T],
        actual: &T,
    ) -> Option<bool> {
        let TermKind::Var(g) = &*function.kind else {
            return None;
        };
        if !self.classes.is_method(g) || arguments.len() < 2 {
            return None;
        }
        let TermKind::App {
            function: direct,
            arguments: given,
        } = &*actual.kind
        else {
            return None;
        };
        let TermKind::Var(direct) = &*direct.kind else {
            return None;
        };
        let (member, head) = self.classes.direct_origins.get(direct)?;
        if member != g {
            return None;
        }
        let class = self.classes.member_owners.get(g)?;
        let instance = self
            .classes
            .instances
            .get(&(class.clone(), head.clone()))
            .cloned()?;
        let own = instance.generics.len() + instance.wheres.len();
        let arity = self.classes.arity(class);
        let method_generics = self.classes.method_generics(g);
        let dictionary_at = arity + method_generics;
        if arguments.len() < dictionary_at + 1 || given.len() != own + arguments.len() - arity - 1 {
            return None;
        }
        let sp = actual.span;
        let mut heads: Vec<T> = std::iter::once(instance.head.clone())
            .chain(instance.arguments.clone())
            .collect();
        for term in &mut heads {
            for (g, a) in instance.generics.iter().zip(given) {
                *term = self.subst(term, g, a);
            }
        }
        let record = call(&instance.global, given[..own].to_vec(), sp);
        Some(
            arguments[..arity]
                .iter()
                .zip(&heads)
                .all(|(a, h)| self.unify(ctx, a, h))
                && self.unify(ctx, &arguments[dictionary_at], &record)
                && arguments[arity..dictionary_at]
                    .iter()
                    .chain(&arguments[dictionary_at + 1..])
                    .zip(&given[own..])
                    .all(|(x, y)| self.unify(ctx, x, y)),
        )
    }

    /// `C::m(record, …)` of an instance's record is the instance's own
    /// function `C::m@H(…)`: what a recursive method needs to be a recursion,
    /// and what the proofs read. A law is the instance's theorem likewise,
    /// when the instance proves it.
    fn direct_member(&self, g: &Name, args: &[T], sp: Span) -> Option<T> {
        let law = self.classes.law_generics(g);
        if !self.classes.is_method(g) && law.is_none() {
            return None;
        }
        // The class's type and the generics of a law come first, then the
        // record; for a law, then the record of the laws, from which the
        // instance's theorem is read.
        let class = self.classes.member_owners.get(g)?;
        let class_arity = self.classes.arity(class);
        let at = class_arity + law.unwrap_or_else(|| self.classes.method_generics(g));
        let from = at + usize::from(law.is_some());
        if args.len() <= from {
            return None;
        }
        let class = self.classes.member_owners.get(g)?;
        let (function, given) = match &*args[from].kind {
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(n) => (n, arguments.as_slice()),
                _ => return None,
            },
            TermKind::Var(n) => (n, &[][..]),
            _ => return None,
        };
        let (c, head) = self.classes.globals.get(function)?;
        if c != class {
            return None;
        }
        let direct = self
            .classes
            .direct_members
            .get(&(g.clone(), head.clone()))?;
        let mut rest = given.to_vec();
        rest.extend(args[class_arity..at].iter().cloned());
        rest.extend(args[from + 1..].iter().cloned());
        Some(call(direct, rest, sp))
    }

    /// For a call `function(arguments…)` whose result is expected to be
    /// `expected`: the type each argument is expected to have, where the
    /// implicit arguments are found from the arguments written (`Some`, already
    /// elaborated) and from `expected`. An argument given as `None` is not
    /// elaborated yet (a `match` or a λ holding one), so a type that depends on
    /// its value is not known. A type left with an unknown in it is `None`.
    /// Nothing solved here stays: the call is elaborated again as written.
    pub(super) fn argument_goals(
        &mut self,
        ctx: &Ctx,
        function: &T,
        arguments: &[Option<T>],
        expected: Option<&T>,
        implicit_kept: bool,
    ) -> Vec<Option<T>> {
        let saved = self.metas.clone();
        // A call the source wrote may still write its implicit arguments out
        // (`List::ind(A, motive, …)`): that reading is taken first when the
        // arguments fit it, as `elab_app_inner` takes it for the call built
        // from them.
        let mut goals = None;
        if implicit_kept {
            goals = self.argument_goals_in(
                ctx,
                function,
                arguments,
                expected,
                false,
                true,
                &mut Vec::new(),
            );
            self.metas = saved.clone();
        }
        if goals.is_none() {
            goals = self.argument_goals_in(
                ctx,
                function,
                arguments,
                expected,
                implicit_kept,
                false,
                &mut Vec::new(),
            );
        }
        self.metas = saved;
        goals.unwrap_or_else(|| vec![None; arguments.len()])
    }

    /// For a call the source wrote leaving out the implicit arguments of a
    /// global without instance arguments: their values as the arguments
    /// given fix them, when every one is fixed and the arguments do not
    /// read as writing them out. The call is then the one with them written
    /// out, as an expansion writes it (`List::ind(A, motive, …, xs)`).
    pub(super) fn implicits_fixed(
        &mut self,
        ctx: &Ctx,
        function: &T,
        arguments: &[Option<T>],
        expected: Option<&T>,
    ) -> Option<Vec<T>> {
        let TermKind::Var(g) = &*function.kind else {
            return None;
        };
        let global = self.globals.get(g)?;
        if global.implicit == 0 || dict_count(&global.ty, global.implicit) > 0 {
            return None;
        }
        let saved = self.metas.clone();
        let positional = self.argument_goals_in(
            ctx,
            function,
            arguments,
            expected,
            false,
            true,
            &mut Vec::new(),
        );
        self.metas = saved.clone();
        if positional.is_some() {
            return None;
        }
        let mut found = Vec::new();
        let read =
            self.argument_goals_in(ctx, function, arguments, expected, true, false, &mut found);
        self.metas = saved;
        read?;
        found.into_iter().collect()
    }

    fn argument_goals_in(
        &mut self,
        ctx: &Ctx,
        function: &T,
        arguments: &[Option<T>],
        expected: Option<&T>,
        implicit_kept: bool,
        fitting: bool,
        found: &mut Vec<Option<T>>,
    ) -> Option<Vec<Option<T>>> {
        let sp = function.span;
        let mut implicit_metas = Vec::new();
        let ty = match &*function.kind {
            TermKind::Var(g)
                if !ctx.iter().any(|(n, _)| n == g) && self.globals.contains_key(g) =>
            {
                let global = &self.globals[g];
                let (mut ty, implicit) = (global.ty.clone(), global.implicit);
                let mut k = implicit + dict_count(&ty, implicit);
                // The implicit arguments may also be written, as a call
                // written whole (`List::ind(A, motive, …, xs, b)`, applied
                // further when the motive gives a Π) has them.
                // A call the source wrote names them (`f(<x: v>, …)`) or
                // leaves them out, its arguments past the declared ones
                // applying the result (`elab_app_inner`).
                if k > 0 && !implicit_kept && arguments.len() >= pi_arity(&ty) {
                    k = 0;
                } else if fitting {
                    return None;
                }
                if k > 0 && !implicit_kept && arguments.len() + k != pi_arity(&ty) {
                    return None;
                }
                if k > 0 && implicit_kept && arguments.len() + k < pi_arity(&ty) {
                    return None;
                }
                for _ in 0..k {
                    let TermKind::Pi { params, result, .. } = (*ty.kind).clone() else {
                        return None;
                    };
                    let name = params[0].0.clone().unwrap_or_else(|| "_".into());
                    let m = self.fresh_name("?");
                    self.metas.insert(m.clone(), None);
                    ty = self.subst(&result, &name, &T::var(&m, sp));
                    implicit_metas.push(m);
                }
                ty
            }
            _ => self.infer(ctx, function).ok()?,
        };
        // As for a call (`implicit_call`), the expected type is matched first
        // when the result does not depend on the arguments, unless an
        // argument then does not fit.
        let start = self.metas.clone();
        let first = self.unify_result_first(ctx, &ty, arguments.len(), expected);
        let base = ty;
        for attempt in 0..1 + usize::from(first) {
            if attempt == 1 {
                self.metas = start.clone();
            }
            let mut ty = base.clone();
            let mut fits = true;
            // The domains, each with the parameters before it whose values
            // are not known.
            let mut domains: Vec<Option<(T, Vec<Name>)>> = Vec::new();
            let mut unknown: Vec<Name> = Vec::new();
            // Past a result that is not yet a Π (`motive(xs)` with the motive
            // left out, applied further when the motive gives a Π), the
            // domains are not known; the ones before it still are.
            let mut stuck = false;
            for arg in arguments {
                if stuck {
                    domains.push(None);
                    continue;
                }
                let whnf = self.whnf(ctx, &ty);
                let TermKind::Pi { params, result, .. } = &*whnf.kind else {
                    if unknown.is_empty() {
                        return None;
                    }
                    stuck = true;
                    domains.push(None);
                    continue;
                };
                let name = params[0].0.clone().unwrap_or_else(|| "_".into());
                let dom = params[0].1.clone();
                domains.push(Some((dom.clone(), unknown.clone())));
                match arg {
                    Some(a) => {
                        if let Ok(aty) = self.infer(ctx, a) {
                            fits &= self.unify(ctx, &dom, &aty);
                        }
                        ty = self.subst(result, &name, a);
                    }
                    None => {
                        unknown.push(name);
                        ty = (**result).clone();
                    }
                }
            }
            if first && attempt == 0 && !fits {
                continue;
            }
            if fitting && !fits {
                return None;
            }
            if let Some(e) = expected
                && !stuck
                && !unknown.iter().any(|u| occurs(&ty, u))
            {
                self.unify(ctx, &ty, e);
            }
            *found = implicit_metas
                .iter()
                .map(|m| {
                    let v = self.resolve(&T::var(m, sp));
                    (!has_meta(&v)).then_some(v)
                })
                .collect();
            return Some(
                domains
                    .into_iter()
                    .map(|d| {
                        let (d, before) = d?;
                        let d = self.resolve(&d);
                        (!has_meta(&d) && !before.iter().any(|u| occurs(&d, u))).then_some(d)
                    })
                    .collect(),
            );
        }
        None
    }

    pub(super) fn resolve(&self, t: &T) -> T {
        let sp = t.span;
        match &*t.kind {
            TermKind::Var(n) if is_meta(n) => match self.metas.get(n) {
                Some(Some(v)) => self.resolve(v),
                _ => t.clone(),
            },
            TermKind::App {
                function,
                arguments,
            } => T::new(
                TermKind::App {
                    function: Box::new(self.resolve(function)),
                    arguments: arguments.iter().map(|a| self.resolve(a)).collect(),
                },
                sp,
            ),
            TermKind::Pi { params, result, .. } => {
                let name = params[0].0.clone().unwrap_or_else(|| "_".into());
                let mut out = pi(&name, self.resolve(&params[0].1), self.resolve(result));
                out.span = sp;
                out
            }
            TermKind::Lam { params, body, .. } => {
                let mut out = lam(&params[0], self.resolve(body));
                out.span = sp;
                out
            }
            _ => t.clone(),
        }
    }

    pub(super) fn unify(&mut self, ctx: &Ctx, pattern: &T, actual: &T) -> bool {
        let p = self.resolve(pattern);
        if !has_meta(&p) {
            return self.conv(ctx, &p, actual);
        }
        let sp = p.span;
        match &*p.kind {
            TermKind::Var(m) if is_meta(m) => {
                // `?m := ?m` is nothing, and `?m := f(?m)` has no solution.
                let actual = self.resolve(actual);
                if matches!(&*actual.kind, TermKind::Var(a) if a == m) {
                    return true;
                }
                if occurs(&actual, m) {
                    return false;
                }
                self.metas.insert(m.clone(), Some(actual));
                true
            }
            TermKind::App {
                function,
                arguments,
            } => {
                if let TermKind::Var(m) = &*function.kind
                    && is_meta(m)
                {
                    // `?m x⃗` with distinct variables: `?m := λ x⃗. actual`.
                    // Anything else (`?F(?A)` against `List(Nat)`, the
                    // unknowns of a higher-kinded generic) is not such a
                    // pattern: it is matched below by its head and its
                    // arguments, which gives one solution, and the checked
                    // term is still checked against it.
                    let vars: Option<Vec<Name>> = arguments
                        .iter()
                        .map(|a| match &*a.kind {
                            TermKind::Var(v) if !is_meta(v) => Some(v.clone()),
                            _ => None,
                        })
                        .collect();
                    if let Some(vars) = vars
                        && vars.iter().enumerate().all(|(i, v)| !vars[..i].contains(v))
                    {
                        let fresh: Vec<Name> = vars.iter().map(|v| self.fresh_name(v)).collect();
                        let mut body = actual.clone();
                        for (v, f) in vars.iter().zip(&fresh) {
                            body = self.subst(&body, v, &T::var(f, sp));
                        }
                        let value = fresh.iter().rev().fold(body, |acc, f| lam(f, acc));
                        self.metas.insert(m.clone(), Some(value));
                        return true;
                    }
                }
                // `C::m(?A, ?r, x⃗)` against `C::m@H(y⃗, x⃗)`: the record is the
                // instance's, and `?A` is its head.
                if let Some(solved) = self.unify_method(ctx, function, arguments, actual) {
                    return solved;
                }
                // As written first (`EffectEq<m, ?t>` against `EffectEq<m, e>`),
                // then unfolded.
                let mut a = actual.clone();
                for round in 0..2 {
                    if round == 1 {
                        a = self.whnf(ctx, actual);
                    }
                    // A numeral is `Zero` or `Succ(k)` against a pattern that
                    // is one of them.
                    let a = &expand_numeral(a.clone());
                    if let TermKind::App {
                        function: f2,
                        arguments: a2,
                    } = &*a.kind
                        && a2.len() == arguments.len()
                    {
                        let (f2, a2) = ((**f2).clone(), a2.clone());
                        if self.unify(ctx, function, &f2)
                            && arguments
                                .iter()
                                .zip(&a2)
                                .all(|(x, y)| self.unify(ctx, x, y))
                        {
                            return true;
                        }
                    }
                }
                // The other side may be the unfolded form of a definition
                // the pattern names (a goal that was reduced): unfold the
                // pattern too.
                let unfolded = self.whnf(ctx, &p);
                if *unfolded.kind != *p.kind {
                    let a = self.whnf(ctx, actual);
                    return self.unify(ctx, &unfolded, &a);
                }
                false
            }
            TermKind::Pi { params, result, .. } => {
                let a = self.whnf(ctx, actual);
                let TermKind::Pi {
                    params: p2,
                    result: r2,
                    ..
                } = &*a.kind
                else {
                    return false;
                };
                if !self.unify(ctx, &params[0].1, &p2[0].1) {
                    return false;
                }
                let n1 = params[0].0.clone().unwrap_or_else(|| "_".into());
                let n2 = p2[0].0.clone().unwrap_or_else(|| "_".into());
                let v = self.fresh_name("x");
                let mut inner = ctx.clone();
                inner.push((v.clone(), p2[0].1.clone()));
                let b1 = self.subst(result, &n1, &T::var(&v, sp));
                let b2 = self.subst(r2, &n2, &T::var(&v, sp));
                self.unify(&inner, &b1, &b2)
            }
            _ => false,
        }
    }
}

/// The implicit arguments of a call: their unknowns, the names of the
/// parameters they stand for, the records of classes among them (with the
/// types wanted), and how many come before the records.
struct Unknowns<'a> {
    metas: &'a [Name],
    names: &'a [Name],
    dicts: &'a [(Name, T)],
    implicit: usize,
}

/// How many of the binders after the first `skip` stand for the record of a
/// class.
pub(super) fn dict_count(ty: &T, skip: usize) -> usize {
    let mut walk = ty;
    let mut n = 0;
    let mut counted = 0;
    while let TermKind::Pi { params, result, .. } = &*walk.kind {
        if n >= skip {
            if params[0].0.as_ref().is_some_and(is_dict) {
                counted += 1;
            } else {
                break;
            }
        }
        n += 1;
        walk = result;
    }
    counted
}

fn pi_arity(ty: &T) -> usize {
    let mut n = 0;
    let mut walk = ty;
    while let TermKind::Pi { result, .. } = &*walk.kind {
        n += 1;
        walk = result;
    }
    n
}

/// `t` with each free local that capture-avoiding renaming made from a
/// binder of the source put back as that binder. A site is read against the
/// source, where the binder is the one written: a `match` that becomes a
/// recursor can rename a parameter it moves under the motive, and an
/// implicit argument found there names the renamed copy.
fn as_written(mut t: T) -> T {
    let bound = super::matching::binders_of(&t);
    let mut aliases = std::collections::HashMap::new();
    crate::surface::walk::term(&mut t.clone(), &mut |part| {
        if let TermKind::Var(Name::Local(local)) = &*part.kind
            && local.origin().is_some()
            && !bound.iter().any(|b| b.as_local() == Some(local))
        {
            let mut written = local.clone();
            while let Some(origin) = written.origin() {
                written = origin.clone();
            }
            aliases.insert(Name::Local(local.clone()), Name::Local(written));
        }
    });
    if !aliases.is_empty() {
        super::matching::remap_locals(&mut t, &aliases);
    }
    t
}
