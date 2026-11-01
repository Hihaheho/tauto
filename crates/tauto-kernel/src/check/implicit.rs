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

use super::classes::{call, head_name, is_dict};
use super::{Ctx, Diagnostic, Kernel, T, describe, err, expand_numeral, lam, occurs, pi};
use crate::surface::TermKind;
use tauto_message::{Message, msg};
use tauto_parol::Span;

fn is_meta(n: &str) -> bool {
    n.starts_with('?')
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

impl Kernel {
    /// Writes out the implicit arguments of every call in `t`. Where a type is expected (a
    /// function's argument, a `let` with its type written, a declaration's result) and `t` has
    /// it only as a subtype of products, `t` is taken to it as `(t: T)` takes it (`ascribe`):
    /// the members it asks for, a label put on or taken off. The two sides of `a = b` are not
    /// held so (`equation`): their type is the one found, not one expected.
    pub(super) fn elab(&mut self, ctx: &Ctx, t: &T, expected: Option<&T>) -> Result<T, Diagnostic> {
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
                    let mk = T::new(TermKind::Var(format!("{f}::Mk")), t.span);
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
        if matches!(&*e.kind, TermKind::Lam { .. } | TermKind::Pi { .. }) || has_meta(&e) {
            return Ok(e);
        }
        let saved = self.metas.clone();
        let have = self.infer(ctx, &e);
        self.metas = saved;
        // A product and a `Pair` written by its name are two types, though the kernel sees
        // the product as that `Pair`: neither stands where the other is written.
        // As written: `#(…)` (`prod_mk`) where a `Pair` is written, and `Pair { … }` where a
        // product is. `prod_mk` itself makes the product of its `Pair`.
        let head = match &*e.kind {
            TermKind::App { function, .. } => match &*function.kind {
                TermKind::Var(f) => Some(f.as_str()),
                _ => None,
            },
            _ => None,
        };
        let literal = matches!(head, Some(f) if f == "prod_mk" || f.ends_with("::prod_mk")
            || f == "Pair::Mk" || f.ends_with("::Pair::Mk"));
        // A type the core wrote back (a product unfolded where a goal was reduced) has the
        // span of the whole at its head; a `Pair` written in the source has its own name's.
        let written = |t: &T| match &*t.kind {
            TermKind::App { function, .. } => function.span != t.span,
            _ => false,
        };
        if literal
            && self.projecting == 0
            && written(want)
            && let Ok(have) = &have
            && self.current.as_deref() != Some("prod_mk")
            && !has_meta(have)
            && !has_meta(want)
            && ((self.product_parts(have).is_some() && self.pair_family(want).is_some())
                || (self.pair_family(have).is_some() && self.product_parts(want).is_some()))
        {
            let (a, b) = (super::describe(have), super::describe(want));
            return Err(Diagnostic::new(
                msg!("kernel-product-not-pair", have = &a, want = &b),
                Some(e.span),
            ));
        }
        match have {
            Ok(have) if self.needs_ascription(ctx, &have, want) => {
                let taken = self.ascribe_at(&e, want, ctx, e.span)?;
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
        // A sort over level variables is not a call: its level is not elaborated.
        if self.core.level_sort(t).is_some() {
            return Ok(t.clone());
        }
        match &*t.kind {
            TermKind::Lam {
                params,
                body,
                types,
            } => {
                let Some(expected) = expected else {
                    return Ok(t.clone());
                };
                let expected = self.whnf(ctx, expected);
                let TermKind::Pi {
                    params: pp, result, ..
                } = &*expected.kind
                else {
                    return Ok(t.clone());
                };
                if let Some(Some(written)) = types.first() {
                    let written = self.elab(ctx, written, None)?;
                    self.check_param_type(&params[0], &written, &pp[0].1, ctx)?;
                }
                let name = pp[0].0.clone().unwrap_or_else(|| "_".into());
                let (x, body) = self.enter_lam(ctx, &params[0], body, &name, &pp[0].1, result);
                let mut inner = ctx.clone();
                inner.push((x.clone(), pp[0].1.clone()));
                let result = self.subst(result, &name, &T::var(&x, sp));
                let body = self.elab(&inner, &body, Some(&result))?;
                let mut out = lam(&x, body);
                out.span = sp;
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
            } if matches!(&*function.kind, TermKind::Var(op) if op == "=")
                && arguments.len() == 2
                && !ctx.iter().any(|(n, _)| n == "=") =>
            {
                self.equation(ctx, &arguments[0], &arguments[1], sp)
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
                msg!("kernel-implicit-nullary", name = g),
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
                self.implicit_call(ctx, g, t, &[], expected, t.span)
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
                match self.implicit_call(ctx, g, t, &[], Some(&expected), t.span) {
                    Ok(e) => match self.infer(ctx, &e) {
                        Ok(actual) if self.unify(ctx, &expected, &actual) => Ok(e),
                        _ => {
                            self.metas = saved;
                            Ok(t.clone())
                        }
                    },
                    Err(_) => {
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
                let suffix = format!(".{n}");
                let found = self.ctors.get(n).or_else(|| {
                    self.ctors
                        .iter()
                        .find(|(k, _)| k.ends_with(&suffix))
                        .map(|(_, v)| v)
                });
                found.is_some_and(|(family, at)| {
                    let ind = &self.inds[family];
                    let c = &ind.ctors[*at];
                    (!ind.params.is_empty() || c.implicit > 0) && c.args.len() == c.implicit
                })
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
                        family == "Pair" || family.ends_with("::Pair")
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
        Ok(call("Eq", vec![ty, lhs, rhs], sp))
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
            } if matches!(&*function.kind, TermKind::Var(op) if op == "-")
                && let [x] = arguments.as_slice()
                && let TermKind::Nat(n) = &*x.kind =>
            {
                (true, n)
            }
            _ => return None,
        };
        let n: u128 = n.parse().ok()?;
        let ty = self.whnf(ctx, expected);
        let TermKind::Var(family) = &*ty.kind else {
            return None;
        };
        if !(family == "Int" || family.ends_with("::Int")) {
            return None;
        }
        let ind = self.inds.get(family)?;
        let ctor = |name: &str| {
            let suffix = format!(".{name}");
            ind.ctors
                .iter()
                .find(|c| c.name == name || c.name.ends_with(&suffix))
                .filter(|c| c.args.len() == 1)
                .map(|c| c.name.clone())
        };
        let (of_nat, neg_succ) = (ctor("IntOfNat")?, ctor("IntNegSucc")?);
        if ind.ctors.len() != 2 || !ind.params.is_empty() {
            return None;
        }
        let sp = t.span;
        let (c, k) = if negative && n > 0 {
            (neg_succ, n - 1)
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
        let global = |n: &str| !ctx.iter().any(|(m, _)| m == n);
        let ctor = |n: &str, arity: usize| {
            global(n)
                && self
                    .globals
                    .get(n)
                    .is_some_and(|g| g.implicit == 1 && pi_arity(&g.ty) == arity)
        };
        if !(global("Nat") && ctor("Cons", 3) && ctor("Nil", 1)) {
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
                    if c == "Cons" && matches!(&*head.kind, TermKind::Nat(_)) =>
                {
                    heads.push((at, function, head));
                    at = tail;
                }
                (TermKind::Var(c), [ty])
                    if c == "Nil" && matches!(&*ty.kind, TermKind::Var(n) if n == "Nat") =>
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
                    arguments: vec![T::var("Nat", node.span), head.clone(), list],
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
    fn implicit_sig(&self, ctx: &Ctx, g: &str) -> Option<(T, usize)> {
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

    fn elab_app(
        &mut self,
        ctx: &Ctx,
        whole: &T,
        function: &T,
        arguments: &[T],
        expected: Option<&T>,
    ) -> Result<T, Diagnostic> {
        let sp = whole.span;
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
            if arguments.len() + k == arity {
                return self.implicit_call(ctx, g, function, arguments, expected, sp);
            }
            // Arguments past the declared ones apply the call's result:
            // `f(a, h)` is `f(a)(h)`. A call at least as long as the
            // parameters may also be one writing the implicit arguments out,
            // `f(u, A, m, x)` being `f(u, A, m)(x)` (as a call written
            // `f(u, A, m)(x)` reads once its applications are flattened);
            // that reading is tried first.
            if arity >= k && arguments.len() + k > arity {
                let applied_at = |at: usize| {
                    let (first, rest) = arguments.split_at(at);
                    let call = T::new(
                        TermKind::App {
                            function: Box::new(function.clone()),
                            arguments: first.to_vec(),
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
                if arguments.len() < arity {
                    return self.elab(ctx, &applied, expected);
                }
                let saved = self.metas.clone();
                let written_out = if arguments.len() == arity {
                    self.plain_app(ctx, whole, function, arguments, expected)
                } else {
                    self.elab(ctx, &applied_at(arity), expected)
                };
                match written_out.and_then(|t| self.infer(ctx, &t).map(|_| t)) {
                    Ok(t) => return Ok(t),
                    Err(e) => {
                        self.metas = saved.clone();
                        return self.elab(ctx, &applied, expected).map_err(|_| {
                            self.metas = saved;
                            e
                        });
                    }
                }
            }
        }
        self.plain_app(ctx, whole, function, arguments, expected)
    }

    /// `elab_app` past the implicit arguments.
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
        } = &*function.kind
            && let Some((a, rest)) = arguments.split_first()
        {
            let mut inner = self.subst(body, &params[0], a);
            if params.len() > 1 {
                inner = T::new(
                    TermKind::Lam {
                        params: params[1..].to_vec(),
                        body: Box::new(inner),
                        types: types.get(1..).map(<[_]>::to_vec).unwrap_or_default(),
                    },
                    function.span,
                );
            }
            if !rest.is_empty() {
                inner = T::new(
                    TermKind::App {
                        function: Box::new(inner),
                        arguments: rest.to_vec(),
                    },
                    sp,
                );
            }
            return self.elab(ctx, &inner, expected);
        }
        let function = match &*function.kind {
            TermKind::Var(_) => function.clone(),
            _ => self.elab(ctx, function, None)?,
        };
        let mut ty = self.infer(ctx, &function)?;
        let mut out = Vec::new();
        for arg in arguments {
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
        g: &str,
        function: &T,
        arguments: &[T],
        expected: Option<&T>,
        whole: Span,
    ) -> Result<T, Diagnostic> {
        let sp = function.span;
        let Some((mut ty, implicit)) = self.implicit_sig(ctx, g) else {
            return err(msg!("kernel-implicit-not-defined", name = g), sp);
        };
        let k = implicit + dict_count(&ty, implicit);
        let mut metas = Vec::new();
        let mut names: Vec<String> = Vec::new();
        // The records of the classes a call needs (`check/classes.rs`): not
        // matched against an argument but found once the types are known.
        let mut dicts: Vec<(String, T)> = Vec::new();
        for i in 0..k {
            let TermKind::Pi { params, result, .. } = (*ty.kind).clone() else {
                return err(msg!("kernel-implicit-fewer-params", name = g), sp);
            };
            let name = params[0].0.clone().unwrap_or_else(|| "_".into());
            let m = self.fresh_name("?");
            self.metas.insert(m.clone(), None);
            if i >= implicit {
                dicts.push((m.clone(), params[0].1.clone()));
            }
            ty = self.subst(&result, &name, &T::var(&m, sp));
            names.push(name);
            metas.push(m);
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
        for attempt in 0..attempts {
            if attempt == 1 {
                self.metas = start.clone();
            }
            let mut out: Vec<T> = Vec::new();
            outcome = self
                .implicit_arguments(
                    ctx,
                    (g, sp),
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
                )
                .map(|mut args| {
                    args.extend(out);
                    self.direct_member(g, &args, sp).unwrap_or_else(|| {
                        // The call as written, so that an error in it can
                        // point at all of it.
                        T::new(
                            TermKind::App {
                                function: Box::new(function.clone()),
                                arguments: args,
                            },
                            whole,
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
        let saved = self.metas.clone();
        if self.unify(ctx, &result, expected) {
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
        (g, sp): (&str, Span),
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
    ) -> Result<Vec<T>, Diagnostic> {
        let mut ty = base.clone();
        let mut deferred: Vec<(usize, T, T)> = Vec::new();
        for arg in arguments {
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
                return err(msg!("kernel-too-many-arguments", name = g), arg.span);
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
                self.elab(ctx, arg, Some(&dom))?
            };
            ty = self.subst(result, &name, &arg);
            out.push(arg);
        }
        if let Some(expected) = expected {
            self.unify_expected(ctx, base, out, &deferred, expected, sp);
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
                    return err(
                        msg!(
                            "kernel-implicit-no-match",
                            name = g,
                            expected = describe(&dom),
                            found = describe(&actual)
                        ),
                        arg.span,
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
                    return err(msg!("kernel-implicit-cannot-infer", name = g), sp);
                }
                return err(
                    msg!(
                        "kernel-implicit-generic",
                        generic = &names[j],
                        name = g,
                        generics = names[..implicit].join(", ")
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
    fn wanted_dictionary(&mut self, ctx: &Ctx, wanted: &T, sp: Span) -> Result<T, Diagnostic> {
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
        let base = class.strip_suffix("::laws").unwrap_or(class);
        while !has_meta(&ty)
            && !head_name(&ty)
                .is_some_and(|h| self.classes.instances.contains_key(&(base.to_string(), h)))
        {
            let w = self.whnf(ctx, &ty);
            if w == ty {
                break;
            }
            ty = w;
        }
        let shown = |laws: bool| {
            let base = class.strip_suffix("::laws").unwrap_or(class);
            let instance = format!("{base}({})", describe(&ty));
            if laws {
                msg!("kernel-implicit-laws-of", instance = instance)
            } else {
                Message::text(instance)
            }
        };
        if has_meta(&ty) || arguments.iter().any(has_meta) {
            return err(msg!("kernel-implicit-class-type", class = class), sp);
        }
        let laws = class.ends_with("::laws");
        for (n, t) in ctx.iter().rev() {
            if is_dict(n) && self.conv(ctx, t, &wanted) {
                return Ok(T::var(n, sp));
            }
        }
        let id = match (base, head_name(&ty).as_deref()) {
            ("Ord", Some("Nat")) => "kernel-implicit-no-instance-ord",
            _ => "kernel-implicit-no-instance",
        };
        let no_instance = || err(msg!(id, instance = shown(laws)), sp);
        let Some(head) = head_name(&ty) else {
            return no_instance();
        };
        let Some(instance) = self
            .classes
            .instances
            .get(&(base.to_string(), head))
            .cloned()
        else {
            return no_instance();
        };
        let global = if laws {
            let Some(g) = &instance.laws_global else {
                return no_instance();
            };
            g.clone()
        } else {
            instance.global.clone()
        };
        let mut metas = Vec::new();
        let mut pattern = instance.head.clone();
        for g in &instance.generics {
            let m = self.fresh_name("?");
            self.metas.insert(m.clone(), None);
            pattern = self.subst(&pattern, g, &T::var(&m, sp));
            metas.push(m);
        }
        let result = (|| {
            if !self.unify(ctx, &pattern, &ty) {
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
                let mut t = t.clone();
                for (g, m) in instance.generics.iter().zip(&metas) {
                    t = self.subst(&t, g, &T::var(m, sp));
                }
                let t = self.resolve(&t);
                let goal = T::app(c, vec![t.clone()], sp);
                let record = self.wanted_dictionary(ctx, &goal, sp)?;
                args.push(record.clone());
                if laws && self.classes.has_laws(c) {
                    let goal = T::app(&format!("{c}::laws"), vec![t, record], sp);
                    args.push(self.wanted_dictionary(ctx, &goal, sp)?);
                }
            }
            Ok(call(&global, args, sp))
        })();
        for m in &metas {
            self.metas.remove(m);
        }
        result
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
        let (class, member) = g.rsplit_once("::")?;
        let head = direct.strip_prefix(&format!("{class}::{member}@"))?;
        let instance = self
            .classes
            .instances
            .get(&(class.to_string(), head.to_string()))
            .cloned()?;
        let own = instance.generics.len() + instance.wheres.len();
        if given.len() != own + arguments.len() - 2 {
            return None;
        }
        let sp = actual.span;
        let mut head_term = instance.head.clone();
        for (g, a) in instance.generics.iter().zip(given) {
            head_term = self.subst(&head_term, g, a);
        }
        let record = call(&instance.global, given[..own].to_vec(), sp);
        Some(
            self.unify(ctx, &arguments[0], &head_term)
                && self.unify(ctx, &arguments[1], &record)
                && arguments[2..]
                    .iter()
                    .zip(&given[own..])
                    .all(|(x, y)| self.unify(ctx, x, y)),
        )
    }

    /// `C::m(record, …)` of an instance's record is the instance's own
    /// function `C::m@H(…)`: what a recursive method needs to be a recursion,
    /// and what the proofs read. A law is the instance's theorem likewise,
    /// when the instance proves it.
    fn direct_member(&self, g: &str, args: &[T], sp: Span) -> Option<T> {
        let law = self.classes.law_generics(g);
        if !self.classes.is_method(g) && law.is_none() {
            return None;
        }
        // The class's type and the generics of a law come first, then the
        // record; for a law, then the record of the laws, from which the
        // instance's theorem is read.
        let at = 1 + law.unwrap_or(0);
        let from = at + usize::from(law.is_some());
        if args.len() <= from {
            return None;
        }
        let (class, member) = g.rsplit_once("::")?;
        let (function, given) = match &*args[from].kind {
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(n) => (n.as_str(), arguments.as_slice()),
                _ => return None,
            },
            TermKind::Var(n) => (n.as_str(), &[][..]),
            _ => return None,
        };
        let (c, head) = self.classes.globals.get(function)?;
        if c != class {
            return None;
        }
        if law.is_some()
            && !self
                .classes
                .instances
                .get(&(c.clone(), head.clone()))
                .is_some_and(|i| i.proved.contains(member))
        {
            return None;
        }
        let mut rest = given.to_vec();
        rest.extend(args[1..at].iter().cloned());
        rest.extend(args[from + 1..].iter().cloned());
        Some(call(&format!("{class}::{member}@{head}"), rest, sp))
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
    ) -> Vec<Option<T>> {
        let saved = self.metas.clone();
        let goals = self.argument_goals_in(ctx, function, arguments, expected);
        self.metas = saved;
        goals.unwrap_or_else(|| vec![None; arguments.len()])
    }

    fn argument_goals_in(
        &mut self,
        ctx: &Ctx,
        function: &T,
        arguments: &[Option<T>],
        expected: Option<&T>,
    ) -> Option<Vec<Option<T>>> {
        let sp = function.span;
        let ty = match &*function.kind {
            TermKind::Var(g)
                if !ctx.iter().any(|(n, _)| n == g) && self.globals.contains_key(g) =>
            {
                let global = &self.globals[g];
                let (mut ty, implicit) = (global.ty.clone(), global.implicit);
                let k = implicit + dict_count(&ty, implicit);
                if k > 0 && arguments.len() + k != pi_arity(&ty) {
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
            let mut domains: Vec<(T, Vec<String>)> = Vec::new();
            let mut unknown: Vec<String> = Vec::new();
            for arg in arguments {
                let whnf = self.whnf(ctx, &ty);
                let TermKind::Pi { params, result, .. } = &*whnf.kind else {
                    return None;
                };
                let name = params[0].0.clone().unwrap_or_else(|| "_".into());
                let dom = params[0].1.clone();
                domains.push((dom.clone(), unknown.clone()));
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
            if let Some(e) = expected
                && !unknown.iter().any(|u| occurs(&ty, u))
            {
                self.unify(ctx, &ty, e);
            }
            return Some(
                domains
                    .into_iter()
                    .map(|(d, before)| {
                        let d = self.resolve(&d);
                        (!has_meta(&d) && !before.iter().any(|u| occurs(&d, u))).then_some(d)
                    })
                    .collect(),
            );
        }
        None
    }

    /// `t` with every solved unknown replaced by its solution.
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

    /// Matches `pattern` (which may hold unknowns) against `actual`.
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
                    let vars: Option<Vec<String>> = arguments
                        .iter()
                        .map(|a| match &*a.kind {
                            TermKind::Var(v) if !is_meta(v) => Some(v.clone()),
                            _ => None,
                        })
                        .collect();
                    let Some(vars) = vars else { return false };
                    for (i, v) in vars.iter().enumerate() {
                        if vars[..i].contains(v) {
                            return false;
                        }
                    }
                    let fresh: Vec<String> = vars.iter().map(|v| self.fresh_name(v)).collect();
                    let mut body = actual.clone();
                    for (v, f) in vars.iter().zip(&fresh) {
                        body = self.subst(&body, v, &T::var(f, sp));
                    }
                    let value = fresh.iter().rev().fold(body, |acc, f| lam(f, acc));
                    self.metas.insert(m.clone(), Some(value));
                    return true;
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
    metas: &'a [String],
    names: &'a [String],
    dicts: &'a [(String, T)],
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
            if params[0].0.as_deref().is_some_and(is_dict) {
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
