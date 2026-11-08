//! `decreasing_by`: well-founded recursion, written out with the library of
//! `std/WellFounded.taut`. The kernel gets no rule for it; the declaration
//! becomes ordinary ones, read before the kernel checks anything.
//!
//! `fn f(x: A, p: P): B decreasing_by W { body }`, where `W` is a `WfRel(A)`,
//! recurs on the first parameter, and the parameters after it may change. In
//! the body a recursive call is `f(y, q, h)`: the arguments, then a proof `h`
//! that `y` is below `x`. It is read as a call of `ih'`, the values at the
//! predecessors, which the declaration `f@step` takes:
//!
//! ```text
//! fn f@step(x: A, ih': ∀ y: A. R(y, x) -> ∀ q: P[y/x]. B[y/x, q/p], p: P): B { body }
//! fn f(x: A, p: P): B { wf_fix(A, R, y => ∀ q: P[y/x]. B[y/x, q/p], wf, f@step, x)(p) }
//! theorem f::eq(x: A, p: P): Eq(B, f(x, p), f@step(x, y => r => q => f(y, q), p))
//! ```
//!
//! `R` and `wf` are what `W` carries. `f::eq` is the unfolding equation: `f`
//! itself does not compute where its proof of well-foundedness is not a
//! constructor. A program that is run reads the declaration as written, with
//! the proofs left out of the calls.

use super::{Diagnostic, Entry, Kernel, T, Verdict};
use crate::surface::Name;
use crate::surface::{FnDecl, Stmt, TheoremDecl};
use crate::surface::{TermKind, walk};
use std::sync::Arc;
use tauto_message::{Message, msg};

fn var(n: impl Into<Name>, sp: tauto_parol::Span) -> T {
    T::new(TermKind::Var(n.into()), sp)
}

fn app(f: T, args: Vec<T>) -> T {
    let span = f.span;
    if args.is_empty() {
        return f;
    }
    T::new(
        TermKind::App {
            function: Box::new(f),
            arguments: args,
        },
        span,
    )
}

fn pi(name: Option<&Name>, domain: T, result: T) -> T {
    let span = result.span;
    T::new(
        TermKind::Pi {
            params: vec![(name.cloned(), domain)],
            result: Box::new(result),
            effects: None,
        },
        span,
    )
}

fn lam(names: &[Name], body: T) -> T {
    names.iter().rev().fold(body, |acc, n| {
        let span = acc.span;
        T::new(
            TermKind::Lam {
                params: vec![n.clone()],
                body: Box::new(acc),
                types: Vec::new(),
            },
            span,
        )
    })
}

fn primed(n: &str) -> Name {
    format!("{n}'").into()
}

impl Kernel {
    /// The statements with each `decreasing_by` function made into the
    /// declarations it stands for.
    pub(super) fn wf_pass(&mut self, stmts: &[Stmt], entries: &mut Vec<Entry>) -> Vec<Stmt> {
        let mut out = Vec::new();
        for stmt in stmts {
            match stmt {
                Stmt::Fn(f)
                    if f.decreasing_by
                        .as_ref()
                        .is_some_and(|y| !super::names_param(f, y)) =>
                {
                    match self.wf_expand(f) {
                        Ok(made) => out.extend(made),
                        Err(d) => entries.push(Entry {
                            name: f.name.clone(),
                            verdict: Verdict::Failed(d),
                        }),
                    }
                }
                other => out.push(other.clone()),
            }
        }
        out
    }

    fn wf_expand(&mut self, f: &FnDecl) -> Result<Vec<Stmt>, Diagnostic> {
        let sp = f.span;
        let fail = |m: Message| Err(Diagnostic::new(m, Some(sp)));
        let Some(w) = &f.decreasing_by else {
            unreachable!("only a function with `decreasing_by` is expanded")
        };
        if let Some(listed) = &f.generates {
            let made = [("theorem".to_string(), format!("{}::eq", f.name))];
            let start = msg!("kernel-wf-list-mismatch", name = (&f.name).to_string());
            if let Some(why) = crate::generated::mismatch(start, &listed.items, &made) {
                let mut d = Diagnostic::new(why, Some(sp));
                d.fix = Some(crate::generated::fix(listed, &made));
                return Err(d);
            }
        }
        let mut required = Vec::new();
        for needed in ["wf_fix", "wf_fix_eq", "wf_rel_lt", "wf_rel_wf"] {
            let Some(reference) = self
                .resolver
                .source_reference(needed)
                .filter(|reference| self.globals.contains_key(reference))
            else {
                return fail(msg!("kernel-wf-needs", name = needed));
            };
            required.push(reference);
        }
        let [wf_fix, wf_fix_eq, wf_rel_lt, wf_rel_wf] = required.as_slice() else {
            unreachable!()
        };
        if f.params.is_empty() {
            return fail(msg!("kernel-wf-no-param"));
        }
        if !f.where_.is_empty() || f.effects.as_ref().is_some_and(|e| !e.is_empty()) {
            return fail(msg!("kernel-wf-where"));
        }
        let Some(result) = &f.result else {
            return fail(msg!("kernel-wf-result"));
        };
        let mut types = Vec::new();
        for t in &f.param_types {
            match t {
                Some(t) => types.push(t.clone()),
                None => return fail(msg!("kernel-wf-typed")),
            }
        }
        let (x, a) = (f.params[0].clone(), types[0].clone());
        let rest: Vec<(Name, T)> = f.params[1..]
            .iter()
            .cloned()
            .zip(types[1..].iter().cloned())
            .collect();
        let generics: Vec<T> = f.generics.iter().map(|g| var(g, sp)).collect();
        let step = self.resolver.generated(
            &f.name,
            tauto_surface::identity::Generation::WellFoundedStep,
        );
        let equation = self.resolver.generated(
            &f.name,
            tauto_surface::identity::Generation::WellFoundedEquation,
        );
        let ih = "ih'".to_string();
        let lt = |y: &T, x: &T| -> T {
            app(
                var(wf_rel_lt, sp),
                vec![a.clone(), w.clone(), y.clone(), x.clone()],
            )
        };

        // `t` with the parameters replaced: `x` by `new_x`, the later
        // parameters by `new_rest`.
        let rename = |this: &mut Self, t: &T, new_x: &str, new_rest: &[Name]| -> T {
            let mut t = this.subst(t, &x, &var(new_x, sp));
            for ((p, _), q) in rest.iter().zip(new_rest) {
                t = this.subst(&t, p, &var(q, sp));
            }
            t
        };
        // `∀ q: P[y/x, …]. B[y/x, …]` over the later parameters, for `y`.
        let tail = |this: &mut Self, y: &str| -> T {
            let qs: Vec<Name> = rest.iter().map(|(p, _)| primed(p)).collect();
            let mut body = rename(this, result, y, &qs);
            for (i, (_, ty)) in rest.iter().enumerate().rev() {
                let before: Vec<Name> = qs[..i].to_vec();
                let mut domain = this.subst(ty, &x, &var(y, sp));
                for ((p, _), q) in rest.iter().zip(&before) {
                    domain = this.subst(&domain, p, &var(q, sp));
                }
                body = pi(Some(&qs[i]), domain, body);
            }
            body
        };

        let y = primed(&x);
        let hypothesis = lt(&var(&y, sp), &var(&x, sp));
        let ih_ty = pi(Some(&y), a.clone(), pi(None, hypothesis, tail(self, &y)));

        // The body, its recursive calls read as calls of `ih'`.
        let mut body = f.body.clone();
        let mut bad: Option<Diagnostic> = None;
        let arity = f.params.len() + 1;
        walk::term(&mut body, &mut |t| match Arc::make_mut(&mut t.kind) {
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(n) if *n == f.name) => {
                if arguments.len() != arity {
                    bad.get_or_insert_with(|| {
                        Diagnostic::new(
                            msg!(
                                "kernel-wf-call-arity",
                                name = (&f.name).to_string(),
                                count = f.params.len(),
                                param = (&x).to_string()
                            ),
                            Some(t.span),
                        )
                    });
                    return;
                }
                let proof = arguments.pop().expect("one more than the parameters");
                arguments.insert(1, proof);
                **function = var(&ih, function.span);
            }
            TermKind::Var(n) if *n == f.name => {
                bad.get_or_insert_with(|| {
                    Diagnostic::new(
                        msg!("kernel-wf-only-called", name = (&f.name).to_string()),
                        Some(t.span),
                    )
                });
            }
            _ => {}
        });
        if let Some(d) = bad {
            return Err(d);
        }

        let mut params = vec![x.clone(), crate::surface::Name::Spelled(ih.clone())];
        params.extend(rest.iter().map(|(p, _)| p.clone()));
        let mut param_types = vec![Some(a.clone()), Some(ih_ty)];
        param_types.extend(rest.iter().map(|(_, t)| Some(t.clone())));
        let aux = FnDecl {
            budget: None,
            vis: Default::default(),
            generates: None,
            name: step.clone(),
            generic_types: f.generic_types.clone(),
            generics: f.generics.clone(),
            rows: f.rows.clone(),
            bounds: f.bounds.clone(),
            bound_spans: f.bound_spans.clone(),
            borrows: vec![None; params.len()],
            params,
            param_types,
            result: Some(result.clone()),
            effects: None,
            where_: Vec::new(),
            span: sp,
            opaque: false,
            decreasing_by: None,
            body,
        };

        let motive = lam(&[primed(&x)], tail(self, &primed(&x)));
        let relation = app(var(wf_rel_lt, sp), vec![a.clone(), w.clone()]);
        let proof_wf = app(var(wf_rel_wf, sp), vec![a.clone(), w.clone()]);
        let step_fn = app(var(&step, sp), generics.clone());
        let fixed = |extra: Vec<T>| -> T {
            let mut args = vec![
                a.clone(),
                relation.clone(),
                motive.clone(),
                proof_wf.clone(),
            ];
            args.extend(extra);
            app(var(wf_fix, sp), args)
        };
        let rest_vars: Vec<T> = rest.iter().map(|(p, _)| var(p, sp)).collect();
        let value = app(fixed(vec![step_fn.clone(), var(&x, sp)]), rest_vars.clone());
        let main = FnDecl {
            budget: f.budget,
            vis: Default::default(),
            generates: None,
            name: f.name.clone(),
            generic_types: f.generic_types.clone(),
            generics: f.generics.clone(),
            rows: f.rows.clone(),
            bounds: f.bounds.clone(),
            bound_spans: f.bound_spans.clone(),
            params: f.params.clone(),
            borrows: vec![None; f.params.len()],
            param_types: f.param_types.clone(),
            result: Some(result.clone()),
            effects: None,
            where_: Vec::new(),
            span: sp,
            opaque: false,
            decreasing_by: None,
            body: value,
        };

        // The unfolding equation.
        let qs: Vec<Name> = rest.iter().map(|(p, _)| primed(p)).collect();
        let recur = |ys: &str| -> T {
            let mut args = generics.clone();
            args.push(var(ys, sp));
            args.extend(qs.iter().map(|q| var(q, sp)));
            app(var(&f.name, sp), args)
        };
        let mut names = vec![y.clone(), crate::surface::Name::Spelled("r'".to_string())];
        names.extend(qs.iter().cloned());
        let ih_value = lam(&names, recur(&y));
        let call_f = |args: Vec<T>| -> T {
            let mut all = generics.clone();
            all.extend(args);
            app(var(&f.name, sp), all)
        };
        let mut f_args = vec![var(&x, sp)];
        f_args.extend(rest_vars.clone());
        let mut step_args = generics.clone();
        step_args.push(var(&x, sp));
        step_args.push(ih_value);
        step_args.extend(rest_vars.clone());
        let statement = app(
            var(&tauto_surface::bindings::library_name("Eq"), sp),
            vec![
                result.clone(),
                call_f(f_args),
                app(var(&step, sp), step_args),
            ],
        );
        let value_at = fixed(vec![step_fn, var(&x, sp)]);
        let at_rest = app(value_at.clone(), rest_vars.clone());
        let z = "z'".to_string();
        let transport = lam(
            std::slice::from_ref(&Name::from(&z)),
            app(
                var(&tauto_surface::bindings::library_name("Eq"), sp),
                vec![
                    result.clone(),
                    at_rest.clone(),
                    app(var(&z, sp), rest_vars.clone()),
                ],
            ),
        );
        let unfolding = {
            let args = vec![
                a.clone(),
                relation.clone(),
                motive.clone(),
                proof_wf.clone(),
                app(var(&step, sp), generics.clone()),
                var(&x, sp),
            ];
            app(var(wf_fix_eq, sp), args)
        };
        let proof = app(
            var(&tauto_surface::bindings::library_name("Eq::subst"), sp),
            vec![
                transport,
                unfolding,
                app(
                    var(&tauto_surface::bindings::library_name("Refl"), sp),
                    vec![result.clone(), at_rest],
                ),
            ],
        );
        let mut eq_params: Vec<(Name, T)> = f.generic_parameters();
        eq_params.push((x.clone(), a.clone()));
        eq_params.extend(rest.iter().cloned());
        let eq = TheoremDecl {
            budget: None,
            vis: Default::default(),
            decreasing_by: None,
            name: equation,
            implicit: f.generics.len(),
            params: eq_params,
            ty: statement,
            body: Some(proof),
            span: sp,
        };
        Ok(vec![Stmt::Fn(aux), Stmt::Fn(main), Stmt::Theorem(eq)])
    }
}
