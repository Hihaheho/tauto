//! `opaque fn`: a function the kernel does not unfold. The declaration
//! becomes ordinary ones, read before the kernel checks anything:
//!
//! ```text
//! fn f@body(x: A): B { body }
//! fn f(x: A): B { f@body(x) }
//! theorem f::eq(x: A): Eq(B, f(x), f@body(x)) { Refl(B, f@body(x)) }
//! ```
//!
//! In `f@body` the recursive calls of `f` are calls of `f@body`. Once `f::eq`
//! is checked, `f` stops unfolding (`Core::seal`): sealing only takes
//! conversions away, so it accepts nothing that the transparent `f` would
//! not. `f::eq` unfolds `f` once, by a step `by rewrite!(f::eq(x)): G0 { … }`,
//! and `f@body` then computes. A program that is run reads the declaration
//! as written.

use super::{Diagnostic, Entry, Kernel, T, Verdict};
use crate::surface::Name;
use crate::surface::{FnDecl, Stmt, TermKind, TheoremDecl, walk};
use std::sync::Arc;
use tauto_message::{Message, msg};
use tauto_surface::identity::Generation;

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

impl Kernel {
    /// The statements with each `opaque fn` made into the declarations it
    /// stands for; `f` is sealed after `f::eq` (`Kernel::declare_one`).
    pub(super) fn opaque_pass(&mut self, stmts: &[Stmt], entries: &mut Vec<Entry>) -> Vec<Stmt> {
        let mut out = Vec::new();
        for stmt in stmts {
            match stmt {
                Stmt::Fn(f) if f.opaque => match self.opaque_expand(f) {
                    Ok(made) => {
                        let equation = self.resolver.generated(&f.name, Generation::OpaqueEquation);
                        let function = self.resolver.global(&f.name);
                        self.seal_after.insert(equation, function);
                        out.extend(made);
                    }
                    Err(d) => entries.push(Entry {
                        name: f.name.clone(),
                        verdict: Verdict::Failed(d),
                    }),
                },
                other => out.push(other.clone()),
            }
        }
        out
    }

    fn opaque_expand(&mut self, f: &FnDecl) -> Result<Vec<Stmt>, Diagnostic> {
        let sp = f.span;
        let fail = |m: Message| Err(Diagnostic::new(m, Some(sp)));
        let eq_name = self.resolver.generated(&f.name, Generation::OpaqueEquation);
        let made = [("theorem".to_string(), eq_name.to_string())];
        if let Some(listed) = &f.generates {
            let start =
                msg!("kernel-opaque-list-mismatch", name = (&f.name).to_string());
            if let Some(why) = crate::generated::mismatch(start, &listed.items, &made) {
                let mut d = Diagnostic::new(why, Some(sp));
                d.fix = Some(crate::generated::fix(listed, &made));
                return Err(d);
            }
        }
        if f.decreasing_by
            .as_ref()
            .is_some_and(|y| !super::names_param(f, y))
        {
            return fail(msg!("kernel-opaque-wf"));
        }
        if !f.where_.is_empty() || f.effects.as_ref().is_some_and(|e| !e.is_empty()) {
            return fail(msg!("kernel-opaque-where"));
        }
        let Some(result) = &f.result else {
            return fail(msg!("kernel-opaque-result"));
        };
        if f.param_types.iter().any(Option::is_none) {
            return fail(msg!("kernel-opaque-typed"));
        }
        let body_name = self.resolver.generated(&f.name, Generation::OpaqueBody);
        let mut body = f.body.clone();
        walk::term(&mut body, &mut |t| {
            if matches!(&*t.kind, TermKind::Var(n) if *n == f.name) {
                *Arc::make_mut(&mut t.kind) = TermKind::Var(body_name.clone());
            }
        });
        let inner = FnDecl {
            name: body_name.clone(),
            opaque: false,
            generates: None,
            body,
            ..f.clone()
        };
        let generics: Vec<T> = f.generics.iter().map(|g| T::var(g, sp)).collect();
        let mut args = generics.clone();
        args.extend(f.params.iter().map(|p| T::var(p, sp)));
        let unfolded = app(T::var(&body_name, sp), args.clone());
        let outer = FnDecl {
            opaque: false,
            decreasing_by: None,
            generates: None,
            body: unfolded.clone(),
            ..f.clone()
        };
        let statement = app(
            T::var(&tauto_surface::bindings::library_name("Eq"), sp),
            vec![
                result.clone(),
                app(T::var(&f.name, sp), args),
                unfolded.clone(),
            ],
        );
        let proof = app(
            T::var(&tauto_surface::bindings::library_name("Refl"), sp),
            vec![result.clone(), unfolded],
        );
        let mut params: Vec<(Name, T)> = f.generic_parameters();
        params.extend(
            f.params
                .iter()
                .cloned()
                .zip(f.param_types.iter().flatten().cloned()),
        );
        let eq = TheoremDecl {
            budget: None,
            vis: f.vis,
            decreasing_by: None,
            name: eq_name,
            implicit: f.generics.len(),
            params,
            ty: statement,
            body: Some(proof),
            span: sp,
        };
        Ok(vec![Stmt::Fn(inner), Stmt::Fn(outer), Stmt::Theorem(eq)])
    }

    /// Stops `f` from unfolding, in the core and in the named checker.
    pub(super) fn seal(&mut self, f: &Name) {
        let _ = self.core.seal(f);
        if let Some(g) = self.globals.get_mut(f) {
            g.value = None;
        }
    }
}
