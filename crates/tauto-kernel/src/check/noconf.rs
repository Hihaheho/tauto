//! No-confusion for an inductive type without indices, generated from its
//! eliminator: constructors are injective and distinct. This is what lets a
//! `match` on an indexed family unify the family's indices with a
//! constructor's.
//!
//! For `I` with constructors `c_j(a⃗)`:
//!
//! * `I::nc(p⃗, P, x, y) : Type`, by recursion on both: `(a_i = b_i → … → P) → P`
//!   when both are `c_j`, and `P` otherwise;
//! * `I::nc_diag(p⃗, P, x) : I::nc(p⃗, P, x, x)`;
//! * `I::noconf(p⃗, P, x, y, e: x = y) : I::nc(p⃗, P, x, y)`.
//!
//! Only arguments whose type mentions no earlier argument (and lives in
//! `Type`) get an equation; the others cannot be compared without
//! heterogeneous equality.

use crate::surface::Name;
use std::collections::BTreeSet;
use tauto_surface::identity::Generation;

use super::inductive::{app, pi_all, var};
use super::{Ctx, Kernel, Sort, T, lam, occurs, pi};

fn eq(ty: &T, a: &T, b: &T) -> T {
    app(
        var(tauto_surface::bindings::library_name("Eq")),
        vec![ty.clone(), a.clone(), b.clone()],
    )
}

fn lams(names: &[Name], body: T) -> T {
    names.iter().rev().fold(body, |acc, n| lam(n, acc))
}

impl Kernel {
    /// Generates `I::nc`, `I::nc_diag` and `I::noconf`; an inductive for which
    /// they do not check simply has no no-confusion.
    pub(super) fn no_confusion(&mut self, family: &Name) {
        if !self
            .globals
            .contains_key(&tauto_surface::bindings::library_name("Eq::rec"))
            || !self
                .inds
                .contains_key(&tauto_surface::bindings::library_name("Eq"))
        {
            return;
        }
        let Some(ind) = self.inds.get(family).cloned() else {
            return;
        };
        let (nc, diag, noconf) = (
            self.resolver.generated(family, Generation::NoConfusionType),
            self.resolver
                .generated(family, Generation::NoConfusionDiagonal),
            self.resolver.generated(family, Generation::NoConfusion),
        );
        // A name already taken keeps its meaning; the type gets no
        // no-confusion.
        if [&nc, &diag, &noconf]
            .iter()
            .any(|n| self.globals.contains_key(n))
        {
            return;
        }
        // The other members of a mutual group get trivial motives and minors.
        let members: Vec<(Name, super::inductive::Ind)> = ind
            .group
            .iter()
            .filter_map(|g| self.inds.get(g).map(|i| (g.clone(), i.clone())))
            .collect();
        if members.len() != ind.group.len()
            || members.iter().any(|(_, m)| m.indices != 0)
            || (members.len() > 1
                && (!self
                    .globals
                    .contains_key(&tauto_surface::bindings::library_name("Unit"))
                    || !self
                        .globals
                        .contains_key(&tauto_surface::bindings::library_name("Star"))))
        {
            return;
        }
        let rec = var(self.resolver.generated(family, Generation::Recursion));
        let pnames: Vec<Name> = ind.params.iter().map(|(n, _)| n.clone()).collect();
        let pvars: Vec<T> = pnames.iter().map(|n| var(n)).collect();
        let this = app(var(family), pvars.clone());
        let ty_sort = var(tauto_surface::bindings::library_name("Type"));

        let mut inj: Vec<Vec<usize>> = Vec::new();
        for c in &ind.ctors {
            let mut ctx: Ctx = ind.params.clone();
            let mut keep = Vec::new();
            for (i, (n, t)) in c.args.iter().enumerate() {
                let independent = c.args[..i].iter().all(|(m, _)| !occurs(t, m));
                let small = self.expect_type(&ctx, t).is_ok_and(|s| s.le(&Sort::ty(0)));
                if independent && small {
                    keep.push(i);
                }
                ctx.push((n.clone(), t.clone()));
            }
            inj.push(keep);
        }

        let fields = |c: &super::inductive::Ctor, tag: &str| -> Vec<Name> {
            (0..c.args.len())
                .map(|i| Name::from(format!("{tag}'{i}")))
                .collect()
        };
        let ihs = |c: &super::inductive::Ctor, tag: &str| -> Vec<Name> {
            (0..c.recs.len())
                .map(|i| Name::from(format!("{tag}h'{i}")))
                .collect()
        };

        let nc_ty = pi_all(
            &ind.params,
            pi(
                "P",
                ty_sort.clone(),
                pi("x", this.clone(), pi("y", this.clone(), ty_sort.clone())),
            ),
        );
        let mut outer_minors = Vec::new();
        for (g, gi) in &members {
            for (j, c) in gi.ctors.iter().enumerate() {
                let a = fields(c, "a");
                let all: Vec<Name> = [a.clone(), ihs(c, "a")].concat();
                if g != family {
                    outer_minors.push(lams(
                        &all,
                        var(tauto_surface::bindings::library_name("Star")),
                    ));
                    continue;
                }
                let mut inner_minors = Vec::new();
                for (g2, gi2) in &members {
                    for (k, d) in gi2.ctors.iter().enumerate() {
                        let b = fields(d, "b");
                        let body = if g2 == family && k == j {
                            let eqs: Vec<(Name, T)> = inj[j]
                                .iter()
                                .map(|&i| {
                                    (
                                        Name::from(format!("q'{i}")),
                                        eq(&c.args[i].1, &var(&a[i]), &var(&b[i])),
                                    )
                                })
                                .collect();
                            pi("k'", pi_all(&eqs, var("P")), var("P"))
                        } else {
                            var("P")
                        };
                        let all2: Vec<Name> = [b, ihs(d, "b")].concat();
                        inner_minors.push(lams(&all2, body));
                    }
                }
                let mut args = pvars.clone();
                for _ in &members {
                    args.push(lam("z'", ty_sort.clone()));
                }
                args.extend(inner_minors);
                args.push(var("y"));
                outer_minors.push(lams(&all, lam("y", app(rec.clone(), args))));
            }
        }
        let motive1 = lam("z'", pi("w'", this.clone(), ty_sort.clone()));
        let mut args = pvars.clone();
        for (g, _) in &members {
            args.push(if g == family {
                motive1.clone()
            } else {
                lam("z'", var(tauto_surface::bindings::library_name("Unit")))
            });
        }
        args.extend(outer_minors);
        args.push(var("x"));
        let body = app(app(rec.clone(), args), vec![var("y")]);
        let mut names = pnames.clone();
        names.extend(["P".into(), "x".into(), "y".into()]);
        let nc_val = lams(&names, body);

        let nc_at = |x: &T, y: &T| -> T {
            let mut args = pvars.clone();
            args.extend([var("P"), x.clone(), y.clone()]);
            app(var(&nc), args)
        };
        let diag_ty = pi_all(
            &ind.params,
            pi(
                "P",
                ty_sort.clone(),
                pi("x", this.clone(), nc_at(&var("x"), &var("x"))),
            ),
        );
        let mut minors = Vec::new();
        for (g, gi) in &members {
            for (j, c) in gi.ctors.iter().enumerate() {
                let a = fields(c, "a");
                let all: Vec<Name> = [a.clone(), ihs(c, "a")].concat();
                if g != family {
                    minors.push(lams(
                        &all,
                        var(tauto_surface::bindings::library_name("Star")),
                    ));
                    continue;
                }
                let refls: Vec<T> = inj[j]
                    .iter()
                    .map(|&i| {
                        app(
                            var(tauto_surface::bindings::library_name("Refl")),
                            vec![c.args[i].1.clone(), var(&a[i])],
                        )
                    })
                    .collect();
                let call = app(var("f"), refls);
                minors.push(lams(&all, lam("f", call)));
            }
        }
        let motive = lam("z'", nc_at(&var("z'"), &var("z'")));
        let mut args = pvars.clone();
        for (g, _) in &members {
            args.push(if g == family {
                motive.clone()
            } else {
                lam("z'", var(tauto_surface::bindings::library_name("Unit")))
            });
        }
        args.extend(minors);
        args.push(var("x"));
        let mut names = pnames.clone();
        names.extend(["P".into(), "x".into()]);
        let diag_val = lams(&names, app(rec.clone(), args));

        let noconf_ty = pi_all(
            &ind.params,
            pi(
                "P",
                ty_sort.clone(),
                pi(
                    "x",
                    this.clone(),
                    pi(
                        "y",
                        this.clone(),
                        pi(
                            "e",
                            eq(&this, &var("x"), &var("y")),
                            nc_at(&var("x"), &var("y")),
                        ),
                    ),
                ),
            ),
        );
        let mut diag_args = pvars.clone();
        diag_args.extend([var("P"), var("x")]);
        let motive = lam("z'", lam("e'", nc_at(&var("x"), &var("z'"))));
        let body = app(
            var(tauto_surface::bindings::library_name("Eq::rec")),
            vec![
                this.clone(),
                var("x"),
                motive,
                app(var(&diag), diag_args),
                var("y"),
                var("e"),
            ],
        );
        let mut names = pnames.clone();
        names.extend(["P".into(), "x".into(), "y".into(), "e".into()]);
        let noconf_val = lams(&names, body);

        let all_names = [nc.clone(), diag.clone(), noconf.clone()];
        let decls = [
            (&nc, nc_ty, nc_val),
            (&diag, diag_ty, diag_val),
            (&noconf, noconf_ty, noconf_val),
        ];
        // Checked before (`check/cache.rs`): only the core checks them again.
        let cache_declarations: Vec<_> = decls
            .iter()
            .map(|(name, ty, value)| {
                crate::surface::Stmt::Def(crate::surface::TheoremDecl {
                    name: (*name).clone(),
                    ty: ty.clone(),
                    body: Some(value.clone()),
                    params: Vec::new(),
                    implicit: 0,
                    span: value.span,
                    vis: Default::default(),
                    budget: None,
                    decreasing_by: None,
                })
            })
            .collect();
        let key = self.key(
            &cache_declarations,
            &[nc.clone(), diag.clone(), noconf.clone()],
        );
        let before = key
            .as_ref()
            .is_some_and(|k| self.cache.as_ref().is_some_and(|c| c.get(k).is_some()));
        for (name, ty, val) in decls {
            let ok = (before
                || self.expect_type(&Vec::new(), &ty).is_ok()
                    && self.check(&Vec::new(), &val, &ty).is_ok())
                && self.core.add_decl(name, &ty, Some(&val), true).is_ok();
            if !ok {
                for n in &all_names {
                    self.globals.remove(n);
                }
                return;
            }
            self.add(name, ty, Some(val), BTreeSet::new());
        }
        if let (Some(key), Some(cache), false) = (&key, &self.cache, before) {
            cache.put(key, &BTreeSet::new());
        }
        if let Some(i) = self.inds.get_mut(family) {
            for (c, keep) in i.ctors.iter_mut().zip(inj) {
                c.inj = keep;
            }
        }
    }
}
