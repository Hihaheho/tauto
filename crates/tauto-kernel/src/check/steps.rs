//! `mutual` functions that share a number of steps.
//!
//! A `mutual` block whose functions each take a number `k: Nat` first and
//! are defined by `match k { Zero => …, Succ(j) => … }`, calling each other
//! on `j`, cannot be compiled by `check/matching.rs`: they all match on
//! `Nat`. Such a block is read as one function over requests, the way one
//! would write it by hand:
//!
//! * `F'request`, a family with a constructor for each function holding its
//!   other parameters;
//! * `F'answer`, a family with a constructor for each result type;
//! * `F'read(steps: Nat, request: F'request) -> F'answer`, whose arms are the
//!   functions' arms, a call `g(j, a⃗)` becoming
//!   `F'get'i(F'read(j, F'request'g(a⃗)), F'Zero'g(a⃗))`;
//! * `F'Zero'f(a⃗) -> R_i`, the `Zero` arm of `f`;
//! * `F'get'i(answer, default) -> R_i`, the value of an answer of the result
//!   type `R_i`, or `default` for an answer of another type (which a request
//!   never gets);
//! * each function, `f(k, a⃗) = F'get'i(F'read(k, F'request'f(a⃗)), F'Zero'f(a⃗))`,
//!   and so is a call.
//!
//! `F` is the block's first function. Only the functions are reported;
//! extraction reads the block as written. The kernel and `check/core.rs`
//! check the terms these make, as any others.

use crate::surface::Name;
use std::collections::HashMap;
use tauto_surface::identity::{Generation, LocalRef};

use tauto_message::{Message, msg};
use tauto_parol::Span;

use super::{Entry, Kernel, Verdict};
use crate::surface::{
    Constructor, FnDecl, InductiveDecl, MatchArm, Pattern, Stmt, SurfaceTerm, TermKind,
};

/// A function of the block: its declaration, the name `Succ` binds, and its
/// two arms.
struct Member<'a> {
    f: &'a FnDecl,
    pred: Name,
    zero: &'a SurfaceTerm,
    succ: &'a SurfaceTerm,
}

fn var(name: impl Into<Name>, span: Span) -> SurfaceTerm {
    SurfaceTerm::new(TermKind::Var(name.into()), span)
}

fn app(function: impl Into<Name>, arguments: Vec<SurfaceTerm>, span: Span) -> SurfaceTerm {
    SurfaceTerm::new(
        TermKind::App {
            function: Box::new(var(function, span)),
            arguments,
        },
        span,
    )
}

fn arm(pattern: Pattern, body: SurfaceTerm) -> MatchArm {
    MatchArm {
        goal: None,
        pattern,
        guard: None,
        body,
    }
}

fn matching(
    scrutinee: &Name,
    result: &SurfaceTerm,
    arms: Vec<MatchArm>,
    span: Span,
) -> SurfaceTerm {
    SurfaceTerm::new(
        TermKind::Match {
            binder: None,
            scrutinee: Box::new(var(scrutinee, span)),
            result: Some(Box::new(result.clone())),
            arms,
        },
        span,
    )
}

fn ctor_pattern(name: &Name, args: &[Name]) -> Pattern {
    Pattern::Ctor {
        name: name.clone(),
        args: args.iter().map(|a| Pattern::Bind(a.clone())).collect(),
    }
}

fn nat_constructor(name: &Name, constructor: &str) -> bool {
    match name {
        Name::Global(reference) => reference.is_primitive(constructor),
        Name::Selection(selection) => selection
            .candidates()
            .iter()
            .any(|r| r.is_primitive(constructor)),
        _ => false,
    }
}

/// The function's two arms, when it is `match k: T { Zero => …, Succ(j) => … }`
/// on its first parameter, typed `Nat`.
fn member(f: &FnDecl) -> Option<Member<'_>> {
    if !f.generics.is_empty() || f.result.is_none() {
        return None;
    }
    let first = f.params.first()?;
    // Request fields do not bind the fuel, and answers have no parameters.
    if f.param_types
        .iter()
        .skip(1)
        .flatten()
        .any(|ty| super::occurs(ty, first))
        || f.params
            .iter()
            .any(|parameter| super::occurs(f.result.as_ref().unwrap(), parameter))
    {
        return None;
    }
    match &*f.param_types.first()?.as_ref()?.kind {
        TermKind::Var(n) if tauto_surface::bindings::is_library(&n, "Nat") => {}
        _ => return None,
    }
    let TermKind::Match {
        scrutinee, arms, ..
    } = &*f.body.kind
    else {
        return None;
    };
    if !matches!(&*scrutinee.kind, TermKind::Var(x) if x == first) || arms.len() != 2 {
        return None;
    }
    let mut zero = None;
    let mut succ = None;
    for a in arms {
        if a.guard.is_some() {
            return None;
        }
        match &a.pattern {
            Pattern::Bind(n) if nat_constructor(n, "Zero") => zero = Some(&a.body),
            Pattern::Ctor { name, args } if nat_constructor(name, "Zero") && args.is_empty() => {
                zero = Some(&a.body)
            }
            Pattern::Ctor { name, args } if nat_constructor(name, "Succ") => {
                match args.as_slice() {
                    [Pattern::Bind(j)] => succ = Some((j.clone(), &a.body)),
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
    let (pred, succ) = succ?;
    Some(Member {
        f,
        pred,
        zero: zero?,
        succ,
    })
}

/// The names a function of the block is called through: its request, the
/// `get` of its result type and its `Zero`.
struct Call {
    request: Name,
    get: Name,
    zero: Name,
}

/// `t` with each call `g(e, a⃗)` of a function `g` of the block made a
/// request: `get(read(e, request_g(a⃗)), zero_g(a⃗))`.
fn requests(t: &SurfaceTerm, calls: &HashMap<Name, Call>, read: &Name) -> SurfaceTerm {
    let sp = t.span;
    let all = |ts: &[SurfaceTerm]| -> Vec<SurfaceTerm> {
        ts.iter().map(|a| requests(a, calls, read)).collect()
    };
    match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } => {
            if let TermKind::Var(g) = &*function.kind
                && let Some(call) = calls.get(g)
                && let Some((steps, rest)) = arguments.split_first()
            {
                let rest = all(rest);
                let asked = app(
                    read,
                    vec![
                        requests(steps, calls, read),
                        app(&call.request, rest.clone(), sp),
                    ],
                    sp,
                );
                return app(&call.get, vec![asked, app(&call.zero, rest, sp)], sp);
            }
            t.with_kind(
                TermKind::App {
                    function: Box::new(requests(function, calls, read)),
                    arguments: all(arguments),
                },
                sp,
            )
        }
        TermKind::Lam {
            params,
            body,
            types,
        } => t.with_kind(
            TermKind::Lam {
                params: params.clone(),
                body: Box::new(requests(body, calls, read)),
                types: types.clone(),
            },
            sp,
        ),
        TermKind::Match {
            scrutinee,
            result,
            binder,
            arms,
        } => t.with_kind(
            TermKind::Match {
                binder: binder.clone(),
                scrutinee: Box::new(requests(scrutinee, calls, read)),
                result: result.clone(),
                arms: arms
                    .iter()
                    .map(|a| MatchArm {
                        goal: a.goal.clone(),
                        pattern: a.pattern.clone(),
                        guard: a.guard.as_ref().map(|g| requests(g, calls, read)),
                        body: requests(&a.body, calls, read),
                    })
                    .collect(),
            },
            sp,
        ),
        TermKind::Field { base, name } => t.with_kind(
            TermKind::Field {
                base: Box::new(requests(base, calls, read)),
                name: name.clone(),
            },
            sp,
        ),
        TermKind::Record { name, fields, .. } => t.with_kind(
            TermKind::Record {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(n, v)| (n.clone(), requests(v, calls, read)))
                    .collect(),
                base: None,
            },
            sp,
        ),
        _ => t.clone(),
    }
}

impl Kernel {
    /// The block read as one function over requests, when its functions all
    /// take their steps first; `None` when it is not of that shape.
    pub(super) fn shared_steps(&mut self, items: &[Stmt], span: Span) -> Option<Vec<Entry>> {
        if items.len() < 2 {
            return None;
        }
        let mut members = Vec::new();
        for s in items {
            let Stmt::Fn(f) = s else {
                return None;
            };
            members.push(member(f)?);
        }
        let base = &members[0].f.name;
        let request = self.resolver.generated(base, Generation::SharedStepRequest);
        let answer = self.resolver.generated(base, Generation::SharedStepAnswer);
        let read = self.resolver.generated(base, Generation::SharedStepRead);
        let steps: Name = LocalRef::fresh("steps'").into();
        let asked: Name = LocalRef::fresh("request'").into();
        let fuel: Name = LocalRef::fresh("k'").into();
        let ty = |name: &Name| var(name, span);

        // The result types, each with its answer and its `get`.
        let mut results: Vec<SurfaceTerm> = Vec::new();
        let mut result_of = Vec::new();
        for m in &members {
            let r = m.f.result.clone().unwrap();
            let i = match results
                .iter()
                .position(|other| crate::surface::same_term_structure(other, &r))
            {
                Some(i) => i,
                None => {
                    results.push(r);
                    results.len() - 1
                }
            };
            result_of.push(i);
        }
        let positions: HashMap<Name, usize> = members
            .iter()
            .enumerate()
            .map(|(i, m)| (m.f.name.clone(), i))
            .collect();
        let request_ctors: Vec<Name> = (0..members.len())
            .map(|i| {
                self.resolver
                    .generated(&request, Generation::Constructor(i))
            })
            .collect();
        let answer_ctors: Vec<Name> = (0..results.len())
            .map(|i| self.resolver.generated(&answer, Generation::Constructor(i)))
            .collect();
        let gets: Vec<Name> = (0..results.len())
            .map(|i| self.resolver.generated(base, Generation::SharedStepGet(i)))
            .collect();
        let zeros: Vec<Name> = members
            .iter()
            .map(|m| {
                self.resolver
                    .generated(&m.f.name, Generation::SharedStepZero)
            })
            .collect();
        let answer_ctor = |i: usize| answer_ctors[i].clone();
        let get = |i: usize| gets[i].clone();
        let request_ctor = |m: &Member| request_ctors[positions[&m.f.name]].clone();
        let zero = |m: &Member| zeros[positions[&m.f.name]].clone();
        let mut calls = HashMap::new();
        for (m, i) in members.iter().zip(&result_of) {
            calls.insert(
                m.f.name.clone(),
                Call {
                    request: request_ctor(m),
                    get: get(*i),
                    zero: zero(m),
                },
            );
        }

        let mut decls: Vec<Stmt> = Vec::new();
        let mut ctors = Vec::new();
        for m in &members {
            let mut params = Vec::new();
            for (n, t) in m.f.params.iter().zip(&m.f.param_types).skip(1) {
                let Some(t) = t else {
                    return Some(self.steps_fail(
                        &members,
                        msg!("kernel-mutual-param-typed"),
                        span,
                    ));
                };
                params.push((n.clone(), t.clone()));
            }
            ctors.push(Constructor {
                name: request_ctor(m),
                implicit: 0,
                params,
                result: ty(&request),
            });
        }
        decls.push(Stmt::Inductive(InductiveDecl {
            vis: Default::default(),
            generates: Default::default(),
            name: request.clone(),
            params: Vec::new(),
            sort: ty(&tauto_surface::bindings::library_name("Type")),
            constructors: ctors,
            span,
        }));
        decls.push(Stmt::Inductive(InductiveDecl {
            vis: Default::default(),
            generates: Default::default(),
            name: answer.clone(),
            params: Vec::new(),
            sort: ty(&tauto_surface::bindings::library_name("Type")),
            constructors: results
                .iter()
                .enumerate()
                .map(|(i, r)| Constructor {
                    name: answer_ctor(i),
                    implicit: 0,
                    params: vec![(LocalRef::fresh("value'").into(), r.clone())],
                    result: ty(&answer),
                })
                .collect(),
            span,
        }));
        for m in &members {
            let body = self.subst(
                m.zero,
                &m.f.params[0],
                &var(&tauto_surface::bindings::library_name("Zero"), span),
            );
            decls.push(Stmt::Fn(FnDecl {
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                decreasing_by: None,
                name: zero(m),
                generic_types: Vec::new(),
                generics: Vec::new(),
                rows: Vec::new(),
                bounds: Vec::new(),
                bound_spans: Vec::new(),
                params: m.f.params[1..].to_vec(),
                borrows: vec![None; m.f.params.len() - 1],
                param_types: m.f.param_types[1..].to_vec(),
                result: m.f.result.clone(),
                effects: None,
                where_: Vec::new(),
                span,
                body,
            }));
        }
        for (i, r) in results.iter().enumerate() {
            let value: Name = LocalRef::fresh("value'").into();
            let answer_parameter: Name = LocalRef::fresh("answer'").into();
            let default: Name = LocalRef::fresh("default'").into();
            let mut arms = vec![arm(
                ctor_pattern(&answer_ctor(i), std::slice::from_ref(&value)),
                var(&value, span),
            )];
            if results.len() > 1 {
                arms.push(arm(Pattern::Wild, var(&default, span)));
            }
            decls.push(Stmt::Fn(FnDecl {
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                decreasing_by: None,
                name: get(i),
                generic_types: Vec::new(),
                generics: Vec::new(),
                rows: Vec::new(),
                bounds: Vec::new(),
                bound_spans: Vec::new(),
                params: vec![answer_parameter.clone(), default],
                borrows: vec![None, None],
                param_types: vec![Some(ty(&answer)), Some(r.clone())],
                result: Some(r.clone()),
                effects: None,
                where_: Vec::new(),
                span,
                body: matching(&answer_parameter, r, arms, span),
            }));
        }
        let mut zero_arms = Vec::new();
        let mut succ_arms = Vec::new();
        for (m, i) in members.iter().zip(&result_of) {
            let pattern = ctor_pattern(&request_ctor(m), &m.f.params[1..]);
            zero_arms.push(arm(
                pattern.clone(),
                app(
                    &answer_ctor(*i),
                    vec![app(
                        &zero(m),
                        m.f.params[1..].iter().map(|p| var(p, span)).collect(),
                        span,
                    )],
                    span,
                ),
            ));
            // A `let` stands for its value (`expand_lets`), calls included.
            let succ = self.expand_lets(m.succ).unwrap_or_else(|_| m.succ.clone());
            let succ = self.subst(
                &succ,
                &m.f.params[0],
                &app(
                    &tauto_surface::bindings::library_name("Succ"),
                    vec![var(&steps, span)],
                    span,
                ),
            );
            let body = self.subst(&succ, &m.pred, &var(&steps, span));
            succ_arms.push(arm(
                pattern,
                app(&answer_ctor(*i), vec![requests(&body, &calls, &read)], span),
            ));
        }
        let answer_ty = ty(&answer);
        decls.push(Stmt::Fn(FnDecl {
            budget: None,
            vis: Default::default(),
            generates: None,
            opaque: false,
            decreasing_by: None,
            name: read.clone(),
            generic_types: Vec::new(),
            generics: Vec::new(),
            rows: Vec::new(),
            bounds: Vec::new(),
            bound_spans: Vec::new(),
            params: vec![fuel.clone(), asked.clone()],
            borrows: vec![None, None],
            param_types: vec![
                Some(ty(&tauto_surface::bindings::library_name("Nat"))),
                Some(ty(&request)),
            ],
            result: Some(answer_ty.clone()),
            effects: None,
            where_: Vec::new(),
            span,
            body: matching(
                &fuel,
                &answer_ty,
                vec![
                    arm(
                        Pattern::Bind(tauto_surface::bindings::library_name("Zero")),
                        matching(&asked, &answer_ty, zero_arms, span),
                    ),
                    arm(
                        ctor_pattern(
                            &tauto_surface::bindings::library_name("Succ"),
                            std::slice::from_ref(&steps),
                        ),
                        matching(&asked, &answer_ty, succ_arms, span),
                    ),
                ],
                span,
            ),
        }));
        for (m, i) in members.iter().zip(&result_of) {
            let args: Vec<SurfaceTerm> = m.f.params[1..].iter().map(|p| var(p, span)).collect();
            let asked = app(
                &read,
                vec![
                    var(&m.f.params[0], span),
                    app(&request_ctor(m), args.clone(), span),
                ],
                span,
            );
            let mut f = m.f.clone();
            f.body = app(&get(*i), vec![asked, app(&zero(m), args, span)], span);
            decls.push(Stmt::Fn(f));
        }

        // The requests, the answers and `read` first; a failure there is the
        // block's.
        self.resolver.statements(&mut decls);
        let helpers = decls.len() - members.len();
        let mut out = Vec::new();
        for (at, d) in decls.iter().enumerate() {
            let verdict = match d {
                Stmt::Inductive(i) => self.inductive(i),
                Stmt::Fn(f) => self.function(f),
                _ => unreachable!(),
            };
            if at < helpers {
                if !matches!(verdict, Verdict::Checked { .. }) {
                    return Some(
                        members
                            .iter()
                            .map(|m| Entry {
                                name: m.f.name.clone(),
                                verdict: verdict.clone(),
                            })
                            .collect(),
                    );
                }
                continue;
            }
            out.push(Entry {
                name: members[at - helpers].f.name.clone(),
                verdict,
            });
        }
        if self.record_sites
            && out
                .iter()
                .all(|entry| matches!(entry.verdict, Verdict::Checked { .. }))
        {
            for member in &members {
                let TermKind::Match { arms, .. } = &*member.f.body.kind else {
                    unreachable!()
                };
                for arm in arms {
                    let written = match &arm.pattern {
                        Pattern::Bind(name) | Pattern::Ctor { name, .. } => name,
                        _ => unreachable!(),
                    };
                    let constructor = if nat_constructor(written, "Zero") {
                        "Zero"
                    } else {
                        "Succ"
                    };
                    let occurrences = self
                        .ctor_site_origins
                        .get(&arm.body.id())
                        .cloned()
                        .unwrap_or_else(|| vec![arm.body.id()]);
                    for occurrence in occurrences {
                        self.ctor_sites.push(super::CtorSite {
                            expression: false,
                            occurrence,
                            span: arm.body.span,
                            written: written.clone(),
                            resolved: tauto_surface::bindings::library_name(constructor),
                        });
                    }
                }
            }
        }
        Some(out)
    }

    fn steps_fail(&self, members: &[Member], message: Message, span: Span) -> Vec<Entry> {
        members
            .iter()
            .map(|m| Entry {
                name: m.f.name.clone(),
                verdict: Verdict::Failed(super::Diagnostic::new(message.clone(), Some(span))),
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tauto_surface::identity::{DeclRef, Selection};

    #[test]
    fn natural_patterns_select_by_identity_from_candidates() {
        let zero = DeclRef::primitive("Zero").unwrap();
        let other = DeclRef::fresh("Zero");
        let selected: Name = Selection::new("renamed", vec![other.clone(), zero]).into();
        assert!(nat_constructor(&selected, "Zero"));
        assert!(!nat_constructor(&selected, "Succ"));
        let unrelated: Name = Selection::new("Zero", vec![other]).into();
        assert!(!nat_constructor(&unrelated, "Zero"));
        assert!(!nat_constructor(&Name::from("Zero"), "Zero"));
    }
}
