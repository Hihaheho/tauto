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

use std::collections::HashMap;

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
    pred: String,
    zero: &'a SurfaceTerm,
    succ: &'a SurfaceTerm,
}

fn var(name: &str, span: Span) -> SurfaceTerm {
    SurfaceTerm::var(name, span)
}

fn app(function: &str, arguments: Vec<SurfaceTerm>, span: Span) -> SurfaceTerm {
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

fn matching(scrutinee: &str, result: &SurfaceTerm, arms: Vec<MatchArm>, span: Span) -> SurfaceTerm {
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

fn ctor_pattern(name: &str, args: &[String]) -> Pattern {
    Pattern::Ctor {
        name: name.to_string(),
        args: args.iter().map(|a| Pattern::Bind(a.clone())).collect(),
    }
}

/// The function's two arms, when it is `match k: T { Zero => …, Succ(j) => … }`
/// on its first parameter, typed `Nat`.
fn member(f: &FnDecl) -> Option<Member<'_>> {
    if !f.generics.is_empty() || f.result.is_none() {
        return None;
    }
    let first = f.params.first()?;
    match &*f.param_types.first()?.as_ref()?.kind {
        TermKind::Var(n) if n == "Nat" => {}
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
            Pattern::Bind(n) if n == "Zero" => zero = Some(&a.body),
            Pattern::Ctor { name, args } if name == "Zero" && args.is_empty() => {
                zero = Some(&a.body)
            }
            Pattern::Ctor { name, args } if name == "Succ" => match args.as_slice() {
                [Pattern::Bind(j)] => succ = Some((j.clone(), &a.body)),
                _ => return None,
            },
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
    request: String,
    get: String,
    zero: String,
}

/// `t` with each call `g(e, a⃗)` of a function `g` of the block made a
/// request: `get(read(e, request_g(a⃗)), zero_g(a⃗))`.
fn requests(t: &SurfaceTerm, calls: &HashMap<String, Call>, read: &str) -> SurfaceTerm {
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
            SurfaceTerm::new(
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
        } => SurfaceTerm::new(
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
        } => SurfaceTerm::new(
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
        TermKind::Field { base, name } => SurfaceTerm::new(
            TermKind::Field {
                base: Box::new(requests(base, calls, read)),
                name: name.clone(),
            },
            sp,
        ),
        TermKind::Record { name, fields, .. } => SurfaceTerm::new(
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
        let request = format!("{base}'request");
        let answer = format!("{base}'answer");
        let read = format!("{base}'read");
        let steps = "steps'".to_string();
        let asked = "request'".to_string();
        let ty = |name: &str| var(name, span);

        let mut results: Vec<(String, SurfaceTerm)> = Vec::new();
        let mut result_of = Vec::new();
        for m in &members {
            let r = m.f.result.clone().unwrap();
            let key = super::describe(&r);
            let i = match results.iter().position(|(k, _)| *k == key) {
                Some(i) => i,
                None => {
                    results.push((key, r));
                    results.len() - 1
                }
            };
            result_of.push(i);
        }
        let answer_ctor = |i: usize| format!("{answer}'{i}");
        let get = |i: usize| format!("{base}'get'{i}");
        let request_ctor = |m: &Member| format!("{request}'{}", m.f.name);
        let zero = |m: &Member| format!("{base}'Zero'{}", m.f.name);
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
            sort: ty("Type"),
            constructors: ctors,
            span,
        }));
        decls.push(Stmt::Inductive(InductiveDecl {
            vis: Default::default(),
            generates: Default::default(),
            name: answer.clone(),
            params: Vec::new(),
            sort: ty("Type"),
            constructors: results
                .iter()
                .enumerate()
                .map(|(i, (_, r))| Constructor {
                    name: answer_ctor(i),
                    implicit: 0,
                    params: vec![("value'".into(), r.clone())],
                    result: ty(&answer),
                })
                .collect(),
            span,
        }));
        for m in &members {
            let body = self.subst(m.zero, &m.f.params[0], &var("Zero", span));
            decls.push(Stmt::Fn(FnDecl {
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                decreasing_by: None,
                name: zero(m),
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
        for (i, (_, r)) in results.iter().enumerate() {
            let mut arms = vec![arm(
                ctor_pattern(&answer_ctor(i), &["value'".into()]),
                var("value'", span),
            )];
            if results.len() > 1 {
                arms.push(arm(Pattern::Wild, var("default'", span)));
            }
            decls.push(Stmt::Fn(FnDecl {
                budget: None,
                vis: Default::default(),
                generates: None,
                opaque: false,
                decreasing_by: None,
                name: get(i),
                generics: Vec::new(),
                rows: Vec::new(),
                bounds: Vec::new(),
                bound_spans: Vec::new(),
                params: vec!["answer'".into(), "default'".into()],
                borrows: vec![None, None],
                param_types: vec![Some(ty(&answer)), Some(r.clone())],
                result: Some(r.clone()),
                effects: None,
                where_: Vec::new(),
                span,
                body: matching("answer'", r, arms, span),
            }));
        }
        let mut zero_arms = Vec::new();
        let mut succ_arms = Vec::new();
        for (m, i) in members.iter().zip(&result_of) {
            let pattern = ctor_pattern(&request_ctor(m), &m.f.params[1..]);
            zero_arms.push(arm(
                pattern.clone(),
                app(&answer_ctor(*i), vec![m.zero.clone()], span),
            ));
            // A `let` stands for its value (`expand_lets`), calls included.
            let succ = self.expand_lets(m.succ).unwrap_or_else(|_| m.succ.clone());
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
            generics: Vec::new(),
            rows: Vec::new(),
            bounds: Vec::new(),
            bound_spans: Vec::new(),
            params: vec!["k'".into(), asked.clone()],
            borrows: vec![None, None],
            param_types: vec![Some(ty("Nat")), Some(ty(&request))],
            result: Some(answer_ty.clone()),
            effects: None,
            where_: Vec::new(),
            span,
            body: matching(
                "k'",
                &answer_ty,
                vec![
                    arm(
                        Pattern::Bind("Zero".into()),
                        matching(&asked, &answer_ty, zero_arms, span),
                    ),
                    arm(
                        ctor_pattern("Succ", std::slice::from_ref(&steps)),
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
