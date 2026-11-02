//! `&mut` and `var` in programs in the proof language.
//!
//! A function that takes `&mut` parameters is read as a pure one that
//! returns, with its value, the parameters' last values:
//!
//! ```text
//! fn f(&mut c: C, x: A): R { body }   is   fn f(c: C, x: A): Mut1(R, C) { body' }
//! ```
//!
//! `MutK(R, S1, …, SK)` is a family with the one constructor
//! `mutK(value': R, s'1: S1, …, s'K: SK)` (fields a program cannot name, so
//! they never stand for a program's own), declared the first time a function
//! needs it. In `body'`, the state (the `&mut` parameters and the `var`s in
//! scope) is passed along by name:
//!
//! * a call `g(&mut x, &mut y.f, e)` is
//!   `match g(x, y.f, e) { mut2(v, x, t) => … }`, `y` then made again with
//!   `t` as its field `f`; the call's value is `v`;
//! * `x := e` and `var x = e` are `match mut0(e) { mut0(x) => … }`;
//! * a `match` (or an `if`, which is a `match` on `true` and `false`) that changes
//!   the state returns the whole state, `mutK(v, s1, …)`, and what follows
//!   takes it apart; in the function's last position each arm ends the
//!   function itself;
//! * the function ends with `mutK(v, p1, …)`, its `&mut` parameters' last
//!   values.
//!
//! The arguments are evaluated in the order written: an argument read before
//! a later one changes the state is bound first. `&x` is `x`, and `()` is
//! `Star` (its type `Unit`). Extraction reads the function as written.

use std::collections::HashSet;
use std::sync::Arc;

use tauto_message::msg;
use tauto_parol::Span;

use super::{Diagnostic, Kernel, err};
use crate::surface::{
    Constructor, FnDecl, InductiveDecl, MatchArm, Pattern, Stmt, SurfaceTerm, TermKind,
};

type T = SurfaceTerm;

fn var(name: &str, span: Span) -> T {
    T::var(name, span)
}

fn app(function: &str, arguments: Vec<T>, span: Span) -> T {
    T::app(function, arguments, span)
}

/// The family and the constructor that carry a value and `k` states.
pub(super) fn family(k: usize) -> (String, String) {
    (format!("Mut{k}"), format!("mut{k}"))
}

fn is_unit(t: &T) -> bool {
    matches!(&*t.kind, TermKind::App { function, arguments }
        if arguments.is_empty() && matches!(&*function.kind, TermKind::Var(f) if f == "Tuple"))
}

/// `t` written as a type: `()` is `Unit`.
fn ty(t: &T) -> T {
    if is_unit(t) {
        return var("Unit", t.span);
    }
    t.clone()
}

fn any(t: &T, p: &dyn Fn(&T) -> bool) -> bool {
    let mut found = false;
    crate::surface::walk::term(&mut t.clone(), &mut |t: &mut T| found |= p(t));
    found
}

fn changes(stmts: &[Stmt]) -> bool {
    stmts
        .iter()
        .any(|s| matches!(s, Stmt::Var { .. } | Stmt::Assign { .. }))
}

/// Whether `t` changes a state: it holds a `&mut`, a `var` or a `:=`.
fn mutates(t: &T) -> bool {
    any(t, &|t| match &*t.kind {
        TermKind::Borrow { mutable: true, .. } => true,
        TermKind::Block(stmts) => changes(stmts),
        _ => false,
    })
}

fn needs(f: &FnDecl) -> bool {
    // A function with effects is read by `check/effects.rs` or not at all.
    if f.effects.as_ref().is_some_and(|e| !e.is_empty()) {
        return false;
    }
    if f.borrows.iter().any(Option::is_some) || f.result.as_ref().is_some_and(is_unit) {
        return true;
    }
    // A loop or a `return` keeps the function executable, and so does a
    // `handle` where the state changes: its arms run under the handler and
    // resume through `k`, so the state cannot be passed along by name.
    if mutates(&f.body) && any(&f.body, &|t| matches!(&*t.kind, TermKind::Handle { .. })) {
        return false;
    }
    let other = any(&f.body, &|t| match &*t.kind {
        TermKind::Block(stmts) => stmts.iter().any(|s| {
            !matches!(
                s,
                Stmt::Let { .. }
                    | Stmt::Var { borrow: false, .. }
                    | Stmt::Assign { .. }
                    | Stmt::Expr(_)
            )
        }),
        _ => false,
    });
    !other
        && any(&f.body, &|t| match &*t.kind {
            TermKind::Borrow { .. } | TermKind::If { .. } => true,
            TermKind::Block(stmts) => changes(stmts),
            _ => is_unit(t),
        })
}

/// `t` made ready for the rewrite:
///
/// * `a && b` and `a || b` whose `b` changes the state are matches on `a`,
///   so `b` runs only when it would;
/// * a `match` on a variable that its arms use matches `mut0(x)` instead: a
///   match on a variable takes it out of scope in the arms.
fn prepare(t: &T) -> T {
    let mut t = t.clone();
    crate::surface::walk::term(&mut t, &mut |t: &mut T| {
        let sp = t.span;
        match Arc::make_mut(&mut t.kind) {
            TermKind::App {
                function,
                arguments,
            } if arguments.len() == 2 && mutates(&arguments[1]) => {
                let TermKind::Var(op) = &*function.kind else {
                    return;
                };
                let (a, b) = (arguments[0].clone(), arguments[1].clone());
                let (then, otherwise) = match op.as_str() {
                    "&&" => (b, var("false", sp)),
                    "||" => (var("true", sp), b),
                    _ => return,
                };
                let arm = |name: &str, body: T| MatchArm {
                    goal: None,
                    pattern: Pattern::Ctor {
                        name: name.into(),
                        args: Vec::new(),
                    },
                    guard: None,
                    body,
                };
                t.kind = Arc::new(TermKind::Match {
                    binder: None,
                    scrutinee: Box::new(a),
                    result: Some(Box::new(var("Bool", sp))),
                    arms: vec![arm("true", then), arm("false", otherwise)],
                });
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                let TermKind::Var(x) = &*scrutinee.kind else {
                    return;
                };
                if !arms.iter().any(|a| super::occurs(&a.body, x)) {
                    return;
                }
                // `match mut0(x) { mut0(x') => match x' { … } }`
                let (_, ctor) = family(0);
                let copy = format!("{x}'m");
                let inner = T::new(
                    TermKind::Match {
                        binder: None,
                        scrutinee: Box::new(var(&copy, sp)),
                        result: None,
                        arms: std::mem::take(arms),
                    },
                    sp,
                );
                **scrutinee = app(&ctor, vec![(**scrutinee).clone()], sp);
                *arms = vec![MatchArm {
                    goal: None,
                    pattern: Pattern::Ctor {
                        name: ctor,
                        args: vec![Pattern::Bind(copy)],
                    },
                    guard: None,
                    body: inner,
                }];
            }
            _ => {}
        }
    });
    t
}

enum Bind {
    /// `match call { mutK(value, outs…) => … }`.
    Call {
        call: T,
        value: String,
        outs: Vec<String>,
    },
    Let {
        name: String,
        ty: Option<T>,
        value: T,
    },
}

struct Rewrite<'k> {
    kernel: &'k Kernel,
    /// The states in scope, the latest last: each name and its type when
    /// known.
    states: Vec<(String, Option<T>)>,
    outs: Vec<String>,
    used: HashSet<usize>,
    fresh: usize,
}

impl Rewrite<'_> {
    fn fresh(&mut self) -> String {
        self.fresh += 1;
        format!("v'{}", self.fresh)
    }

    fn state(&self, name: &str) -> Option<&Option<T>> {
        self.states
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, t)| t)
    }

    fn ctor(&mut self, k: usize, value: T, states: Vec<T>, span: Span) -> T {
        self.used.insert(k);
        let mut args = vec![value];
        args.extend(states);
        app(&family(k).1, args, span)
    }

    /// `binds` around `rest`, the first outermost; `goal` is the type of
    /// the whole, when known.
    fn wrap(&mut self, binds: Vec<Bind>, mut rest: T, goal: Option<&T>) -> T {
        for b in binds.into_iter().rev() {
            let span = rest.span;
            rest = match b {
                Bind::Call { call, value, outs } => {
                    self.used.insert(outs.len());
                    let mut args = vec![Pattern::Bind(value)];
                    args.extend(outs.into_iter().map(Pattern::Bind));
                    T::new(
                        TermKind::Match {
                            binder: None,
                            scrutinee: Box::new(call),
                            result: goal.cloned().map(Box::new),
                            arms: vec![MatchArm {
                                goal: None,
                                pattern: Pattern::Ctor {
                                    name: family(args.len() - 1).1,
                                    args,
                                },
                                guard: None,
                                body: rest,
                            }],
                        },
                        span,
                    )
                }
                Bind::Let { name, ty, value } => T::new(
                    TermKind::Block(vec![
                        Stmt::Let {
                            name,
                            ty,
                            value,
                            borrow: false,
                            borrow_mut: false,
                        },
                        Stmt::Expr(rest),
                    ]),
                    span,
                ),
            };
        }
        rest
    }

    fn assign(&mut self, name: &str, value: T, binds: &mut Vec<Bind>) {
        let span = value.span;
        let value = match self.state(name).cloned().flatten() {
            Some(t) => vec![t, value],
            None => vec![value],
        };
        self.used.insert(0);
        binds.push(Bind::Call {
            call: app(&family(0).1, value, span),
            value: name.to_string(),
            outs: Vec::new(),
        });
    }

    fn record_of(&self, name: &str, span: Span) -> Result<(String, Vec<String>), Diagnostic> {
        let head = match self.state(name) {
            Some(Some(t)) => match &*t.kind {
                TermKind::Var(n) => Some(n.clone()),
                TermKind::App { function, .. } => match &*function.kind {
                    TermKind::Var(n) => Some(n.clone()),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
        let records = self.kernel.records();
        match head.and_then(|h| records.get(&h).cloned()) {
            Some(r) => Ok(r),
            None => err(msg!("kernel-mut-field-family", name = name), span),
        }
    }

    /// The terms `ts`, evaluated in order, each read before what follows it
    /// changes the state.
    fn all(&mut self, ts: &[T], binds: &mut Vec<Bind>) -> Result<Vec<T>, Diagnostic> {
        let mut parts = Vec::new();
        for t in ts {
            let mut own = Vec::new();
            let v = self.expr(t, &mut own, None)?;
            parts.push((own, v));
        }
        let last_change = parts.iter().rposition(|(b, _)| !b.is_empty());
        let mut values = Vec::new();
        for (i, (own, v)) in parts.into_iter().enumerate() {
            binds.extend(own);
            let read_early = last_change.is_some_and(|l| i < l)
                && !matches!(
                    &*v.kind,
                    TermKind::Nat(_) | TermKind::Float(_) | TermKind::Text(_) | TermKind::Bool(_)
                );
            if read_early {
                let name = self.fresh();
                let span = v.span;
                self.used.insert(0);
                binds.push(Bind::Call {
                    call: app(&family(0).1, vec![v], span),
                    value: name.clone(),
                    outs: Vec::new(),
                });
                values.push(var(&name, span));
            } else {
                values.push(v);
            }
        }
        Ok(values)
    }

    /// The value of `t`, what it needs bound first pushed to `binds`. `want`
    /// is its type when known, which a `match` that changes the state needs.
    fn expr(&mut self, t: &T, binds: &mut Vec<Bind>, want: Option<&T>) -> Result<T, Diagnostic> {
        let sp = t.span;
        let same = |kind| Ok(T::new(kind, sp));
        match &*t.kind {
            _ if is_unit(t) => Ok(var("Star", sp)),
            TermKind::App {
                function,
                arguments,
            } => {
                let TermKind::Var(g) = &*function.kind else {
                    let function = self.expr(function, binds, None)?;
                    let arguments = self.all(arguments, binds)?;
                    return same(TermKind::App {
                        function: Box::new(function),
                        arguments,
                    });
                };
                // The places `&mut` lends, the values passed for them first.
                let mut places = Vec::new();
                let mut plain = Vec::new();
                for a in arguments {
                    match &*a.kind {
                        TermKind::Borrow {
                            mutable: true,
                            term,
                        } => {
                            let place = match &*term.kind {
                                TermKind::Var(x) if self.state(x).is_some() => (x.clone(), None),
                                TermKind::Field { base, name } => match &*base.kind {
                                    TermKind::Var(x) if self.state(x).is_some() => {
                                        (x.clone(), Some(name.clone()))
                                    }
                                    _ => {
                                        return err(msg!("kernel-mut-lends"), a.span);
                                    }
                                },
                                _ => {
                                    return err(msg!("kernel-mut-lends"), a.span);
                                }
                            };
                            places.push(place);
                            plain.push((**term).clone());
                        }
                        _ => plain.push(a.clone()),
                    }
                }
                let arguments = self.all(&plain, binds)?;
                let call = same(TermKind::App {
                    function: Box::new(var(g, function.span)),
                    arguments,
                })?;
                if places.is_empty() {
                    return Ok(call);
                }
                let value = self.fresh();
                let mut outs = Vec::new();
                let mut fields = Vec::new();
                for (x, field) in &places {
                    match field {
                        None => outs.push(x.clone()),
                        Some(f) => {
                            let t = self.fresh();
                            outs.push(t.clone());
                            fields.push((x.clone(), f.clone(), t));
                        }
                    }
                }
                self.used.insert(outs.len());
                binds.push(Bind::Call {
                    call,
                    value: value.clone(),
                    outs,
                });
                for (x, f, t) in fields {
                    let (ctor, names) = self.record_of(&x, sp)?;
                    let made = names
                        .iter()
                        .map(|n| match n == &f {
                            true => var(&t, sp),
                            false => T::new(
                                TermKind::Field {
                                    base: Box::new(var(&x, sp)),
                                    name: n.clone(),
                                },
                                sp,
                            ),
                        })
                        .collect();
                    self.assign(&x, app(&ctor, made, sp), binds);
                }
                Ok(var(&value, sp))
            }
            TermKind::Borrow {
                mutable: false,
                term,
            } => self.expr(term, binds, want),
            TermKind::Borrow { mutable: true, .. } => err(msg!("kernel-mut-argument"), sp),
            TermKind::Field { base, name } => same(TermKind::Field {
                base: Box::new(self.expr(base, binds, None)?),
                name: name.clone(),
            }),
            TermKind::Record { name, fields, .. } => {
                let values: Vec<T> = fields.iter().map(|(_, v)| v.clone()).collect();
                let values = self.all(&values, binds)?;
                same(TermKind::Record {
                    name: name.clone(),
                    fields: fields.iter().map(|(n, _)| n.clone()).zip(values).collect(),
                    base: None,
                })
            }
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } if mutates(t) => {
                err(msg!("kernel-mut-lambda"), sp)
            }
            TermKind::If { .. } => {
                let m = if_match(t);
                self.expr(&m, binds, want)
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } => {
                let scrutinee = self.expr(scrutinee, binds, None)?;
                if self.states.is_empty() || !arms.iter().any(|a| mutates(&a.body)) {
                    let goal = result.as_deref().map(ty).or(want.cloned());
                    let arms = arms
                        .iter()
                        .map(|a| {
                            Ok(MatchArm {
                                goal: a.goal.clone(),
                                pattern: a.pattern.clone(),
                                guard: a.guard.clone(),
                                body: self.pure(&a.body, goal.as_ref())?,
                            })
                        })
                        .collect::<Result<_, Diagnostic>>()?;
                    return same(TermKind::Match {
                        binder: binder.clone(),
                        scrutinee: Box::new(scrutinee),
                        result: result.clone().or(goal.clone().map(Box::new)),
                        arms,
                    });
                }
                // The whole state goes in and comes out.
                let Some(value_ty) = result.as_deref().map(ty).or(want.cloned()) else {
                    return err(msg!("kernel-mut-match-type"), sp);
                };
                // The latest binding of each state, all typed.
                let mut names: Vec<String> = Vec::new();
                for (n, _) in self.states.iter().rev() {
                    if !names.contains(n) {
                        names.push(n.clone());
                    }
                }
                names.reverse();
                let mut tys = vec![value_ty];
                for n in &names {
                    match self.state(n).cloned().flatten() {
                        Some(t) => tys.push(t),
                        None => {
                            return err(msg!("kernel-mut-var-type", name = n), sp);
                        }
                    }
                }
                let k = names.len();
                let finish = names.clone();
                let whole_ty = app(&family(k).0, tys, sp);
                let arms = arms
                    .iter()
                    .map(|a| {
                        let body = self.tail(&a.body, &finish, Some(&whole_ty))?;
                        Ok(MatchArm {
                            goal: a.goal.clone(),
                            pattern: a.pattern.clone(),
                            guard: a.guard.clone(),
                            body,
                        })
                    })
                    .collect::<Result<_, Diagnostic>>()?;
                self.used.insert(k);
                let whole = same(TermKind::Match {
                    binder: binder.clone(),
                    scrutinee: Box::new(scrutinee),
                    result: Some(Box::new(whole_ty)),
                    arms,
                })?;
                let value = self.fresh();
                binds.push(Bind::Call {
                    call: whole,
                    value: value.clone(),
                    outs: names,
                });
                Ok(var(&value, sp))
            }
            TermKind::Block(stmts) => self.block(stmts, binds, want, true),
            TermKind::Var(_)
            | TermKind::Nat(_)
            | TermKind::Float(_)
            | TermKind::Text(_)
            | TermKind::Bool(_)
            | TermKind::Hole(_)
            | TermKind::Pi { .. } => Ok(t.clone()),
            // A lambda that changes no state: its `if`s are matches, as they
            // are outside it.
            TermKind::Lam { .. } => {
                let mut t = t.clone();
                crate::surface::walk::term(&mut t, &mut |t: &mut T| {
                    if matches!(&*t.kind, TermKind::If { .. }) {
                        *t = if_match(t);
                    }
                });
                Ok(t)
            }
            _ if !mutates(t) => Ok(t.clone()),
            _ => err(msg!("kernel-mut-term"), sp),
        }
    }

    fn pure(&mut self, t: &T, want: Option<&T>) -> Result<T, Diagnostic> {
        let mut binds = Vec::new();
        let v = self.expr(t, &mut binds, want)?;
        Ok(self.wrap(binds, v, want))
    }

    /// The statements of a block; its value is the last one's (when
    /// `valued`).
    fn block(
        &mut self,
        stmts: &[Stmt],
        binds: &mut Vec<Bind>,
        want: Option<&T>,
        valued: bool,
    ) -> Result<T, Diagnostic> {
        let depth = self.states.len();
        let mut value = None;
        for (i, s) in stmts.iter().enumerate() {
            let last = valued && i + 1 == stmts.len();
            match s {
                Stmt::Let {
                    name,
                    ty: t,
                    value: v,
                    ..
                } => {
                    let t = t.as_ref().map(ty);
                    let v = self.expr(v, binds, t.as_ref())?;
                    if self.states.is_empty() {
                        binds.push(Bind::Let {
                            name: name.clone(),
                            ty: t,
                            value: v,
                        });
                    } else {
                        // A `let` stands for its value (`expand_lets`), which
                        // would read the state as it is where the name is
                        // used: bound, it reads the state as it is here.
                        let span = v.span;
                        let args = t.into_iter().chain(std::iter::once(v)).collect();
                        self.used.insert(0);
                        binds.push(Bind::Call {
                            call: app(&family(0).1, args, span),
                            value: name.clone(),
                            outs: Vec::new(),
                        });
                    }
                }
                Stmt::Var {
                    name,
                    ty: t,
                    value: v,
                    borrow: false,
                } => {
                    let t = t.as_ref().map(ty);
                    let v = self.expr(v, binds, t.as_ref())?;
                    self.states.push((name.clone(), t));
                    self.assign(name, v, binds);
                }
                Stmt::Assign { place: Some(p), .. } => {
                    return err(
                        msg!(
                            "kernel-effect-assign-field",
                            place = crate::surface::print::print_term(p)
                        ),
                        p.span,
                    );
                }
                Stmt::Assign { name, value: v, .. } => {
                    if self.state(name).is_none() {
                        return err(msg!("kernel-mut-assign", name = name), v.span);
                    }
                    let want = self.state(name).cloned().flatten();
                    let v = self.expr(v, binds, want.as_ref())?;
                    self.assign(name, v, binds);
                }
                Stmt::Expr(e) if last => value = Some(self.expr(e, binds, want)?),
                Stmt::Expr(e) => {
                    let unit = var("Unit", e.span);
                    self.expr(e, binds, Some(&unit))?;
                }
                _ => {
                    return err(msg!("kernel-mut-block"), t_span(stmts));
                }
            }
        }
        self.states.truncate(depth);
        Ok(value.unwrap_or_else(|| var("Star", t_span(stmts))))
    }

    /// `t` in last position: the term that ends with `mutK(v, finish…)`.
    /// `goal` is its type, when known.
    fn tail(&mut self, t: &T, finish: &[String], goal: Option<&T>) -> Result<T, Diagnostic> {
        let sp = t.span;
        match &*t.kind {
            TermKind::If { .. } => self.tail(&if_match(t), finish, goal),
            // Each arm ends the function: a `match` on the steps stays one
            // (`steps.rs`).
            TermKind::Match {
                scrutinee,
                binder,
                arms,
                ..
            } if !finish.is_empty() || arms.iter().any(|a| mutates(&a.body)) => {
                let mut binds = Vec::new();
                let scrutinee = self.expr(scrutinee, &mut binds, None)?;
                let arms = arms
                    .iter()
                    .map(|a| {
                        Ok(MatchArm {
                            goal: a.goal.clone(),
                            pattern: a.pattern.clone(),
                            guard: a.guard.clone(),
                            body: self.tail(&a.body, finish, goal)?,
                        })
                    })
                    .collect::<Result<_, Diagnostic>>()?;
                let m = T::new(
                    TermKind::Match {
                        binder: binder.clone(),
                        scrutinee: Box::new(scrutinee),
                        result: goal.cloned().map(Box::new),
                        arms,
                    },
                    sp,
                );
                Ok(self.wrap(binds, m, goal))
            }
            TermKind::Block(stmts) if matches!(stmts.last(), Some(Stmt::Expr(_))) => {
                let Some((Stmt::Expr(last), init)) = stmts.split_last() else {
                    unreachable!()
                };
                let depth = self.states.len();
                let mut binds = Vec::new();
                self.block(init, &mut binds, None, false)?;
                // `block` drops the `var`s it declared; the last term sees
                // them.
                let mut inner = Vec::new();
                for s in init {
                    if let Stmt::Var { name, ty: t, .. } = s {
                        inner.push((name.clone(), t.as_ref().map(ty)));
                    }
                }
                self.states.extend(inner);
                let body = self.tail(last, finish, goal);
                self.states.truncate(depth);
                Ok(self.wrap(binds, body?, goal))
            }
            _ => {
                let mut binds = Vec::new();
                // Without states, the value's type is the goal.
                let want = if finish.is_empty() { goal } else { None };
                let v = self.expr(t, &mut binds, want)?;
                let end = match finish.len() {
                    0 => v,
                    k => {
                        let states = finish.iter().map(|n| var(n, sp)).collect();
                        self.ctor(k, v, states, sp)
                    }
                };
                Ok(self.wrap(binds, end, goal))
            }
        }
    }
}

fn t_span(stmts: &[Stmt]) -> Span {
    for s in stmts {
        match s {
            Stmt::Expr(e)
            | Stmt::Let { value: e, .. }
            | Stmt::Var { value: e, .. }
            | Stmt::Assign { value: e, .. } => return e.span,
            _ => {}
        }
    }
    Span::default()
}

pub(super) fn if_match(t: &T) -> T {
    let TermKind::If {
        condition,
        then,
        otherwise,
    } = &*t.kind
    else {
        unreachable!()
    };
    let arm = |name: &str, body: T| MatchArm {
        goal: None,
        pattern: Pattern::Ctor {
            name: name.into(),
            args: Vec::new(),
        },
        guard: None,
        body,
    };
    let otherwise = otherwise
        .as_deref()
        .cloned()
        .unwrap_or_else(|| var("Star", t.span));
    T::new(
        TermKind::Match {
            binder: None,
            scrutinee: condition.clone(),
            result: None,
            arms: vec![arm("true", (**then).clone()), arm("false", otherwise)],
        },
        t.span,
    )
}

impl Kernel {
    /// `stmt` with its functions' `&mut` and `var`s read as above, the
    /// families `MutK` they use declared first.
    pub(super) fn mutable_sugar(&mut self, stmt: &Stmt) -> Result<Stmt, (String, Diagnostic)> {
        match stmt {
            Stmt::Fn(f) if needs(f) => Ok(Stmt::Fn(self.mutable_fn(f)?)),
            Stmt::Mutual { items, span }
                if items.iter().any(|s| matches!(s, Stmt::Fn(f) if needs(f))) =>
            {
                let items = items
                    .iter()
                    .map(|s| match s {
                        Stmt::Fn(f) if needs(f) => Ok(Stmt::Fn(self.mutable_fn(f)?)),
                        s => Ok(s.clone()),
                    })
                    .collect::<Result<_, _>>()?;
                Ok(Stmt::Mutual { items, span: *span })
            }
            s => Ok(s.clone()),
        }
    }

    fn mutable_fn(&mut self, f: &FnDecl) -> Result<FnDecl, (String, Diagnostic)> {
        let failed = |d| (f.name.clone(), d);
        let mut rw = Rewrite {
            kernel: self,
            states: Vec::new(),
            outs: Vec::new(),
            used: HashSet::new(),
            fresh: 0,
        };
        let mut out_tys = Vec::new();
        for ((p, b), t) in f.params.iter().zip(&f.borrows).zip(&f.param_types) {
            if *b == Some(true) {
                let t = t.as_ref().map(ty);
                rw.states.push((p.clone(), t.clone()));
                rw.outs.push(p.clone());
                match t {
                    Some(t) => out_tys.push(t),
                    None => {
                        return Err(failed(Diagnostic::new(
                            msg!("kernel-mut-param-type", name = p),
                            Some(f.span),
                        )));
                    }
                }
            }
        }
        let outs = rw.outs.clone();
        let result = f.result.as_ref().map(|r| {
            let r = ty(r);
            match out_tys.len() {
                0 => r,
                k => {
                    let mut args = vec![r];
                    args.extend(out_tys.iter().cloned());
                    app(&family(k).0, args, r_span(f))
                }
            }
        });
        rw.used.insert(0);
        let body = rw
            .tail(&prepare(&f.body), &outs, result.as_ref())
            .map_err(failed)?;
        let mut used: Vec<usize> = rw.used.into_iter().collect();
        if !outs.is_empty() {
            used.push(outs.len());
        }
        used.sort();
        used.dedup();
        for k in used {
            self.declare_mut(k, f.span).map_err(failed)?;
        }
        Ok(FnDecl {
            borrows: vec![None; f.params.len()],
            param_types: f.param_types.iter().map(|t| t.as_ref().map(ty)).collect(),
            result,
            body,
            ..f.clone()
        })
    }

    /// `Mut'k`, unless declared.
    fn declare_mut(&mut self, k: usize, span: Span) -> Result<(), Diagnostic> {
        let (name, ctor) = family(k);
        if self.inds.contains_key(&name) {
            return Ok(());
        }
        let params: Vec<(String, T)> = std::iter::once("R".to_string())
            .chain((1..=k).map(|i| format!("S{i}")))
            .map(|p| (p, var("Type", span)))
            .collect();
        let fields = std::iter::once(("value'".to_string(), var("R", span)))
            .chain((1..=k).map(|i| (format!("s'{i}"), var(&format!("S{i}"), span))))
            .collect();
        let result = app(
            &name,
            params.iter().map(|(p, _)| var(p, span)).collect(),
            span,
        );
        let decl = InductiveDecl {
            vis: Default::default(),
            generates: Default::default(),
            name: name.clone(),
            params,
            sort: var("Type", span),
            constructors: vec![Constructor {
                name: ctor,
                implicit: 0,
                params: fields,
                result,
            }],
            span,
        };
        match self.inductive(&decl) {
            super::Verdict::Checked { .. } => Ok(()),
            super::Verdict::Failed(d) => Err(d),
            v => err(
                msg!(
                    "kernel-mut-verdict",
                    name = name,
                    verdict = format!("{v:?}")
                ),
                span,
            ),
        }
    }
}

fn r_span(f: &FnDecl) -> Span {
    f.result.as_ref().map(|r| r.span).unwrap_or(f.span)
}
