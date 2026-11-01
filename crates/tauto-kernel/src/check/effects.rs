//! Functions with effects, read as terms of the proof language. The kernel
//! gets no rule for them: each is written with the prelude's `Comp` and the
//! functions on it, before the kernel checks anything.
//!
//! `effect e(P0, …): R` makes
//!
//! ```text
//! inductive e@op: Type { e@args(a0: P0, …): e@op }
//! fn e@res(o: e@op): Type { match o: Type { e@args(a0, …) => R } }
//! fn e@arm<B>(f: (a0: P0, …, k: (R) -> B) -> B, o: e@op, k: (e@res(o)) -> B): B
//! ```
//!
//! A row is its effects in the order of their names. Its operations are
//! `OpSum(e0@op, OpSum(e1@op, … OpNone))` and the answers `res_sum(…)`, so
//! `fn f(x: X): A ! {e…}` is `fn f(x: X): Comp(Op, Res, A)`:
//!
//! * a value is `comp_ret(Op, Res, v)`;
//! * `perform e(a…)` is `comp_perform(Op, Res, i(e@args(a…)))`, `i` the
//!   injection of `e` into the row;
//! * `let x = c; rest` is `comp_bind(Op, Res, c, x => rest)`;
//! * a call of a function whose row is part of this one is lifted into it by
//!   a handler that forwards every operation;
//! * `handle { c } with { e(p…), k => b; return v => r }` is `comp_handle` on
//!   `c` read in the row with the handled effects; an arm is `e@arm` on the
//!   arm's body, every other effect is forwarded with `comp_forward`.
//!
//! A `handle` that leaves no effect, in a function without effects, a
//! theorem or a definition, is `comp_value` of the computation it is read as.
//! A program that is run reads the declarations as written.

use super::{Kernel, T, Verdict};
use crate::surface::{Constructor, FnDecl, Handler, InductiveDecl, MatchArm, Pattern, Stmt};
use crate::surface::{TermKind, walk};
use std::collections::{HashMap, HashSet};
use tauto_message::{Message, msg};
use tauto_parol::Span;

/// What is known of the effects and of the functions with effects.
#[derive(Clone, Default)]
pub(super) struct Effects {
    /// An effect read in proofs: how many parameters its operation takes.
    sigs: HashMap<String, usize>,
    /// A function read in proofs: its row.
    pub(super) fns: HashMap<String, Vec<String>>,
    /// A function read in proofs whose row has a variable: the variable, and
    /// the parameters that are functions whose rows have it.
    poly: HashMap<String, (String, Vec<usize>)>,
    /// A function with effects, or one whose `handle`s, not read in proofs, and why.
    pub(super) skipped: HashMap<String, Message>,
    /// The declarations made for the effects.
    pub(super) generated: HashSet<String>,
    /// The type of the answer to each effect, and the result type of each
    /// function with effects that has no generics.
    results: HashMap<String, T>,
    /// The declarations of the effects made for the `var`s of the function
    /// being read, to come before it.
    pending: Vec<Stmt>,
    /// The functions without effects whose `handle`s are read in proofs.
    pub(super) handling: HashSet<String>,
    /// Each effect's `resume` as written, `None` for the default `<=1`.
    pub(super) resumes: HashMap<String, Option<String>>,
}

impl Effects {
    /// How many leading parameters a function read in proofs has for its
    /// row variable, which a call of it as written leaves out.
    pub(super) fn row_params(&self, name: &str) -> usize {
        match self.poly.contains_key(name) {
            true => 2,
            false => 0,
        }
    }
}

fn var(n: &str, sp: Span) -> T {
    T::var(n, sp)
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

fn call(f: &str, args: Vec<T>, sp: Span) -> T {
    app(var(f, sp), args)
}

fn pi(name: Option<&str>, domain: T, result: T) -> T {
    let span = result.span;
    T::new(
        TermKind::Pi {
            params: vec![(name.map(String::from), domain)],
            result: Box::new(result),
            effects: None,
        },
        span,
    )
}

fn lam(names: &[String], body: T) -> T {
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

fn one_arm(scrutinee: T, result: T, ctor: &str, binders: &[String], body: T) -> T {
    let sp = scrutinee.span;
    T::new(
        TermKind::Match {
            scrutinee: Box::new(scrutinee),
            result: Some(Box::new(result)),
            binder: None,
            arms: vec![MatchArm {
                pattern: Pattern::Ctor {
                    name: ctor.into(),
                    args: binders.iter().cloned().map(Pattern::Bind).collect(),
                },
                guard: None,
                goal: None,
                body,
            }],
        },
        sp,
    )
}

fn op_name(e: &str) -> String {
    format!("{e}@op")
}

fn args_name(e: &str) -> String {
    format!("{e}@args")
}

fn res_name(e: &str) -> String {
    format!("{e}@res")
}

fn arm_name(e: &str) -> String {
    format!("{e}@arm")
}

/// The effects of a row in the order of their names, each once, and its
/// variable `|e`, if it has one, last.
fn canonical(row: &[String]) -> Vec<String> {
    let (mut tail, mut row): (Vec<String>, Vec<String>) =
        row.iter().cloned().partition(|e| row_var(e).is_some());
    row.sort();
    row.dedup();
    tail.dedup();
    row.append(&mut tail);
    row
}

/// The variable `e` of a row's entry `|e`.
fn row_var(e: &str) -> Option<&str> {
    e.strip_prefix('|')
}

/// The parameters a row variable `e` is read as: the operations of the
/// effects it stands for, and their answers.
fn var_op(e: &str) -> String {
    format!("{e}@rowop")
}

fn var_res(e: &str) -> String {
    format!("{e}@rowres")
}

/// The row variables of a row, in the order written.
fn row_vars(row: &[String]) -> Vec<String> {
    row.iter()
        .filter_map(|e| row_var(e))
        .map(String::from)
        .collect()
}

/// The type of the value of a parameter `effect_params` wrote:
/// `Comp(O, R, A)` or `(…) -> Comp(O, R, A)` gives `A`.
fn comp_value(t: &T) -> Option<T> {
    match &*t.kind {
        TermKind::Pi { result, .. } => comp_value(result),
        TermKind::App {
            function,
            arguments,
        } if matches!(&*function.kind, TermKind::Var(c) if c == "Comp") && arguments.len() == 3 => {
            Some(arguments[2].clone())
        }
        _ => None,
    }
}

/// The operations of `row`.
fn op_ty(row: &[String], sp: Span) -> T {
    match row.split_first() {
        None => var("OpNone", sp),
        Some((e, _)) if let Some(v) = row_var(e) => var(&var_op(v), sp),
        Some((e, rest)) => call("OpSum", vec![var(&op_name(e), sp), op_ty(rest, sp)], sp),
    }
}

/// The answers to the operations of `row`.
fn res_fn(row: &[String], sp: Span) -> T {
    match row.split_first() {
        None => var("res_none", sp),
        Some((e, _)) if let Some(v) = row_var(e) => var(&var_res(v), sp),
        Some((e, rest)) => lam(
            &["o'".to_string()],
            call(
                "res_sum",
                vec![
                    var(&op_name(e), sp),
                    op_ty(rest, sp),
                    var(&res_name(e), sp),
                    res_fn(rest, sp),
                    var("o'", sp),
                ],
                sp,
            ),
        ),
    }
}

/// `x`, an operation of `e`, as an operation of `row`.
fn inject(row: &[String], e: &str, x: T, sp: Span) -> T {
    let p = row
        .iter()
        .position(|r| r == e)
        .expect("the effect is in the row");
    // An operation of a row variable's effects is already one of the end
    // of the row.
    let mut t = match row_var(e) {
        Some(_) => x,
        None => call(
            "OpHere",
            vec![var(&op_name(e), sp), op_ty(&row[p + 1..], sp), x],
            sp,
        ),
    };
    for j in (0..p).rev() {
        t = call(
            "OpThere",
            vec![var(&op_name(&row[j]), sp), op_ty(&row[j + 1..], sp), t],
            sp,
        );
    }
    t
}

/// What can go wrong reading a function with effects.
type Read<X> = Result<X, Message>;

/// Where a computation is read: its row, and the local functions whose calls
/// are computations (the continuations of handlers), with their rows.
#[derive(Clone)]
struct Cx {
    row: Vec<String>,
    locals: HashMap<String, Vec<String>>,
    /// The variables whose types are known.
    types: HashMap<String, T>,
    /// The `var`s in scope: the effects that read and write each.
    vars: HashMap<String, (String, String)>,
    /// The type of the value of the computation, when known.
    expect: Option<T>,
}

/// `c` with the type of its value written, when it is known, so that the
/// generics of what is around it are found.
fn typed(c: T, ty: Option<&T>, cx: &Cx, sp: Span) -> T {
    match ty {
        Some(ty) => call(
            "the",
            vec![call("Comp", vec![cx.op(sp), cx.res(sp), ty.clone()], sp), c],
            sp,
        ),
        None => c,
    }
}

impl Cx {
    fn expecting(&self, ty: Option<T>) -> Cx {
        Cx {
            expect: ty,
            ..self.clone()
        }
    }

    fn op(&self, sp: Span) -> T {
        op_ty(&self.row, sp)
    }
    fn res(&self, sp: Span) -> T {
        res_fn(&self.row, sp)
    }
}

impl Kernel {
    /// A declaration made for an effect, or a function with effects, that
    /// does not check is not usable in proofs; the program is still run.
    pub(super) fn effect_verdict(&mut self, name: &str, verdict: Verdict) -> Verdict {
        let Verdict::Failed(d) = &verdict else {
            return verdict;
        };
        let read = self.effects.generated.contains(name)
            || self.effects.fns.contains_key(name)
            || self.effects.handling.contains(name);
        if read {
            // Not usable in proofs, like any other declaration that is skipped.
            self.globals.remove(name);
        }
        if self.effects.generated.contains(name) {
            return Verdict::Skipped(msg!("kernel-effect-types", why = d.to_string()).to_string());
        }
        if self.effects.fns.contains_key(name) || self.effects.handling.contains(name) {
            return Verdict::Skipped(
                msg!("kernel-effect-reading-fails", why = d.to_string()).to_string(),
            );
        }
        verdict
    }

    /// The statements with each effect's declarations made, and each function
    /// with effects (and each `handle`) read as terms of the proof language.
    pub(super) fn effect_pass(&mut self, stmts: &[Stmt]) -> Vec<Stmt> {
        let mut out = Vec::new();
        for stmt in stmts {
            match stmt {
                Stmt::Effect(e) => {
                    out.push(stmt.clone());
                    if let Some(made) = self.effect_decls(e) {
                        out.extend(made);
                    }
                }
                Stmt::Fn(f) if f.effects.as_ref().is_some_and(|e| !e.is_empty()) => {
                    let row = f.effects.as_deref().unwrap_or_default();
                    let poly = match self.unread_row(row, &f.generics) {
                        Some(why) => Err(why),
                        None => row_poly(f),
                    };
                    let poly = match poly {
                        Ok(poly) => poly,
                        Err(why) => {
                            self.effects.skipped.insert(f.name.clone(), why);
                            out.push(stmt.clone());
                            continue;
                        }
                    };
                    let row_generics = poly.iter().map(|(v, _)| v.clone()).collect::<Vec<_>>();
                    match poly {
                        Some(poly) => self.effects.poly.insert(f.name.clone(), poly),
                        None => self.effects.poly.remove(&f.name),
                    };
                    self.effects.fns.insert(f.name.clone(), canonical(row));
                    if f.generics.iter().all(|g| row_generics.contains(g))
                        && let Some(r) = &f.result
                    {
                        self.effects.results.insert(f.name.clone(), r.clone());
                    }
                    let read = self.effect_fn(f);
                    out.append(&mut self.effects.pending);
                    match read {
                        Ok(g) => out.push(Stmt::Fn(g)),
                        Err(why) => {
                            self.effects.fns.remove(&f.name);
                            self.effects.poly.remove(&f.name);
                            self.effects.skipped.insert(f.name.clone(), why);
                            out.push(stmt.clone());
                        }
                    }
                }
                Stmt::Fn(f) if self.has_handle(&f.body) && self.effects_known() => {
                    match self.pure_fn(f) {
                        Ok(g) => {
                            self.effects.handling.insert(f.name.clone());
                            out.append(&mut self.effects.pending);
                            out.push(Stmt::Fn(g));
                        }
                        Err(why) => {
                            self.effects.skipped.insert(f.name.clone(), why);
                            out.push(stmt.clone())
                        }
                    }
                }
                Stmt::Fn(_) | Stmt::Theorem(_) | Stmt::Def(_) => {
                    let mut s = stmt.clone();
                    walk::stmt(&mut s, &mut |t| {
                        if matches!(&*t.kind, TermKind::Handle { .. })
                            && let Ok(v) = self.pure_handle(t)
                        {
                            *t = v;
                        }
                    });
                    out.append(&mut self.effects.pending);
                    out.push(s);
                }
                _ => out.push(stmt.clone()),
            }
        }
        out
    }

    /// Why a row is not read in proofs, if it is not.
    fn unread_row(&self, row: &[String], generics: &[String]) -> Option<Message> {
        if let Some(v) = row_vars(row).into_iter().find(|v| !generics.contains(v)) {
            return Some(msg!("kernel-effect-row-variable", name = v));
        }
        if canonical(row)
            .iter()
            .filter(|e| row_var(e).is_some())
            .count()
            > 1
        {
            return Some(msg!("kernel-effect-row-variables"));
        }
        row.iter()
            .filter(|e| row_var(e).is_none())
            .find(|e| !self.effects.sigs.contains_key(*e))
            .map(|e| msg!("kernel-effect-unread", name = e))
    }

    /// `e@op`, `e@res` and `e@arm` for `effect e`, when its types are written.
    fn effect_decls(&mut self, e: &crate::surface::EffectDecl) -> Option<Vec<Stmt>> {
        if !e.generics.is_empty() {
            return None;
        }
        let params: Vec<T> = e.params.iter().cloned().collect::<Option<_>>()?;
        let result = e.result.clone().unwrap_or_else(|| var("Unit", e.span));
        Some(self.make_effect(&e.name, params, result, e.span))
    }

    /// The declarations of an effect named `name`.
    fn make_effect(&mut self, name: &str, params: Vec<T>, result: T, sp: Span) -> Vec<Stmt> {
        let result_ty = result.clone();
        let names: Vec<String> = (0..params.len()).map(|i| format!("a{i}")).collect();
        let (op, args, res, arm) = (
            op_name(name),
            args_name(name),
            res_name(name),
            arm_name(name),
        );
        let ty = var("Type", sp);
        let family = Stmt::Inductive(InductiveDecl {
            vis: Default::default(),
            name: op.clone(),
            params: Vec::new(),
            sort: ty.clone(),
            constructors: vec![Constructor {
                name: args.clone(),
                implicit: 0,
                params: names.iter().cloned().zip(params.iter().cloned()).collect(),
                result: var(&op, sp),
            }],
            generates: Default::default(),
            span: sp,
        });
        let fn_decl =
            |name: &str, generics: Vec<String>, ps: Vec<(String, T)>, result: T, body: T| FnDecl {
                budget: None,
                vis: Default::default(),
                name: name.into(),
                rows: vec![false; generics.len()],
                bounds: vec![None; generics.len()],
                bound_spans: Vec::new(),
                generics,
                borrows: vec![None; ps.len()],
                params: ps.iter().map(|(n, _)| n.clone()).collect(),
                param_types: ps.into_iter().map(|(_, t)| Some(t)).collect(),
                result: Some(result),
                effects: None,
                where_: Vec::new(),
                span: sp,
                opaque: false,
                decreasing_by: None,
                generates: None,
                body,
            };
        let answers = fn_decl(
            &res,
            Vec::new(),
            vec![("o".into(), var(&op, sp))],
            ty.clone(),
            one_arm(var("o", sp), ty, &args, &names, result.clone()),
        );
        // `f: (a0: P0, …, k: (R) -> B) -> B`
        let b = var("B", sp);
        let to_b = |d: T| pi(None, d, b.clone());
        let mut f_ty = pi(Some("k"), to_b(result), b.clone());
        for (n, p) in names.iter().zip(&params).rev() {
            f_ty = pi(Some(n), p.clone(), f_ty);
        }
        let answer_o = call(&res, vec![var("o", sp)], sp);
        let arm_body = app(
            one_arm(
                var("o", sp),
                to_b(to_b(answer_o.clone())),
                &args,
                &names,
                call("f", names.iter().map(|n| var(n, sp)).collect(), sp),
            ),
            vec![var("k", sp)],
        );
        let arm_decl = fn_decl(
            &arm,
            vec!["B".into()],
            vec![
                ("f".into(), f_ty),
                ("o".into(), var(&op, sp)),
                ("k".into(), to_b(answer_o)),
            ],
            b.clone(),
            arm_body,
        );
        self.effects.sigs.insert(name.to_string(), params.len());
        self.effects.results.insert(name.to_string(), result_ty);
        for n in [&op, &res, &arm] {
            self.effects.generated.insert(n.clone());
        }
        vec![family, Stmt::Fn(answers), Stmt::Fn(arm_decl)]
    }

    /// `f` read as a function to `Comp`.
    fn effect_fn(&mut self, f: &FnDecl) -> Read<FnDecl> {
        let sp = f.span;
        let Some(result) = &f.result else {
            return Err(msg!("kernel-effect-no-result"));
        };
        if f.param_types.iter().any(Option::is_none) {
            return Err(msg!("kernel-effect-untyped-param"));
        }
        if !f.where_.is_empty() {
            return Err(msg!("kernel-effect-where"));
        }
        let (mut param_types, locals) = self.effect_params(f)?;
        let row_generic = self.effects.poly.get(&f.name).map(|(v, _)| v.clone());
        let cx = Cx {
            row: self.effects.fns[&f.name].clone(),
            locals,
            types: f
                .params
                .iter()
                .cloned()
                .zip(param_types.iter().cloned())
                .chain(
                    f.generics
                        .iter()
                        .filter(|g| Some(*g) != row_generic.as_ref())
                        .map(|g| (g.clone(), var("Type", sp))),
                )
                .collect(),
            vars: HashMap::new(),
            expect: Some(result.clone()),
        };
        let body = self.computation(&ifs_as_matches(&f.body), &cx)?;
        let mut g = f.clone();
        // A row variable `e` is two parameters before the others: the
        // operations of the effects it stands for and their answers. The
        // function holds for every such row, as the program it reads does.
        if let Some(v) = &row_generic {
            let at = g.generics.iter().position(|x| x == v).expect("a generic");
            g.generics.remove(at);
            g.bounds.remove(at);
            let op = var(&var_op(v), sp);
            g.params.splice(0..0, [var_op(v), var_res(v)]);
            g.borrows.splice(0..0, [None, None]);
            param_types.splice(0..0, [var("Type", sp), pi(None, op, var("Type", sp))]);
        }
        g.param_types = param_types.into_iter().map(Some).collect();
        g.effects = None;
        g.result = Some(call(
            "Comp",
            vec![cx.op(sp), cx.res(sp), result.clone()],
            sp,
        ));
        g.body = body;
        Ok(g)
    }

    /// Whether reading `t` needs `Comp`: it performs, handles, or calls a
    /// function with effects.
    fn effectful(&self, t: &T, cx: &Cx) -> bool {
        let mut found = false;
        let mut t = t.clone();
        walk::term(&mut t, &mut |s| match &*s.kind {
            TermKind::Perform { .. } | TermKind::Handle { .. } => found = true,
            TermKind::Var(n) if cx.vars.contains_key(n) => found = true,
            TermKind::Block(stmts)
                if stmts
                    .iter()
                    .any(|s| matches!(s, Stmt::Var { .. } | Stmt::Assign { .. })) =>
            {
                found = true
            }
            TermKind::App { function, .. } => {
                if let TermKind::Var(n) = &*function.kind
                    && (cx.locals.contains_key(n) || self.effects.fns.contains_key(n))
                {
                    found = true;
                }
            }
            _ => {}
        });
        found
    }

    fn pure_or(&self, t: &T, cx: &Cx, what: Message) -> Read<()> {
        match self.effectful(t, cx) {
            true => Err(msg!("kernel-effect-bind-first", what = what)),
            false => Ok(()),
        }
    }

    /// `t`, a computation in `cx`, as a term of type `Comp(…)`.
    fn computation(&mut self, t: &T, cx: &Cx) -> Read<T> {
        let sp = t.span;
        if !self.effectful(t, cx) {
            return Ok(call(
                "Comp::ret",
                vec![cx.op(sp), cx.res(sp), t.clone()],
                sp,
            ));
        }
        match &*t.kind {
            TermKind::Var(x) if cx.vars.contains_key(x) => {
                let get = cx.vars[x].0.clone();
                self.perform(&get, &[], cx, sp)
            }
            TermKind::Block(stmts) => self.block(stmts, cx, sp),
            TermKind::Perform { effect, args } => self.perform(effect, args, cx, sp),
            TermKind::App {
                function,
                arguments,
            } => {
                self.pure_or(function, cx, msg!("kernel-effect-called-function"))?;
                let (mut args, binds) = self.arguments(arguments, cx)?;
                let mut row = match &*function.kind {
                    TermKind::Var(g) => match cx.locals.get(g) {
                        Some(row) => Some((g.clone(), row.clone())),
                        None => self.effects.fns.get(g).map(|row| (g.clone(), row.clone())),
                    },
                    _ => None,
                };
                if let Some((g, callee)) = &mut row
                    && !cx.locals.contains_key(g)
                    && let Some((_, uses)) = self.effects.poly.get(g)
                {
                    let tail = self.row_argument(callee, uses, arguments, cx);
                    callee.retain(|e| row_var(e).is_none());
                    args.splice(0..0, [op_ty(&tail, sp), res_fn(&tail, sp)]);
                    callee.extend(tail);
                }
                let applied = app((**function).clone(), args);
                let c = match row {
                    Some((g, row)) => self.lift(applied, &row, cx, &g)?,
                    None => call("Comp::ret", vec![cx.op(sp), cx.res(sp), applied], sp),
                };
                Ok(self.bind_all(binds, c, cx, sp))
            }
            TermKind::Match {
                scrutinee,
                result,
                binder: None,
                arms,
            } => {
                if self.effectful(scrutinee, cx) {
                    let x = self.fresh_name("m");
                    let c = self.computation(scrutinee, cx)?;
                    let c = typed(c, self.guess(scrutinee, cx).as_ref(), cx, sp);
                    let m = T::new(
                        TermKind::Match {
                            scrutinee: Box::new(var(&x, sp)),
                            result: result.clone(),
                            binder: None,
                            arms: arms.clone(),
                        },
                        sp,
                    );
                    let rest = self.computation(&m, cx)?;
                    return Ok(self.bind_all(vec![(x, c)], rest, cx, sp));
                }
                let mut out = Vec::new();
                for a in arms {
                    if a.guard.is_some() {
                        return Err(msg!("kernel-effect-guard"));
                    }
                    out.push(MatchArm {
                        pattern: a.pattern.clone(),
                        guard: None,
                        goal: None,
                        body: self.computation(&a.body, cx)?,
                    });
                }
                let result = result.as_ref().map(|r| {
                    Box::new(call("Comp", vec![cx.op(sp), cx.res(sp), (**r).clone()], sp))
                });
                Ok(T::new(
                    TermKind::Match {
                        scrutinee: scrutinee.clone(),
                        result,
                        binder: None,
                        arms: out,
                    },
                    sp,
                ))
            }
            TermKind::If {
                condition,
                then,
                otherwise: Some(otherwise),
            } => {
                self.pure_or(condition, cx, msg!("kernel-effect-if-condition"))?;
                Ok(T::new(
                    TermKind::If {
                        condition: condition.clone(),
                        then: Box::new(self.computation(then, cx)?),
                        otherwise: Some(Box::new(self.computation(otherwise, cx)?)),
                    },
                    sp,
                ))
            }
            TermKind::Handle { body, handlers } => self.handle(body, handlers, cx, sp),
            // A record's fields are read as a call's arguments: in the order
            // written, those with effects bound first.
            TermKind::Record { name, fields, .. } => {
                let values: Vec<T> = fields.iter().map(|(_, v)| v.clone()).collect();
                let (values, binds) = self.arguments(&values, cx)?;
                let record = T::new(
                    TermKind::Record {
                        name: name.clone(),
                        fields: fields.iter().map(|(n, _)| n.clone()).zip(values).collect(),
                        base: None,
                    },
                    sp,
                );
                let c = call("Comp::ret", vec![cx.op(sp), cx.res(sp), record], sp);
                Ok(self.bind_all(binds, c, cx, sp))
            }
            _ => Err(msg!("kernel-effect-body-form")),
        }
    }

    /// The effects the row variable of a function stands for in a call of it
    /// with `arguments`: those of the row of a function passed for a
    /// parameter whose row has the variable, or else those of `cx`, other
    /// than the function's own.
    fn row_argument(
        &self,
        callee: &[String],
        uses: &[usize],
        arguments: &[T],
        cx: &Cx,
    ) -> Vec<String> {
        let passed = uses.iter().find_map(|&i| match &*arguments.get(i)?.kind {
            TermKind::Var(n) => match cx.locals.get(n) {
                Some(row) => Some(row),
                None if !self.effects.poly.contains_key(n) => self.effects.fns.get(n),
                None => None,
            },
            _ => None,
        });
        passed
            .unwrap_or(&cx.row)
            .iter()
            .filter(|e| row_var(e).is_some() || !callee.contains(e))
            .cloned()
            .collect()
    }

    /// `perform effect(args)` in `cx`.
    fn perform(&mut self, effect: &str, args: &[T], cx: &Cx, sp: Span) -> Read<T> {
        if !cx.row.iter().any(|e| e == effect) {
            return Err(msg!("kernel-effect-not-in-row", name = effect));
        }
        if self.effects.sigs.get(effect) != Some(&args.len()) {
            return Err(msg!("kernel-effect-arity", name = effect));
        }
        let (args, binds) = self.arguments(args, cx)?;
        let o = call(&args_name(effect), args, sp);
        let c = call(
            "Comp::op",
            vec![cx.op(sp), cx.res(sp), inject(&cx.row, effect, o, sp)],
            sp,
        );
        Ok(self.bind_all(binds, c, cx, sp))
    }

    /// The arguments with those that have effects replaced by names, and the
    /// computations those names are bound to, in the order written.
    fn arguments(&mut self, args: &[T], cx: &Cx) -> Read<(Vec<T>, Vec<(String, T)>)> {
        let mut out = Vec::new();
        let mut binds = Vec::new();
        for a in args {
            // A call of a function without effects is kept, its arguments
            // bound first, so that each bound computation has a known type.
            if let TermKind::App {
                function,
                arguments,
            } = &*a.kind
                && self.effectful(a, cx)
                && !self.effectful(function, cx)
                && !matches!(&*function.kind, TermKind::Var(g)
                    if cx.locals.contains_key(g) || self.effects.fns.contains_key(g))
            {
                let (inner, more) = self.arguments(arguments, cx)?;
                binds.extend(more);
                out.push(app((**function).clone(), inner));
                continue;
            }
            if self.effectful(a, cx) {
                let x = self.fresh_name("a");
                let c = self.computation(a, &cx.expecting(self.guess(a, cx)))?;
                binds.push((x.clone(), typed(c, self.guess(a, cx).as_ref(), cx, a.span)));
                out.push(var(&x, a.span));
            } else {
                out.push(a.clone());
            }
        }
        Ok((out, binds))
    }

    fn bind_all(&mut self, binds: Vec<(String, T)>, c: T, cx: &Cx, sp: Span) -> T {
        binds.into_iter().rev().fold(c, |rest, (x, value)| {
            call(
                "Comp::bind",
                vec![cx.op(sp), cx.res(sp), value, lam(&[x], rest)],
                sp,
            )
        })
    }

    /// `c`, a computation of `row`, in the row of `cx`.
    fn lift(&mut self, c: T, row: &[String], cx: &Cx, g: &str) -> Read<T> {
        if row == cx.row.as_slice() {
            return Ok(c);
        }
        if let Some(e) = row.iter().find(|e| !cx.row.contains(e)) {
            return Err(msg!(
                "kernel-effect-call-not-in-row",
                function = g,
                name = e
            ));
        }
        let sp = c.span;
        let mut arms = Vec::new();
        for e in row {
            let (x, k) = (self.fresh_name("x"), self.fresh_name("k"));
            let body = call(
                "Comp::forward",
                vec![
                    cx.op(sp),
                    cx.res(sp),
                    inject(&cx.row, e, var(&x, sp), sp),
                    var(&k, sp),
                ],
                sp,
            );
            arms.push(lam(&[x, k], body));
        }
        let arm = self.arm_tree(row, &arms, sp);
        Ok(call(
            "Comp::lift",
            vec![
                op_ty(row, sp),
                res_fn(row, sp),
                cx.op(sp),
                cx.res(sp),
                c,
                arm,
            ],
            sp,
        ))
    }

    /// The operation arm of a handler of `row`, from an arm for each effect.
    fn arm_tree(&mut self, row: &[String], arms: &[T], sp: Span) -> T {
        let o = self.fresh_name("o");
        let k = self.fresh_name("k");
        let body = match row.split_first() {
            None => call("arm_none", vec![var(&o, sp), var(&k, sp)], sp),
            Some((e, _)) if row_var(e).is_some() => {
                app(arms[0].clone(), vec![var(&o, sp), var(&k, sp)])
            }
            Some((e, rest)) => {
                let there = self.arm_tree(rest, &arms[1..], sp);
                call(
                    "arm_sum",
                    vec![
                        var(&op_name(e), sp),
                        op_ty(rest, sp),
                        var(&res_name(e), sp),
                        res_fn(rest, sp),
                        arms[0].clone(),
                        there,
                        var(&o, sp),
                        var(&k, sp),
                    ],
                    sp,
                )
            }
        };
        lam(&[o, k], body)
    }

    fn block(&mut self, stmts: &[Stmt], cx: &Cx, sp: Span) -> Read<T> {
        let Some((first, rest)) = stmts.split_first() else {
            return Err(msg!("kernel-effect-block-value"));
        };
        if rest.is_empty() {
            let Stmt::Expr(last) = first else {
                return Err(msg!("kernel-effect-block-value"));
            };
            return self.computation(last, cx);
        }
        Ok(match first {
            Stmt::Let {
                name,
                value,
                borrow: false,
                borrow_mut: false,
                ty,
            } => {
                let known = ty.clone().or_else(|| self.guess(value, cx));
                let mut inner = cx.clone();
                inner.locals.remove(name);
                match &known {
                    Some(t) => inner.types.insert(name.clone(), t.clone()),
                    None => inner.types.remove(name),
                };
                let after = self.block(rest, &inner, sp)?;
                if self.effectful(value, cx) {
                    let c = self.computation(value, &cx.expecting(known.clone()))?;
                    let c = typed(c, known.as_ref(), cx, sp);
                    call(
                        "Comp::bind",
                        vec![
                            cx.op(sp),
                            cx.res(sp),
                            c,
                            lam(std::slice::from_ref(name), after),
                        ],
                        sp,
                    )
                } else {
                    T::new(
                        TermKind::Block(vec![
                            Stmt::Let {
                                name: name.clone(),
                                ty: ty.clone(),
                                value: value.clone(),
                                borrow: false,
                                borrow_mut: false,
                            },
                            Stmt::Expr(after),
                        ]),
                        sp,
                    )
                }
            }
            Stmt::Expr(e) if self.effectful(e, cx) => {
                let after = self.block(rest, cx, sp)?;
                let known = self.guess(e, cx);
                let c = self.computation(e, &cx.expecting(known.clone()))?;
                let c = typed(c, known.as_ref(), cx, sp);
                call(
                    "Comp::bind",
                    vec![cx.op(sp), cx.res(sp), c, lam(&["_".to_string()], after)],
                    sp,
                )
            }
            // A statement without effects gives a value nobody uses.
            Stmt::Expr(_) => self.block(rest, cx, sp)?,
            Stmt::Var {
                name,
                ty,
                value,
                borrow: false,
            } => self.var(name, ty.as_ref(), value, rest, cx, sp)?,
            Stmt::Assign { place: Some(p), .. } => {
                return Err(msg!(
                    "kernel-effect-assign-field",
                    place = crate::surface::print::print_term(p)
                ));
            }
            Stmt::Assign { name, value, .. } => {
                let Some((_, put)) = cx.vars.get(name).cloned() else {
                    return Err(msg!("kernel-effect-assign-not-var", name = name));
                };
                let after = self.block(rest, cx, sp)?;
                let c = self.perform(&put, std::slice::from_ref(value), cx, sp)?;
                let c = typed(c, Some(&var("Unit", sp)), cx, sp);
                call(
                    "Comp::bind",
                    vec![cx.op(sp), cx.res(sp), c, lam(&["_".to_string()], after)],
                    sp,
                )
            }
            _ => return Err(msg!("kernel-effect-block-statement")),
        })
    }

    /// `var name: S = value; rest`: `rest` reads and writes `name` with two
    /// effects of its own, handled here by passing the value along.
    fn var(
        &mut self,
        name: &str,
        ty: Option<&T>,
        value: &T,
        rest: &[Stmt],
        cx: &Cx,
        sp: Span,
    ) -> Read<T> {
        let Some(state) = ty.cloned().or_else(|| self.guess(value, cx)) else {
            return Err(msg!("kernel-effect-var-type", name = name));
        };
        let Some(a) = cx.expect.clone() else {
            return Err(msg!("kernel-effect-block-type", name = name));
        };
        self.fresh += 1;
        let (get, put) = (
            format!("{name}@get{}", self.fresh),
            format!("{name}@put{}", self.fresh),
        );
        let mut made = self.make_effect(&get, Vec::new(), state.clone(), sp);
        made.extend(self.make_effect(&put, vec![state.clone()], var("Unit", sp), sp));
        self.effects.pending.extend(made);
        let mut row = cx.row.clone();
        row.extend([get.clone(), put.clone()]);
        let mut inner = cx.clone();
        inner.row = canonical(&row);
        inner.vars.insert(name.into(), (get.clone(), put.clone()));
        inner.types.insert(name.into(), state.clone());
        inner.locals.remove(name);
        let body = self.block(rest, &inner, sp)?;
        let body = typed(body, Some(&a), &inner, sp);
        let fresh = |k: &mut Self, base: &str| k.fresh_name(base);
        let mut arms = Vec::new();
        for e in &inner.row {
            let (x, k) = (fresh(self, "x"), fresh(self, "k"));
            let (k1, s1, v1, r1) = (
                fresh(self, "k"),
                fresh(self, "s"),
                fresh(self, "v"),
                fresh(self, "r"),
            );
            let v = |n: &str| var(n, sp);
            let arm = if *e == get {
                let f = lam(
                    &[k1.clone(), s1.clone()],
                    app(app(v(&k1), vec![v(&s1)]), vec![v(&s1)]),
                );
                call(&arm_name(e), vec![f, v(&x), v(&k)], sp)
            } else if *e == put {
                let f = lam(
                    &[v1.clone(), k1.clone(), s1.clone()],
                    app(app(v(&k1), vec![v("Star")]), vec![v(&v1)]),
                );
                call(&arm_name(e), vec![f, v(&x), v(&k)], sp)
            } else {
                let back = lam(
                    std::slice::from_ref(&r1),
                    app(app(v(&k), vec![v(&r1)]), vec![v(&s1)]),
                );
                lam(
                    std::slice::from_ref(&s1),
                    call(
                        "Comp::forward",
                        vec![cx.op(sp), cx.res(sp), inject(&cx.row, e, v(&x), sp), back],
                        sp,
                    ),
                )
            };
            arms.push(lam(&[x, k], arm));
        }
        let (a1, s2) = (fresh(self, "a"), fresh(self, "s"));
        let ret = lam(
            &[a1.clone(), s2],
            call("Comp::ret", vec![cx.op(sp), cx.res(sp), var(&a1, sp)], sp),
        );
        let arm = self.arm_tree(&inner.row, &arms, sp);
        let passing = pi(
            None,
            state.clone(),
            call("Comp", vec![cx.op(sp), cx.res(sp), a], sp),
        );
        let handled = call(
            "the",
            vec![
                passing,
                call(
                    "Comp::fold",
                    vec![inner.op(sp), inner.res(sp), ret, arm, body],
                    sp,
                ),
            ],
            sp,
        );
        let (init, binds) = self.arguments(std::slice::from_ref(value), cx)?;
        Ok(self.bind_all(binds, app(handled, init), cx, sp))
    }

    /// The type of the value of `t`, when it is plain to see: a variable of
    /// known type, an operation, a call of a function whose result is written,
    /// a block ending in one of those.
    fn guess(&self, t: &T, cx: &Cx) -> Option<T> {
        match &*t.kind {
            TermKind::Var(x) if cx.locals.contains_key(x) => cx.types.get(x).and_then(comp_value),
            TermKind::Var(x) => cx.types.get(x).cloned(),
            TermKind::Nat(_) => Some(var("Nat", t.span)),
            TermKind::Handle { body, handlers } => {
                let body_ty = self.guess(body, cx);
                match handlers.iter().find_map(|h| match h {
                    Handler::Return { pattern, body } => Some((pattern, body)),
                    _ => None,
                }) {
                    None => body_ty,
                    Some((pattern, r)) => {
                        let mut inner = cx.clone();
                        if let (Pattern::Bind(v), Some(ty)) = (pattern, body_ty) {
                            inner.types.insert(v.clone(), ty);
                        }
                        self.guess(r, &inner)
                    }
                }
            }
            TermKind::Perform { effect, .. } => self.effects.results.get(effect).cloned(),
            TermKind::App { function, .. } => match &*function.kind {
                TermKind::Var(g) if !cx.types.contains_key(g) && !cx.locals.contains_key(g) => {
                    self.effects.results.get(g).cloned()
                }
                TermKind::Var(g) if cx.locals.contains_key(g) => {
                    cx.types.get(g).and_then(comp_value)
                }
                _ => None,
            },
            TermKind::Block(stmts) => {
                let mut inner = cx.clone();
                for s in stmts {
                    match s {
                        Stmt::Let {
                            name, ty, value, ..
                        } => {
                            match ty.clone().or_else(|| self.guess(value, &inner)) {
                                Some(t) => inner.types.insert(name.clone(), t),
                                None => inner.types.remove(name),
                            };
                        }
                        Stmt::Expr(_) => {}
                        _ => return None,
                    }
                }
                match stmts.last() {
                    Some(Stmt::Expr(e)) => self.guess(e, &inner),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `handle { body } with { handlers }`, a computation in `cx`.
    fn handle(&mut self, body: &T, handlers: &[Handler], cx: &Cx, sp: Span) -> Read<T> {
        let mut ops: HashMap<String, (Vec<String>, String, T)> = HashMap::new();
        let mut ret: Option<(String, T)> = None;
        for h in handlers {
            match h {
                Handler::Return { pattern, body } => {
                    let v = match pattern {
                        Pattern::Bind(v) => v.clone(),
                        Pattern::Wild => self.fresh_name("v"),
                        _ => return Err(msg!("kernel-effect-return-pattern")),
                    };
                    ret = Some((v, body.clone()));
                }
                Handler::Operation {
                    effect,
                    patterns,
                    cont,
                    guard,
                    body,
                    ..
                } => {
                    if guard.is_some() {
                        return Err(msg!("kernel-effect-handler-guard"));
                    }
                    if self.effects.sigs.get(effect) != Some(&patterns.len()) {
                        return Err(msg!("kernel-effect-not-read", name = effect));
                    }
                    let mut names = Vec::new();
                    for p in patterns {
                        names.push(match p {
                            Pattern::Bind(v) => v.clone(),
                            Pattern::Wild => self.fresh_name("p"),
                            _ => return Err(msg!("kernel-effect-handler-pattern")),
                        });
                    }
                    let k = cont.clone().unwrap_or_else(|| self.fresh_name("k"));
                    if ops
                        .insert(effect.clone(), (names, k, body.clone()))
                        .is_some()
                    {
                        return Err(msg!("kernel-effect-two-arms", name = effect));
                    }
                }
            }
        }
        let ret_written = ret.is_some();
        let mut inner_row = cx.row.clone();
        inner_row.extend(ops.keys().cloned());
        let inner = Cx {
            row: canonical(&inner_row),
            locals: cx.locals.clone(),
            types: cx.types.clone(),
            vars: cx.vars.clone(),
            expect: None,
        };
        let mut arms = Vec::new();
        for e in &inner.row {
            let x = self.fresh_name("x");
            let k = self.fresh_name("k");
            let arm = match ops.get(e) {
                Some((names, kname, body)) => {
                    let mut armcx = cx.clone();
                    armcx.locals.insert(kname.clone(), cx.row.clone());
                    let b = self.computation(body, &armcx)?;
                    let mut ps = names.clone();
                    ps.push(kname.clone());
                    call(
                        &arm_name(e),
                        vec![lam(&ps, b), var(&x, sp), var(&k, sp)],
                        sp,
                    )
                }
                None => call(
                    "Comp::forward",
                    vec![
                        cx.op(sp),
                        cx.res(sp),
                        inject(&cx.row, e, var(&x, sp), sp),
                        var(&k, sp),
                    ],
                    sp,
                ),
            };
            arms.push(lam(&[x, k], arm));
        }
        let ret = match ret {
            Some((v, r)) => lam(&[v], self.computation(&r, cx)?),
            None => {
                let v = self.fresh_name("v");
                lam(
                    std::slice::from_ref(&v),
                    call("Comp::ret", vec![cx.op(sp), cx.res(sp), var(&v, sp)], sp),
                )
            }
        };
        let body_ty = match ret_written {
            true => self.guess(body, &inner),
            false => cx.expect.clone(),
        };
        let c = self.computation(body, &inner.expecting(body_ty.clone()))?;
        let c = typed(c, body_ty.as_ref(), &inner, sp);
        let arm = self.arm_tree(&inner.row, &arms, sp);
        Ok(call(
            "Comp::handle_in",
            vec![
                inner.op(sp),
                inner.res(sp),
                cx.op(sp),
                cx.res(sp),
                c,
                ret,
                arm,
            ],
            sp,
        ))
    }

    fn effects_known(&self) -> bool {
        !self.effects.sigs.is_empty()
    }

    fn has_handle(&self, t: &T) -> bool {
        let mut found = false;
        let mut t = t.clone();
        walk::term(&mut t, &mut |s| {
            if matches!(&*s.kind, TermKind::Handle { .. }) {
                found = true
            }
        });
        found
    }

    /// A function without effects whose body handles them: its body read as a
    /// computation that performs nothing, and its value taken.
    fn pure_fn(&mut self, f: &FnDecl) -> Read<FnDecl> {
        let sp = f.span;
        let Some(result) = &f.result else {
            return Err(msg!("kernel-no-result-type"));
        };
        if self.effects.sigs.is_empty() {
            return Err(msg!("kernel-effect-none-read"));
        }
        if f.param_types.iter().any(Option::is_none) {
            return Err(msg!("kernel-effect-untyped-param"));
        }
        let (param_types, locals) = self.effect_params(f)?;
        let cx = Cx {
            row: Vec::new(),
            locals,
            types: f
                .params
                .iter()
                .cloned()
                .zip(param_types.iter().cloned())
                .chain(f.generics.iter().map(|g| (g.clone(), var("Type", sp))))
                .collect(),
            vars: HashMap::new(),
            expect: Some(result.clone()),
        };
        let saved = self.effects.pending.len();
        let body = match self.computation(&ifs_as_matches(&f.body), &cx) {
            Ok(b) => b,
            Err(e) => {
                self.effects.pending.truncate(saved);
                return Err(e);
            }
        };
        let mut g = f.clone();
        g.param_types = param_types.into_iter().map(Some).collect();
        g.body = call("Comp::value", vec![typed(body, Some(result), &cx, sp)], sp);
        Ok(g)
    }

    /// The parameters' types, a function with effects `(A…) -> R ! {e…}`
    /// written as `(A…) -> Comp(…, R)`, and the row of each such parameter,
    /// so that calling it is read as calling a function with effects.
    fn effect_params(&self, f: &FnDecl) -> Read<(Vec<T>, HashMap<String, Vec<String>>)> {
        let mut types = Vec::new();
        let mut locals = HashMap::new();
        for (p, t) in f.params.iter().zip(f.param_types.iter().flatten()) {
            let TermKind::Pi {
                params,
                result,
                effects: Some(row),
            } = &*t.kind
            else {
                types.push(t.clone());
                continue;
            };
            if row.is_empty() {
                types.push(t.clone());
                continue;
            }
            if !row_vars(row).is_empty() && !self.effects.poly.contains_key(&f.name) {
                return Err(msg!("kernel-effect-param-row-variable", name = p));
            }
            if let Some(why) = self.unread_row(row, &f.generics) {
                return Err(msg!("kernel-effect-param-row-unread", name = p, why = why));
            }
            let row = canonical(row);
            let sp = t.span;
            let comp = call(
                "Comp",
                vec![op_ty(&row, sp), res_fn(&row, sp), (**result).clone()],
                sp,
            );
            locals.insert(p.clone(), row);
            // Without parameters it is the computation itself, as a function
            // with effects and no parameters is.
            if params.is_empty() {
                types.push(comp);
                continue;
            }
            types.push(T::new(
                TermKind::Pi {
                    params: params.clone(),
                    result: Box::new(comp),
                    effects: None,
                },
                sp,
            ));
        }
        Ok((types, locals))
    }

    /// A `handle` that leaves no effect, where no effect may be: its value.
    fn pure_handle(&mut self, t: &T) -> Read<T> {
        let t = ifs_as_matches(t);
        let TermKind::Handle { body, handlers } = &*t.kind else {
            unreachable!("only a `handle` is read")
        };
        if !self.effects.sigs.is_empty() || !self.effects.fns.is_empty() {
            let cx = Cx {
                row: Vec::new(),
                locals: HashMap::new(),
                types: HashMap::new(),
                vars: HashMap::new(),
                expect: None,
            };
            let c = self.handle(body, handlers, &cx, t.span)?;
            return Ok(call("Comp::value", vec![c], t.span));
        }
        Err(msg!("kernel-effect-none-read"))
    }
}

/// The variable of `f`'s row, if it has one, and the parameters that are
/// functions whose rows have it.
fn row_poly(f: &FnDecl) -> Read<Option<(String, Vec<usize>)>> {
    let own = row_vars(f.effects.as_deref().unwrap_or_default());
    let mut uses = Vec::new();
    for (i, t) in f.param_types.iter().enumerate() {
        let Some(t) = t else { continue };
        let TermKind::Pi {
            effects: Some(row), ..
        } = &*t.kind
        else {
            continue;
        };
        for v in row_vars(row) {
            if !own.contains(&v) {
                return Err(msg!(
                    "kernel-effect-param-row-own",
                    name = &f.params[i],
                    variable = &v
                ));
            }
            uses.push(i);
        }
    }
    Ok(own.into_iter().next().map(|v| (v, uses)))
}

/// `t` with each `if` written as the `match` on `Bool` it stands for, since the
/// read body is checked as it is.
fn ifs_as_matches(t: &T) -> T {
    let mut t = t.clone();
    walk::term(&mut t, &mut |s| {
        if matches!(&*s.kind, TermKind::If { .. }) {
            *s = super::mutable::if_match(s);
        }
    });
    t
}
