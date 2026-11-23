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
//! An effect's type generics `G…` are the first parameters of each of the
//! three, and a row holds the effect's instances (`fail(Nat)`): the
//! operations of `fail(Nat)` are `fail@op(Nat)`.
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

use super::inductive::app;
use super::wf::{lam, pi, var};
use super::{Kernel, T, Verdict};
use crate::surface::Name;
use crate::surface::{
    Constructor, FnDecl, Handler, InductiveDecl, Instance, MatchArm, Pattern, Stmt,
};
use crate::surface::{TermKind, walk};
use std::collections::{HashMap, HashSet};
use tauto_message::{Message, msg};
use tauto_parol::Span;

#[derive(Clone, Default)]
pub(super) struct Effects {
    /// An effect read in proofs: how many parameters its operation takes.
    pub(super) sigs: tauto_identity::ForkedMap<Name, usize>,
    /// An effect read in proofs that has type generics: their names. A row
    /// holds its instances (`fail(Nat)`), each with its type arguments.
    type_params: tauto_identity::ForkedMap<Name, Vec<Name>>,
    /// A function read in proofs: its row.
    pub(super) fns: tauto_identity::ForkedMap<Name, Vec<Name>>,
    /// Source parameters before a computation returns a function value.
    arities: tauto_identity::ForkedMap<Name, usize>,
    /// A function read in proofs: its generics and its parameters' types, to
    /// find the instances its row has at a call (`fail(E)` at `E := Nat`).
    signatures: tauto_identity::ForkedMap<Name, (Vec<Name>, Vec<Option<T>>)>,
    /// Source generics that remain before the explicit row parameters.
    generics: tauto_identity::ForkedMap<Name, usize>,
    /// Written effect rows of function-valued ordinary parameters.
    callback_rows: tauto_identity::ForkedMap<Name, Vec<Option<Vec<Name>>>>,
    /// A function read in proofs whose row has a variable: the variable, and
    /// the parameters that are functions whose rows have it.
    poly: tauto_identity::ForkedMap<Name, (Name, Vec<usize>)>,
    /// A function with effects, or one whose `handle`s, not read in proofs, and why.
    pub(super) skipped: tauto_identity::ForkedMap<Name, Message>,
    /// The declarations made for the effects.
    pub(super) generated: tauto_identity::ForkedSet<Name>,
    /// The type of the answer to each effect, and the result type of each
    /// function with effects that has no generics.
    pub(super) results: tauto_identity::ForkedMap<Name, T>,
    /// The read operation that gives each source local its checked type.
    pub(super) locals: tauto_identity::ForkedMap<Name, Name>,
    /// The declarations of the effects made for the `var`s of the function
    /// being read, to come before it.
    pending: Vec<Stmt>,
    /// The functions without effects whose `handle`s are read in proofs.
    pub(super) handling: tauto_identity::ForkedSet<Name>,
    /// Each effect's `resume` as written, `None` for the default `<=1`.
    pub(super) resumes: tauto_identity::ForkedMap<Name, Option<String>>,
    /// The functions with effects whose `decreasing_by` could not be written
    /// out, for the pass that called `effect_pass` to report.
    pub(super) failed: Vec<super::Entry>,
}

impl Effects {
    /// Leaves in this copy only what it wrote since it was made.
    pub(super) fn subtract(&mut self, since: u64) {
        self.sigs.subtract(since);
        self.type_params.subtract(since);
        self.fns.subtract(since);
        self.arities.subtract(since);
        self.signatures.subtract(since);
        self.generics.subtract(since);
        self.callback_rows.subtract(since);
        self.poly.subtract(since);
        self.skipped.subtract(since);
        self.generated.subtract(since);
        self.results.subtract(since);
        self.locals.subtract(since);
        self.handling.subtract(since);
        self.resumes.subtract(since);
    }

    /// Takes in what a copy of these effects wrote (`check/fork.rs`); false
    /// as [`tauto_identity::ForkedMap::absorb`] is.
    pub(super) fn absorb(&mut self, other: Effects) -> bool {
        let Effects {
            sigs,
            type_params,
            fns,
            arities,
            signatures,
            generics,
            callback_rows,
            poly,
            skipped,
            generated,
            results,
            locals,
            pending: _,
            failed: _,
            handling,
            resumes,
        } = other;
        let mut alone = true;
        alone &= self.sigs.absorb(sigs);
        alone &= self.type_params.absorb(type_params);
        alone &= self.fns.absorb(fns);
        alone &= self.arities.absorb(arities);
        alone &= self.signatures.absorb(signatures);
        alone &= self.generics.absorb(generics);
        alone &= self.callback_rows.absorb(callback_rows);
        alone &= self.poly.absorb(poly);
        alone &= self.skipped.absorb(skipped);
        alone &= self.generated.absorb(generated);
        alone &= self.results.absorb(results);
        alone &= self.locals.absorb(locals);
        alone &= self.handling.absorb(handling);
        alone &= self.resumes.absorb(resumes);
        alone
    }

    /// Whether an effect read in proofs has type generics. Its operations
    /// are a family, which a package does not run as one of the host's.
    pub(super) fn has_type_params(&self, name: &Name) -> bool {
        self.type_params.contains_key(name)
    }

    /// How many parameters after the generics a function read in proofs
    /// has for its row variable, which a source call leaves out.
    pub(super) fn row_params(&self, name: &Name) -> usize {
        match self.poly.contains_key(name) {
            true => 2,
            false => 0,
        }
    }
}

fn call(f: impl Into<Name>, args: Vec<T>, sp: Span) -> T {
    app(var(f, sp), args)
}

fn one_arm(scrutinee: T, result: T, ctor: impl Into<Name>, binders: &[Name], body: T) -> T {
    let sp = scrutinee.span;
    T::new(
        TermKind::Match {
            scrutinee: Box::new(scrutinee),
            result: Some(Box::new(result)),
            binder: None,
            arms: vec![MatchArm {
                pattern: Pattern::Ctor {
                    name: ctor.into(),
                    args: binders.iter().cloned().map(Pattern::bind).collect(),
                },
                guard: None,
                goal: None,
                body,
            }],
            binder_unused: None,
        },
        sp,
    )
}

fn effect_name(e: &Name, generation: tauto_surface::identity::Generation, suffix: &str) -> Name {
    match e {
        Name::Global(reference) => reference.generated(generation).into(),
        Name::Spelled(_) => Name::from(format!("{e}@{suffix}")),
        _ => panic!("an effect helper belongs to a declaration"),
    }
}

fn op_name(e: &Name) -> Name {
    effect_name(
        e,
        tauto_surface::identity::Generation::EffectOperations,
        "op",
    )
}
pub(super) fn args_name(e: &Name) -> Name {
    effect_name(
        e,
        tauto_surface::identity::Generation::EffectArguments,
        "args",
    )
}
fn res_name(e: &Name) -> Name {
    effect_name(e, tauto_surface::identity::Generation::EffectResult, "res")
}
fn arm_name(e: &Name) -> Name {
    effect_name(e, tauto_surface::identity::Generation::EffectArm, "arm")
}

/// The effects of a row in the order of their names, each once, and its
/// variable `|e`, if it has one, last.
fn canonical(row: &[Name]) -> Vec<Name> {
    let (mut tail, mut row): (Vec<Name>, Vec<Name>) =
        row.iter().cloned().partition(|e| row_var(e).is_some());
    row.sort();
    row.dedup();
    tail.dedup();
    row.append(&mut tail);
    row
}

/// The variable `e` of a row's entry `|e`.
fn row_var(e: &Name) -> Option<Name> {
    e.row_variable()
}

fn row_name(e: &Name, generation: tauto_surface::identity::LocalGeneration, suffix: &str) -> Name {
    match e {
        Name::Local(reference) => Name::Local(reference.generated(generation)),
        Name::Spelled(_) => Name::from(format!("{e}@{suffix}")),
        _ => panic!("a row helper belongs to a local parameter"),
    }
}
fn var_op(e: &Name) -> Name {
    row_name(
        e,
        tauto_surface::identity::LocalGeneration::RowOperations,
        "rowop",
    )
}
fn var_res(e: &Name) -> Name {
    row_name(
        e,
        tauto_surface::identity::LocalGeneration::RowResults,
        "rowres",
    )
}

/// The row variables of a row, in the order written.
fn row_vars(row: &[Name]) -> Vec<Name> {
    row.iter().filter_map(|e| row_var(e)).collect()
}

/// The type of the value of a parameter `effect_params` wrote:
/// `Comp(O, R, A)` or `(…) -> Comp(O, R, A)` gives `A`.
fn comp_value(t: &T) -> Option<T> {
    match &*t.kind {
        TermKind::Pi { result, .. } => comp_value(result),
        TermKind::App {
            function,
            arguments,
        } if matches!(&*function.kind, TermKind::Var(c) if tauto_surface::bindings::is_library(&c, "Comp"))
            && arguments.len() == 3 =>
        {
            Some(arguments[2].clone())
        }
        _ => None,
    }
}

/// The variables in scope that `state`, a `var`'s type, names, with their
/// types: type generics of any kind and term parameters (`n` in `Vec(n)`),
/// with what their types name in turn, each after what its type names.
fn state_generics(state: &T, cx: &Cx) -> Vec<(Name, T)> {
    fn names(t: &T, cx: &Cx, out: &mut Vec<Name>) {
        walk::visit(t, &mut |s| {
            if let TermKind::Var(v) = &*s.kind
                && cx.types.contains_key(v)
                && !cx.vars.contains_key(v)
                && !out.contains(v)
            {
                out.push(v.clone());
            }
            true
        });
    }
    let mut todo = Vec::new();
    names(state, cx, &mut todo);
    let mut i = 0;
    while i < todo.len() {
        let k = cx.types[&todo[i]].clone();
        names(&k, cx, &mut todo);
        i += 1;
    }
    let mut out: Vec<(Name, T)> = Vec::new();
    while !todo.is_empty() {
        let at = todo
            .iter()
            .position(|v| {
                let mut needs = Vec::new();
                names(&cx.types[v], cx, &mut needs);
                needs
                    .iter()
                    .all(|n| n == v || out.iter().any(|(o, _)| o == n))
            })
            .unwrap_or(0);
        let v = todo.remove(at);
        out.push((v.clone(), cx.types[&v].clone()));
    }
    out
}

/// The row entry of the effect `e` at its own type generics `generics`.
fn instance(e: &Name, generics: &[(Name, T)], sp: Span) -> Name {
    match (e, generics.is_empty()) {
        (Name::Global(r), false) => Name::Effect(std::sync::Arc::new(
            tauto_surface::identity::EffectUse::new(
                r.clone(),
                generics.iter().map(|(g, _)| var(g, sp)).collect(),
                Vec::new(),
                false,
                e.to_string(),
            ),
        )),
        _ => e.clone(),
    }
}

/// The effect a row's entry is an instance of: `fail` for `fail(Nat)`.
fn head(e: &Name) -> Name {
    match e {
        Name::Effect(u) => Name::Global(u.effect().clone()),
        _ => e.clone(),
    }
}

/// The type arguments of a row's entry: `Nat` for `fail(Nat)`.
fn type_args(e: &Name) -> Vec<T> {
    match e {
        Name::Effect(u) => u.arguments().to_vec(),
        _ => Vec::new(),
    }
}

/// `f` of the effect of the entry `e`, applied to the entry's type arguments
/// and then to `rest`.
fn instance_call(f: Name, e: &Name, rest: Vec<T>, sp: Span) -> T {
    let mut args = type_args(e);
    args.extend(rest);
    match args.is_empty() {
        true => var(&f, sp),
        false => call(f, args, sp),
    }
}

/// The operations of the entry `e`: `e@op`, or `fail@op(Nat)` for `fail(Nat)`.
fn op_of(e: &Name, sp: Span) -> T {
    instance_call(op_name(&head(e)), e, Vec::new(), sp)
}

/// The answers to the operations of the entry `e`.
fn res_of(e: &Name, sp: Span) -> T {
    if type_args(e).is_empty() {
        return var(&res_name(e), sp);
    }
    let o = Name::from("o''");
    lam(
        std::slice::from_ref(&o),
        instance_call(res_name(&head(e)), e, vec![var(&o, sp)], sp),
    )
}

/// Each of `generics` that `pattern` names where `t` has a type: what
/// `pattern` is, read as a type of `t`'s shape.
fn match_type(pattern: &T, t: &T, generics: &[Name], found: &mut HashMap<Name, T>) {
    match (&*pattern.kind, &*t.kind) {
        (TermKind::Var(v), _) if generics.contains(v) => {
            found.entry(v.clone()).or_insert_with(|| t.clone());
        }
        (
            TermKind::App {
                function: f,
                arguments: ps,
            },
            TermKind::App {
                function: h,
                arguments: ts,
            },
        ) if ps.len() == ts.len() => {
            match_type(f, h, generics, found);
            for (p, t) in ps.iter().zip(ts) {
                match_type(p, t, generics, found);
            }
        }
        _ => {}
    }
}

/// The operations of `row`.
fn op_ty(row: &[Name], sp: Span) -> T {
    match row.split_first() {
        None => var(&tauto_surface::bindings::library_name("OpNone"), sp),
        Some((e, _)) if let Some(v) = row_var(e) => var(&var_op(&v), sp),
        Some((e, rest)) => call(
            &tauto_surface::bindings::library_name("OpSum"),
            vec![op_of(e, sp), op_ty(rest, sp)],
            sp,
        ),
    }
}

/// The answers to the operations of `row`.
fn res_fn(row: &[Name], sp: Span) -> T {
    match row.split_first() {
        None => var(&tauto_surface::bindings::library_name("res_none"), sp),
        Some((e, _)) if let Some(v) = row_var(e) => var(&var_res(&v), sp),
        Some((e, rest)) => lam(
            &[Name::from("o'")],
            call(
                "res_sum",
                vec![
                    op_of(e, sp),
                    op_ty(rest, sp),
                    res_of(e, sp),
                    res_fn(rest, sp),
                    var("o'", sp),
                ],
                sp,
            ),
        ),
    }
}

/// `x`, an operation of `e`, as an operation of `row`.
fn inject(row: &[Name], e: &Name, x: T, sp: Span) -> T {
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
            vec![op_of(e, sp), op_ty(&row[p + 1..], sp), x],
            sp,
        ),
    };
    for j in (0..p).rev() {
        t = call(
            "OpThere",
            vec![op_of(&row[j], sp), op_ty(&row[j + 1..], sp), t],
            sp,
        );
    }
    t
}

type Read<X> = Result<X, Message>;

/// Where a computation is read: its row, and the local functions whose calls
/// are computations (the continuations of handlers), with their rows.
#[derive(Clone)]
struct Cx {
    row: Vec<Name>,
    locals: HashMap<Name, Vec<Name>>,
    /// The variables whose types are known.
    types: HashMap<Name, T>,
    /// The `var`s in scope: the effects that read and write each.
    vars: HashMap<Name, (Name, Name)>,
    /// The type of the value of the computation, when known.
    expect: Option<T>,
}

/// `c` with the type of its value written, when it is known, so that the
/// generics of what is around it are found.
fn typed(c: T, ty: Option<&T>, cx: &Cx, sp: Span) -> T {
    match ty {
        Some(ty) => call(
            "the",
            vec![
                call(
                    &tauto_surface::bindings::library_name("Comp"),
                    vec![cx.op(sp), cx.res(sp), ty.clone()],
                    sp,
                ),
                c,
            ],
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
    pub(super) fn effect_verdict(&mut self, name: &Name, verdict: Verdict) -> Verdict {
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
            return Verdict::Skipped(msg!("kernel-effect-types", why = d.to_string()));
        }
        if self.effects.fns.contains_key(name) || self.effects.handling.contains(name) {
            return Verdict::Skipped(msg!("kernel-effect-reading-fails", why = d.to_string()));
        }
        verdict
    }

    /// The statements with each effect's declarations made, and each function
    /// with effects (and each `handle`) read as terms of the proof language.
    pub(super) fn effect_pass(&mut self, stmts: &[Stmt]) -> Vec<Stmt> {
        let mut out = Vec::new();
        // Operators at the fixed-width families are their functions
        // (`check/machine.rs`), read here like any other call.
        let results: HashMap<Name, T> = stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Fn(f) => f.result.clone().map(|r| (f.name.clone(), r)),
                _ => None,
            })
            .collect();
        let read: Vec<Stmt>;
        let stmts = if self.machine_visible() {
            read = stmts
                .iter()
                .map(|s| match s {
                    Stmt::Fn(f) => Stmt::Fn(self.machine_operators(f, &results)),
                    _ => s.clone(),
                })
                .collect();
            read.as_slice()
        } else {
            stmts
        };
        for stmt in stmts {
            match stmt {
                Stmt::Effect(e) => {
                    out.push(stmt.clone());
                    if let Some(made) = self.effect_decls(e) {
                        out.extend(made);
                    }
                }
                Stmt::Fn(f) if f.effects.as_ref().is_some_and(|e| !e.is_empty()) => {
                    let lent = match self.lend(f, stmts) {
                        Ok(lent) => lent,
                        Err(why) => {
                            self.effects.skipped.insert(f.name.clone(), why);
                            out.push(stmt.clone());
                            continue;
                        }
                    };
                    let f = &lent;
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
                    let dicts = dictionaries_of(f);
                    self.effects
                        .arities
                        .insert(f.name.clone(), f.params.len() - dicts);
                    self.effects.signatures.insert(
                        f.name.clone(),
                        (f.generics.clone(), f.param_types[dicts..].to_vec()),
                    );
                    self.effects
                        .generics
                        .insert(f.name.clone(), f.generics.len() - row_generics.len());
                    self.effects.callback_rows.insert(
                        f.name.clone(),
                        f.param_types
                            .iter()
                            .skip(dicts)
                            .map(|ty| match ty.as_ref().map(|ty| &*ty.kind) {
                                Some(TermKind::Pi { effects, .. }) => effects.clone(),
                                _ => None,
                            })
                            .collect(),
                    );
                    if f.generics.iter().all(|g| row_generics.contains(g))
                        && let Some(r) = &f.result
                    {
                        self.effects.results.insert(f.name.clone(), r.clone());
                    }
                    let mut read = self.effect_fn(f);
                    if lent.body != stmt_body(stmt)
                        && let Ok(g) = &mut read
                    {
                        annotate_binds(&mut g.body);
                    }
                    out.append(&mut self.effects.pending);
                    match read {
                        // `decreasing_by` is written out on the computation:
                        // its recursive calls are in the continuations, and
                        // the row's two parameters are passed along.
                        Ok(g)
                            if g.decreasing_by
                                .as_ref()
                                .is_some_and(|y| !super::names_param(&g, y)) =>
                        {
                            let fixed = self.effects.row_params(&g.name);
                            match self.wf_expand(&g, fixed) {
                                Ok(made) => out.extend(made),
                                Err(d) => self.effects.failed.push(super::Entry {
                                    name: g.name.clone(),
                                    verdict: Verdict::Failed(d),
                                }),
                            }
                        }
                        Ok(g) => out.push(Stmt::Fn(g)),
                        Err(why) => {
                            self.effects.fns.remove(&f.name);
                            self.effects.poly.remove(&f.name);
                            self.effects.skipped.insert(f.name.clone(), why);
                            out.push(stmt.clone());
                        }
                    }
                }
                Stmt::Fn(f)
                    if (self.has_handle(&f.body) || self.has_effect_call(&f.body))
                        && self.effects_known() =>
                {
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
    fn unread_row(&self, row: &[Name], generics: &[Name]) -> Option<Message> {
        if let Some(v) = row_vars(row).into_iter().find(|v| !generics.contains(v)) {
            return Some(msg!("kernel-effect-row-variable", name = (v).to_string()));
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
            .find(|e| !self.read_instance(e))
            .map(|e| msg!("kernel-effect-unread", name = (e).to_string()))
    }

    /// Whether a row's entry is an effect read in proofs, and, for an effect
    /// with type generics, an instance of it with a type for each generic.
    fn read_instance(&self, e: &Name) -> bool {
        if let Name::Effect(u) = e
            && (u.is_universal() || !u.parameters().is_empty())
        {
            return false;
        }
        let h = head(e);
        if !self.effects.sigs.contains_key(&h) {
            return false;
        }
        let wanted = self.effects.type_params.get(&h).map_or(0, Vec::len);
        type_args(e).len() == wanted
    }

    /// The entry of `row` that `perform effect(…)` is an operation of.
    fn instance_in(&self, effect: &Name, row: &[Name]) -> Read<Name> {
        if row.contains(effect) {
            return Ok(effect.clone());
        }
        let h = head(effect);
        let mut found = row.iter().filter(|e| row_var(e).is_none() && head(e) == h);
        match (found.next(), found.next()) {
            (Some(e), None) => Ok(e.clone()),
            (None, _) => Err(msg!(
                "kernel-effect-not-in-row",
                name = (effect).to_string()
            )),
            (Some(_), Some(_)) => Err(msg!("kernel-effect-instances", name = (effect).to_string())),
        }
    }

    /// The row of a call of `g` with `arguments`: an instance whose types
    /// name `g`'s generics (`fail(E)`) at the types the arguments give them.
    fn instantiate_row(
        &mut self,
        g: &Name,
        row: &[Name],
        arguments: &[T],
        cx: &Cx,
    ) -> Read<Vec<Name>> {
        let Some((generics, params)) = self.effects.signatures.get(g).cloned() else {
            return Ok(row.to_vec());
        };
        let mentions = |t: &T| {
            !walk::visit(
                t,
                &mut |s| !matches!(&*s.kind, TermKind::Var(v) if generics.contains(v)),
            )
        };
        if !row.iter().any(|e| type_args(e).iter().any(mentions)) {
            return Ok(row.to_vec());
        }
        // The arguments after any written generics.
        let skip = arguments.len().saturating_sub(params.len());
        let mut found: HashMap<Name, T> = HashMap::new();
        for (p, a) in params.iter().zip(&arguments[skip..]) {
            let (Some(p), Some(t)) = (p, self.guess(a, cx)) else {
                continue;
            };
            match_type(p, &t, &generics, &mut found);
        }
        let mut out = Vec::new();
        for e in row {
            let Name::Effect(u) = e else {
                out.push(e.clone());
                continue;
            };
            let mut args = Vec::new();
            for a in u.arguments() {
                let mut a = a.clone();
                for (v, t) in &found {
                    a = self.subst(&a, v, t);
                }
                if mentions(&a) {
                    return Err(msg!(
                        "kernel-effect-instance-unknown",
                        name = (e).to_string()
                    ));
                }
                args.push(a);
            }
            out.push(Name::Effect(std::sync::Arc::new(
                tauto_surface::identity::EffectUse::new(
                    u.effect().clone(),
                    args,
                    u.parameters().to_vec(),
                    u.is_universal(),
                    u.display(),
                ),
            )));
        }
        Ok(canonical(&out))
    }

    /// The type of the answer to the entry `e`: the effect's, its generics
    /// replaced by the entry's type arguments.
    fn result_of(&mut self, e: &Name) -> Option<T> {
        let h = head(e);
        let mut r = self.effects.results.get(&h)?.clone();
        let names = self
            .effects
            .type_params
            .get(&h)
            .cloned()
            .unwrap_or_default();
        for (g, a) in names.iter().zip(type_args(e)) {
            r = self.subst(&r, g, &a);
        }
        Some(r)
    }

    /// `e@op`, `e@res` and `e@arm` for `effect e`, when its types are written.
    fn effect_decls(&mut self, e: &crate::surface::EffectDecl) -> Option<Vec<Stmt>> {
        // A row variable of an effect's operation (`test<!e>`) is not read.
        if e.rows.iter().any(|r| *r) {
            return None;
        }
        let params: Vec<T> = e.params.iter().cloned().collect::<Option<_>>()?;
        let result = e
            .result
            .clone()
            .unwrap_or_else(|| var(&tauto_surface::bindings::library_name("Unit"), e.span));
        let ty = var(&tauto_surface::bindings::library_name("Type"), e.span);
        let generics: Vec<(Name, T)> = e.generics.iter().map(|g| (g.clone(), ty.clone())).collect();
        Some(self.make_effect(&e.name, &generics, params, result, e.span))
    }

    /// The declarations of an effect named `name`. Its type generics are
    /// parameters of each: `e@op(G…)`, `e@res(G…, o)`, `e@arm(G…, f, o, k)`.
    fn make_effect(
        &mut self,
        name: &Name,
        typed_generics: &[(Name, T)],
        params: Vec<T>,
        result: T,
        sp: Span,
    ) -> Vec<Stmt> {
        let result_ty = result.clone();
        let names: Vec<Name> = (0..params.len())
            .map(|i| Name::from(format!("a{i}")))
            .collect();
        let (op, args, res, arm) = (
            op_name(name),
            args_name(name),
            res_name(name),
            arm_name(name),
        );
        let ty = var(&tauto_surface::bindings::library_name("Type"), sp);
        let type_params: Vec<(Name, T)> = typed_generics.to_vec();
        let generics: Vec<Name> = typed_generics.iter().map(|(g, _)| g.clone()).collect();
        let generics = generics.as_slice();
        let op_ty = match generics.is_empty() {
            true => var(&op, sp),
            false => call(&op, generics.iter().map(|g| var(g, sp)).collect(), sp),
        };
        let family = Stmt::Inductive(InductiveDecl {
            vis: Default::default(),
            name: op.clone(),
            params: type_params.clone(),
            sort: ty.clone(),
            constructors: vec![Constructor {
                name: args.clone(),
                implicit: 0,
                params: names.iter().cloned().zip(params.iter().cloned()).collect(),
                result: op_ty.clone(),
            }],
            generates: Default::default(),
            span: sp,
        });
        let fn_decl =
            |name: &Name, generics: Vec<Name>, ps: Vec<(Name, T)>, result: T, body: T| FnDecl {
                lends: None,
                budget: None,
                vis: Default::default(),
                name: name.into(),
                rows: vec![false; generics.len()],
                bounds: vec![None; generics.len()],
                bound_spans: Vec::new(),
                generic_types: Vec::new(),
                generics,
                borrows: vec![None; ps.len()],
                params: ps.iter().map(|(n, _)| n.clone()).collect(),
                param_types: ps.into_iter().map(|(_, t)| Some(t)).collect(),
                result: Some(result),
                effects: None,
                written_effects: None,
                row_hole: None,
                where_: Vec::new(),
                span: sp,
                opaque: false,
                ghost: false,
                decreasing_by: None,
                generates: None,
                body,
                unused: None,
                unused_generics: Vec::new(),
                unused_params: Vec::new(),
            };
        let with_types = |ps: Vec<(Name, T)>| type_params.iter().cloned().chain(ps).collect();
        let answers = fn_decl(
            &res,
            Vec::new(),
            with_types(vec![("o".into(), op_ty.clone())]),
            ty.clone(),
            one_arm(var("o", sp), ty, &args, &names, result.clone()),
        );
        // `f: (a0: P0, …, k: (R) -> B) -> B`
        let b = var("B", sp);
        let to_b = |d: T| pi(None, d, b.clone());
        let mut f_ty = pi(Some(&Name::from("k")), to_b(result), b.clone());
        for (n, p) in names.iter().zip(&params).rev() {
            f_ty = pi(Some(n), p.clone(), f_ty);
        }
        let mut answer_args: Vec<T> = generics.iter().map(|g| var(g, sp)).collect();
        answer_args.push(var("o", sp));
        let answer_o = call(&res, answer_args, sp);
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
            with_types(vec![
                ("f".into(), f_ty),
                ("o".into(), op_ty),
                ("k".into(), to_b(answer_o)),
            ]),
            b.clone(),
            arm_body,
        );
        self.effects.sigs.insert(name.clone(), params.len());
        match generics.is_empty() {
            true => self.effects.type_params.remove(name),
            false => self
                .effects
                .type_params
                .insert(name.clone(), generics.to_vec()),
        };
        self.effects.results.insert(name.clone(), result_ty);
        for n in [&op, &res, &arm] {
            self.effects.generated.insert(n.clone());
        }
        vec![family, Stmt::Fn(answers), Stmt::Fn(arm_decl)]
    }

    fn effect_fn(&mut self, f: &FnDecl) -> Read<FnDecl> {
        let sp = f.span;
        let Some(result) = &f.result else {
            return Err(msg!("kernel-effect-no-result"));
        };
        if f.param_types.iter().any(Option::is_none) {
            return Err(msg!("kernel-effect-untyped-param"));
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
                    f.generic_parameters()
                        .into_iter()
                        .filter(|(g, _)| Some(g) != row_generic.as_ref()),
                )
                .collect(),
            vars: HashMap::new(),
            expect: Some(result.clone()),
        };
        let body = self.computation(&ifs_as_matches(&f.body), &cx)?;
        let mut g = f.clone();
        // A row variable `e` is two ordinary parameters after the generics: the
        // operations of the effects it stands for and their answers. The
        // function holds for every such row, as the program it reads does.
        if let Some(v) = &row_generic {
            let at = g.generics.iter().position(|x| x == v).expect("a generic");
            g.generics.remove(at);
            if at < g.generic_types.len() {
                g.generic_types.remove(at);
            }
            if at < g.bounds.len() {
                g.bounds.remove(at);
            }
            if at < g.rows.len() {
                g.rows.remove(at);
            }
            if at < g.bound_spans.len() {
                g.bound_spans.remove(at);
            }
            let op = var(&var_op(&v), sp);
            // After the dictionaries of a `where`, which come first.
            let k = dictionaries_of(f);
            g.params.splice(k..k, [var_op(v), var_res(v)]);
            g.borrows.splice(k..k, [None, None]);
            param_types.splice(
                k..k,
                [
                    var(&tauto_surface::bindings::library_name("Type"), sp),
                    pi(
                        None,
                        op,
                        var(&tauto_surface::bindings::library_name("Type"), sp),
                    ),
                ],
            );
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
            // A numeral returned where a fixed-width family is expected is
            // that family's (`check/machine.rs`): `Comp::ret` alone does not
            // say which type its value has.
            let value = match &cx.expect {
                Some(ty) if self.machine_visible() => match self.machine_numeral(t, ty) {
                    Some(v) => v,
                    None if self.machine_mentions(ty) && has_numeral(t) => {
                        call("the", vec![ty.clone(), t.clone()], sp)
                    }
                    None => t.clone(),
                },
                _ => t.clone(),
            };
            return Ok(call("Comp::ret", vec![cx.op(sp), cx.res(sp), value], sp));
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
                if let TermKind::Var(name) = &*function.kind
                    && !cx.locals.contains_key(name)
                    && let Some(&arity) = self.effects.arities.get(name)
                    && arguments.len() > arity
                    && let Some(result) = self.effects.results.get(name).cloned()
                    && matches!(&*result.kind, TermKind::Pi { .. })
                {
                    let prefix = T::new(
                        TermKind::App {
                            function: function.clone(),
                            arguments: arguments[..arity].to_vec(),
                        },
                        sp,
                    );
                    let computation =
                        self.computation(&prefix, &cx.expecting(Some(result.clone())))?;
                    let computation = typed(computation, Some(&result), cx, sp);
                    let returned = self.fresh_name("returned");
                    let mut inner = cx.clone();
                    inner.types.insert(returned.clone(), result);
                    let applied = app(var(&returned, sp), arguments[arity..].to_vec());
                    let rest = self.computation(&applied, &inner)?;
                    return Ok(self.bind_all(vec![(returned, computation)], rest, cx, sp));
                }
                self.pure_or(function, cx, msg!("kernel-effect-called-function"))?;
                // The positions of the arguments that are callbacks in the
                // callee's row variable: λs there are read in that row.
                let callbacks: Vec<usize> = match &*function.kind {
                    TermKind::Var(g) if !cx.locals.contains_key(g) => {
                        match self.effects.poly.get(g) {
                            Some((_, uses)) => {
                                let generics = self.effects.generics.get(g).copied().unwrap_or(0);
                                let arity = self.effects.arities.get(g).copied().unwrap_or(0);
                                let named = matches!(arguments.first().map(|t| &*t.kind),
                                    Some(TermKind::Record { name, .. })
                                        if name.spelling() == Some(tauto_surface::IMPLICITS));
                                let prefix = if named {
                                    1
                                } else if arguments.len() >= arity + generics {
                                    generics
                                } else {
                                    0
                                };
                                uses.iter().map(|i| prefix + i).collect()
                            }
                            None => Vec::new(),
                        }
                    }
                    _ => Vec::new(),
                };
                let (mut args, binds) = self.arguments_keeping(arguments, cx, &callbacks)?;
                let mut row = match &*function.kind {
                    TermKind::Var(g) => match cx.locals.get(g) {
                        Some(row) => Some((g.clone(), row.clone())),
                        None => self.effects.fns.get(g).map(|row| (g.clone(), row.clone())),
                    },
                    _ => None,
                };
                if let Some((g, callee)) = &mut row
                    && !cx.locals.contains_key(g)
                {
                    *callee = self.instantiate_row(g, callee, arguments, cx)?;
                }
                if let Some((g, callee)) = &mut row
                    && !cx.locals.contains_key(g)
                    && let Some((_, uses)) = self.effects.poly.get(g).cloned()
                {
                    // Written generics precede the ordinary parameters in
                    // the lowered telescope. Omitted generics are still
                    // inferred by the ordinary application elaborator.
                    let generics = self.effects.generics.get(g).copied().unwrap_or(0);
                    let arity = self.effects.arities.get(g).copied().unwrap_or(0);
                    let named = matches!(arguments.first().map(|t| &*t.kind),
                        Some(TermKind::Record { name, .. })
                            if name.spelling() == Some(tauto_surface::IMPLICITS));
                    // `f(<x: v>, a)`: the named generics are one argument.
                    let prefix = if named {
                        1
                    } else if arguments.len() >= arity + generics {
                        generics
                    } else {
                        0
                    };
                    let tail = self.row_argument(g, callee, &uses, &arguments[prefix..], cx);
                    // A callback's source lambda returns a value; the
                    // checked parameter returns a computation in its row.
                    for i in uses {
                        let at = prefix + i;
                        let Some(argument) = args.get(at).cloned() else {
                            continue;
                        };
                        if let TermKind::Lam {
                            params,
                            body,
                            types,
                            ..
                        } = &*argument.kind
                        {
                            let mut inner = cx.clone();
                            inner.row = self
                                .effects
                                .callback_rows
                                .get(g)
                                .and_then(|rows| rows.get(i))
                                .and_then(Option::as_ref)
                                .map(|row| {
                                    let mut row: Vec<_> = row
                                        .iter()
                                        .filter(|e| row_var(e).is_none())
                                        .cloned()
                                        .collect();
                                    row.extend(tail.clone());
                                    canonical(&row)
                                })
                                .unwrap_or_else(|| tail.clone());
                            inner.expect = None;
                            for (name, ty) in params.iter().zip(types) {
                                if let Some(ty) = ty {
                                    inner.types.insert(name.clone(), ty.clone());
                                }
                            }
                            let body = self.computation(body, &inner)?;
                            let lowered = T::new(
                                TermKind::Lam {
                                    params: params.clone(),
                                    body: Box::new(body),
                                    types: types.clone(),
                                    unused_params: Vec::new(),
                                },
                                argument.span,
                            );
                            self.retain_ctor_site_origin(&argument, &lowered);
                            args[at] = lowered;
                        }
                    }
                    callee.retain(|e| row_var(e).is_none());
                    args.splice(prefix..prefix, [op_ty(&tail, sp), res_fn(&tail, sp)]);
                    callee.extend(tail);
                }
                let applied = t.with_kind(
                    TermKind::App {
                        function: function.clone(),
                        arguments: args,
                    },
                    sp,
                );
                self.retain_ctor_site_origin(t, &applied);
                let c = match row {
                    Some((g, row)) => self.lift(applied, &row, cx, &g)?,
                    None => call(
                        &tauto_surface::bindings::library_name("Comp::ret"),
                        vec![cx.op(sp), cx.res(sp), applied],
                        sp,
                    ),
                };
                Ok(self.bind_all(binds, c, cx, sp))
            }
            TermKind::Match {
                scrutinee,
                result,
                binder: None,
                arms,
                ..
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
                            binder_unused: None,
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
                    Box::new(call(
                        &tauto_surface::bindings::library_name("Comp"),
                        vec![cx.op(sp), cx.res(sp), (**r).clone()],
                        sp,
                    ))
                });
                Ok(T::new(
                    TermKind::Match {
                        scrutinee: scrutinee.clone(),
                        result,
                        binder: None,
                        arms: out,
                        binder_unused: None,
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
            // A field of a value with effects (`p.x`, `p` a `var`): the value
            // first, then its field.
            TermKind::Field { base, name } => {
                let (values, binds) = self.arguments(std::slice::from_ref(&**base), cx)?;
                let field = T::new(
                    TermKind::Field {
                        base: Box::new(values.into_iter().next().expect("one value")),
                        name: name.clone(),
                    },
                    sp,
                );
                let c = call(
                    &tauto_surface::bindings::library_name("Comp::ret"),
                    vec![cx.op(sp), cx.res(sp), field],
                    sp,
                );
                Ok(self.bind_all(binds, c, cx, sp))
            }
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
                let c = call(
                    &tauto_surface::bindings::library_name("Comp::ret"),
                    vec![cx.op(sp), cx.res(sp), record],
                    sp,
                );
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
        g: &Name,
        callee: &[Name],
        uses: &[usize],
        arguments: &[T],
        cx: &Cx,
    ) -> Vec<Name> {
        // What the parameter's row spells out besides the variable is what
        // the callee handles of the argument: it is not left in `e`.
        let handled: Vec<Name> = uses
            .iter()
            .filter_map(|&i| self.effects.callback_rows.get(g)?.get(i)?.clone())
            .flatten()
            .filter(|e| row_var(e).is_none())
            .collect();
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
            .filter(|e| row_var(e).is_some() || !(callee.contains(e) || handled.contains(e)))
            .cloned()
            .collect()
    }

    /// `perform effect(args)` in `cx`.
    fn perform(&mut self, effect: &Name, args: &[T], cx: &Cx, sp: Span) -> Read<T> {
        let entry = self.instance_in(effect, &cx.row)?;
        if self.effects.sigs.get(&head(&entry)) != Some(&args.len()) {
            return Err(msg!("kernel-effect-arity", name = (effect).to_string()));
        }
        let (args, binds) = self.arguments(args, cx)?;
        let o = instance_call(args_name(&head(&entry)), &entry, args, sp);
        let c = call(
            "Comp::op",
            vec![cx.op(sp), cx.res(sp), inject(&cx.row, &entry, o, sp)],
            sp,
        );
        Ok(self.bind_all(binds, c, cx, sp))
    }

    /// The arguments with those that have effects replaced by names, and the
    /// computations those names are bound to, in the order written.
    fn arguments(&mut self, args: &[T], cx: &Cx) -> Read<(Vec<T>, Vec<(Name, T)>)> {
        self.arguments_keeping(args, cx, &[])
    }

    /// `arguments`, where the arguments at `keep` that are λs are left as
    /// they are: the call reads them as computations in the callee's row.
    fn arguments_keeping(
        &mut self,
        args: &[T],
        cx: &Cx,
        keep: &[usize],
    ) -> Result<(Vec<T>, Vec<(Name, T)>), Message> {
        let mut out = Vec::new();
        let mut binds = Vec::new();
        for (at, a) in args.iter().enumerate() {
            if keep.contains(&at) && matches!(&*a.kind, TermKind::Lam { .. }) {
                out.push(a.clone());
                continue;
            }
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
                let known = self.guess(a, cx);
                let c = self.computation(a, &cx.expecting(known.clone()))?;
                binds.push((x.clone(), typed(c, known.as_ref(), cx, a.span)));
                out.push(var(&x, a.span));
            } else {
                out.push(a.clone());
            }
        }
        Ok((out, binds))
    }

    fn bind_all(&mut self, binds: Vec<(Name, T)>, c: T, cx: &Cx, sp: Span) -> T {
        binds.into_iter().rev().fold(c, |rest, (x, value)| {
            call(
                "Comp::bind",
                vec![cx.op(sp), cx.res(sp), value, lam(&[x], rest)],
                sp,
            )
        })
    }

    /// `c`, a computation of `row`, in the row of `cx`.
    fn lift(&mut self, c: T, row: &[Name], cx: &Cx, g: &str) -> Read<T> {
        if row == cx.row.as_slice() {
            return Ok(c);
        }
        if let Some(e) = row.iter().find(|e| !cx.row.contains(e)) {
            return Err(msg!(
                "kernel-effect-call-not-in-row",
                function = g,
                name = (e).to_string()
            ));
        }
        let sp = c.span;
        let mut arms = Vec::new();
        for e in row {
            let (x, k) = (self.fresh_name("x"), self.fresh_name("k"));
            let body = call(
                &tauto_surface::bindings::library_name("Comp::forward"),
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
    fn arm_tree(&mut self, row: &[Name], arms: &[T], sp: Span) -> T {
        let o = self.fresh_name("o");
        let k = self.fresh_name("k");
        let body = match row.split_first() {
            None => call(
                &tauto_surface::bindings::library_name("arm_none"),
                vec![var(&o, sp), var(&k, sp)],
                sp,
            ),
            Some((e, _)) if row_var(e).is_some() => {
                app(arms[0].clone(), vec![var(&o, sp), var(&k, sp)])
            }
            Some((e, rest)) => {
                let there = self.arm_tree(rest, &arms[1..], sp);
                call(
                    "arm_sum",
                    vec![
                        op_of(e, sp),
                        op_ty(rest, sp),
                        res_of(e, sp),
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
                stack: _,
                name,
                value,
                borrow: false,
                borrow_mut: false,
                ty,
                unused,
            } => {
                // `^name` is lint metadata only: effect reading is the same as
                // `let name := …`.
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
                                stack: None,
                                name: name.clone(),
                                ty: ty.clone(),
                                value: value.clone(),
                                borrow: false,
                                borrow_mut: false,
                                unused: *unused,
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
                    vec![cx.op(sp), cx.res(sp), c, lam(&[Name::from("_")], after)],
                    sp,
                )
            }
            // A statement without effects gives a value nobody uses.
            Stmt::Expr(_) => self.block(rest, cx, sp)?,
            Stmt::Var {
                stack: _,
                name,
                ty,
                value,
                borrow: false,
                ..
            } => self.var(name, ty.as_ref(), value, rest, cx, sp)?,
            Stmt::Assign { place: Some(p), .. } => {
                return Err(msg!(
                    "kernel-effect-assign-field",
                    place = crate::surface::print::print_term(p)
                ));
            }
            // Only a `var` is written here, and a `var` is not a borrow.
            Stmt::Assign {
                name,
                deref: Some(_),
                ..
            } => {
                return Err(msg!(
                    "kernel-deref-needs-mut-borrow",
                    place = name.to_string()
                ));
            }
            Stmt::Assign { name, value, .. } => {
                let Some((_, put)) = cx.vars.get(name).cloned() else {
                    return Err(msg!(
                        "kernel-effect-assign-not-var",
                        name = (name).to_string()
                    ));
                };
                let after = self.block(rest, cx, sp)?;
                let c = self.perform(&put, std::slice::from_ref(value), cx, sp)?;
                let c = typed(
                    c,
                    Some(&var(&tauto_surface::bindings::library_name("Unit"), sp)),
                    cx,
                    sp,
                );
                call(
                    "Comp::bind",
                    vec![cx.op(sp), cx.res(sp), c, lam(&[Name::from("_")], after)],
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
        name: &Name,
        ty: Option<&T>,
        value: &T,
        rest: &[Stmt],
        cx: &Cx,
        sp: Span,
    ) -> Read<T> {
        let Some(state) = ty.cloned().or_else(|| self.guess(value, cx)) else {
            return Err(msg!("kernel-effect-var-type", name = (name).to_string()));
        };
        let Some(a) = cx.expect.clone() else {
            return Err(msg!("kernel-effect-block-type", name = (name).to_string()));
        };
        self.fresh += 1;
        let (get, put) = (
            Name::Global(tauto_surface::identity::DeclRef::fresh(format!(
                "{name}@get{}",
                self.fresh
            ))),
            Name::Global(tauto_surface::identity::DeclRef::fresh(format!(
                "{name}@put{}",
                self.fresh
            ))),
        );
        // The type generics `S` names become the two effects' own, and the
        // row holds their instances at `S` (`s@get(S)`), as for any effect
        // with type generics.
        let generics = state_generics(&state, cx);
        self.effects.locals.insert(name.clone(), get.clone());
        let mut made = self.make_effect(&get, &generics, Vec::new(), state.clone(), sp);
        made.extend(self.make_effect(
            &put,
            &generics,
            vec![state.clone()],
            var(&tauto_surface::bindings::library_name("Unit"), sp),
            sp,
        ));
        self.effects.pending.extend(made);
        let (get, put) = (instance(&get, &generics, sp), instance(&put, &generics, sp));
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
            let v = |n: &Name| var(n, sp);
            let arm = if *e == get {
                let f = lam(
                    &[k1.clone(), s1.clone()],
                    app(app(v(&k1), vec![v(&s1)]), vec![v(&s1)]),
                );
                instance_call(arm_name(&head(e)), e, vec![f, v(&x), v(&k)], sp)
            } else if *e == put {
                let f = lam(
                    &[v1.clone(), k1.clone(), s1.clone()],
                    app(
                        app(
                            v(&k1),
                            vec![v(&tauto_surface::bindings::library_name("Star"))],
                        ),
                        vec![v(&v1)],
                    ),
                );
                instance_call(arm_name(&head(e)), e, vec![f, v(&x), v(&k)], sp)
            } else {
                let back = lam(
                    std::slice::from_ref(&r1),
                    app(app(v(&k), vec![v(&r1)]), vec![v(&s1)]),
                );
                lam(
                    std::slice::from_ref(&s1),
                    call(
                        &tauto_surface::bindings::library_name("Comp::forward"),
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
            call(
                &tauto_surface::bindings::library_name("Comp::ret"),
                vec![cx.op(sp), cx.res(sp), var(&a1, sp)],
                sp,
            ),
        );
        let arm = self.arm_tree(&inner.row, &arms, sp);
        let passing = pi(
            None,
            state.clone(),
            call(
                &tauto_surface::bindings::library_name("Comp"),
                vec![cx.op(sp), cx.res(sp), a],
                sp,
            ),
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
    fn guess(&mut self, t: &T, cx: &Cx) -> Option<T> {
        match &*t.kind {
            TermKind::Var(x) if cx.locals.contains_key(x) => cx.types.get(x).and_then(comp_value),
            // A `var` is what its `get` answers.
            TermKind::Var(x) if cx.vars.contains_key(x) => {
                self.effects.results.get(&cx.vars[x].0).cloned()
            }
            TermKind::Var(x) => cx.types.get(x).cloned(),
            TermKind::Nat(_) => Some(var(&tauto_surface::bindings::library_name("Nat"), t.span)),
            TermKind::Handle { body, handlers } => {
                let body_ty = self.guess(body, cx);
                match handlers.iter().find_map(|h| match h {
                    Handler::Return { pattern, body } => Some((pattern, body)),
                    _ => None,
                }) {
                    None => body_ty,
                    Some((pattern, r)) => {
                        let mut inner = cx.clone();
                        if let (Pattern::Bind { name: v, .. }, Some(ty)) = (pattern, body_ty) {
                            inner.types.insert(v.clone(), ty);
                        }
                        self.guess(r, &inner)
                    }
                }
            }
            TermKind::Perform { effect, .. } => {
                let entry = self.instance_in(effect, &cx.row).ok()?;
                self.result_of(&entry)
            }
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(g) if !cx.types.contains_key(g) && !cx.locals.contains_key(g) => {
                    let mut ty = self.effects.results.get(g)?.clone();
                    if let Some(&arity) = self.effects.arities.get(g) {
                        if arguments.len() < arity {
                            return None;
                        }
                        for argument in &arguments[arity..] {
                            let TermKind::Pi {
                                params,
                                result,
                                effects,
                                ..
                            } = &*ty.kind
                            else {
                                return None;
                            };
                            let (name, _) = params.first()?;
                            let rest = if params.len() == 1 {
                                (**result).clone()
                            } else {
                                T::new(
                                    TermKind::Pi {
                                        params: params[1..].to_vec(),
                                        result: result.clone(),
                                        effects: effects.clone(),
                                        unused: Vec::new(),
                                    },
                                    ty.span,
                                )
                            };
                            ty = match name {
                                Some(name) => self.subst(&rest, name, argument),
                                None => rest,
                            };
                        }
                    }
                    Some(ty)
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

    fn handle(&mut self, body: &T, handlers: &[Handler], cx: &Cx, sp: Span) -> Read<T> {
        let mut ops: HashMap<Name, (Vec<Name>, Name, T)> = HashMap::new();
        let mut ret: Option<(Name, T)> = None;
        for h in handlers {
            match h {
                Handler::Return { pattern, body } => {
                    let v = match pattern {
                        Pattern::Bind { name: v, .. } => v.clone(),
                        Pattern::Wild => self.fresh_name("v"),
                        _ => return Err(msg!("kernel-effect-return-pattern")),
                    };
                    ret = Some((v, body.clone()));
                }
                Handler::Operation {
                    effect,
                    instance,
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
                        return Err(msg!("kernel-effect-not-read", name = (effect).to_string()));
                    }
                    let effect = &self.handled_instance(effect, instance)?;
                    let mut names = Vec::new();
                    for p in patterns {
                        names.push(match p {
                            Pattern::Bind { name: v, .. } => v.clone(),
                            Pattern::Wild => self.fresh_name("p"),
                            _ => return Err(msg!("kernel-effect-handler-pattern")),
                        });
                    }
                    let k = cont.clone().unwrap_or_else(|| self.fresh_name("k"));
                    if ops
                        .insert(effect.clone(), (names, k, body.clone()))
                        .is_some()
                    {
                        return Err(msg!("kernel-effect-two-arms", name = (effect).to_string()));
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
        // A handler that leaves no effect and writes no outer `var` is read
        // as the value its fold gives, not as a tree to take the value of:
        // the arms and the return clause are ordinary functions, and
        // `Comp::value` of a tree whose arm goes through a `match` that does
        // not reduce yet would not reduce either.
        let by_value = cx.row.is_empty() && cx.vars.is_empty();
        let mut arms = Vec::new();
        for e in &inner.row {
            let x = self.fresh_name("x");
            let k = self.fresh_name("k");
            let arm = match ops.get(e) {
                Some((names, kname, body)) => {
                    let mut armcx = cx.clone();
                    let b = if by_value {
                        self.pure_value(body, &armcx)?
                    } else {
                        armcx.locals.insert(kname.clone(), cx.row.clone());
                        self.computation(body, &armcx)?
                    };
                    let mut ps = names.clone();
                    ps.push(kname.clone());
                    instance_call(
                        arm_name(&head(e)),
                        e,
                        vec![lam(&ps, b), var(&x, sp), var(&k, sp)],
                        sp,
                    )
                }
                None => call(
                    &tauto_surface::bindings::library_name("Comp::forward"),
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
            Some((v, r)) if by_value => lam(&[v], self.pure_value(&r, cx)?),
            Some((v, r)) => lam(&[v], self.computation(&r, cx)?),
            None if by_value => {
                let v = self.fresh_name("v");
                lam(std::slice::from_ref(&v), var(&v, sp))
            }
            None => {
                let v = self.fresh_name("v");
                lam(
                    std::slice::from_ref(&v),
                    call(
                        &tauto_surface::bindings::library_name("Comp::ret"),
                        vec![cx.op(sp), cx.res(sp), var(&v, sp)],
                        sp,
                    ),
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
        if by_value {
            let value = call(
                "Comp::handle_val",
                vec![inner.op(sp), inner.res(sp), c, ret, arm],
                sp,
            );
            let value = match &cx.expect {
                Some(ty) => call("the", vec![ty.clone(), value], sp),
                None => value,
            };
            return Ok(call(
                &tauto_surface::bindings::library_name("Comp::ret"),
                vec![cx.op(sp), cx.res(sp), value],
                sp,
            ));
        }
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

    /// `t`, in a context with no effects, as a value.
    fn pure_value(&mut self, t: &T, cx: &Cx) -> Read<T> {
        if !self.effectful(t, cx) {
            return Ok(t.clone());
        }
        let c = self.computation(t, cx)?;
        Ok(call(
            &tauto_surface::bindings::library_name("Comp::value"),
            vec![typed(c, cx.expect.as_ref(), cx, t.span)],
            t.span,
        ))
    }

    /// The row's entry an arm `effect<A…>(…)` answers: the effect itself, or
    /// for an effect with type generics its instance at the arm's types.
    fn handled_instance(&self, effect: &Name, instance: &Instance) -> Read<Name> {
        let Some(generics) = self.effects.type_params.get(effect) else {
            return Ok(effect.clone());
        };
        if !instance.forall.is_empty() {
            return Err(msg!(
                "kernel-effect-handler-forall",
                name = (effect).to_string()
            ));
        }
        let Name::Global(reference) = effect else {
            return Err(msg!("kernel-effect-not-read", name = (effect).to_string()));
        };
        if instance.args.len() != generics.len() {
            return Err(msg!(
                "kernel-effect-handler-instance",
                name = (effect).to_string()
            ));
        }
        let display = format!(
            "{effect}({})",
            instance
                .args
                .iter()
                .map(super::describe)
                .collect::<Vec<_>>()
                .join(", ")
        );
        Ok(Name::Effect(std::sync::Arc::new(
            tauto_surface::identity::EffectUse::new(
                reference.clone(),
                instance.args.clone(),
                Vec::new(),
                false,
                display,
            ),
        )))
    }

    fn effects_known(&self) -> bool {
        !self.effects.sigs.is_empty() || !self.effects.fns.is_empty()
    }

    fn has_effect_call(&self, t: &T) -> bool {
        let mut found = false;
        let mut t = t.clone();
        walk::term(&mut t, &mut |s| {
            if let TermKind::App { function, .. } = &*s.kind
                && let TermKind::Var(name) = &*function.kind
                && self.effects.fns.contains_key(name)
            {
                found = true;
            }
        });
        found
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

    /// A function without effects whose body handles them or calls a row
    /// instantiated as empty: read as a computation and take its value.
    fn pure_fn(&mut self, f: &FnDecl) -> Read<FnDecl> {
        // A borrow's type is the value's type to the proofs (see `unborrow`).
        let mut unborrowed = f.clone();
        unborrowed.body = unborrow(&f.body);
        let f = &unborrowed;
        let sp = f.span;
        let Some(result) = &f.result else {
            return Err(msg!("kernel-no-result-type"));
        };
        if !self.effects_known() {
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
                .chain(f.generic_parameters())
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
        g.body = call(
            &tauto_surface::bindings::library_name("Comp::value"),
            vec![typed(body, Some(result), &cx, sp)],
            sp,
        );
        Ok(g)
    }

    /// The parameters' types, a function with effects `(A…) -> R ! {e…}`
    /// written as `(A…) -> Comp(…, R)`, and the row of each such parameter,
    /// so that calling it is read as calling a function with effects.
    fn effect_params(&self, f: &FnDecl) -> Read<(Vec<T>, HashMap<Name, Vec<Name>>)> {
        let mut types = Vec::new();
        let mut locals = HashMap::new();
        for (p, t) in f.params.iter().zip(f.param_types.iter().flatten()) {
            let TermKind::Pi {
                params,
                result,
                effects: Some(row),
                ..
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
                return Err(msg!(
                    "kernel-effect-param-row-variable",
                    name = (p).to_string()
                ));
            }
            if let Some(why) = self.unread_row(row, &f.generics) {
                return Err(msg!(
                    "kernel-effect-param-row-unread",
                    name = (p).to_string(),
                    why = why
                ));
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
                    unused: Vec::new(),
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
            return Ok(call(
                &tauto_surface::bindings::library_name("Comp::value"),
                vec![c],
                t.span,
            ));
        }
        Err(msg!("kernel-effect-none-read"))
    }
}

/// The variable of `f`'s row, if it has one, and the parameters that are
/// functions whose rows have it.
/// How many leading parameters are the dictionaries of a `where`: no call
/// writes them.
fn dictionaries_of(f: &FnDecl) -> usize {
    f.params
        .iter()
        .take_while(|n| n.as_str().starts_with(tauto_surface::surface::DICT))
        .count()
}

fn row_poly(f: &FnDecl) -> Read<Option<(Name, Vec<usize>)>> {
    let own = row_vars(f.effects.as_deref().unwrap_or_default());
    let skip = dictionaries_of(f);
    let mut uses = Vec::new();
    for (i, t) in f.param_types.iter().enumerate().skip(skip) {
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
                    name = (&f.params[i]).to_string(),
                    variable = (&v).to_string()
                ));
            }
            uses.push(i - skip);
        }
    }
    Ok(own.into_iter().next().map(|v| (v, uses)))
}

/// Whether a numeral is written in `t`.
fn has_numeral(t: &T) -> bool {
    let mut found = false;
    let mut t = t.clone();
    walk::term(&mut t, &mut |s| {
        if matches!(&*s.kind, TermKind::Nat(_)) {
            found = true;
        }
    });
    found
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

/// A borrow's type is the value's type to the proofs: the ownership checker
/// guarantees nothing else names what is lent while it is lent.
fn unborrow(t: &T) -> T {
    let mut t = t.clone();
    walk::term(&mut t, &mut |s| {
        if let TermKind::Borrow { term, .. } = &*s.kind {
            *s = (**term).clone();
        }
    });
    t
}

impl Kernel {
    /// `f`, a function with effects, with its `&mut` read as values passed
    /// along (`docs/design/effect-proofs.md`, 「借用と affine」), before it
    /// is read as a computation tree:
    ///
    /// * `fn f(c: &mut C, x: A): R ! {e}` is `fn f(c: C, x: A): Mut1(R, C) ! {e}`
    ///   whose body is `{ var c: C := c; let r: R := body; mut1(r, c) }`, so
    ///   that `c` is passed along as a `var` is, in the order the effects run;
    /// * a call `g(&mut y, &mut z.f, e)`, `y` and `z` a `var` or a `&mut`
    ///   parameter, is `{ let m := g(y, z.f, e); match m { mut2(v, s, t) =>
    ///   { y := s; z := Z { f: t, … }; v } } }`;
    /// * `z.f := v` is `z := Z { f: v, … }`;
    /// * `&x` is `x`.
    ///
    /// The ownership checker (`docs/design/ownership.md`) guarantees that
    /// what is lent `&mut` has no other name while the call runs, so the
    /// value passed back is the only change to it.
    fn lend(&mut self, f: &FnDecl, stmts: &[Stmt]) -> Read<FnDecl> {
        let lends = |t: &T| {
            let mut found = false;
            walk::term(&mut t.clone(), &mut |s| {
                found |= matches!(&*s.kind, TermKind::Borrow { .. });
                if let TermKind::Block(b) = &*s.kind {
                    found |= b
                        .iter()
                        .any(|s| matches!(s, Stmt::Assign { place: Some(_), .. }));
                }
            });
            found
        };
        if f.borrows.iter().all(Option::is_none) && !lends(&f.body) {
            return Ok(f.clone());
        }
        let sp = f.span;
        let mut records = self.records();
        for s in stmts {
            if let Stmt::Inductive(d) = s
                && let [c] = d.constructors.as_slice()
            {
                let names = c.params.iter().map(|(n, _)| n.clone()).collect();
                records.insert(d.name.clone(), (c.name.clone(), names));
            }
        }
        let mut states: HashMap<Name, Option<T>> = HashMap::new();
        let mut outs = Vec::new();
        let mut param_types = Vec::new();
        for ((p, b), t) in f.params.iter().zip(&f.borrows).zip(&f.param_types) {
            let t = t.as_ref().map(unborrow);
            if *b == Some(true) {
                let Some(ty) = &t else {
                    return Err(msg!("kernel-effect-untyped-param"));
                };
                outs.push((p.clone(), ty.clone()));
                states.insert(p.clone(), t.clone());
            }
            param_types.push(t);
        }
        let mut body = f.body.clone();
        walk::term(&mut body, &mut |t| {
            if let TermKind::Block(b) = &*t.kind {
                for s in b {
                    if let Stmt::Var { name, ty, .. } = s {
                        states.insert(name.clone(), ty.as_ref().map(unborrow));
                    }
                }
            }
        });
        // A `&mut` parameter becomes a `var` below: a write through it,
        // `*c := v`, is that `var`'s `c := v`. Written without `*`, it would
        // rebind the borrow.
        let params: HashSet<Name> = outs.iter().map(|(p, _)| p.clone()).collect();
        let mut rebinds: Option<Message> = None;
        walk::term(&mut body, &mut |t| {
            if let TermKind::Block(b) = &*t.kind
                && b.iter()
                    .any(|s| matches!(s, Stmt::Assign { name, .. } if params.contains(name)))
            {
                let sp = t.span;
                let mut b = b.clone();
                for s in &mut b {
                    if let Stmt::Assign {
                        name,
                        place: None,
                        deref,
                        ..
                    } = s
                        && params.contains(name)
                    {
                        if deref.take().is_none() {
                            rebinds.get_or_insert(msg!(
                                "kernel-assign-through-borrow",
                                place = name.to_string()
                            ));
                        }
                    }
                }
                *t = t.with_kind(TermKind::Block(b), sp);
            }
        });
        if let Some(why) = rebinds {
            return Err(why);
        }
        let record = |x: &Name, field: &str, value: T, sp: Span| -> Read<T> {
            let head = match states.get(x).cloned().flatten().map(|t| t.kind.clone()) {
                Some(k) => match &*k {
                    TermKind::Var(n) => Some(n.clone()),
                    TermKind::App { function, .. } => match &*function.kind {
                        TermKind::Var(n) => Some(n.clone()),
                        _ => None,
                    },
                    _ => None,
                },
                None => None,
            };
            let Some((ctor, names)) = head.and_then(|h| records.get(&h).cloned()) else {
                return Err(msg!("kernel-mut-field-family", name = x.to_string()));
            };
            let mut value = Some(value);
            let made = names
                .iter()
                .map(|n| match n.as_str() == field {
                    true => value.take().expect("one field of that name"),
                    false => T::new(
                        TermKind::Field {
                            base: Box::new(var(x.clone(), sp)),
                            name: n.to_string(),
                        },
                        sp,
                    ),
                })
                .collect();
            if value.is_some() {
                return Err(msg!("kernel-mut-field-family", name = x.to_string()));
            }
            Ok(call(ctor, made, sp))
        };
        if let Some(why) = super::mutable::lent_then_written(&body, true) {
            return Err(why.message);
        }
        let results = self.effects.results.clone();
        let mut failed: Option<Message> = None;
        let mut used = HashSet::new();
        let mut fresh = 0usize;
        walk::term(&mut body, &mut |t| {
            if failed.is_some() {
                return;
            }
            let sp = t.span;
            match &*t.kind {
                TermKind::Block(b)
                    if b.iter()
                        .any(|s| matches!(s, Stmt::Assign { place: Some(_), .. })) =>
                {
                    let mut b = b.clone();
                    for s in &mut b {
                        let Stmt::Assign {
                            name,
                            place: Some(p),
                            value,
                            ..
                        } = s
                        else {
                            continue;
                        };
                        let field = match &*p.kind {
                            TermKind::Field { base, name: field } if matches!(&*base.kind, TermKind::Var(x) if x == name) => {
                                field.clone()
                            }
                            _ => {
                                failed = Some(msg!(
                                    "kernel-effect-assign-field",
                                    place = crate::surface::print::print_term(p)
                                ));
                                return;
                            }
                        };
                        match record(name, &field, value.clone(), sp) {
                            Ok(v) => {
                                *s = Stmt::Assign {
                                    name: name.clone(),
                                    place: None,
                                    value: v,
                                    deref: None,
                                }
                            }
                            Err(why) => {
                                failed = Some(why);
                                return;
                            }
                        }
                    }
                    *t = t.with_kind(TermKind::Block(b), sp);
                }
                TermKind::App {
                    function,
                    arguments,
                } if arguments
                    .iter()
                    .any(|a| matches!(&*a.kind, TermKind::Borrow { mutable: true, .. })) =>
                {
                    let mut plain = Vec::new();
                    let mut places: Vec<(Name, Option<String>)> = Vec::new();
                    for a in arguments {
                        match &*a.kind {
                            TermKind::Borrow {
                                mutable: true,
                                term,..
                            } => {
                                let place = match &*term.kind {
                                    TermKind::Var(x) if states.contains_key(x) => (x.clone(), None),
                                    TermKind::Field { base, name } => match &*base.kind {
                                        TermKind::Var(x) if states.contains_key(x) => {
                                            (x.clone(), Some(name.clone()))
                                        }
                                        _ => {
                                            failed = Some(msg!("kernel-mut-lends"));
                                            return;
                                        }
                                    },
                                    _ => {
                                        failed = Some(msg!("kernel-mut-lends"));
                                        return;
                                    }
                                };
                                places.push(place);
                                plain.push((**term).clone());
                            }
                            _ => plain.push(a.clone()),
                        }
                    }
                    fresh += 1;
                    let m = Name::from(format!("lent'{fresh}"));
                    let v = Name::from(format!("lent'{fresh}'v"));
                    let mut args = vec![Pattern::Bind { name: v.clone(), unused: None }];
                    let mut writes = Vec::new();
                    for (i, (x, field)) in places.iter().enumerate() {
                        let s = Name::from(format!("lent'{fresh}'{i}"));
                        args.push(Pattern::Bind { name: s.clone(), unused: None });
                        let value = match field {
                            None => var(s, sp),
                            Some(fd) => match record(x, fd, var(s, sp), sp) {
                                Ok(v) => v,
                                Err(why) => {
                                    failed = Some(why);
                                    return;
                                }
                            },
                        };
                        writes.push(Stmt::Assign {
                            name: x.clone(),
                            place: None,
                            value,
                            deref: None,
                        });
                    }
                    used.insert(places.len());
                    writes.push(Stmt::Expr(var(v, sp)));
                    // The value's type, when the callee is a function with
                    // effects read before: the first of its `MutK`.
                    let value_ty = match &*function.kind {
                        TermKind::Var(g) => results.get(g).and_then(|r| match &*r.kind {
                            TermKind::App { arguments, .. } => arguments.first().cloned(),
                            _ => None,
                        }),
                        _ => None,
                    };
                    let callee = t.with_kind(
                        TermKind::App {
                            function: function.clone(),
                            arguments: plain,
                        },
                        sp,
                    );
                    let taken = T::new(
                        TermKind::Match {
                            binder: None,
                            scrutinee: Box::new(var(m.clone(), sp)),
                            result: value_ty.map(Box::new),
                            arms: vec![MatchArm {
                                goal: None,
                                pattern: Pattern::Ctor {
                                    name: super::mutable::family(places.len()).1,
                                    args,
                                },
                                guard: None,
                                body: T::new(TermKind::Block(writes), sp),
                            }],
                            binder_unused: None,
                        },
                        sp,
                    );
                    let call_ty = match &*function.kind {
                        TermKind::Var(g) => results.get(g).cloned(),
                        _ => None,
                    };

                    *t = T::new(
                        TermKind::Block(vec![
                            Stmt::Let {
                                stack: None,
                                name: m,
                                ty: call_ty,
                                value: callee,
                                borrow: false,
                                borrow_mut: false,
                                unused: None,
                            },
                            Stmt::Expr(taken),
                        ]),
                        sp,
                    );
                }
                TermKind::Borrow {
                    mutable: false,
                    term,..
                } => *t = (**term).clone(),
                TermKind::Borrow { mutable: true, .. } => {
                    failed = Some(msg!("kernel-mut-argument"));
                }
                _ => {}
            }
        });
        if let Some(why) = failed {
            return Err(why);
        }
        let mut result = f.result.clone();
        if !outs.is_empty() {
            let r = result
                .clone()
                .ok_or_else(|| msg!("kernel-effect-no-result"))?;
            let k = outs.len();
            used.insert(k);
            let value = Name::from("lent'result");
            let mut stmts: Vec<Stmt> = outs
                .iter()
                .map(|(p, ty)| Stmt::Var {
                    stack: None,
                    name: p.clone(),
                    ty: Some(ty.clone()),
                    value: var(p.clone(), sp),
                    borrow: false,
                    unused: None,
                })
                .collect();
            stmts.push(Stmt::Let {
                stack: None,
                name: value.clone(),
                ty: Some(r.clone()),
                value: body,
                borrow: false,
                borrow_mut: false,
                unused: None,
            });
            let mut parts = vec![var(value, sp)];
            parts.extend(outs.iter().map(|(p, _)| var(p.clone(), sp)));
            stmts.push(Stmt::Expr(call(super::mutable::family(k).1, parts, sp)));
            body = T::new(TermKind::Block(stmts), sp);
            let mut tys = vec![r];
            tys.extend(outs.iter().map(|(_, t)| t.clone()));
            result = Some(call(super::mutable::family(k).0, tys, sp));
        }
        for k in used {
            self.declare_mut(k, sp)
                .map_err(|d| msg!("kernel-effect-lend", why = d.to_string()))?;
        }
        Ok(FnDecl {
            borrows: vec![None; f.params.len()],
            param_types,
            result,
            body,
            ..f.clone()
        })
    }
}

fn stmt_body(s: &Stmt) -> T {
    match s {
        Stmt::Fn(f) => f.body.clone(),
        _ => unreachable!("a function"),
    }
}

/// Writes on each `x => …` that `Comp::bind` continues with the type of
/// the value bound, where the bound computation says it
/// (`the(Comp(Op, Res, T), c)`): what `&mut` passes back is taken apart
/// by a `match` and its fields read, which needs the type at the binder.
fn annotate_binds(t: &mut T) {
    walk::term(t, &mut |s| {
        let TermKind::App {
            function,
            arguments,
        } = &*s.kind
        else {
            return;
        };
        if !matches!(&*function.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(n, "Comp::bind"))
            || arguments.len() != 4
        {
            return;
        }
        let known = match &*arguments[2].kind {
            TermKind::App {
                function,
                arguments: the,
            } if matches!(&*function.kind, TermKind::Var(n) if tauto_surface::bindings::is_library(n, "the"))
                && the.len() == 2 =>
            {
                match &*the[0].kind {
                    TermKind::App {
                        arguments: comp, ..
                    } if comp.len() == 3 => Some(comp[2].clone()),
                    _ => None,
                }
            }
            _ => None,
        };
        let Some(known) = known else { return };
        let TermKind::Lam {
            params,
            body,
            types,
            ..
        } = &*arguments[3].kind
        else {
            return;
        };
        if params.len() != 1 || !types.is_empty() {
            return;
        }
        let mut arguments = arguments.clone();
        arguments[3] = arguments[3].with_kind(
            TermKind::Lam {
                params: params.clone(),
                body: body.clone(),
                types: vec![Some(known)],
                unused_params: Vec::new(),
            },
            arguments[3].span,
        );
        *s = s.with_kind(
            TermKind::App {
                function: function.clone(),
                arguments,
            },
            s.span,
        );
    });
}
