//! Dependent `match` and structural recursion, compiled to eliminators.
//!
//! `match x: T { c(a⃗) => e … }` on a parameter `x` of an inductive family
//! becomes `I::rec p⃗ (λ i⃗ t. T[t/x]) (λ a⃗ ih⃗. e) … i⃗ x` (`I::ind` when the
//! result is a proposition). A call `f(…, a, …)` of the function being
//! defined, on a recursive field `a` of the constructor, becomes that field's
//! induction hypothesis. The motive generalizes the later parameters, and the
//! earlier ones a call changes, so those arguments may change; an earlier
//! parameter the matched value's type mentions stays unchanged (unless it is
//! an index of the matched family). A call on a part deeper than a field
//! (a field of a field, matched in the arm) is compiled with a motive that
//! pairs each value with the values at its parts (`DeepScope`). Any other
//! recursion is not accepted: there is no termination
//! analysis beyond this, so a definition the eliminator cannot express is
//! rejected rather than trusted.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::inductive::{Ctor, Ind, pi_all};
use super::{
    CtorSite, Ctx, Diagnostic, Kernel, Sort, T, describe, err, expand_numeral, lam, occurs, pi,
};
use crate::surface::{Pattern, SurfaceTerm, TermKind};
use tauto_message::{Message, msg};
use tauto_parol::Span;

fn app(f: T, args: Vec<T>) -> T {
    if args.is_empty() {
        return f;
    }
    let span = f.span;
    T::new(
        TermKind::App {
            function: Box::new(f),
            arguments: args,
        },
        span,
    )
}

/// The recursive fields of the matched value: each one's value (its
/// induction hypothesis), its family's place in the group, and how many
/// arguments a function-typed one takes.
type Smaller = HashMap<String, (T, usize, usize)>;

/// A recursion on parts of the matched value deeper than its fields. The
/// function is compiled with the motive `x ↦ M(x) ∧ below(x)`, where
/// `below(x)` holds the values at every part of `x`: for each recursive
/// field `r` of its constructor, `M(r) ∧ below(r)`, ending in `True` (`Unit`
/// and `BelowPair` for data). Each recursive field of the arm has a variable
/// of type `below(r)`; a `match` on the field generalizes it, so in its arms
/// that variable's type unfolds to the parts one level further down.
#[derive(Clone)]
pub(super) struct DeepScope {
    fns: HashMap<String, FnInfo>,
    prop: bool,
    /// A variable whose `below` is reached from a variable in scope by
    /// projections (`true` the first component): `(var, below var, path)`.
    vars: Vec<(String, String, Vec<bool>)>,
    /// A recursive field of the arm the scope was opened in, with a variable
    /// of type `M(r)` holding the function's value at it: a `match` on the
    /// field generalizes it, so in its arms its type has the constructor, as
    /// a call on the constructor rebuilt from the arm's fields does.
    at: Vec<(String, String)>,
    /// The names the arm the scope was opened in binds again
    /// (`Header::rebound`).
    rebound: Vec<String>,
}

/// `(A₁, (A₂, … Aₖ))` of pairs.
fn tuple_ty(prop: bool, ts: &[T]) -> T {
    match ts {
        [t] => t.clone(),
        [t, rest @ ..] => pair_ty(prop, t, &tuple_ty(prop, rest)),
        [] => unreachable!("a tuple of at least one"),
    }
}

fn tuple(prop: bool, ts: &[T], mut vs: Vec<T>) -> T {
    if ts.len() == 1 {
        return vs.pop().unwrap();
    }
    let first = vs.remove(0);
    let rest = tuple_ty(prop, &ts[1..]);
    let tail = tuple(prop, &ts[1..], vs);
    pair(prop, &ts[0], &rest, first, tail)
}

fn component(prop: bool, ts: &[T], p: T, j: usize) -> T {
    if ts.len() == 1 {
        return p;
    }
    let rest = tuple_ty(prop, &ts[1..]);
    if j == 0 {
        proj(prop, &ts[0], &rest, p, true)
    } else {
        component(prop, &ts[1..], proj(prop, &ts[0], &rest, p, false), j - 1)
    }
}

/// `A ∧ B` or `BelowPair(A, B)`.
fn pair_ty(prop: bool, a: &T, b: &T) -> T {
    let f = if prop { "And" } else { "BelowPair" };
    app(T::var(f, a.span), vec![a.clone(), b.clone()])
}

fn pair(prop: bool, a: &T, b: &T, x: T, y: T) -> T {
    let f = if prop { "AndIntro" } else { "Mk" };
    app(T::var(f, a.span), vec![a.clone(), b.clone(), x, y])
}

fn proj(prop: bool, a: &T, b: &T, p: T, first: bool) -> T {
    let sp = a.span;
    let elim = if prop { "And::ind" } else { "BelowPair::rec" };
    let x = "x'p".to_string();
    let y = "y'p".to_string();
    let (ty, out) = if first { (a, &x) } else { (b, &y) };
    app(
        T::var(elim, sp),
        vec![
            a.clone(),
            b.clone(),
            lam("t'p", ty.clone()),
            lam(&x, lam(&y, T::var(out, sp))),
            p,
        ],
    )
}

fn unit(prop: bool, sp: tauto_parol::Span) -> (T, T) {
    if prop {
        (T::var("True", sp), T::var("Trivial", sp))
    } else {
        (T::var("Unit", sp), T::var("Star", sp))
    }
}

pub(super) struct FnSpec<'a> {
    pub name: Option<&'a str>,
    /// How many leading parameters are generics, which a call may leave out.
    pub implicit: usize,
    pub params: Vec<(String, T)>,
    pub result: T,
    pub body: &'a SurfaceTerm,
}

/// What a recursive call needs to know about the function it calls.
#[derive(Clone)]
pub(super) struct FnInfo {
    params: Vec<String>,
    /// `C::m` for the method `C::m@H` of an instance being defined
    /// (`check/classes.rs`): a call of it whose matched argument is a field of
    /// the value matched is the recursion; any other is a call of another
    /// instance's.
    alias: bool,
    implicit: usize,
    xpos: usize,
    idx_params: Vec<String>,
    /// The earlier parameters the motive generalizes: a call may change them.
    pre: Vec<String>,
    /// The later parameters the motive generalizes; a call that changes
    /// another asks for it in `wants`.
    post: Vec<String>,
    /// The earlier parameters it could generalize (the matched value's type
    /// does not mention them); a call that changes one of them asks for it
    /// in `wants`, and the group is compiled again.
    movable: Vec<String>,
    wants: Rc<RefCell<Vec<String>>>,
    /// The family of the matched parameter, as its place in the group.
    fam: usize,
    /// The indices that are not variables, as `(type, index)`: an induction
    /// hypothesis takes one equation for each, `Refl` at a recursive call.
    general: Vec<(T, T)>,
    /// The arguments the match is applied to, when the body is
    /// `(match x: (H) -> G { … })(h)`: a recursive call is the induction
    /// hypothesis applied to them, at the call's arguments.
    tail: bool,
    spec: usize,
}

/// The head of a call that `fill_tails` applies to the arguments its
/// function's match is applied to: `tail'f(value, arguments of the call)`.
const TAIL: &str = "tail'";

/// An index of the matched family that is not a plain variable (`Succ(n)`,
/// `0`, …): the motive quantifies over it with an equation, and each
/// constructor's arm unifies the two sides.
struct GenIdx {
    k: usize,
    ty: T,
    arg: T,
}

/// A field fixed by unification: `f = t`, with `t` free of fields.
struct Sol {
    f: String,
    t: T,
    ty: T,
    proof: T,
}

enum Plan {
    /// The constructor cannot have this index: a proof of the goal.
    Impossible(T),
    Solved(Vec<Sol>),
}

struct Eqn {
    l: T,
    r: T,
    ty: T,
    proof: T,
}

fn eq_ty(ty: &T, a: &T, b: &T) -> T {
    app(T::var("Eq", a.span), vec![ty.clone(), a.clone(), b.clone()])
}

/// From `p: a = b` a proof of `b = a` that computes when `p` is `Refl`.
fn sym_proof(ty: &T, a: &T, b: &T, p: T) -> T {
    let sp = a.span;
    let motive = lam("y'", lam("e'", eq_ty(ty, &T::var("y'", sp), a)));
    app(
        T::var("Eq::ind", sp),
        vec![
            ty.clone(),
            a.clone(),
            motive,
            app(T::var("Refl", sp), vec![ty.clone(), a.clone()]),
            b.clone(),
            p,
        ],
    )
}

fn lams(names: &[String], body: T) -> T {
    names.iter().rev().fold(body, |acc, n| lam(n, acc))
}

struct Header<'a> {
    x: String,
    xpos: usize,
    family: String,
    pargs: Vec<T>,
    idx_args: Vec<T>,
    motive: T,
    /// The parameters the motive generalizes: the earlier ones a call
    /// changes (`pre`), then the later ones.
    after: Vec<(String, T)>,
    pre: Vec<String>,
    movable: Vec<String>,
    is_prop: bool,
    arms: &'a [crate::surface::MatchArm],
    span: tauto_parol::Span,
    general: Vec<GenIdx>,
}

impl Header<'_> {
    /// The names an arm binds again: the matched variable (the constructor
    /// there), the parameters the motive generalizes, and the arm's own
    /// variables. Such a name at a call is not the parameter of that name.
    fn rebound(&self, local: &[(String, T)], params: usize) -> Vec<String> {
        let mut out = vec![self.x.clone()];
        out.extend(self.after.iter().map(|(n, _)| n.clone()));
        out.extend(
            local[params.min(local.len())..]
                .iter()
                .map(|(n, _)| n.clone()),
        );
        out
    }

    /// An arm's variable may not take the name of the matched variable or of
    /// a parameter the motive generalizes: the arm binds those again around
    /// its body, so the name would stand for two values at once.
    fn hidden(&self, names: &[String], c: &str) -> Result<(), Diagnostic> {
        let Some(n) = names
            .iter()
            .find(|n| **n == self.x || self.after.iter().any(|(m, _)| m == *n))
        else {
            return Ok(());
        };
        let what = if *n == self.x {
            msg!("kernel-match-the-matched-value")
        } else {
            msg!("kernel-match-the-parameter", name = n)
        };
        err(
            msg!("kernel-match-arm-hides", arm = c, name = n, what = what),
            self.span,
        )
    }
}

impl Kernel {
    /// The body of `name(params): result` with its top-level `match`
    /// compiled; `None` when the body is not a `match`.
    pub(super) fn compile_match(
        &mut self,
        name: Option<&str>,
        implicit: usize,
        params: &[(String, T)],
        result: &T,
        body: &SurfaceTerm,
    ) -> Result<Option<T>, Diagnostic> {
        let (_, inner) = peel_applied(body);
        let TermKind::Match { scrutinee, .. } = &*inner.kind else {
            return Ok(None);
        };
        // A match on a term is compiled by `elaborate`, not as a definition.
        if !matches!(&*scrutinee.kind, TermKind::Var(x) if params.iter().any(|(n, _)| n == x)) {
            return Ok(None);
        }
        // A match on an `Int` with numerals for patterns is the branches on `==`
        // `elaborate` makes of it, not a match on the constructors of `Int`, so
        // `-1` is not read as a numeral pattern of `Nat`.
        if let TermKind::Match {
            scrutinee,
            result: motive,
            binder: None,
            arms,
        } = &*inner.kind
            && self
                .int_chain(scrutinee, motive.as_deref(), arms, params, inner.span)
                .is_some()
        {
            return Ok(None);
        }
        let spec = FnSpec {
            name,
            implicit,
            params: params.to_vec(),
            result: result.clone(),
            body,
        };
        Ok(self.compile_group(&[spec])?.into_iter().next())
    }

    fn read_header<'a>(
        &mut self,
        spec: &'a FnSpec<'a>,
        wanted: &[String],
    ) -> Result<Header<'a>, Diagnostic> {
        let TermKind::Match {
            scrutinee,
            result: motive_result,
            binder,
            arms,
        } = &*spec.body.kind
        else {
            return err(msg!("kernel-match-mutual-by-match"), spec.body.span);
        };
        let params = &spec.params;
        let sp = spec.body.span;
        let TermKind::Var(x) = &*scrutinee.kind else {
            return err(msg!("kernel-match-on-parameter"), scrutinee.span);
        };
        if binder.is_some() {
            return err(msg!("kernel-match-as-variable"), scrutinee.span);
        }
        let Some(xpos) = params.iter().position(|(n, _)| n == x) else {
            return err(msg!("kernel-match-not-variable", name = x), scrutinee.span);
        };
        let ctx: Ctx = params.to_vec();
        let xty = self.whnf_pair(&ctx[..xpos].to_vec(), &params[xpos].1);
        if matches!(&*xty.kind, TermKind::Var(v) if v == "?") {
            return err(msg!("kernel-match-lambda-type", name = x), scrutinee.span);
        }
        let (family, fargs) = match &*xty.kind {
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(i) => (i.clone(), arguments.clone()),
                _ => return err(msg!("kernel-match-not-inductive"), sp),
            },
            TermKind::Var(i) => (i.clone(), vec![]),
            _ => return err(msg!("kernel-match-not-inductive"), sp),
        };
        let (family, fargs) = match self.nested_member(&family, &fargs) {
            Some(member) => (member, Vec::new()),
            None => (family, fargs),
        };
        let Some(ind) = self.inds.get(&family).cloned() else {
            if family == "Quot" {
                return err(msg!("kernel-match-quot"), sp);
            }
            return err(msg!("kernel-match-family-not-inductive", name = family), sp);
        };
        let np = ind.params.len();
        let (pargs, idx_args) = fargs.split_at(np.min(fargs.len()));

        let target = match motive_result {
            Some(t) => {
                let t = self.shape_type(t, &ctx)?;
                self.elab(&ctx, &t, None)?
            }
            None => spec.result.clone(),
        };
        // An earlier parameter stays fixed when the matched value's type
        // mentions it, or the type of one that stays fixed does; the others
        // the motive can generalize, like the later ones.
        let mut fixed: Vec<String> = Vec::new();
        for (n, _) in params[..xpos].iter().rev() {
            if occurs(&xty, n)
                || fixed.iter().any(|f| {
                    params
                        .iter()
                        .find(|(m, _)| m == f)
                        .is_some_and(|(_, d)| occurs(d, n))
                })
            {
                fixed.push(n.clone());
            }
        }
        let movable: Vec<String> = params[..xpos]
            .iter()
            .map(|(n, _)| n.clone())
            .filter(|n| !fixed.contains(n))
            .collect();
        // What a generalized parameter's type mentions is generalized after it.
        let mut pre: Vec<(String, T)> = Vec::new();
        for (n, d) in &params[..xpos] {
            if movable.contains(n) && (wanted.contains(n) || pre.iter().any(|(m, _)| occurs(d, m)))
            {
                pre.push((n.clone(), d.clone()));
            }
        }
        let pre_names: Vec<String> = pre.iter().map(|(n, _)| n.clone()).collect();
        let mut after: Vec<(String, T)> = pre;
        after.extend(params[xpos + 1..].iter().cloned());
        // A function whose arms call no member of its group needs no
        // induction hypothesis to vary over the later parameters. It is
        // compiled like a match nested in a term, so that factoring a match
        // out into such a function gives a term convertible with the inline
        // one.
        let recursive = spec.name.is_some()
            && self.defining.iter().any(|(n, _)| {
                let method = n.split_once('@').map(|(m, _)| m);
                arms.iter().any(|a| {
                    let mut found = false;
                    crate::surface::walk::term(&mut a.body.clone(), &mut |t: &mut T| {
                        if let TermKind::Var(v) = &*t.kind
                            && (v == n || method == Some(v.as_str()))
                        {
                            found = true;
                        }
                    });
                    found
                })
            });
        if recursive {
            // A later parameter is generalized only when its type depends on
            // the matched value, its indices or a generalized parameter, or a
            // recursive call changes it (`wanted`). The others stay in scope
            // as they are, so the function unfolds to the eliminator at the
            // same motive a match written in place has, and the two are equal.
            let mut deps: Vec<String> = vec![x.clone()];
            deps.extend(pre_names.iter().cloned());
            for a in idx_args {
                if let TermKind::Var(v) = &*a.kind {
                    deps.push(v.clone());
                }
            }
            after.retain(|(n, d)| {
                let keep = pre_names.contains(n)
                    || wanted.contains(n)
                    || deps.iter().any(|v| occurs(d, v));
                if keep {
                    deps.push(n.clone());
                }
                keep
            });
        } else {
            // A match nested in a term cannot be recursed into, so only the
            // later variables that depend on the matched value or on its
            // indices are generalized; the others stay in scope as they are.
            // A binder of the arrow type the match is written under is
            // generalized only when an arm uses it: otherwise the match stays
            // the eliminator it is without that binder, and
            // `(Eq(A, p.fst, p.snd)) -> Eq(A, match p … , p.fst)` reads its
            // match as `p.fst` reads.
            let mut deps: Vec<String> = vec![x.clone()];
            for a in idx_args {
                if let TermKind::Var(v) = &*a.kind {
                    deps.push(v.clone());
                }
            }
            let arrow_binders = &self.arrow_binders;
            let unused_binder =
                |n: &String| arrow_binders.contains(n) && !arms.iter().any(|a| occurs(&a.body, n));
            after.retain(|(n, d)| {
                let keep = pre_names.contains(n)
                    || wanted.contains(n)
                    || (!unused_binder(n) && deps.iter().any(|v| occurs(d, v)));
                if keep {
                    deps.push(n.clone());
                }
                keep
            });
        }
        let mut motive_body = after
            .iter()
            .rev()
            .fold(target, |acc, (n, d)| pi(n, d.clone(), acc));
        let mut binders = Vec::new();
        let mut general = Vec::new();
        let mut seen: Vec<String> = Vec::new();
        let pnames: Vec<String> = ind.params.iter().map(|(n, _)| n.clone()).collect();
        for (k, a) in idx_args.iter().enumerate() {
            let b = format!("i'{k}");
            match &*a.kind {
                TermKind::Var(v)
                    if v != x && params.iter().any(|(n, _)| n == v) && !seen.contains(v) =>
                {
                    seen.push(v.clone());
                    motive_body = self.subst(&motive_body, v, &T::var(&b, sp));
                }
                _ => {
                    let ty = self.instantiate(&ind.index_tys[k].1, &pnames, pargs);
                    general.push(GenIdx {
                        k,
                        ty,
                        arg: a.clone(),
                    });
                }
            }
            binders.push(b);
        }
        // The target may mention the matched value at the type it had; the
        // motive's value has the generalized indices, so it is cast along the
        // equations.
        let mut xrep = T::var("t'", sp);
        if !general.is_empty() && occurs(&motive_body, x) {
            let mut idx_vec: Vec<T> = (0..idx_args.len())
                .map(|k| T::var(&format!("i'{k}"), sp))
                .collect();
            let elim = if self.family_is_prop(&family) {
                "Eq::ind"
            } else {
                "Eq::rec"
            };
            for g in &general {
                let mut at = idx_vec.clone();
                at[g.k] = T::var("y'", sp);
                let mut fam_args = pargs.to_vec();
                fam_args.extend(at);
                let m = lam("y'", lam("c'", app(T::var(&family, sp), fam_args)));
                xrep = app(
                    T::var(elim, sp),
                    vec![
                        g.ty.clone(),
                        T::var(&format!("i'{}", g.k), sp),
                        m,
                        xrep,
                        g.arg.clone(),
                        T::var(&format!("e'{}", g.k), sp),
                    ],
                );
                idx_vec[g.k] = g.arg.clone();
            }
        }
        motive_body = self.subst(&motive_body, x, &xrep);
        for g in general.iter().rev() {
            let e = eq_ty(&g.ty, &T::var(&format!("i'{}", g.k), sp), &g.arg);
            motive_body = pi(&format!("e'{}", g.k), e, motive_body);
        }
        binders.push("t'".into());
        let motive = binders.iter().rev().fold(motive_body, |acc, b| lam(b, acc));
        let is_prop = self.expect_type(&ctx, &spec.result)? == Sort::Prop;
        Ok(Header {
            x: x.clone(),
            xpos,
            family,
            pargs: pargs.to_vec(),
            idx_args: idx_args.to_vec(),
            motive,
            after,
            pre: pre_names,
            movable,
            is_prop,
            arms,
            span: sp,
            general,
        })
    }

    /// Defines the functions of a group (one, or the members of a `mutual`
    /// block), each by a `match` on a parameter of a different family of one
    /// mutual inductive group. They share the minor premises, so a call may
    /// pass from one to another on a field of the matched value.
    pub(super) fn compile_group(&mut self, specs: &[FnSpec]) -> Result<Vec<T>, Diagnostic> {
        // `(match x: (H) -> G { … })(h)` is the match, applied to `h`.
        let mut tails: Vec<Vec<SurfaceTerm>> = Vec::new();
        let specs: Vec<FnSpec> = specs
            .iter()
            .map(|spec| {
                let (tail, body) = match spec.name {
                    Some(_) => peel_applied(spec.body),
                    None => (Vec::new(), spec.body),
                };
                tails.push(tail);
                FnSpec {
                    name: spec.name,
                    implicit: spec.implicit,
                    params: spec.params.clone(),
                    result: spec.result.clone(),
                    body,
                }
            })
            .collect();
        let specs = &specs[..];
        let mut defining = Vec::new();
        let mut implicit = Vec::new();
        for spec in specs {
            if let Some(name) = spec.name {
                implicit.push((name.to_string(), spec.implicit));
                let ty = spec
                    .params
                    .iter()
                    .rev()
                    .fold(spec.result.clone(), |acc, (n, d)| pi(n, d.clone(), acc));
                defining.push((name.to_string(), ty));
            }
        }
        let outer = (!defining.is_empty()).then(|| {
            (
                std::mem::replace(&mut self.defining, defining),
                std::mem::replace(&mut self.defining_implicit, implicit),
            )
        });
        // A call that changes an earlier parameter the motive can generalize
        // asks for it; the group is compiled again with it generalized.
        let mut gens: Vec<Vec<String>> = vec![Vec::new(); specs.len()];
        let out = loop {
            let wants: Vec<Rc<RefCell<Vec<String>>>> =
                specs.iter().map(|_| Rc::default()).collect();
            let tails: Vec<&[SurfaceTerm]> = tails.iter().map(|t| t.as_slice()).collect();
            let noted = self.ctor_sites.len();
            let out = self.compile_group_in(specs, &tails, &gens, &wants);
            let mut more = false;
            if out.is_err() {
                self.ctor_sites.truncate(noted);
                for (g, w) in gens.iter_mut().zip(&wants) {
                    for n in w.borrow().iter() {
                        if !g.contains(n) {
                            g.push(n.clone());
                            more = true;
                        }
                    }
                }
            }
            if !more {
                break out;
            }
        };
        if let Some((outer, implicit)) = outer {
            self.defining = outer;
            self.defining_implicit = implicit;
        }
        out
    }

    fn compile_group_in(
        &mut self,
        specs: &[FnSpec],
        tails: &[&[SurfaceTerm]],
        gens: &[Vec<String>],
        wants: &[Rc<RefCell<Vec<String>>>],
    ) -> Result<Vec<T>, Diagnostic> {
        let mut headers = Vec::new();
        for (spec, wanted) in specs.iter().zip(gens) {
            headers.push(self.read_header(spec, wanted)?);
        }
        let sp = headers[0].span;
        let Some(first) = self.inds.get(&headers[0].family).cloned() else {
            return err(msg!("kernel-match-not-inductive"), sp);
        };
        let group = first.group.clone();
        let nf = group.len();
        // The functions that match on each family. Several on one family
        // share its motive, as a tuple of theirs.
        let mut spec_of_fam: Vec<Vec<usize>> = vec![Vec::new(); nf];
        for (s, h) in headers.iter().enumerate() {
            let Some(pos) = group.iter().position(|g| *g == h.family) else {
                return err(msg!("kernel-match-one-group"), h.span);
            };
            spec_of_fam[pos].push(s);
            if h.is_prop != headers[0].is_prop {
                return err(msg!("kernel-match-proofs-or-data"), h.span);
            }
        }
        let is_prop = headers[0].is_prop;
        let kind = if is_prop { "ind" } else { "rec" };
        for h in &headers {
            if !self.recs.contains_key(&format!("{}::{kind}", h.family)) {
                return err(
                    msg!("kernel-match-no-large-elimination", name = &h.family),
                    h.span,
                );
            }
        }
        let mut applied: Vec<Vec<T>> = Vec::new();
        for (spec, tail) in specs.iter().zip(tails) {
            let mut args = Vec::new();
            for a in tail.iter() {
                args.push(self.elaborate(a, &spec.params)?);
            }
            applied.push(args);
        }
        let mut filled: HashMap<String, (Vec<String>, Vec<T>)> = HashMap::new();
        let mut fns: HashMap<String, FnInfo> = HashMap::new();
        for (s, h) in headers.iter().enumerate() {
            if let Some(name) = specs[s].name {
                let params = &specs[s].params;
                let idx_params = h
                    .idx_args
                    .iter()
                    .filter_map(|a| match &*a.kind {
                        TermKind::Var(v) if params[..h.xpos].iter().any(|(n, _)| n == v) => {
                            Some(v.clone())
                        }
                        _ => None,
                    })
                    .collect();
                // The records a call leaves out are passed unchanged, like the
                // generics.
                let records = params[specs[s].implicit.min(params.len())..]
                    .iter()
                    .take_while(|(n, _)| n.starts_with(crate::surface::DICT))
                    .count();
                let info = FnInfo {
                    params: params.iter().map(|(n, _)| n.clone()).collect(),
                    alias: false,
                    implicit: specs[s].implicit + records,
                    xpos: h.xpos,
                    idx_params,
                    pre: h.pre.clone(),
                    post: h
                        .after
                        .iter()
                        .map(|(n, _)| n.clone())
                        .filter(|n| params[h.xpos + 1..].iter().any(|(m, _)| m == n))
                        .collect(),
                    movable: h.movable.clone(),
                    wants: wants[s].clone(),
                    fam: group.iter().position(|g| *g == h.family).unwrap(),
                    general: h
                        .general
                        .iter()
                        .map(|g| (g.ty.clone(), g.arg.clone()))
                        .collect(),
                    tail: !applied[s].is_empty(),
                    spec: s,
                };
                if !applied[s].is_empty() {
                    filled.insert(name.to_string(), (info.params.clone(), applied[s].clone()));
                }
                if let Some((method, _)) = name.split_once('@')
                    && method.contains("::")
                {
                    fns.insert(
                        method.to_string(),
                        FnInfo {
                            alias: true,
                            ..info.clone()
                        },
                    );
                }
                fns.insert(name.to_string(), info);
            }
        }

        // One motive per family; a family no function matches on gets a
        // trivial one.
        let trivial_ty = if is_prop { "True" } else { "Unit" };
        let trivial_val = if is_prop { "Trivial" } else { "Star" };
        let mut motives = Vec::new();
        for (f, g) in group.iter().enumerate() {
            match spec_of_fam[f].as_slice() {
                [s] => motives.push(headers[*s].motive.clone()),
                [_, _, ..] => {
                    let n = self.inds[g].indices;
                    let vars: Vec<String> = (0..n)
                        .map(|k| format!("i'{k}"))
                        .chain(["t'".into()])
                        .collect();
                    let at: Vec<T> = vars.iter().map(|v| T::var(v, sp)).collect();
                    let ts: Vec<T> = spec_of_fam[f]
                        .iter()
                        .map(|&s| app(headers[s].motive.clone(), at.clone()))
                        .collect();
                    motives.push(lams(&vars, tuple_ty(is_prop, &ts)));
                }
                [] => {
                    let ind = self.inds.get(g).cloned().unwrap();
                    let mut m = T::var(trivial_ty, sp);
                    for k in (0..=ind.indices).rev() {
                        m = lam(&format!("i'{k}"), m);
                    }
                    motives.push(m);
                }
            }
        }

        // A recursion on a deeper part of the matched value: the motive pairs
        // each value with the values at its parts (`DeepScope`).
        let (deeper, rebuilt) = self.recurs_deeper(specs, &headers, group.len());
        let deep = if deeper {
            let below = self.below_fn(&specs[0], &headers[0])?;
            let h = &headers[0];
            let n = self.inds[&h.family].indices;
            let vars: Vec<String> = (0..n)
                .map(|k| format!("i'{k}"))
                .chain(["t'".into()])
                .collect();
            let at: Vec<T> = vars.iter().map(|v| T::var(v, sp)).collect();
            motives[0] = lams(
                &vars,
                pair_ty(
                    is_prop,
                    &app(h.motive.clone(), at.clone()),
                    &app(below.clone(), at),
                ),
            );
            Some(below)
        } else {
            None
        };

        let mut minors = Vec::new();
        for (f, g) in group.iter().enumerate() {
            let ind = self.inds.get(g).cloned().unwrap();
            let here = spec_of_fam[f].clone();
            if here.is_empty() {
                for c in &ind.ctors {
                    let mut m = T::var(trivial_val, sp);
                    for _ in 0..c.recs.len() + c.args.len() {
                        let n = self.fresh_name("_");
                        m = lam(&n, m);
                    }
                    minors.push(m);
                }
                continue;
            }
            // Each function's arm of each constructor: its fields, induction
            // hypotheses and value.
            let mut arms_of: Vec<Vec<(Vec<String>, Vec<String>, T)>> = Vec::new();
            for &s in &here {
                let mut arms_here = Vec::new();
                let h = &headers[s];
                let spec = &specs[s];
                let params = &spec.params;
                let mut chosen: HashMap<usize, (Vec<String>, &SurfaceTerm)> = HashMap::new();
                let mut written: HashMap<usize, &SurfaceTerm> = HashMap::new();
                let arms = self.nest_arms(h.arms)?;
                // `_ => e` stands for each constructor no arm names, with its
                // fields unnamed; it is the last arm and stands for at least one.
                // `y => e` is the default arm that names the matched value: in
                // each constructor's arm `y` is that constructor of its fields.
                let mut default: Option<&SurfaceTerm> = None;
                let mut default_name: Option<String> = None;
                for (at, arm) in arms.iter().enumerate() {
                    if arm.guard.is_some() {
                        return err(msg!("kernel-match-guards"), arm.body.span);
                    }
                    let named = match &arm.pattern {
                        Pattern::Bind(n) if !self.ctors.contains_key(n) => Some(n.clone()),
                        _ => None,
                    };
                    if arm.pattern == Pattern::Wild || named.is_some() {
                        if at + 1 != arms.len() {
                            let message = match named {
                                Some(n) => msg!("kernel-match-named-last", name = n),
                                None => msg!("kernel-match-default-last"),
                            };
                            return err(message, arm.body.span);
                        }
                        if named.is_some() && !h.general.is_empty() {
                            return err(msg!("kernel-match-named-indices"), arm.body.span);
                        }
                        default = Some(&arm.body);
                        default_name = named;
                        continue;
                    }
                    let (cname, args): (String, Vec<Pattern>) = match &arm.pattern {
                        Pattern::Ctor { name, args } => {
                            if let Some(n) = self.unknown_implicit(name, args) {
                                return err(
                                    msg!(
                                        "kernel-pattern-unknown-implicit",
                                        name = name,
                                        implicit = &n
                                    ),
                                    arm.body.span,
                                );
                            }
                            (name.clone(), self.full_fields(name, args.clone()))
                        }
                        Pattern::Bind(n) if self.ctors.contains_key(n) => (n.clone(), vec![]),
                        _ => {
                            return err(msg!("kernel-match-lists-ctors"), arm.body.span);
                        }
                    };
                    // A constructor written by its own name (`Mk`) is the
                    // matched type's constructor of that name, whatever
                    // other type (of the same file, or the prelude's
                    // `BelowPair`) has a constructor so named too.
                    let spelled = cname.clone();
                    let cname = if ind.ctors.iter().any(|c| c.name == cname) {
                        cname
                    } else {
                        let mut own = ind
                            .ctors
                            .iter()
                            .filter(|c| c.name.rsplit_once("::").is_some_and(|(_, s)| s == cname));
                        match (own.next(), own.next()) {
                            (Some(c), None) => c.name.clone(),
                            _ => cname,
                        }
                    };
                    // Extraction writes this constructor for the pattern. They are noted
                    // in the order the kernel meets the patterns of an arm (a nested
                    // pattern's constructors after the one around it).
                    if self.record_sites {
                        self.ctor_sites.push(CtorSite {
                            span: arm.body.span,
                            written: spelled,
                            resolved: cname.clone(),
                        });
                    }
                    let Some((fam, j)) = self.ctors.get(&cname).cloned() else {
                        // A near spelling of one of the matched type's
                        // constructors (`mk_pair` for `MkPair`) is named here,
                        // as the checker of executable code names it.
                        let hint = tauto_surface::suggest::closest_name(
                            &cname,
                            ind.ctors.iter().map(|c| c.name.as_str()),
                        );
                        let message = match hint {
                            Some(hint) => {
                                msg!("kernel-match-not-ctor-hint", name = &cname, hint = hint)
                            }
                            None => msg!("kernel-match-not-ctor", name = &cname),
                        };
                        return err(message, arm.body.span);
                    };
                    let real = ind.alias.as_ref().map_or(g.as_str(), |a| a.0.as_str());
                    if fam != real {
                        // A name written alone matches the constructor of
                        // that name wherever one is visible; it binds only
                        // when no constructor has the name.
                        let alone = match &arm.pattern {
                            Pattern::Bind(_) => true,
                            Pattern::Ctor { args, .. } => args.is_empty(),
                            _ => false,
                        };
                        let id = if alone {
                            "kernel-match-other-ctor-alone"
                        } else {
                            "kernel-match-other-ctor"
                        };
                        // The suggested binder starts lowercase, since a
                        // capitalized name reads as a constructor.
                        let mut cs = cname.chars();
                        let binder = cs.next().map_or(String::new(), |c| {
                            c.to_lowercase().chain(cs).collect::<String>() + "_"
                        });
                        return err(
                            msg!(
                                id,
                                name = &cname,
                                family = &fam,
                                matched = g,
                                binder = &binder
                            ),
                            arm.body.span,
                        );
                    }
                    let names = args
                        .iter()
                        .map(|p| match p {
                            Pattern::Bind(n) => Ok(n.clone()),
                            Pattern::Wild => Ok(self.fresh_name("_")),
                            _ => err(msg!("kernel-match-field-pattern"), arm.body.span),
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    if names.len() != ind.ctors[j].args.len() {
                        return err(
                            msg!(
                                "kernel-match-field-count",
                                name = &cname,
                                fields = ind.ctors[j].args.len(),
                                written = names.len()
                            ),
                            arm.body.span,
                        );
                    }
                    if chosen.insert(j, (names, &arm.body)).is_some() {
                        return err(msg!("kernel-match-twice", name = &cname), arm.body.span);
                    }
                    if let Some(g) = &arm.goal {
                        written.insert(j, g);
                    }
                }
                if let Some(d) = default
                    && ind
                        .ctors
                        .iter()
                        .enumerate()
                        .all(|(j, _)| chosen.contains_key(&j))
                {
                    let message = match &default_name {
                        Some(n) => msg!("kernel-match-named-unused", name = n),
                        None => msg!("kernel-match-default-unused"),
                    };
                    return err(message, d.span);
                }
                let fill = |k: &mut Self, c: &Ctor| {
                    default.map(|d| {
                        let names: Vec<String> = c.args.iter().map(|_| k.fresh_name("_")).collect();
                        (names, d)
                    })
                };
                for (j, c) in ind.ctors.iter().enumerate() {
                    if !h.general.is_empty() && here.len() > 1 {
                        return err(msg!("kernel-match-same-family-indices"), h.span);
                    }
                    if !h.general.is_empty() {
                        let arm = chosen.remove(&j);
                        let minor = match arm {
                            Some(arm) => {
                                self.general_minor(g, &ind, c, spec, h, Some(arm), f, &fns)?
                            }
                            // A constructor its indices rule out needs no arm; the
                            // default stands for the others.
                            None => match self.general_minor(g, &ind, c, spec, h, None, f, &fns) {
                                Ok(m) => m,
                                Err(e) => match fill(self, c) {
                                    Some(arm) => {
                                        self.general_minor(g, &ind, c, spec, h, Some(arm), f, &fns)?
                                    }
                                    None => return Err(e),
                                },
                            },
                        };
                        minors.push(minor);
                        continue;
                    }
                    let (named, filled) = match chosen.remove(&j) {
                        Some(arm) => (None, Some(arm)),
                        None => (default_name.clone(), fill(self, c)),
                    };
                    let Some((names, arm_body)) = filled else {
                        return err(msg!("kernel-match-missing-case", name = &c.name), h.span);
                    };
                    h.hidden(&names, &c.name)?;
                    let mut ihs = Vec::new();
                    let mut smaller: Smaller = HashMap::new();
                    for r in &c.recs {
                        let ih = self.fresh_name("ih");
                        smaller.insert(names[r.arg].clone(), (T::var(&ih, sp), r.fam, r.ys.len()));
                        ihs.push(ih);
                    }
                    let mut local: Vec<(String, T)> = params.to_vec();
                    let (mut from, mut to) = self.ctor_binding(&ind, &h.pargs);
                    for ((_, ty), pat) in c.args.iter().zip(&names) {
                        let ty = self.instantiate(ty, &from, &to);
                        local.push((pat.clone(), ty));
                        from.push(c.args[local.len() - params.len() - 1].0.clone());
                        to.push(T::var(pat, sp));
                    }
                    // In a recursion on deeper parts, each recursive field has the
                    // values at its parts as a variable, and its own value is the
                    // first half of its hypothesis.
                    let mut belows: Vec<(String, String, T, T, String)> = Vec::new();
                    // With a call on a rebuilt constructor, each one's value too.
                    let mut ats: Vec<(String, String, T, T, String)> = Vec::new();
                    // The entries of this constructor's `below`, with their values.
                    let mut tuple: Vec<(T, T)> = Vec::new();
                    if let Some(below) = &deep {
                        for (r, ih) in c.recs.iter().zip(&ihs) {
                            if !r.ys.is_empty() {
                                // A function-typed field: its values at each
                                // argument, with no parts further down.
                                let (entry, ys, m, b) = self.function_entry(
                                    r,
                                    &from,
                                    &to,
                                    &names[r.arg],
                                    &h.motive,
                                    below,
                                );
                                let at_ys = ys.iter().map(|y| T::var(y, sp)).collect();
                                let value = lams(
                                    &ys,
                                    proj(is_prop, &m, &b, app(T::var(ih, sp), at_ys), true),
                                );
                                let held =
                                    app(T::var("the", sp), vec![entry.clone(), value.clone()]);
                                smaller.insert(names[r.arg].clone(), (held, r.fam, ys.len()));
                                tuple.push((entry, value));
                                continue;
                            }
                            let mut at: Vec<T> = r
                                .idx
                                .iter()
                                .map(|t| self.instantiate(t, &from, &to))
                                .collect();
                            at.push(T::var(&names[r.arg], sp));
                            let m = app(h.motive.clone(), at.clone());
                            let b = app(below.clone(), at);
                            let v = self.fresh_name("below");
                            local.push((v.clone(), b.clone()));
                            if rebuilt {
                                let a = self.fresh_name("at");
                                local.push((a.clone(), m.clone()));
                                ats.push((
                                    names[r.arg].clone(),
                                    a,
                                    m.clone(),
                                    b.clone(),
                                    ih.clone(),
                                ));
                            }
                            let value = proj(is_prop, &m, &b, T::var(ih, sp), true);
                            smaller.insert(names[r.arg].clone(), (value, r.fam, 0));
                            tuple.push((pair_ty(is_prop, &m, &b), T::var(ih, sp)));
                            belows.push((names[r.arg].clone(), v, m, b, ih.clone()));
                        }
                    }
                    // Inside the arm the matched value is the constructor and the
                    // parameters after it, and the plain indices, are refined.
                    let cval = app(T::var(&c.name, sp), to.clone());
                    for p in &mut local[h.xpos + 1..params.len()] {
                        p.1 = self.subst(&p.1, &h.x, &cval);
                    }
                    for (k, a) in h.idx_args.iter().enumerate() {
                        if let TermKind::Var(v) = &*a.kind
                            && *v != h.x
                            && let Some(at) = params.iter().position(|(n, _)| n == v)
                            && at < h.xpos
                            && !h.general.iter().any(|g| g.k == k)
                        {
                            let value = self.instantiate(&c.idx[k], &from, &to);
                            for p in &mut local[h.xpos + 1..params.len()] {
                                p.1 = self.subst(&p.1, v, &value);
                            }
                        }
                    }
                    let mut margs: Vec<T> = c
                        .idx
                        .iter()
                        .map(|t| self.instantiate(t, &from, &to))
                        .collect();
                    margs.push(cval.clone());
                    let goal = self.whnf(&local, &app(h.motive.clone(), margs));
                    let goal = self.under_after(goal, &h.after);
                    if let Some(w) = written.remove(&j) {
                        self.check_arm_goal(&local, w, goal.as_ref())?;
                    }
                    let outer_scope = if deep.is_some() {
                        let vars = belows
                            .iter()
                            .map(|(f, v, ..)| (f.clone(), v.clone(), Vec::new()))
                            .collect();
                        self.deep.replace(DeepScope {
                            fns: fns.clone(),
                            prop: is_prop,
                            vars,
                            at: ats
                                .iter()
                                .map(|(f, a, ..)| (f.clone(), a.clone()))
                                .collect(),
                            rebound: h.rebound(&local, params.len()),
                        })
                    } else {
                        None
                    };
                    let parts = if spec.name.is_none() {
                        self.parts_of(&h.x, c, &names, &local)
                    } else {
                        Vec::new()
                    };
                    // The parts reached before this match, the matched value among
                    // them: a call on one is its value, read here, where the arm has
                    // refined the `below` variables' types (outside, they show the
                    // matched variable, not the constructor).
                    let reached = if spec.name.is_none() {
                        self.reached_values(&local)
                    } else {
                        Vec::new()
                    };
                    let pushed = parts.len();
                    if let Some(scope) = &mut self.deep {
                        scope.vars.extend(
                            parts
                                .iter()
                                .map(|(f, v, p, _)| (f.clone(), v.clone(), p.clone())),
                        );
                    }
                    // The name of an arm `y =>` is a variable of the constructor's
                    // type while the arm is elaborated, then the constructor.
                    self.matched.push((h.x.clone(), cval.clone()));
                    let shaped = match named {
                        Some(n) => match self.infer(&local, &cval) {
                            Ok(ty) => {
                                let mut arm_local = local.clone();
                                arm_local.push((n.clone(), ty));
                                self.elaborate_at(arm_body, &arm_local, goal.as_ref())
                                    .map(|t| self.subst(&t, &n, &cval))
                            }
                            Err(e) => Err(e),
                        },
                        None => self.elaborate_at(arm_body, &local, goal.as_ref()),
                    };
                    self.matched.pop();
                    if deep.is_some() {
                        self.deep = outer_scope;
                    } else if let Some(scope) = &mut self.deep {
                        scope.vars.truncate(scope.vars.len() - pushed);
                    }
                    let shaped = shaped?;
                    let shaped = self.with_generics(&shaped, &local, goal.as_ref(), &fns);
                    let shaped = match (&self.deep, parts.is_empty() && reached.is_empty()) {
                        (Some(scope), false) => {
                            let fns = scope.fns.clone();
                            // A name bound twice in scope, or again by the arm the
                            // scope was opened in, is not the parameter.
                            let mut rebound = scope.rebound.clone();
                            rebound.extend(h.rebound(&local, params.len()));
                            for (k, (n, _)) in local.iter().enumerate() {
                                if local[..k].iter().any(|(m, _)| m == n) {
                                    rebound.push(n.clone());
                                }
                            }
                            let shaped = self.with_generics(&shaped, &local, goal.as_ref(), &fns);
                            let smaller: Smaller = parts
                                .into_iter()
                                .map(|(f, _, _, value)| (f, (value, 0, 0)))
                                .chain(reached.into_iter().map(|(f, value)| (f, (value, 0, 0))))
                                .collect();
                            // In this arm the matched part is its constructor, so
                            // a call on the constructor rebuilt from the arm's
                            // fields is a call on the part.
                            let shaped = if smaller.contains_key(&h.x) {
                                rebuilt_as(&shaped, &fns, &cval, &h.x)
                            } else {
                                shaped
                            };
                            replace_in(&shaped, &fns, &smaller, true, &rebound)?
                        }
                        _ => shaped,
                    };
                    let rebound = h.rebound(&local, params.len());
                    let replaced = if fns.is_empty() {
                        shaped
                    } else if spec_of_fam.iter().any(|l| l.len() > 1) {
                        // A field of a family several functions match on has their
                        // values as a tuple: each function's call is its component.
                        let mut t = shaped;
                        for (name, info) in &fns {
                            let mut mine = smaller.clone();
                            for r in &c.recs {
                                let on = &spec_of_fam[r.fam];
                                let Some(at_comp) = on.iter().position(|&l| l == info.spec) else {
                                    continue;
                                };
                                if on.len() < 2 {
                                    continue;
                                }
                                if !r.ys.is_empty() {
                                    return err(msg!("kernel-match-same-family-function"), h.span);
                                }
                                let mut at: Vec<T> = r
                                    .idx
                                    .iter()
                                    .map(|t| self.instantiate(t, &from, &to))
                                    .collect();
                                at.push(T::var(&names[r.arg], sp));
                                let ts: Vec<T> = on
                                    .iter()
                                    .map(|&l| app(headers[l].motive.clone(), at.clone()))
                                    .collect();
                                let entry = mine.get_mut(&names[r.arg]).unwrap();
                                entry.0 = component(is_prop, &ts, entry.0.clone(), at_comp);
                            }
                            let one: HashMap<String, FnInfo> =
                                [(name.clone(), info.clone())].into_iter().collect();
                            t = replace_in(&t, &one, &mine, false, &rebound)?;
                        }
                        t
                    } else {
                        replace_calls(&shaped, &fns, &smaller, &rebound)?
                    };
                    // The arm is a minor premise, which an induction hypothesis
                    // runs on a field: in a function being defined, the matched
                    // variable stands for this constructor there, not for the
                    // outermost value.
                    let replaced = if fns.is_empty() {
                        replaced
                    } else {
                        self.subst(&replaced, &h.x, &cval)
                    };
                    let mut replaced = replaced;
                    for (_, v, m, b, ih) in &belows {
                        let rest = proj(is_prop, m, b, T::var(ih, sp), false);
                        replaced = self.subst(&replaced, v, &rest);
                    }
                    for (_, a, m, b, ih) in &ats {
                        let value = proj(is_prop, m, b, T::var(ih, sp), true);
                        replaced = self.subst(&replaced, a, &value);
                    }
                    let with_after = h
                        .after
                        .iter()
                        .rev()
                        .fold(replaced, |acc, (n, _)| lam(n, acc));
                    let with_after = match &deep {
                        Some(below) => {
                            let mut at: Vec<T> = c
                                .idx
                                .iter()
                                .map(|t| self.instantiate(t, &from, &to))
                                .collect();
                            at.push(cval.clone());
                            let (mut ty, mut val) = unit(is_prop, sp);
                            for (entry, value) in tuple.iter().rev() {
                                val = pair(is_prop, entry, &ty, value.clone(), val);
                                ty = pair_ty(is_prop, entry, &ty);
                            }
                            pair(
                                is_prop,
                                &app(h.motive.clone(), at.clone()),
                                &app(below.clone(), at),
                                with_after,
                                val,
                            )
                        }
                        None => with_after,
                    };
                    arms_here.push((names, ihs, with_after));
                }
                arms_of.push(arms_here);
            }
            for (j, c) in ind.ctors.iter().enumerate() {
                if arms_of[0].len() <= j {
                    // Made by `general_minor`, for a single function.
                    continue;
                }
                let (names, ihs, first) = arms_of[0][j].clone();
                let mut vals = vec![first];
                for arms in &arms_of[1..] {
                    let (ns, is, mut v) = arms[j].clone();
                    for (a, b) in ns.iter().zip(&names).chain(is.iter().zip(&ihs)) {
                        v = self.subst(&v, a, &T::var(b, sp));
                    }
                    vals.push(v);
                }
                let value = if here.len() == 1 {
                    vals.pop().unwrap()
                } else {
                    let (mut from, mut to) = self.ctor_binding(&ind, &headers[here[0]].pargs);
                    for ((a, _), n) in c.args.iter().zip(&names) {
                        from.push(a.clone());
                        to.push(T::var(n, sp));
                    }
                    let mut at: Vec<T> = c
                        .idx
                        .iter()
                        .map(|t| self.instantiate(t, &from, &to))
                        .collect();
                    at.push(app(T::var(&c.name, sp), to));
                    let ts: Vec<T> = here
                        .iter()
                        .map(|&l| app(headers[l].motive.clone(), at.clone()))
                        .collect();
                    tuple(is_prop, &ts, vals)
                };
                let with_ihs = ihs.iter().rev().fold(value, |acc, b| lam(b, acc));
                minors.push(names.iter().rev().fold(with_ihs, |acc, b| lam(b, acc)));
            }
        }

        let mut out = Vec::new();
        for h in &headers {
            let mut args: Vec<T> = h.pargs.clone();
            args.extend(motives.iter().cloned());
            args.extend(minors.iter().cloned());
            args.extend(h.idx_args.iter().cloned());
            args.push(T::var(&h.x, sp));
            let eliminated = app(T::var(&format!("{}::{kind}", h.family), sp), args);
            let on = &spec_of_fam[group.iter().position(|g| *g == h.family).unwrap()];
            let eliminated = if on.len() > 1 {
                let mut at = h.idx_args.clone();
                at.push(T::var(&h.x, sp));
                let ts: Vec<T> = on
                    .iter()
                    .map(|&l| app(headers[l].motive.clone(), at.clone()))
                    .collect();
                let me = on
                    .iter()
                    .position(|&l| std::ptr::eq(&headers[l], h))
                    .unwrap();
                component(is_prop, &ts, eliminated, me)
            } else {
                eliminated
            };
            let eliminated = match &deep {
                Some(below) => {
                    let mut at = h.idx_args.clone();
                    at.push(T::var(&h.x, sp));
                    proj(
                        is_prop,
                        &app(h.motive.clone(), at.clone()),
                        &app(below.clone(), at),
                        eliminated,
                        true,
                    )
                }
                None => eliminated,
            };
            let refls: Vec<T> = h
                .general
                .iter()
                .map(|g| app(T::var("Refl", sp), vec![g.ty.clone(), g.arg.clone()]))
                .collect();
            let eliminated = app(eliminated, refls);
            out.push(app(
                eliminated,
                h.after.iter().map(|(n, _)| T::var(n, sp)).collect(),
            ));
        }
        for (o, args) in out.iter_mut().zip(&applied) {
            if !args.is_empty() {
                *o = app(o.clone(), args.clone());
            }
            if !filled.is_empty() {
                *o = self.fill_tails(o, &filled);
            }
        }
        Ok(out)
    }
}

impl Kernel {
    /// `shape`, compiling the matches in `t` against the variables in scope.
    pub(super) fn elaborate(
        &mut self,
        t: &SurfaceTerm,
        ctx: &[(String, T)],
    ) -> Result<T, Diagnostic> {
        self.elaborate_at(t, ctx, None)
    }

    /// The branches on `==` a `match` on an `Int` with numerals for patterns stands
    /// for (`sugar::literal_chain`), or `None` where the arms are not numerals and an
    /// arm of the other values, or the scrutinee is not of std's `Int`.
    fn int_chain(
        &mut self,
        scrutinee: &SurfaceTerm,
        result: Option<&SurfaceTerm>,
        arms: &[crate::surface::MatchArm],
        ctx: &[(String, T)],
        sp: tauto_parol::Span,
    ) -> Option<SurfaceTerm> {
        let (last, literals) = arms.split_last()?;
        if literals.is_empty()
            || !literals
                .iter()
                .all(|a| matches!(a.pattern, Pattern::Int(_)))
            || !matches!(last.pattern, Pattern::Wild | Pattern::Bind(_))
        {
            return None;
        }
        let saved = self.metas.clone();
        let typed = self.typed(scrutinee, ctx);
        self.metas = saved;
        let (_, ty) = typed.ok()?;
        let is_int = match &*ty.kind {
            TermKind::Var(n) if n == "Int" || n.ends_with("::Int") => {
                self.inds.get(n).is_some_and(|ind| {
                    ind.ctors.len() == 2
                        && ind.ctors.iter().any(|c| c.name.ends_with("IntOfNat"))
                        && ind.ctors.iter().any(|c| c.name.ends_with("IntNegSucc"))
                })
            }
            _ => false,
        };
        if !is_int {
            return None;
        }
        let mut arms = arms.to_vec();
        if let Some(rest) = arms.last_mut()
            && let Pattern::Bind(other) = &rest.pattern
        {
            let other = other.clone();
            rest.body = self.subst(&rest.body, &other, scrutinee);
            rest.pattern = Pattern::Wild;
        }
        super::sugar::literal_chain(scrutinee, result, &arms, super::sugar::Literal::Int, sp)
    }

    /// `elaborate` where `t` is expected to have type `goal`: a `match`
    /// written there (or made from a nested pattern) needs no result type.
    pub(super) fn elaborate_at(
        &mut self,
        t: &SurfaceTerm,
        ctx: &[(String, T)],
        goal: Option<&T>,
    ) -> Result<T, Diagnostic> {
        let sp = t.span;
        match &*t.kind {
            // A `match` on an `Int` with numerals for patterns is the branches on `==`
            // it stands for, as a `match` of `Text` literals is (`sugar.rs`). The arm of
            // the other values has the scrutinee for its name.
            TermKind::Match {
                scrutinee,
                result,
                binder: None,
                arms,
            } if (result.is_some() || goal.is_some())
                && let Some(chain) =
                    self.int_chain(scrutinee, result.as_deref(), arms, ctx, sp) =>
            {
                self.elaborate_at(&chain, ctx, goal)
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } if result.is_some() || goal.is_some() => {
                let result = match (result, goal) {
                    (Some(r), _) => {
                        let r = self.shape_type(r, ctx)?;
                        let mut typing: Ctx = self.defining.clone();
                        typing.extend(ctx.iter().cloned());
                        self.elab(&typing, &r, None)?
                    }
                    (None, Some(g)) => g.clone(),
                    (None, None) => unreachable!(),
                };
                let on_variable = match &*scrutinee.kind {
                    TermKind::Var(x) => ctx.iter().any(|(n, _)| n == x),
                    _ => false,
                };
                if !on_variable {
                    return self.match_on_term(
                        scrutinee,
                        &result,
                        binder.as_deref(),
                        arms,
                        ctx,
                        sp,
                    );
                }
                let TermKind::Var(x) = &*scrutinee.kind else {
                    unreachable!()
                };
                if binder.is_some() {
                    return err(msg!("kernel-match-as-variable"), scrutinee.span);
                }
                let indices = self.index_variables(ctx, x);
                let ctx = &depending_last(ctx, x, &indices);
                match self.compile_match(None, 0, ctx, &result, t)? {
                    Some(compiled) => Ok(compiled),
                    None => err(msg!("kernel-match-not-compiled"), sp),
                }
            }
            TermKind::Match { .. } => err(msg!("kernel-match-result-type"), sp),
            // `if c { a } else { b }` is `match c: T { true => a  false => b }`, with `T` the
            // type expected here, or else the type of a branch (`if_type`).
            TermKind::If {
                otherwise: None, ..
            } => err(msg!("kernel-if-no-else"), sp),
            TermKind::If {
                then,
                otherwise: Some(otherwise),
                ..
            } => {
                let result = match goal {
                    Some(_) => None,
                    None => Some(Box::new(self.if_type(then, otherwise, ctx, sp)?)),
                };
                let written = match super::mutable::if_match(t).into_kind() {
                    TermKind::Match {
                        binder,
                        scrutinee,
                        arms,
                        ..
                    } => TermKind::Match {
                        binder,
                        scrutinee,
                        result,
                        arms,
                    },
                    _ => unreachable!(),
                };
                self.elaborate_at(&SurfaceTerm::new(written, sp), ctx, goal)
            }
            // `T::ind`, `T::rec`, `T::nc`: a name the checker made for the type
            // `T`, written as it is shown, unless `T` is a variable in scope.
            TermKind::Field { base, name }
                if matches!(&*base.kind, TermKind::Var(c)
                    if !ctx.iter().any(|(n, _)| n == c)
                        && self.globals.contains_key(format!("{c}::{name}").as_str())) =>
            {
                let TermKind::Var(c) = &*base.kind else {
                    unreachable!()
                };
                let var = SurfaceTerm::new(TermKind::Var(format!("{c}::{name}")), sp);
                self.elaborate_at(&var, ctx, goal)
            }
            TermKind::Field { base, name } => self.field(base, name, ctx, sp),
            TermKind::Ascribe { term, ty } => self.ascribe(term, ty, ctx, sp),
            // `@a e` (the family `@label.a` applied to `e`): for `e` a type, the type
            // `@a e`; for a value, the value wrapped, `@label.a.Mk(e)`, of type `@a T`.
            TermKind::App {
                function,
                arguments,
            } if let TermKind::Var(f) = &*function.kind
                && super::sugar::label_of(f).is_some()
                && let [inner] = arguments.as_slice()
                && !self.is_type(inner, ctx) =>
            {
                let built = SurfaceTerm::app(&format!("{f}::Mk"), vec![inner.clone()], sp);
                self.elaborate_at(&built, ctx, goal)
            }
            // A type with a `match` in it: each domain is in scope in what
            // follows, so the match can be on a parameter before it.
            TermKind::Pi {
                params,
                result,
                effects,
            } if has_written_match(t) || has_equality(t) => {
                let mut inner = ctx.to_vec();
                let mut shaped = Vec::new();
                for (n, d) in params {
                    let d = self.elaborate(d, &inner)?;
                    if let Some(n) = n {
                        inner.push((n.clone(), d.clone()));
                    }
                    shaped.push((n.clone(), d));
                }
                let result = self.elaborate(result, &inner)?;
                let mut acc = result;
                for (n, d) in shaped.into_iter().rev() {
                    acc = T::new(
                        TermKind::Pi {
                            params: vec![(n, d)],
                            result: Box::new(acc),
                            effects: effects.clone(),
                        },
                        sp,
                    );
                }
                Ok(acc)
            }
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(op) if op == "==" || op == "!=")
                && arguments.len() == 2 =>
            {
                let TermKind::Var(op) = &*function.kind else {
                    unreachable!()
                };
                self.equality(op == "!=", &arguments[0], &arguments[1], ctx, sp)
            }
            TermKind::App {
                function,
                arguments,
            } if arguments
                .iter()
                .any(|a| has_match(a) || matches!(&*a.kind, TermKind::If { .. })) =>
            {
                self.call_with_matches(function, arguments, ctx, goal, sp)
            }
            TermKind::App {
                function,
                arguments,
            } => {
                let domains = self.lambda_domains(function, arguments.len(), ctx);
                let function = self.elaborate(function, ctx)?;
                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(i, a)| match (&*a.kind, domains.get(i)) {
                        (
                            TermKind::Lam {
                                params,
                                body,
                                types,
                            },
                            Some(Some(ds)),
                        ) if ds.len() == params.len() => {
                            let ds = self.domains_named(params, ds);
                            self.check_param_types(params, types, &ds, ctx)?;
                            let mut inner = ctx.to_vec();
                            inner.extend(params.iter().cloned().zip(ds));
                            let mut acc = self.elaborate(body, &inner)?;
                            for p in params.iter().rev() {
                                acc = lam(p, acc);
                            }
                            Ok(acc)
                        }
                        _ => self.elaborate(a, ctx),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(T::new(
                    TermKind::App {
                        function: Box::new(function),
                        arguments,
                    },
                    sp,
                ))
            }
            TermKind::Lam {
                params,
                body,
                types,
            } => {
                let mut inner = ctx.to_vec();
                let mut rest = goal.cloned();
                // The written types not held to a goal here: `elab` holds them
                // to the type the λ is given.
                let mut unchecked = Vec::new();
                for (i, p) in params.iter().enumerate() {
                    let written = self.written_param_type(types.get(i), &inner)?;
                    // The goal, when it is a Π, gives the parameter its type.
                    let mut typing: Ctx = self.defining.clone();
                    typing.extend(inner.iter().cloned());
                    let step = rest.as_ref().and_then(|g| {
                        let g = self.whnf(&typing, g);
                        match &*g.kind {
                            TermKind::Pi { params, result, .. } => Some((
                                params[0].0.clone().unwrap_or_else(|| "_".into()),
                                params[0].1.clone(),
                                (**result).clone(),
                            )),
                            _ => None,
                        }
                    });
                    match step {
                        Some((n, dom, result)) => {
                            if let Some(w) = &written {
                                self.check_param_type(p, w, &dom, &typing)?;
                            }
                            inner.push((p.clone(), dom));
                            rest = Some(self.subst(&result, &n, &T::var(p, sp)));
                        }
                        None => {
                            // Without a goal, the body sees the parameter as
                            // the type written on it (a `match` on it, and the
                            // implicit arguments of a call on it, are read from
                            // it); `elab` holds it to the type the λ is given.
                            let ty = match &written {
                                Some(w) => w.clone(),
                                None => T::var("?", sp),
                            };
                            inner.push((p.clone(), ty));
                            rest = None;
                        }
                    }
                    unchecked.push(written.filter(|_| rest.is_none()));
                }
                let body = self.elaborate_at(body, &inner, rest.as_ref())?;
                let mut acc = body;
                for (p, w) in params.iter().zip(unchecked).rev() {
                    acc = T::new(
                        TermKind::Lam {
                            params: vec![p.clone()],
                            body: Box::new(acc),
                            types: w.into_iter().map(Some).collect(),
                        },
                        sp,
                    );
                }
                Ok(acc)
            }
            // `∃ x: D. P` is the prelude's `Exists(D, x => P)`, as `shape`
            // writes it, with the projections in `D` and `P` compiled.
            TermKind::Exists {
                binder,
                domain,
                body,
            } => {
                let written = T::new(
                    TermKind::App {
                        function: Box::new(T::var("Exists", sp)),
                        arguments: vec![
                            (**domain).clone(),
                            T::new(
                                TermKind::Lam {
                                    params: vec![binder.clone()],
                                    body: body.clone(),
                                    types: vec![Some((**domain).clone())],
                                },
                                sp,
                            ),
                        ],
                    },
                    sp,
                );
                self.elaborate_at(&written, ctx, goal)
            }
            _ => self.shape(t),
        }
    }
}

impl Kernel {
    /// The type written on a λ's parameter, `(x: A) => …`, read where the λ
    /// is (outside its parameters).
    fn written_param_type(
        &mut self,
        written: Option<&Option<SurfaceTerm>>,
        ctx: &[(String, T)],
    ) -> Result<Option<T>, Diagnostic> {
        match written {
            Some(Some(ty)) => {
                let mut ty = self.elaborate(ty, ctx)?;
                // In an arm the matched value is the arm's constructor, as it
                // is in the type the λ is given; a variable the arm binds
                // again under the same name is not the matched one.
                for (x, cval) in self.matched.clone() {
                    if ctx.iter().filter(|(n, _)| *n == x).count() == 1 {
                        ty = self.subst(&ty, &x, &cval);
                    }
                }
                let mut typing: Ctx = self.defining.clone();
                typing.extend(ctx.iter().cloned());
                Ok(Some(self.elab(&typing, &ty, None)?))
            }
            _ => Ok(None),
        }
    }

    /// A λ's parameter `p` written as `(p: written)` where the function it is
    /// given to takes a `given`: the two are the same type, or the λ is not
    /// what it says.
    pub(super) fn check_param_type(
        &mut self,
        p: &str,
        written: &T,
        given: &T,
        typing: &Ctx,
    ) -> Result<(), Diagnostic> {
        if self.conv(typing, written, given) {
            return Ok(());
        }
        // The type the call gives may still leave out the implicit arguments
        // of a function substituted into it (`(a => always(a))(a)`): compare
        // it once they are written out.
        let elaborated = self
            .shape(given)
            .ok()
            .and_then(|g| self.elab(typing, &g, None).ok());
        if let Some(g) = &elaborated
            && self.conv(typing, written, g)
        {
            return Ok(());
        }
        err(
            msg!(
                "kernel-match-param-written",
                name = p,
                written = crate::surface::print::print_term(&Kernel::eqs_written(written)),
                given = crate::surface::print::print_term(&Kernel::eqs_written(given)),
            ),
            written.span,
        )
    }

    fn check_param_types(
        &mut self,
        params: &[String],
        types: &[Option<SurfaceTerm>],
        given: &[T],
        ctx: &[(String, T)],
    ) -> Result<(), Diagnostic> {
        // A later parameter's written type may name an earlier parameter,
        // so each is read with the parameters before it in scope.
        let mut inner = ctx.to_vec();
        for (i, (p, d)) in params.iter().zip(given).enumerate() {
            if let Some(w) = self.written_param_type(types.get(i), &inner)? {
                let mut typing: Ctx = self.defining.clone();
                typing.extend(inner.iter().cloned());
                self.check_param_type(p, &w, d, &typing)?;
            }
            inner.push((p.clone(), d.clone()));
        }
        Ok(())
    }

    /// A call some of whose arguments hold a `match`: the other arguments are
    /// elaborated first, and the implicit arguments they and `goal` determine
    /// give the type each of those arguments has, which is the result type of
    /// a `match` written there and the types of a λ's parameters.
    fn call_with_matches(
        &mut self,
        function: &SurfaceTerm,
        arguments: &[SurfaceTerm],
        ctx: &[(String, T)],
        goal: Option<&T>,
        sp: tauto_parol::Span,
    ) -> Result<T, Diagnostic> {
        let domains = self.lambda_domains(function, arguments.len(), ctx);
        let function = self.elaborate(function, ctx)?;
        let mut out: Vec<Option<T>> = Vec::new();
        for a in arguments {
            out.push(if has_match(a) || matches!(&*a.kind, TermKind::If { .. }) {
                None
            } else {
                Some(self.elaborate(a, ctx)?)
            });
        }
        let mut typing: Ctx = self.defining.clone();
        typing.extend(ctx.iter().cloned());
        // The arguments as the kernel has them, to find the implicit ones by.
        let written: Vec<Option<T>> = out
            .iter()
            .map(|a| {
                a.as_ref().and_then(|a| {
                    let a = self.shape(a).ok()?;
                    self.elab(&typing, &a, None).ok()
                })
            })
            .collect();
        // An argument whose implicit arguments only the others fix
        // (`Refl`) is left out like a `match`: the rest may still fix them.
        let shaped_function = self.shape(&function).ok();
        let goals = match &shaped_function {
            Some(f) => self.argument_goals(&typing, f, &written, goal),
            None => vec![None; arguments.len()],
        };
        let mut elaborated = Vec::new();
        for (i, (a, done)) in arguments.iter().zip(out).enumerate() {
            if let Some(done) = done {
                elaborated.push(done);
                continue;
            }
            let arg_goal = goals.get(i).cloned().flatten();
            let e = match (&*a.kind, &arg_goal, domains.get(i)) {
                (
                    TermKind::Lam {
                        params,
                        body,
                        types,
                    },
                    None,
                    Some(Some(ds)),
                ) if ds.len() == params.len() => {
                    let ds = self.domains_named(params, ds);
                    self.check_param_types(params, types, &ds, ctx)?;
                    let mut inner = ctx.to_vec();
                    inner.extend(params.iter().cloned().zip(ds));
                    let mut acc = self.elaborate(body, &inner)?;
                    for p in params.iter().rev() {
                        acc = lam(p, acc);
                    }
                    acc
                }
                _ => self.elaborate_at(a, ctx, arg_goal.as_ref())?,
            };
            elaborated.push(e);
        }
        Ok(T::new(
            TermKind::App {
                function: Box::new(function),
                arguments: elaborated,
            },
            sp,
        ))
    }

    /// For a call of a global with `n` arguments: for each argument whose
    /// parameter is a function type with closed domains, those domains.
    /// A lambda given there has them as the types of its parameters, so a
    /// `match` in its body can be on them.
    fn lambda_domains(
        &self,
        function: &SurfaceTerm,
        n: usize,
        ctx: &[(String, T)],
    ) -> Vec<Option<Vec<(Option<String>, T)>>> {
        let TermKind::Var(f) = &*function.kind else {
            return Vec::new();
        };
        if ctx.iter().any(|(x, _)| x == f) {
            return Vec::new();
        }
        let Some(g) = self.globals.get(f) else {
            return Vec::new();
        };
        let mut telescope = Vec::new();
        let mut ty = &g.ty;
        while let TermKind::Pi { params, result, .. } = &*ty.kind {
            telescope.push((params[0].0.clone(), params[0].1.clone()));
            ty = result;
        }
        let skip = if n + g.implicit == telescope.len() {
            g.implicit
        } else {
            0
        };
        let bound: Vec<String> = telescope.iter().filter_map(|(x, _)| x.clone()).collect();
        let closed = |t: &T| !bound.iter().any(|x| occurs(t, x));
        telescope
            .iter()
            .skip(skip)
            .map(|(_, d)| {
                let mut ds = Vec::new();
                let mut d = d;
                while let TermKind::Pi { params, result, .. } = &*d.kind {
                    if !closed(&params[0].1) {
                        return None;
                    }
                    ds.push(params[0].clone());
                    d = result;
                }
                (!ds.is_empty()).then_some(ds)
            })
            .collect()
    }

    /// The domains `lambda_domains` found for a λ's parameters, with the
    /// names their Π binds read as the λ's own: in `∀ x: A. (P(x)) -> …`
    /// given `(y: A, h: P(y)) => …`, the second domain is `P(y)`.
    fn domains_named(&mut self, params: &[String], ds: &[(Option<String>, T)]) -> Vec<T> {
        let mut out: Vec<T> = Vec::new();
        for (i, (_, d)) in ds.iter().enumerate() {
            let mut d = d.clone();
            for (j, (n, _)) in ds[..i].iter().enumerate() {
                if let Some(n) = n
                    && n != &params[j]
                {
                    d = self.subst(&d, n, &T::var(&params[j], d.span));
                }
            }
            out.push(d);
        }
        out
    }

    /// The type of `if c { a } else { b }` where none is expected: the type of `a`, or of
    /// `b` when the form of `a` leaves its type open or `a` has none to find, as for the
    /// two sides of `=`.
    fn if_type(
        &mut self,
        then: &SurfaceTerm,
        otherwise: &SurfaceTerm,
        ctx: &[(String, T)],
        sp: tauto_parol::Span,
    ) -> Result<T, Diagnostic> {
        let mut typing: Ctx = self.defining.clone();
        typing.extend(ctx.iter().cloned());
        for branch in [then, otherwise] {
            let saved = self.metas.clone();
            let found = self.branch_type(branch, ctx, &typing);
            self.metas = saved;
            if let Some(ty) = found {
                return Ok(ty);
            }
        }
        err(msg!("kernel-if-type-open"), sp)
    }

    /// The type of `branch`, or `None` when its form leaves it open or it has none.
    fn branch_type(
        &mut self,
        branch: &SurfaceTerm,
        ctx: &[(String, T)],
        typing: &Ctx,
    ) -> Option<T> {
        let e = self.elaborate(branch, ctx).ok()?;
        let e = self.shape(&e).ok()?;
        if self.type_open(typing, &e) {
            return None;
        }
        let e = self.elab(typing, &e, None).ok()?;
        let ty = self.infer(typing, &e).ok()?;
        Some(self.resolve(&ty))
    }

    fn typed(&mut self, t: &SurfaceTerm, ctx: &[(String, T)]) -> Result<(T, T), Diagnostic> {
        let e = self.elaborate(t, ctx)?;
        let mut typing: Ctx = self.defining.clone();
        typing.extend(ctx.iter().cloned());
        let e = self.shape(&e)?;
        let e = self.elab(&typing, &e, None)?;
        let ty = self.infer(&typing, &e)?;
        let ty = self.whnf_pair(&typing, &ty);
        Ok((e, ty))
    }

    /// `x.f` for `x` of a family with one constructor: a match on `x` that
    /// gives the field.
    fn field(
        &mut self,
        base: &SurfaceTerm,
        name: &str,
        ctx: &[(String, T)],
        sp: tauto_parol::Span,
    ) -> Result<T, Diagnostic> {
        // `Url::query(t)`: a field is taken from a value, never from its type.
        if let TermKind::Var(f) = &*base.kind
            && !ctx.iter().any(|(x, _)| x == f)
            && self.inds.contains_key(f)
        {
            return err(msg!("kernel-field-of-type", family = f, name = name), sp);
        }
        let (_, ty) = self.typed(base, ctx)?;
        let (family, args) = match &*ty.kind {
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(f) => (f.clone(), arguments.clone()),
                _ => return err(msg!("kernel-field-not-inductive"), sp),
            },
            TermKind::Var(f) => (f.clone(), Vec::new()),
            _ => return err(msg!("kernel-field-not-inductive"), sp),
        };
        let Some((ctor, fields)) = self.records().get(&family).cloned() else {
            return err(
                msg!("kernel-field-many-ctors", family = &family, name = name),
                sp,
            );
        };
        let Some(at) = fields.iter().position(|f| f == name) else {
            return err(msg!("kernel-field-none", family = &family, name = name), sp);
        };
        let ind = &self.inds[&family];
        let c = &ind.ctors[0];
        let fty = c.args[c.implicit + at].1.clone();
        if fields.iter().any(|f| occurs(&fty, f)) {
            return err(msg!("kernel-field-depends", name = name), sp);
        }
        let pnames: Vec<String> = ind.params.iter().map(|(n, _)| n.clone()).collect();
        let np = pnames.len().min(args.len());
        let fty = self.instantiate(&fty, &pnames, &args[..np]);
        let vars: Vec<String> = fields.iter().map(|f| self.fresh_name(f)).collect();
        let arm = crate::surface::MatchArm {
            goal: None,
            pattern: Pattern::Ctor {
                name: ctor,
                args: vars.iter().map(|v| Pattern::Bind(v.clone())).collect(),
            },
            guard: None,
            body: SurfaceTerm::new(TermKind::Var(vars[at].clone()), sp),
        };
        self.match_on_term(base, &fty, None, &[arm], ctx, sp)
    }

    /// `(e: T)`: `e` at the written type `T`. Where `T` is the type of `e`, `e` as it is.
    /// Where the type of `e` is a product (`Pair` nested to the right) and `T` takes some of
    /// its members (`A × B <: A`, `A × B × C <: A × C`, in any order), the members `T`
    /// names, taken out of `e` by `.fst` and `.snd` and put together in the order `T`
    /// writes them. A member is found by its type; two members of one type are a clash.
    /// A label (`@a T`, the family `@label.a(T)`) is part of the type: `@a Nat` and `@b Nat`
    /// are two members. Where no member has the type `T` asks for, a labelled member `@a T`
    /// whose `T` it is gives its `.value` (`@a T <: T`). Where `T` is `@a A` and `e` is an
    /// `A`, `e` is wrapped as `@label.a.Mk(e)`.
    fn ascribe(
        &mut self,
        term: &SurfaceTerm,
        written: &SurfaceTerm,
        ctx: &[(String, T)],
        sp: tauto_parol::Span,
    ) -> Result<T, Diagnostic> {
        let mut typing: Ctx = self.defining.clone();
        typing.extend(ctx.iter().cloned());
        let w = self.elaborate(written, ctx)?;
        let w = self.shape(&w)?;
        let w = self.elab(&typing, &w, None)?;
        self.ascribe_at(term, &w, ctx, sp)
    }

    /// Whether a term of type `have` meets the expected type `want` only through the
    /// subtyping of products (`ascribe`): one of the two is a product or a labelled type, and
    /// `have` is not already a `want`. A type with a variable still to find (a generic not
    /// fixed yet) is left to the call: a member is not picked by a guess.
    pub(super) fn needs_ascription(&mut self, typing: &Ctx, have: &T, want: &T) -> bool {
        if super::implicit::has_meta(have) || super::implicit::has_meta(want) {
            return false;
        }
        let wn = self.whnf(typing, want);
        if matches!(&*wn.kind, TermKind::Pi { .. }) || super::sort_of(&wn).is_some() {
            return false;
        }
        // A product is told by its own name `Prod`, before it is unfolded to the `Pair` the
        // kernel sees: a `Pair` written by its name has no members to take.
        let product = |this: &mut Self, t: &T| {
            this.product_parts(t).is_some() || {
                let n = this.whnf(typing, t);
                this.label_parts(&n).is_some()
            }
        };
        if !(product(self, have) || product(self, want)) {
            return false;
        }
        if self.product_parts(have).is_some() && self.product_parts(want).is_some() {
            return !self.conv(typing, have, want);
        }
        let h = self.whnf(typing, have);
        !self.subtype(typing, &h, &wn)
    }

    /// `term` at the type `w` (elaborated): `ascribe` for a type already read.
    pub(super) fn ascribe_at(
        &mut self,
        term: &SurfaceTerm,
        w: &T,
        ctx: &[(String, T)],
        sp: tauto_parol::Span,
    ) -> Result<T, Diagnostic> {
        let w = w.clone();
        let mut typing: Ctx = self.defining.clone();
        typing.extend(ctx.iter().cloned());
        let (e, ty) = self.typed(term, ctx)?;
        // The type as written, before `Prod` is unfolded to the `Pair` the kernel sees.
        let ty = match self.infer(&typing, &e) {
            Ok(written) if self.product_parts(&written).is_some() => written,
            _ => ty,
        };
        if self.subtype(&typing, &ty, &w) {
            return Ok(e);
        }
        let wn = self.whnf(&typing, &w);
        if let Some((family, inner)) = self.label_parts(&wn)
            && self.conv(&typing, &ty, &inner)
        {
            // One application of the constructor, with the parameter written out: the
            // value is not elaborated again against the labelled type.
            let mk = T::new(TermKind::Var(format!("{family}::Mk")), sp);
            return Ok(T::new(
                TermKind::App {
                    function: Box::new(mk),
                    arguments: vec![inner, e],
                },
                sp,
            ));
        }
        let have = self.members(&typing, &ty, term.clone());
        // A product fitted to a type that a product was unfolded to (the motive of a `match`
        // on a product, say): that type's `Pair` spine is the product's.
        let w = if self.product_parts(&ty).is_some() && self.product_parts(&w).is_none() {
            self.as_written_product(&typing, &w)
        } else {
            w
        };
        let want = self.members(&typing, &w, SurfaceTerm::var("_", sp));
        let unlabelled: Vec<Option<T>> = have
            .iter()
            .map(|(t, _)| {
                let t = self.whnf(&typing, t);
                self.label_parts(&t).map(|(_, inner)| inner)
            })
            .collect();
        if have.len() < 2 && unlabelled[0].is_none() {
            let (a, b) = (describe(&ty), describe(&w));
            return err(msg!("kernel-ascribe-mismatch", have = &a, want = &b), sp);
        }
        // Members are matched by their types only where both products are closed (no type
        // variable, no unknown) and no two members of one product have the same type:
        // otherwise the correspondence would be a guess, and the members are written by
        // position, or each is told apart by a label.
        if have.len() >= 2 || want.len() >= 2 {
            let open = |t: &T| {
                super::free_vars(t)
                    .iter()
                    .any(|v| v.starts_with('?') || super::is_local(&typing, v))
            };
            if open(&ty) || open(&w) {
                let (a, b) = (describe(&ty), describe(&w));
                return err(msg!("kernel-ascribe-open", have = &a, want = &b), sp);
            }
            for side in [&have, &want] {
                for i in 0..side.len() {
                    for j in i + 1..side.len() {
                        if self.conv(&typing, &side[i].0, &side[j].0) {
                            let a = describe(&side[i].0);
                            return err(msg!("kernel-ascribe-clash", member = &a), sp);
                        }
                    }
                }
            }
        }
        let mut taken: Vec<usize> = Vec::new();
        let mut unwrap: Vec<bool> = Vec::new();
        for (part, _) in &want {
            let mut at: Vec<usize> = (0..have.len())
                .filter(|i| self.conv(&typing, &have[*i].0, part))
                .collect();
            let mut through_label = false;
            if at.is_empty() {
                // `@a T <: T`: a labelled member whose `T` is asked for.
                at = (0..have.len())
                    .filter(|i| {
                        unlabelled[*i]
                            .as_ref()
                            .is_some_and(|inner| self.conv(&typing, inner, part))
                    })
                    .collect();
                through_label = true;
            }
            match at.as_slice() {
                [i] if !taken.contains(i) => {
                    taken.push(*i);
                    unwrap.push(through_label);
                }
                [] => {
                    let (a, b) = (describe(part), describe(&ty));
                    return err(
                        msg!("kernel-ascribe-no-member", member = &a, product = &b),
                        sp,
                    );
                }
                _ => {
                    let a = describe(part);
                    return err(msg!("kernel-ascribe-clash", member = &a), sp);
                }
            }
        }
        let mut picked: Vec<SurfaceTerm> = taken
            .iter()
            .zip(&unwrap)
            .map(|(i, u)| {
                let member = have[*i].1.clone();
                if *u {
                    SurfaceTerm::new(
                        TermKind::Field {
                            base: Box::new(member),
                            name: "value".into(),
                        },
                        sp,
                    )
                } else {
                    member
                }
            })
            .collect();
        let last = picked.pop().expect("one or more");
        if picked.is_empty() {
            self.projecting += 1;
            let taken = self.elaborate_at(&last, ctx, Some(&w));
            self.projecting -= 1;
            return taken;
        }
        if self.product_parts(&w).is_none() {
            let (a, b) = (describe(&ty), describe(&w));
            return err(msg!("kernel-ascribe-mismatch", have = &a, want = &b), sp);
        }
        let built = picked.into_iter().rev().fold(last, |snd, fst| {
            SurfaceTerm::app("prod_mk", vec![fst, snd], sp)
        });
        // The members are taken out of the value as the `Pair` it is unfolded to.
        self.projecting += 1;
        let taken = self.elaborate_at(&built, ctx, Some(&w));
        self.projecting -= 1;
        taken
    }

    /// Whether `t` is a type: its type is a sort. A term whose type is not found is
    /// taken for a value.
    fn is_type(&mut self, t: &SurfaceTerm, ctx: &[(String, T)]) -> bool {
        let saved = self.metas.clone();
        let typed = self.typed(t, ctx);
        self.metas = saved;
        typed.is_ok_and(|(_, ty)| super::sort_of(&ty).is_some())
    }

    /// `ty`'s label family (`@label.a`) and the type it labels, when it is `@a T`.
    fn label_parts(&self, ty: &T) -> Option<(String, T)> {
        let TermKind::App {
            function,
            arguments,
        } = &*ty.kind
        else {
            return None;
        };
        let TermKind::Var(f) = &*function.kind else {
            return None;
        };
        match arguments.as_slice() {
            [inner] if super::sugar::label_of(f).is_some() => Some((f.clone(), inner.clone())),
            _ => None,
        }
    }

    /// `ty` (a `Pair` nested to the right, as a product is unfolded to) read back as the
    /// product `Prod` nested so; a type that is no `Pair` is itself.
    fn as_written_product(&mut self, typing: &Ctx, ty: &T) -> T {
        let n = self.whnf_pair(typing, ty);
        match self.pair_family(&n) {
            Some((_, args)) => {
                let rest = self.as_written_product(typing, &args[1]);
                T::new(
                    TermKind::App {
                        function: Box::new(T::var("Prod", ty.span)),
                        arguments: vec![args[0].clone(), rest],
                    },
                    ty.span,
                )
            }
            None => ty.clone(),
        }
    }

    /// The two members of `ty` when it is the product `Prod(A, B)`, as written: the name
    /// `Prod` is looked at before it is unfolded to the `Pair` the kernel sees.
    pub(super) fn product_parts(&self, ty: &T) -> Option<Vec<T>> {
        let TermKind::App {
            function,
            arguments,
        } = &*ty.kind
        else {
            return None;
        };
        let TermKind::Var(f) = &*function.kind else {
            return None;
        };
        (arguments.len() == 2 && (f == "Prod" || f.ends_with("::Prod"))).then(|| arguments.clone())
    }

    pub(super) fn pair_family(&self, ty: &T) -> Option<(String, Vec<T>)> {
        let TermKind::App {
            function,
            arguments,
        } = &*ty.kind
        else {
            return None;
        };
        let TermKind::Var(f) = &*function.kind else {
            return None;
        };
        (arguments.len() == 2 && (f == "Pair" || f.ends_with("::Pair")))
            .then(|| (f.clone(), arguments.clone()))
    }

    /// The members of the product `ty` (`Prod` nested to the right), each with the
    /// projection out of `base` that gives it; a type that is no product, a `Pair` written by
    /// its name among them, is its own one member.
    fn members(&mut self, typing: &Ctx, ty: &T, base: SurfaceTerm) -> Vec<(T, SurfaceTerm)> {
        let sp = base.span;
        let project = |b: &SurfaceTerm, name: &str| {
            SurfaceTerm::new(
                TermKind::Field {
                    base: Box::new(b.clone()),
                    name: name.into(),
                },
                sp,
            )
        };
        let mut out = Vec::new();
        let mut ty = ty.clone();
        let mut base = base;
        while let Some(args) = self.product_parts(&ty) {
            out.push((args[0].clone(), project(&base, "fst")));
            base = project(&base, "snd");
            ty = args[1].clone();
        }
        out.push((self.whnf(typing, &ty), base));
        out
    }

    /// `a == b` (and `a != b`) by the type of `a`: `nat_eq`, `bool_eq` or
    /// `text_eq` (and `not` of it).
    fn equality(
        &mut self,
        negated: bool,
        a: &SurfaceTerm,
        b: &SurfaceTerm,
        ctx: &[(String, T)],
        sp: tauto_parol::Span,
    ) -> Result<T, Diagnostic> {
        let (_, ty) = self.typed(a, ctx)?;
        let f = match &*ty.kind {
            TermKind::Var(n) if n == "Nat" => "Nat::eq",
            TermKind::Var(n) if n == "Bool" => "Bool::eq",
            TermKind::Var(n) if n == "Text" => "Text::eq",
            _ if self.equality_function(&ty).is_some() => {
                let eq = self.equality_function(&ty).unwrap();
                let call = SurfaceTerm::new(
                    TermKind::App {
                        function: Box::new(eq),
                        arguments: vec![a.clone(), b.clone()],
                    },
                    sp,
                );
                return self.elaborate(
                    &if negated {
                        SurfaceTerm::new(
                            TermKind::App {
                                function: Box::new(SurfaceTerm::new(
                                    TermKind::Var("not".into()),
                                    sp,
                                )),
                                arguments: vec![call],
                            },
                            sp,
                        )
                    } else {
                        call
                    },
                    ctx,
                );
            }
            _ => {
                return err(
                    msg!(
                        "kernel-eq-no-deq",
                        ty = describe(&ty),
                        head = describe(&ty).split('(').next().unwrap_or_default()
                    ),
                    sp,
                );
            }
        };
        // Read by its full name where another declaration took the short one
        // (`std::Text::text_eq`).
        let full;
        let f = if self.globals.contains_key(f) {
            f
        } else {
            let suffix = format!(".{f}");
            let mut found = self.globals.keys().filter(|k| k.ends_with(&suffix));
            match (found.next(), found.next()) {
                (Some(one), None) => {
                    full = one.clone();
                    full.as_str()
                }
                _ => return err(msg!("kernel-eq-not-declared", name = f), sp),
            }
        };
        let call = |g: &str, args: Vec<SurfaceTerm>| {
            SurfaceTerm::new(
                TermKind::App {
                    function: Box::new(SurfaceTerm::new(TermKind::Var(g.into()), sp)),
                    arguments: args,
                },
                sp,
            )
        };
        let mut t = call(f, vec![a.clone(), b.clone()]);
        if negated {
            t = call("not", vec![t]);
        }
        self.elaborate(&t, ctx)
    }

    /// `match e: T { … }` on a term that is not a variable: the match is
    /// compiled on a fresh variable `x` of the type of `e`, and `e` is put
    /// for `x`. Unless the match names its equation or writes the arms'
    /// goals, the result type does not mention `x`, and the match is a case
    /// analysis only; when it does, so do the assumptions whose types show
    /// `e`, as if moved into the result type and applied after. A call on a field of `e` is not recursion.
    fn match_on_term(
        &mut self,
        scrutinee: &SurfaceTerm,
        result: &T,
        binder: Option<&str>,
        arms: &[crate::surface::MatchArm],
        ctx: &[(String, T)],
        sp: tauto_parol::Span,
    ) -> Result<T, Diagnostic> {
        let e = self.elaborate(scrutinee, ctx)?;
        // The functions being defined are typed as variables here; a call
        // of one becomes its induction hypothesis afterwards.
        let mut typing: Ctx = self.defining.clone();
        typing.extend(ctx.iter().cloned());
        let e = self.shape(&e)?;
        let e = self.elab(&typing, &e, None)?;
        let ty = self.infer(&typing, &e)?;
        let x = self.fresh_name("m");
        // A match that names the equation or writes the arms' goals is one whose
        // result type shows the term; any other is a case analysis only.
        let written = binder.is_some() || arms.iter().any(|a| a.goal.is_some());
        // Unfolding parts of `result` to find `e` gives a more precise goal
        // than putting `x` only where `result` shows `e` as written; both are
        // the result type of a match on `x` that is `result` at `e`. Arms
        // whose written types are as `result` shows them (a parameter typed
        // `put(f, k, v)(i)` with `nat_eq(i, k)` its equation) are checked
        // with the plain one when the precise one does not fit them.
        // Unfolding hands back kernel terms, where a function without
        // parameters is the bare constant; they are elaborated again with the
        // arms, so they are put back as written (`ctx0()`).
        let (result, plain) = if written {
            let precise = self.generalize(&typing, &e, &x, result);
            let precise = self.calls_written_in(&typing, &precise);
            let plain = self.generalize_plain(&typing, &e, &x, result);
            let plain = self.calls_written_in(&typing, &plain);
            let (precise, plain) = match binder {
                Some(h) => (
                    link_equations(&precise, &e, &x, h),
                    link_equations(&plain, &e, &x, h),
                ),
                None => (precise, plain),
            };
            let plain = (describe(&plain) != describe(&precise)).then_some(plain);
            (precise, plain)
        } else {
            (result.clone(), None)
        };
        let result = &result;
        let mut inner = ctx.to_vec();
        // An assumption whose type shows the term is generalized with it: it
        // is moved after `x` with `x` put for the term, so each arm has it,
        // by its own name, with the arm's constructor. One that a later
        // variable's type mentions, or that the term itself mentions, stays
        // as it is. Arms written for the assumptions as they are (an arm
        // that rewrites `h` with the equation itself) are checked with them
        // kept when the generalized ones do not fit them.
        let mut kept = ctx.to_vec();
        let mut moved: Vec<(String, T)> = Vec::new();
        if written {
            let by = T::var(&x, sp);
            let keys = [describe(scrutinee), describe(&e)];
            let mut i = 0;
            while i < inner.len() {
                let (n, d) = inner[i].clone();
                let (mut g, mut hit) = (d, false);
                for key in &keys {
                    let (t2, h) = abstract_term(&g, &e, key, &by);
                    g = t2;
                    hit |= h;
                }
                let needed = occurs(&e, &n)
                    || occurs(&ty, &n)
                    || inner[i + 1..].iter().any(|(_, d2)| occurs(d2, &n));
                if hit && !needed {
                    inner.remove(i);
                    moved.push((n, g));
                } else {
                    i += 1;
                }
            }
        }
        let generalized = !moved.is_empty();
        inner.push((x.clone(), ty.clone()));
        inner.extend(moved);
        kept.push((x.clone(), ty.clone()));
        // The equation is a later parameter, which the match generalizes: each
        // arm has it by its name.
        if let Some(h) = binder {
            inner.push((h.to_string(), eq_ty(&ty, &e, &T::var(&x, sp))));
            kept.push((h.to_string(), eq_ty(&ty, &e, &T::var(&x, sp))));
        }
        // A `let` before the match is in its arms as `the(T, v)`; where `T`
        // shows the term, the `let` is generalized like a variable of that
        // type: the arms have a variable of `T` with the arm's constructor for
        // `e`, and `the(T, v)` is put for it afterwards.
        let mut arms = arms.to_vec();
        let mut lets: Vec<(String, T)> = Vec::new();
        if written {
            let by = T::var(&x, sp);
            let keys = [describe(scrutinee), describe(&e)];
            let mut found: Vec<(String, T, T)> = Vec::new();
            for arm in &mut arms {
                crate::surface::walk::term(&mut arm.body, &mut |t: &mut T| {
                    let TermKind::App {
                        function,
                        arguments,
                    } = &*t.kind
                    else {
                        return;
                    };
                    if !matches!(&*function.kind, TermKind::Var(f) if f == "the")
                        || arguments.len() != 2
                    {
                        return;
                    }
                    let (mut ty, mut hit) = (arguments[0].clone(), false);
                    for key in &keys {
                        let (t2, h) = abstract_term(&ty, &e, key, &by);
                        ty = t2;
                        hit |= h;
                    }
                    if !hit {
                        return;
                    }
                    let text = describe(t);
                    let name = match found.iter().find(|(d, _, _)| *d == text) {
                        Some((_, v, _)) => describe(v),
                        None => {
                            let name = format!("{x}_let{}", found.len());
                            found.push((text, T::var(&name, t.span), ty));
                            lets.push((name.clone(), t.clone()));
                            name
                        }
                    };
                    *t = T::var(&name, t.span);
                });
            }
            for (_, v, ty) in found {
                let TermKind::Var(name) = &*v.kind else {
                    continue;
                };
                let mut typing: Ctx = self.defining.clone();
                typing.extend(inner.iter().cloned());
                let ty = self.shape(&ty)?;
                let ty = self.elab(&typing, &ty, None)?;
                inner.push((name.clone(), ty.clone()));
                kept.push((name.clone(), ty));
            }
        }
        let on_x = SurfaceTerm::new(
            TermKind::Match {
                binder: None,
                scrutinee: Box::new(T::var(&x, scrutinee.span)),
                result: None,
                arms,
            },
            sp,
        );
        let mut compiled = self.compile_match(None, 0, &inner, result, &on_x);
        if let Some(plain) = &plain
            && !matches!(&compiled, Ok(Some(c)) if self.elaborates(&inner, c))
            && let Ok(Some(c)) = self.compile_match(None, 0, &inner, &plain, &on_x)
            && self.elaborates(&inner, &c)
        {
            compiled = Ok(Some(c));
        }
        if generalized && !matches!(&compiled, Ok(Some(c)) if self.elaborates(&inner, c)) {
            for goal in std::iter::once(result).chain(plain.as_ref()) {
                if let Ok(Some(c)) = self.compile_match(None, 0, &kept, goal, &on_x)
                    && self.elaborates(&kept, &c)
                {
                    compiled = Ok(Some(c));
                    break;
                }
            }
        }
        let Some(compiled) = compiled? else {
            return err(msg!("kernel-match-not-compiled"), sp);
        };
        let compiled = match binder {
            Some(h) => {
                let refl = app(T::var("Refl", sp), vec![ty, e.clone()]);
                self.subst(&compiled, h, &refl)
            }
            None => compiled,
        };
        let mut compiled = compiled;
        for (name, value) in &lets {
            compiled = self.subst(&compiled, name, value);
        }
        Ok(self.subst(&compiled, &x, &e))
    }

    /// Whether `t`, in the arms' context, elaborates: its arms check
    /// against the result type it was compiled with.
    fn elaborates(&mut self, inner: &[(String, T)], t: &T) -> bool {
        let mut typing: Ctx = self.defining.clone();
        typing.extend(inner.iter().cloned());
        match self.shape(t) {
            Ok(shaped) => self.elab(&typing, &shaped, None).is_ok(),
            Err(_) => false,
        }
    }

    /// `result` with the term `e` the match is on put for the variable `x`,
    /// where `result` shows it, or shows it once reduced (`sorted(insert(a,
    /// l))` is a `match` on the comparison `insert` makes): the result type of
    /// a match on `x`. Where `e` is not there, `result` as it is.
    fn generalize(&mut self, typing: &Ctx, e: &T, x: &str, result: &T) -> T {
        let by = T::var(x, e.span);
        let key = describe(e);
        // Unfolding does not bring in a local variable, so a part that lacks
        // one of the locals `e` has cannot show `e` once unfolded either, and
        // is left as written: a large closed term (a table, a fixed list) is
        // not computed here.
        let needs = locals_of(typing, e);
        let (found, hit) = self.put_for(typing, result, e, &key, &by, &needs, 8);
        if hit {
            return found;
        }
        self.generalize_plain(typing, e, x, result)
    }

    /// `result` with `x` put for `e` where `result` shows it as written, or,
    /// where it does not, where both reduced the same way show it.
    fn generalize_plain(&mut self, typing: &Ctx, e: &T, x: &str, result: &T) -> T {
        let by = T::var(x, e.span);
        let (found, hit) = abstract_term(result, e, &describe(e), &by);
        if hit {
            return found;
        }
        // Both reduced the same way: what `e` is where `result` has been
        // unfolded.
        let reduced = self.reduce_args(typing, result, &locals_of(typing, e), 8);
        let e = self.reduce_args(typing, e, &[], 8);
        let (found, hit) = abstract_term(&reduced, &e, &describe(&e), &by);
        if hit { found } else { result.clone() }
    }

    /// `t` with `by` put for `e` (written as `key`) where `t` shows it, and
    /// where a part of `t` shows it only once unfolded (`read(s, Cons(c, r))`
    /// is `step(s, kind(c), …)`), that part unfolded, `depth` unfoldings down.
    /// A part that does not show `e` either way is kept as written, and so is
    /// `e` itself: it is put for before what is around it is reduced.
    fn put_for(
        &mut self,
        typing: &Ctx,
        t: &T,
        e: &T,
        key: &str,
        by: &T,
        needs: &[String],
        depth: usize,
    ) -> (T, bool) {
        if describe(t) == key {
            return (by.clone(), true);
        }
        let sp = t.span;
        let (found, hit) = match &*t.kind {
            TermKind::App {
                function,
                arguments,
            } => {
                let mut hit = false;
                let arguments = arguments
                    .iter()
                    .map(|a| {
                        let (a, h) = self.put_for(typing, a, e, key, by, needs, depth);
                        hit |= h;
                        a
                    })
                    .collect();
                let found = T::new(
                    TermKind::App {
                        function: function.clone(),
                        arguments,
                    },
                    sp,
                );
                (found, hit)
            }
            TermKind::Pi {
                params,
                result,
                effects,
            } => {
                let (d, hd) = self.put_for(typing, &params[0].1, e, key, by, needs, depth);
                let shadow = params[0].0.as_deref().is_some_and(|n| occurs(e, n));
                let (r, hr) = if shadow {
                    ((**result).clone(), false)
                } else {
                    self.put_for(typing, result, e, key, by, needs, depth)
                };
                let mut params = params.clone();
                params[0].1 = d;
                let found = T::new(
                    TermKind::Pi {
                        params,
                        result: Box::new(r),
                        effects: effects.clone(),
                    },
                    sp,
                );
                (found, hd || hr)
            }
            TermKind::Lam {
                params,
                body,
                types,
            } if !params.iter().any(|n| occurs(e, n)) => {
                let (b, hit) = self.put_for(typing, body, e, key, by, needs, depth);
                let found = T::new(
                    TermKind::Lam {
                        params: params.clone(),
                        body: Box::new(b),
                        types: types.clone(),
                    },
                    sp,
                );
                (found, hit)
            }
            _ => (t.clone(), false),
        };
        if hit {
            return (found, true);
        }
        // Only an application unfolds; it is kept as written unless unfolding
        // shows `e`.
        if depth == 0 || !matches!(&*t.kind, TermKind::App { .. }) || !has_all(t, needs) {
            return (t.clone(), false);
        }
        let w = self.whnf(typing, t);
        if describe(&w) == describe(t) {
            return (t.clone(), false);
        }
        match self.put_for(typing, &w, e, key, by, needs, depth - 1) {
            (found, true) => (found, true),
            _ => (t.clone(), false),
        }
    }

    /// `t` reduced at its head, and then the arguments of what is left (a
    /// stuck eliminator has the term it is stuck on among them), `depth`
    /// levels down. Equal to `t` by conversion. A part without all of `needs`
    /// is kept as it is.
    fn reduce_args(&mut self, typing: &Ctx, t: &T, needs: &[String], depth: usize) -> T {
        if !has_all(t, needs) {
            return t.clone();
        }
        let t = self.whnf(typing, t);
        if depth == 0 {
            return t;
        }
        match &*t.kind {
            TermKind::App {
                function,
                arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .map(|a| match &*a.kind {
                        TermKind::App { .. } | TermKind::Lam { .. } => {
                            self.reduce_args(typing, a, needs, depth - 1)
                        }
                        _ => a.clone(),
                    })
                    .collect();
                T::new(
                    TermKind::App {
                        function: function.clone(),
                        arguments,
                    },
                    t.span,
                )
            }
            TermKind::Lam {
                params,
                body,
                types,
                ..
            } if matches!(&*body.kind, TermKind::App { .. } | TermKind::Lam { .. }) => {
                let body = self.reduce_args(typing, body, needs, depth - 1);
                T::new(
                    TermKind::Lam {
                        params: params.clone(),
                        body: Box::new(body),
                        types: types.clone(),
                    },
                    t.span,
                )
            }
            _ => t,
        }
    }

    /// `Δ ⊢ G from …`: the goal as written is the one the match computes,
    /// up to conversion.
    fn check_arm_goal(
        &mut self,
        local: &[(String, T)],
        written: &T,
        computed: Option<&T>,
    ) -> Result<(), Diagnostic> {
        let Some(computed) = computed else {
            return Ok(());
        };
        let mut typing: Ctx = self.defining.clone();
        typing.extend(local.iter().cloned());
        let w = self.shape_type(written, local)?;
        let w = self.elab(&typing, &w, None)?;
        if self.conv(&typing, &w, computed) {
            return Ok(());
        }
        err(
            msg!(
                "kernel-match-arm-goal",
                computed = describe(computed),
                written = describe(&w)
            ),
            written.span,
        )
    }

    /// The type of an arm's body: its goal under the later parameters, which
    /// the arm binds by their own names.
    fn under_after(&mut self, mut goal: T, after: &[(String, T)]) -> Option<T> {
        for (n, _) in after {
            let TermKind::Pi { params, result, .. } = &*goal.kind else {
                return None;
            };
            let bound = params[0].0.clone().unwrap_or_else(|| "_".into());
            goal = if bound == *n || bound == "_" {
                (**result).clone()
            } else {
                let result = (**result).clone();
                self.subst(&result, &bound, &T::var(n, result.span))
            };
        }
        Some(goal)
    }
}

/// A recursive field of the matched value, or a function-typed one applied to
/// all its arguments (`k(u, s)`), with those arguments.
fn smaller_field<'a>(t: &'a T, smaller: &Smaller) -> Option<(&'a String, &'a [T])> {
    let (v, args): (&String, &[T]) = match &*t.kind {
        TermKind::Var(v) => (v, &[]),
        TermKind::App {
            function,
            arguments,
        } => match &*function.kind {
            TermKind::Var(v) => (v, arguments),
            _ => return None,
        },
        _ => return None,
    };
    smaller
        .get(v)
        .is_some_and(|(_, _, arity)| *arity == args.len())
        .then_some((v, args))
}

/// The local variables free in `e`: what a part must have to show `e`, as
/// unfolding does not bring one in.
fn locals_of(typing: &Ctx, e: &T) -> Vec<String> {
    super::free_vars(e)
        .into_iter()
        .filter(|n| typing.iter().any(|(m, _)| m == n))
        .collect()
}

fn has_all(t: &T, names: &[String]) -> bool {
    if names.is_empty() {
        return true;
    }
    let free = super::free_vars(t);
    names.iter().all(|n| free.contains(n))
}

/// In a generalized goal, a match on the same term with its own equation
/// (`R::rec(t => (x = t) -> M, …, x, Refl(T, x))`, from unfolding a call that
/// matches on `e` with `eqn`) has that equation as `e = t` again, and is
/// given the outer equation `h: e = x` for it in place of `Refl(T, x)`. Putting
/// `x` for `e` there as well makes the inner arms have `x = c` where what is
/// written in them needs `e = c`. Once `h` is `Refl(T, e)` and `x` is `e`, the
/// goal is the one before: this changes only how the arms see it.
fn link_equations(t: &T, e: &T, x: &str, h: &str) -> T {
    let sp = t.span;
    let is_x = |t: &T| matches!(&*t.kind, TermKind::Var(v) if v == x);
    match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } => {
            let mut arguments: Vec<T> = arguments
                .iter()
                .map(|a| link_equations(a, e, x, h))
                .collect();
            let refl_x = arguments.last().is_some_and(|a| {
                matches!(&*a.kind, TermKind::App { function, arguments }
                    if matches!(&*function.kind, TermKind::Var(r) if r == "Refl")
                        && arguments.len() == 2
                        && is_x(&arguments[1]))
            });
            if refl_x && arguments.len() >= 2 {
                let motive = &arguments[0];
                if let TermKind::Lam {
                    params,
                    body,
                    types,
                } = &*motive.kind
                    && params.len() == 1
                    && let TermKind::Pi {
                        params: pis,
                        result,
                        effects,
                    } = &*body.kind
                    && let TermKind::App {
                        function: eq,
                        arguments: eq_args,
                    } = &*pis[0].1.kind
                    && matches!(&*eq.kind, TermKind::Var(n) if n == "Eq")
                    && eq_args.len() == 3
                    && is_x(&eq_args[1])
                    && matches!(&*eq_args[2].kind, TermKind::Var(v) if *v == params[0])
                {
                    let mut pis = pis.clone();
                    pis[0].1 = eq_ty(&eq_args[0], e, &eq_args[2]);
                    let body = T::new(
                        TermKind::Pi {
                            params: pis,
                            result: result.clone(),
                            effects: effects.clone(),
                        },
                        body.span,
                    );
                    arguments[0] = T::new(
                        TermKind::Lam {
                            params: params.clone(),
                            body: Box::new(body),
                            types: types.clone(),
                        },
                        motive.span,
                    );
                    let last = arguments.len() - 1;
                    arguments[last] = T::var(h, arguments[last].span);
                }
            }
            T::new(
                TermKind::App {
                    function: Box::new(link_equations(function, e, x, h)),
                    arguments,
                },
                sp,
            )
        }
        TermKind::Pi {
            params,
            result,
            effects,
        } => {
            let mut params = params.clone();
            for p in &mut params {
                p.1 = link_equations(&p.1, e, x, h);
            }
            T::new(
                TermKind::Pi {
                    params,
                    result: Box::new(link_equations(result, e, x, h)),
                    effects: effects.clone(),
                },
                sp,
            )
        }
        TermKind::Lam {
            params,
            body,
            types,
        } if !params.iter().any(|n| n == h || n == x) => T::new(
            TermKind::Lam {
                params: params.clone(),
                body: Box::new(link_equations(body, e, x, h)),
                types: types.clone(),
            },
            sp,
        ),
        _ => t.clone(),
    }
}

/// Replaces subterms written as `key` (the text of `of`) with `by` and reports
/// whether any were found. A binder of a variable mentioned by `of` prevents
/// replacement in its body.
fn abstract_term(t: &T, of: &T, key: &str, by: &T) -> (T, bool) {
    let sp = t.span;
    match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } => {
            if describe(t) == key {
                return (by.clone(), true);
            }
            let (function, mut hit) = abstract_term(function, of, key, by);
            let arguments = arguments
                .iter()
                .map(|a| {
                    let (a, h) = abstract_term(a, of, key, by);
                    hit |= h;
                    a
                })
                .collect();
            (
                T::new(
                    TermKind::App {
                        function: Box::new(function),
                        arguments,
                    },
                    sp,
                ),
                hit,
            )
        }
        TermKind::Pi {
            params,
            result,
            effects,
        } => {
            let (d, hd) = abstract_term(&params[0].1, of, key, by);
            let shadow = params[0].0.as_deref().is_some_and(|n| occurs(of, n));
            let (r, hr) = if shadow {
                ((**result).clone(), false)
            } else {
                abstract_term(result, of, key, by)
            };
            let mut params = params.clone();
            params[0].1 = d;
            (
                T::new(
                    TermKind::Pi {
                        params,
                        result: Box::new(r),
                        effects: effects.clone(),
                    },
                    sp,
                ),
                hd || hr,
            )
        }
        TermKind::Lam {
            params,
            body,
            types,
        } => {
            if params.iter().any(|n| occurs(of, n)) {
                return (t.clone(), false);
            }
            let (b, hit) = abstract_term(body, of, key, by);
            (
                T::new(
                    TermKind::Lam {
                        params: params.clone(),
                        body: Box::new(b),
                        types: types.clone(),
                    },
                    sp,
                ),
                hit,
            )
        }
        _ => (t.clone(), false),
    }
}

/// `t` without the arguments it applies a `match` to: `(match …)(a⃗)` is the
/// match and `a⃗`, and so is `(match …)(a₁)(a₂)`, the same application.
fn peel_applied(t: &SurfaceTerm) -> (Vec<SurfaceTerm>, &SurfaceTerm) {
    if let TermKind::App {
        function,
        arguments,
    } = &*t.kind
    {
        let (mut first, inner) = peel_applied(function);
        if matches!(&*inner.kind, TermKind::Match { .. }) {
            first.extend(arguments.iter().cloned());
            return (first, inner);
        }
    }
    (Vec::new(), t)
}

/// `t` with each call of a function being defined whose argument at its
/// matched parameter is `cval`, the constructor of an arm on `x` written out
/// from the arm's fields, made a call on `x`. Under a binder of `x` or of a
/// field, `cval` is another value and the call stays.
fn rebuilt_as(t: &T, fns: &HashMap<String, FnInfo>, cval: &T, x: &str) -> T {
    let sp = t.span;
    let mut names = super::free_vars(cval);
    names.push(x.to_string());
    match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } => {
            let mut arguments: Vec<T> = arguments
                .iter()
                .map(|a| rebuilt_as(a, fns, cval, x))
                .collect();
            if let TermKind::Var(n) = &*function.kind
                && let Some(info) = fns.get(n)
                && !info.tail
            {
                let at = if arguments.len() + info.implicit == info.params.len() {
                    info.xpos.checked_sub(info.implicit)
                } else {
                    Some(info.xpos)
                };
                if let Some(a) = at.and_then(|at| arguments.get_mut(at))
                    && same_term(a, cval)
                {
                    *a = T::var(x, a.span);
                }
            }
            T::new(
                TermKind::App {
                    function: Box::new(rebuilt_as(function, fns, cval, x)),
                    arguments,
                },
                sp,
            )
        }
        TermKind::Lam {
            params,
            body,
            types,
        } if !params.iter().any(|p| names.contains(p)) => T::new(
            TermKind::Lam {
                params: params.clone(),
                body: Box::new(rebuilt_as(body, fns, cval, x)),
                types: types.clone(),
            },
            sp,
        ),
        _ => t.clone(),
    }
}

fn same_term(a: &T, b: &T) -> bool {
    match (&*a.kind, &*b.kind) {
        (TermKind::Var(m), TermKind::Var(n)) => m == n,
        (
            TermKind::App {
                function: f,
                arguments: xs,
            },
            TermKind::App {
                function: g,
                arguments: ys,
            },
        ) => {
            same_term(f, g)
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|(x, y)| same_term(x, y))
        }
        _ => false,
    }
}

fn leaves_generics_out(t: &T, fns: &HashMap<String, FnInfo>) -> bool {
    let mut found = false;
    crate::surface::walk::term(&mut t.clone(), &mut |s: &mut T| {
        if let TermKind::App {
            function,
            arguments,
        } = &*s.kind
            && let TermKind::Var(n) = &*function.kind
            && let Some(info) = fns.get(n)
            && info.implicit > 0
            && arguments.len() + info.implicit == info.params.len()
        {
            found = true;
        }
    });
    found
}

fn function_name(t: &T) -> &str {
    match &*t.kind {
        TermKind::Var(n) => n,
        _ => "",
    }
}

fn is_recursion(info: &FnInfo, arguments: &[T], smaller: &Smaller) -> bool {
    let at = if arguments.len() + info.implicit == info.params.len() {
        info.xpos.checked_sub(info.implicit)
    } else {
        Some(info.xpos)
    };
    at.and_then(|at| arguments.get(at))
        .is_some_and(|a| smaller_field(a, smaller).is_some_and(|(v, _)| smaller[v].1 == info.fam))
}

/// What to do about a call that is not structural: the next step, from the
/// arguments of the call. A part of the matched value passed for another
/// parameter is the usual slip when the parameters are reordered, and the
/// call with the two swapped is shown; a parameter that changes in the call is
/// what `decreasing_by` can name; a call that changes nothing makes no
/// progress, and no choice of parameter fixes that.
fn not_smaller_hint(
    info: &FnInfo,
    function: &T,
    arguments: &[T],
    left_out: usize,
    smaller: &Smaller,
    sp: Span,
) -> Message {
    let x = &info.params[info.xpos];
    let swapped = (0..arguments.len()).filter(|&q| q != info.xpos).find(|&q| {
        smaller_field(&arguments[q], smaller).is_some_and(|(v, _)| smaller[v].1 == info.fam)
    });
    if let Some(q) = swapped {
        let mut moved = arguments.to_vec();
        moved.swap(info.xpos, q);
        let call = T::new(
            TermKind::App {
                function: function.clone().into(),
                arguments: moved[left_out..].to_vec(),
            },
            sp,
        );
        return msg!(
            "kernel-rec-hint-swapped",
            part = describe(&arguments[q]),
            param = x,
            other = &info.params[q],
            suggestion = describe(&call)
        );
    }
    let changed: Vec<&String> = (0..arguments.len())
        .filter(|&q| q != info.xpos)
        .filter(|&q| {
            // A variable that is not the parameter's own: a part bound by a
            // pattern on that parameter, which a structural recursion on it
            // takes. An argument that builds a value (`Succ(acc)`) grows.
            matches!(&*arguments[q].kind, TermKind::Var(v) if *v != info.params[q])
        })
        .map(|q| &info.params[q])
        .collect();
    match changed.as_slice() {
        [] if passes_unchanged(&arguments[info.xpos], x) => {
            msg!("kernel-rec-hint-stuck", param = x)
        }
        [] => msg!("kernel-rec-hint-part", param = x),
        [one] => msg!("kernel-rec-hint-by-one", param = *one),
        many => msg!(
            "kernel-rec-hint-by-many",
            params = many
                .iter()
                .map(|n| format!("`{n}`"))
                .collect::<Vec<_>>()
                .join(", "),
            first = many[0]
        ),
    }
}

/// Calls of the functions being defined on a field of the matched value
/// become that field's induction hypothesis.
fn replace_calls(
    t: &T,
    fns: &HashMap<String, FnInfo>,
    smaller: &Smaller,
    rebound: &[String],
) -> Result<T, Diagnostic> {
    replace_in(t, fns, smaller, false, rebound)
}

/// `replace_calls`, or with `partial` only the calls on the variables of
/// `smaller`, leaving the others to the function's own arms.
fn replace_in(
    t: &T,
    fns: &HashMap<String, FnInfo>,
    smaller: &Smaller,
    partial: bool,
    rebound: &[String],
) -> Result<T, Diagnostic> {
    let sp = t.span;
    Ok(match &*t.kind {
        TermKind::Var(n) if !partial && fns.get(n).is_some_and(|i| !i.alias) => {
            return err(msg!("kernel-rec-without-call", name = n), sp);
        }
        // Arguments past the declared ones apply the call's result, as in a
        // call that is not recursive: `f(t, h)` is `f(t)(h)`.
        TermKind::App {
            function,
            arguments,
        } if matches!(&*function.kind, TermKind::Var(n)
            if fns.get(n).is_some_and(|i| arguments.len() > i.params.len())) =>
        {
            let k = fns[function_name(function)].params.len();
            let call = T::new(
                TermKind::App {
                    function: function.clone(),
                    arguments: arguments[..k].to_vec(),
                },
                sp,
            );
            replace_in(
                &app(call, arguments[k..].to_vec()),
                fns,
                smaller,
                partial,
                rebound,
            )?
        }
        TermKind::App {
            function,
            arguments,
        } if matches!(&*function.kind, TermKind::Var(n) if fns.contains_key(n))
            && !((partial || matches!(&*function.kind, TermKind::Var(n) if fns[n].alias))
                && !is_recursion(&fns[function_name(function)], arguments, smaller)) =>
        {
            let TermKind::Var(n) = &*function.kind else {
                unreachable!()
            };
            let info = &fns[n];
            let shown = describe(t);
            // A call that leaves the generics out passes them unchanged.
            let left_out = if arguments.len() + info.implicit == info.params.len() {
                info.implicit
            } else {
                0
            };
            let arguments: &[T] = if arguments.len() + info.implicit == info.params.len() {
                &info.params[..info.implicit]
                    .iter()
                    .map(|p| T::var(p, sp))
                    .chain(arguments.iter().cloned())
                    .collect::<Vec<_>>()
            } else {
                arguments
            };
            if arguments.len() != info.params.len() {
                return err(
                    msg!(
                        "kernel-rec-arity",
                        name = &shown,
                        given = arguments.len(),
                        expected = info.params.len()
                    ),
                    sp,
                );
            }
            let x = &info.params[info.xpos];
            if !smaller_field(&arguments[info.xpos], smaller)
                .is_some_and(|(v, _)| smaller[v].1 == info.fam)
            {
                // The matched value has parts of another family of its group,
                // as `h: Tree` in `Cons(h, r)` of a `List(Tree)`: those are
                // matched by a function on that family, in one block with this.
                let mut others: Vec<&String> = smaller
                    .iter()
                    .filter(|(_, (_, f, _))| *f != info.fam)
                    .map(|(v, _)| v)
                    .collect();
                others.sort();
                let argument = describe(&arguments[info.xpos]);
                let hint = not_smaller_hint(info, function, arguments, left_out, smaller, sp);
                let message = match others.first() {
                    Some(v) => msg!(
                        "kernel-rec-not-smaller-group",
                        name = &shown,
                        function = n,
                        param = x,
                        argument = argument,
                        part = *v,
                        hint = hint
                    ),
                    None => msg!(
                        "kernel-rec-not-smaller",
                        name = &shown,
                        function = n,
                        param = x,
                        argument = argument,
                        hint = hint
                    ),
                };
                return err(message, sp);
            }
            let changed: Vec<&String> = (0..info.xpos)
                .filter(|&p| {
                    let n = &info.params[p];
                    // The parameter's own name passes it unchanged only where
                    // nothing binds that name again: a variable of the arm, or
                    // a parameter this function's motive generalizes, holds
                    // another value under the same name.
                    !(passes_unchanged(&arguments[p], n) && !rebound.contains(n))
                        && !info.idx_params.contains(n)
                        && !info.pre.contains(n)
                })
                .map(|p| &info.params[p])
                .collect();
            let changed_later: Vec<String> = (info.xpos + 1..info.params.len())
                .filter(|&p| {
                    let n = &info.params[p];
                    !info.post.contains(n)
                        && !(passes_unchanged(&arguments[p], n) && !rebound.contains(n))
                })
                .map(|p| info.params[p].clone())
                .collect();
            if !changed_later.is_empty() {
                // Compiled again with them generalized.
                info.wants.borrow_mut().extend(changed_later);
                return err(msg!("kernel-rec-changes-later", name = &shown), sp);
            }
            if !changed.is_empty() {
                if changed.iter().all(|n| info.movable.contains(n)) {
                    // Compiled again with them generalized.
                    info.wants
                        .borrow_mut()
                        .extend(changed.iter().map(|n| (*n).clone()));
                    return err(msg!("kernel-rec-changes-earlier", name = &shown), sp);
                }
                let fixed: Vec<String> = changed
                    .iter()
                    .filter(|n| !info.movable.contains(n))
                    .map(|n| format!("`{n}`"))
                    .collect();
                let id = if fixed.len() == 1 {
                    "kernel-rec-fixed-one"
                } else {
                    "kernel-rec-fixed-many"
                };
                return err(
                    msg!(id, name = &shown, param = x, fixed = fixed.join(", ")),
                    sp,
                );
            }
            let (v, field_args) = smaller_field(&arguments[info.xpos], smaller)
                .expect("checked as a call on a recursive field");
            // A function-typed field is called on its arguments, which its
            // induction hypothesis takes too.
            let mut rest: Vec<T> = field_args
                .iter()
                .map(|a| replace_in(a, fns, smaller, partial, rebound))
                .collect::<Result<_, _>>()?;
            rest.extend(
                info.general
                    .iter()
                    .map(|(ty, arg)| app(T::var("Refl", sp), vec![ty.clone(), arg.clone()])),
            );
            for p in &info.pre {
                let at = info.params.iter().position(|n| n == p).unwrap();
                rest.push(replace_in(&arguments[at], fns, smaller, partial, rebound)?);
            }
            for (p, a) in arguments.iter().enumerate().skip(info.xpos + 1) {
                if info.post.contains(&info.params[p]) {
                    rest.push(replace_in(a, fns, smaller, partial, rebound)?);
                }
            }
            let value = app(smaller[v].0.clone(), rest);
            if info.tail {
                let mut marked = vec![value];
                for a in arguments {
                    marked.push(replace_in(a, fns, smaller, partial, rebound)?);
                }
                app(T::var(&format!("{TAIL}{n}"), sp), marked)
            } else {
                value
            }
        }
        TermKind::App {
            function,
            arguments,
        } => T::new(
            TermKind::App {
                function: Box::new(replace_in(function, fns, smaller, partial, rebound)?),
                arguments: arguments
                    .iter()
                    .map(|a| replace_in(a, fns, smaller, partial, rebound))
                    .collect::<Result<_, _>>()?,
            },
            sp,
        ),
        TermKind::Lam {
            params: ps,
            body,
            types,
        } => {
            let mut inner = rebound.to_vec();
            inner.extend(ps.iter().cloned());
            T::new(
                TermKind::Lam {
                    params: ps.clone(),
                    body: Box::new(replace_in(body, fns, smaller, partial, &inner)?),
                    types: types.clone(),
                },
                sp,
            )
        }
        // A function defined into `Prop` calls itself under a `∀` or an arrow.
        TermKind::Pi {
            params,
            result,
            effects,
        } => {
            let mut params = params.clone();
            let mut inner = rebound.to_vec();
            for (n, d) in &mut params {
                *d = replace_in(d, fns, smaller, partial, &inner)?;
                inner.extend(n.iter().cloned());
            }
            T::new(
                TermKind::Pi {
                    params,
                    result: Box::new(replace_in(result, fns, smaller, partial, &inner)?),
                    effects: effects.clone(),
                },
                sp,
            )
        }
        _ => t.clone(),
    })
}

impl Kernel {
    /// The body of a function with `decreasing_by y`: a match on `y` with one
    /// arm per constructor, each the body as written with `y` that
    /// constructor, so that a call on one of its fields is the recursion. A
    /// match on `y` inside the body takes the arm of that constructor. A body
    /// that is a match on `y` already is as written.
    pub(super) fn structural_on(
        &mut self,
        params: &[(String, T)],
        body: &T,
        y: &T,
    ) -> Result<T, Diagnostic> {
        let sp = y.span;
        let TermKind::Var(y) = &*y.kind else {
            return err(msg!("kernel-decreasing-structural"), sp);
        };
        let Some(pos) = params.iter().position(|(n, _)| n == y) else {
            return err(msg!("kernel-decreasing-not-param", name = y), sp);
        };
        if let TermKind::Match { scrutinee, .. } = &*peel_applied(body).1.kind
            && matches!(&*scrutinee.kind, TermKind::Var(v) if v == y)
        {
            return Ok(body.clone());
        }
        let yty = self.whnf_pair(&params[..pos].to_vec(), &params[pos].1);
        let (family, fargs) = match &*yty.kind {
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(i) => (i.clone(), arguments.clone()),
                _ => (String::new(), Vec::new()),
            },
            TermKind::Var(i) => (i.clone(), Vec::new()),
            _ => (String::new(), Vec::new()),
        };
        let (family, fargs) = match self.nested_member(&family, &fargs) {
            Some(member) => (member, Vec::new()),
            None => (family, fargs),
        };
        let Some(ind) = self.inds.get(&family).cloned() else {
            return err(msg!("kernel-decreasing-not-inductive", name = y), sp);
        };
        let pargs = fargs[..ind.params.len().min(fargs.len())].to_vec();
        let mut arms = Vec::new();
        for c in &ind.ctors {
            let names: Vec<String> = c.args.iter().map(|(n, _)| self.fresh_name(n)).collect();
            let (_, mut to) = self.ctor_binding(&ind, &pargs);
            to.extend(names.iter().map(|n| T::var(n, sp)));
            let cval = app(T::var(&c.name, sp), to);
            let known = self.known_ctor(body, y, &c.name, &names)?;
            arms.push(crate::surface::MatchArm {
                pattern: Pattern::Ctor {
                    name: c.name.clone(),
                    args: names.iter().map(|n| Pattern::Bind(n.clone())).collect(),
                },
                guard: None,
                goal: None,
                body: self.subst(&known, y, &cval),
            });
        }
        Ok(T::new(
            TermKind::Match {
                scrutinee: Box::new(T::var(y, sp)),
                result: None,
                binder: None,
                arms,
            },
            body.span,
        ))
    }

    /// `t` where each match on `y` is the arm of constructor `c`, whose fields
    /// are the variables `names`.
    fn known_ctor(&mut self, t: &T, y: &str, c: &str, names: &[String]) -> Result<T, Diagnostic> {
        let mut t = t.clone();
        let mut failed = None;
        crate::surface::walk::term(&mut t, &mut |u: &mut T| {
            if failed.is_some() {
                return;
            }
            let TermKind::Match {
                scrutinee,
                binder: None,
                arms,
                result,
            } = &*u.kind
            else {
                return;
            };
            if !matches!(&*scrutinee.kind, TermKind::Var(v) if v == y) {
                return;
            }
            let arms = match self.nest_arms(arms) {
                Ok(a) => a,
                Err(d) => {
                    failed = Some(d);
                    return;
                }
            };
            let picked = arms.iter().find_map(|a| match &a.pattern {
                Pattern::Ctor { name, args } if name == c => {
                    let args = self.full_fields(name, args.clone());
                    let mut body = a.body.clone();
                    for (p, n) in args.iter().zip(names) {
                        if let Pattern::Bind(b) = p {
                            body = self.subst(&body, b, &T::var(n, u.span));
                        }
                    }
                    Some(body)
                }
                Pattern::Bind(name) if name == c => Some(a.body.clone()),
                Pattern::Wild => Some(a.body.clone()),
                Pattern::Bind(v) if !self.ctors.contains_key(v) => {
                    Some(self.subst(&a.body, v, &T::var(y, u.span)))
                }
                _ => None,
            });
            match picked {
                // The result type written stays on the arm: `y` is the
                // constructor there.
                Some(b) => match result {
                    Some(r) => *u = app(T::var("the", u.span), vec![(**r).clone(), b]),
                    None => *u = b,
                },
                None => {
                    failed = Some(Diagnostic::new(
                        msg!("kernel-match-missing-case", name = c),
                        Some(u.span),
                    ))
                }
            }
        });
        match failed {
            Some(d) => Err(d),
            None => Ok(t),
        }
    }

    /// Applies each recursive call's value (`tail'f(value, a⃗)`, from
    /// `replace_in`) to the arguments `f`'s match is applied to, at the
    /// call's arguments `a⃗`.
    fn fill_tails(&mut self, t: &T, filled: &HashMap<String, (Vec<String>, Vec<T>)>) -> T {
        let sp = t.span;
        match &*t.kind {
            TermKind::App {
                function,
                arguments,
            } => {
                let arguments: Vec<T> = arguments
                    .iter()
                    .map(|a| self.fill_tails(a, filled))
                    .collect();
                if let TermKind::Var(n) = &*function.kind
                    && let Some(name) = n.strip_prefix(TAIL)
                    && let Some((params, tail)) = filled.get(name)
                {
                    let tail = tail
                        .iter()
                        .map(|a| self.instantiate(a, params, &arguments[1..]))
                        .collect();
                    return app(arguments[0].clone(), tail);
                }
                let function = self.fill_tails(function, filled);
                T::new(
                    TermKind::App {
                        function: Box::new(function),
                        arguments,
                    },
                    sp,
                )
            }
            TermKind::Lam {
                params,
                body,
                types,
            } => T::new(
                TermKind::Lam {
                    params: params.clone(),
                    body: Box::new(self.fill_tails(body, filled)),
                    types: types.clone(),
                },
                sp,
            ),
            TermKind::Pi {
                params,
                result,
                effects,
            } => {
                let mut params = params.clone();
                for (_, d) in &mut params {
                    *d = self.fill_tails(d, filled);
                }
                T::new(
                    TermKind::Pi {
                        params,
                        result: Box::new(self.fill_tails(result, filled)),
                        effects: effects.clone(),
                    },
                    sp,
                )
            }
            _ => t.clone(),
        }
    }
}

impl Kernel {
    /// The minor premise of constructor `c` when the matched family has an
    /// index that is not a variable: its fields, induction hypotheses and
    /// one equation per such index, then the later parameters. The
    /// equations are unified (injectivity and disjointness of constructors
    /// by no-confusion); a field they fix is replaced in the arm, whose body
    /// is transported back by `Eq::rec`/`Eq::ind`.
    /// Whether a function calls itself on a variable that is not a field of
    /// the matched value, as the arms name them: a part deeper down, reached
    /// by a match (or a nested pattern) in the arm.
    /// Whether a recursion on `specs` reaches parts deeper than the fields,
    /// and whether it does so by a constructor rebuilt from a part's fields.
    fn recurs_deeper(&self, specs: &[FnSpec], headers: &[Header], members: usize) -> (bool, bool) {
        let [spec] = specs else { return (false, false) };
        let Some(name) = spec.name else {
            return (false, false);
        };
        let h = &headers[0];
        if members != 1 || !h.general.is_empty() {
            return (false, false);
        }
        let at = h.xpos;
        let mut fields: Vec<String> = Vec::new();
        for arm in h.arms {
            if let Pattern::Ctor { args, .. } = &arm.pattern {
                for p in args {
                    if let Pattern::Bind(n) = p {
                        fields.push(n.clone());
                    }
                }
            }
        }
        let params: Vec<&String> = spec.params.iter().map(|(n, _)| n).collect();
        let full = spec.params.len();
        let implicit = spec.implicit;
        let mut found = false;
        let mut rebuilt = false;
        for arm in h.arms {
            crate::surface::walk::term(&mut arm.body.clone(), &mut |t: &mut T| {
                if let TermKind::App {
                    function,
                    arguments,
                } = &*t.kind
                    && matches!(&*function.kind, TermKind::Var(f) if f == name)
                {
                    let at = if arguments.len() + implicit == full {
                        at.checked_sub(implicit)
                    } else {
                        Some(at)
                    };
                    match at.and_then(|a| arguments.get(a)).map(|a| &*a.kind) {
                        Some(TermKind::Var(v)) if !fields.contains(v) && !params.contains(&v) => {
                            found = true;
                        }
                        // A constructor rebuilt from the fields of a part.
                        Some(TermKind::App { function, .. }) if matches!(&*function.kind, TermKind::Var(c) if self.inds.values().any(|i| i.ctors.iter().any(|k| k.name == *c))) =>
                        {
                            found = true;
                            rebuilt = true;
                        }
                        _ => {}
                    }
                }
            });
        }
        (found, rebuilt)
    }

    /// `below(t)` as a function of the indices and the value: for each
    /// recursive field `r` of `t`'s constructor, `M(r) ∧ below(r)`, ending in
    /// `True` (`BelowPair` and `Unit` for data).
    fn below_fn(&mut self, spec: &FnSpec, h: &Header) -> Result<T, Diagnostic> {
        let sp = h.span;
        let ind = self.inds[&h.family].clone();
        let elim = format!("{}::rec", h.family);
        if !self.recs.contains_key(&elim) {
            return err(
                msg!(
                    "kernel-rec-deep-elimination",
                    name = &h.x,
                    family = &h.family
                ),
                sp,
            );
        }
        let sort = if h.is_prop {
            T::var("Prop", sp)
        } else {
            let whole = pi_all(&h.after, spec.result.clone());
            if self.expect_type(&spec.params, &whole)? != Sort::ty(0) {
                return err(msg!("kernel-rec-deep-result"), sp);
            }
            T::var("Type", sp)
        };
        let n = ind.indices;
        let mut minors = Vec::new();
        for c in &ind.ctors {
            let names: Vec<String> = c.args.iter().map(|_| self.fresh_name("f")).collect();
            let ihs: Vec<String> = c.recs.iter().map(|_| self.fresh_name("b")).collect();
            let (mut from, mut to) = self.ctor_binding(&ind, &h.pargs);
            for ((an, _), name) in c.args.iter().zip(&names) {
                from.push(an.clone());
                to.push(T::var(name, sp));
            }
            let mut ty = unit(h.is_prop, sp).0;
            for (r, ih) in c.recs.iter().zip(&ihs).rev() {
                if !r.ys.is_empty() {
                    let below = T::var(ih, sp);
                    let (entry, ..) =
                        self.function_entry(r, &from, &to, &names[r.arg], &h.motive, &below);
                    ty = pair_ty(h.is_prop, &entry, &ty);
                    continue;
                }
                let mut at: Vec<T> = r
                    .idx
                    .iter()
                    .map(|t| self.instantiate(t, &from, &to))
                    .collect();
                at.push(T::var(&names[r.arg], sp));
                let entry = pair_ty(h.is_prop, &app(h.motive.clone(), at), &T::var(ih, sp));
                ty = pair_ty(h.is_prop, &entry, &ty);
            }
            minors.push(lams(&names, lams(&ihs, ty)));
        }
        let vars: Vec<String> = (0..n)
            .map(|k| format!("i'{k}"))
            .chain(["t'".into()])
            .collect();
        let mut args = h.pargs.clone();
        args.push(lams(&vars, sort));
        args.extend(minors);
        args.extend(vars.iter().map(|v| T::var(v, sp)));
        Ok(lams(&vars, app(T::var(&elim, sp), args)))
    }

    /// In an arm of a match on `x`, a variable whose parts a recursion
    /// reaches: for each recursive field, `(field, below var, path, value)`,
    /// where the value is the function's value at the field.
    fn parts_of(
        &mut self,
        x: &str,
        c: &Ctor,
        names: &[String],
        local: &[(String, T)],
    ) -> Vec<(String, String, Vec<bool>, T)> {
        let Some(scope) = &self.deep else {
            return Vec::new();
        };
        let prop = scope.prop;
        let Some((_, v, path)) = scope.vars.iter().rev().find(|(f, ..)| f == x).cloned() else {
            return Vec::new();
        };
        let Some((_, mut ty)) = local.iter().rev().find(|(n, _)| *n == v).cloned() else {
            return Vec::new();
        };
        let sp = ty.span;
        let mut term = T::var(&v, sp);
        for first in &path {
            let Some((a, b)) = self.pair_parts(local, &ty, prop) else {
                return Vec::new();
            };
            term = proj(prop, &a, &b, term, *first);
            ty = if *first { a } else { b };
        }
        let mut out = Vec::new();
        let mut path = path;
        for r in &c.recs {
            let Some((entry, rest)) = self.pair_parts(local, &ty, prop) else {
                return out;
            };
            if !r.ys.is_empty() {
                // A function-typed field has no parts further down.
                term = proj(prop, &entry, &rest, term, false);
                ty = rest;
                path.push(false);
                continue;
            }
            let Some((m, b)) = self.pair_parts(local, &entry, prop) else {
                return out;
            };
            let at = proj(prop, &entry, &rest, term.clone(), true);
            let value = proj(prop, &m, &b, at, true);
            let mut field_path = path.clone();
            field_path.extend([true, false]);
            out.push((names[r.arg].clone(), v.clone(), field_path, value));
            term = proj(prop, &entry, &rest, term, false);
            ty = rest;
            path.push(false);
        }
        out
    }

    /// The entry of `below` for a function-typed recursive field `field`:
    /// `∀ y⃗. M(field(y⃗))`, with the fresh `y⃗`, `M(field(y⃗))` and
    /// `below(field(y⃗))`.
    fn function_entry(
        &mut self,
        r: &super::inductive::Rec,
        from: &[String],
        to: &[T],
        field: &str,
        motive: &T,
        below: &T,
    ) -> (T, Vec<String>, T, T) {
        let sp = motive.span;
        let (mut from, mut to) = (from.to_vec(), to.to_vec());
        let mut ys = Vec::new();
        let mut tys = Vec::new();
        for (n, t) in &r.ys {
            let y = self.fresh_name(n);
            tys.push(self.instantiate(t, &from, &to));
            from.push(n.clone());
            to.push(T::var(&y, sp));
            ys.push(y);
        }
        let mut at: Vec<T> = r
            .idx
            .iter()
            .map(|t| self.instantiate(t, &from, &to))
            .collect();
        at.push(app(
            T::var(field, sp),
            ys.iter().map(|y| T::var(y, sp)).collect(),
        ));
        let m = app(motive.clone(), at.clone());
        let b = app(below.clone(), at);
        let entry = ys
            .iter()
            .zip(&tys)
            .rev()
            .fold(m.clone(), |acc, (y, t)| pi(y, t.clone(), acc));
        (entry, ys, m, b)
    }

    /// The parts a recursion reaches from the variables in scope, each with
    /// the function's value at it, projected from its `below` variable with
    /// the types `local` gives it.
    fn reached_values(&mut self, local: &[(String, T)]) -> Vec<(String, T)> {
        let Some(scope) = &self.deep else {
            return Vec::new();
        };
        let prop = scope.prop;
        let mut out: Vec<(String, T)> = Vec::new();
        for (f, a) in &scope.at {
            if local.iter().any(|(n, _)| n == a) {
                out.push((f.clone(), T::var(a, local[0].1.span)));
            }
        }
        for (f, v, path) in scope.vars.clone().into_iter().rev() {
            if out.iter().any(|(g, _)| *g == f) {
                continue;
            }
            // The path ends at `below(f)`, the second half of `M(f) ∧ below(f)`.
            let Some((false, path)) = path.split_last() else {
                continue;
            };
            let Some((_, mut ty)) = local.iter().rev().find(|(n, _)| *n == v).cloned() else {
                continue;
            };
            let mut term = Some(T::var(&v, ty.span));
            for first in path.iter().chain([&true]) {
                let Some((a, b)) = self.pair_parts(local, &ty, prop) else {
                    term = None;
                    break;
                };
                term = term.map(|t| proj(prop, &a, &b, t, *first));
                ty = if *first { a } else { b };
            }
            if let Some(term) = term {
                out.push((f, term));
            }
        }
        out
    }

    /// `(A, B)` of `A ∧ B` (or `BelowPair(A, B)`), up to reduction.
    fn pair_parts(&mut self, local: &[(String, T)], ty: &T, prop: bool) -> Option<(T, T)> {
        let w = self.whnf_pair(&local.to_vec(), ty);
        let f = if prop { "And" } else { "BelowPair" };
        match &*w.kind {
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(n) if n == f) && arguments.len() == 2 => {
                Some((arguments[0].clone(), arguments[1].clone()))
            }
            _ => None,
        }
    }

    /// An arm whose recursive call leaves the generics out, with them
    /// written: they are inferred from the other arguments, and the call is
    /// checked with what they are.
    fn with_generics(
        &mut self,
        t: &T,
        local: &[(String, T)],
        goal: Option<&T>,
        fns: &HashMap<String, FnInfo>,
    ) -> T {
        if !leaves_generics_out(t, fns) {
            return t.clone();
        }
        let mut typing: Ctx = self.defining.clone();
        typing.extend(local.iter().cloned());
        self.elab(&typing, t, goal).unwrap_or_else(|_| t.clone())
    }

    #[allow(clippy::too_many_arguments)]
    fn general_minor(
        &mut self,
        family: &str,
        ind: &Ind,
        c: &Ctor,
        spec: &FnSpec,
        h: &Header,
        arm: Option<(Vec<String>, &SurfaceTerm)>,
        fam_pos: usize,
        fns: &HashMap<String, FnInfo>,
    ) -> Result<T, Diagnostic> {
        let sp = h.span;
        let (names, body) = match arm {
            Some((n, b)) => (n, Some(b)),
            None => (c.args.iter().map(|_| self.fresh_name("_")).collect(), None),
        };
        h.hidden(&names, &c.name)?;
        let ihs: Vec<String> = c.recs.iter().map(|_| self.fresh_name("ih")).collect();
        let eqs: Vec<String> = h.general.iter().map(|_| self.fresh_name("e")).collect();
        let binders: Vec<String> = [names.clone(), ihs.clone(), eqs.clone()].concat();

        let mut local: Vec<(String, T)> = spec.params.to_vec();
        let (mut from, mut to) = self.ctor_binding(ind, &h.pargs);
        let mut field_tys: Vec<(String, T)> = Vec::new();
        for (i, (an, ty)) in c.args.iter().enumerate() {
            let ty = self.instantiate(ty, &from, &to);
            field_tys.push((names[i].clone(), ty.clone()));
            local.push((names[i].clone(), ty));
            from.push(an.clone());
            to.push(T::var(&names[i], sp));
        }
        let idx: Vec<T> = c
            .idx
            .iter()
            .map(|t| self.instantiate(t, &from, &to))
            .collect();
        // A recursive field of the matched family has its induction
        // hypothesis in scope (with its type, so the transport below carries
        // it), and a call on the field becomes it.
        let mut smaller: Smaller = HashMap::new();
        for (r, ih) in c.recs.iter().zip(&ihs) {
            if r.fam != fam_pos {
                continue;
            }
            let ys: Vec<(String, T)> =
                r.ys.iter()
                    .map(|(n, t)| (n.clone(), self.instantiate(t, &from, &to)))
                    .collect();
            let field = app(
                T::var(&names[r.arg], sp),
                ys.iter().map(|(n, _)| T::var(n, sp)).collect(),
            );
            let mut margs: Vec<T> = r
                .idx
                .iter()
                .map(|t| self.instantiate(t, &from, &to))
                .collect();
            margs.push(field);
            let applied = app(h.motive.clone(), margs);
            // Reduced, it is a kernel term, where a function without
            // parameters is the bare constant; the arm is elaborated again
            // with it, so it is put back as written (`policy()`).
            let ty = pi_all(&ys, self.whnf(&local, &applied));
            let ty = self.calls_written_in(&local, &ty);
            local.push((ih.clone(), ty));
            smaller.insert(names[r.arg].clone(), (T::var(&ih, sp), r.fam, r.ys.len()));
        }
        let cval = app(T::var(&c.name, sp), to.clone());
        for p in &mut local[h.xpos + 1..spec.params.len()] {
            p.1 = self.subst(&p.1, &h.x, &cval);
        }

        let mut applied_args = idx.clone();
        applied_args.push(cval.clone());
        let applied = app(h.motive.clone(), applied_args);
        let goal = self.whnf(&local, &applied);
        let mut goal = self.calls_written_in(&local, &goal);
        // The binders are the motive's equations, under whatever names the
        // reduction gave them.
        let mut named = Vec::new();
        for _ in &h.general {
            let TermKind::Pi { params, result, .. } = &*goal.kind else {
                return err(msg!("kernel-match-no-equation-binder"), sp);
            };
            named.push(params[0].0.clone());
            goal = (**result).clone();
        }
        for (b, e) in named.iter().zip(&eqs) {
            if let Some(b) = b {
                goal = self.subst(&goal, b, &T::var(e, sp));
            }
        }
        let work: Vec<Eqn> = h
            .general
            .iter()
            .zip(&eqs)
            .map(|(g, e)| Eqn {
                l: idx[g.k].clone(),
                r: g.arg.clone(),
                ty: g.ty.clone(),
                proof: T::var(e, sp),
            })
            .collect();
        let after: Vec<String> = h.after.iter().map(|(n, _)| n.clone()).collect();
        // Any variable in scope can be replaced by unification, except the
        // matched one and the later parameters (they stay in the goal).
        let solvable: Vec<String> = local
            .iter()
            .map(|(n, _)| n.clone())
            .filter(|n| *n != h.x && !after.contains(n))
            .collect();
        let plan = self.unify_indices(&local, &solvable, work, &goal, family, sp)?;
        let sols = match plan {
            Plan::Impossible(absurd) => return Ok(lams(&binders, absurd)),
            Plan::Solved(sols) => sols,
        };
        let Some(body) = body else {
            return err(msg!("kernel-match-missing-case", name = &c.name), h.span);
        };
        let arm_goal = self.under_after(goal.clone(), &h.after);
        if sols.is_empty() {
            self.matched.push((h.x.clone(), cval.clone()));
            let shaped = self.elaborate_at(body, &local, arm_goal.as_ref());
            self.matched.pop();
            let shaped = shaped?;
            let shaped = self.with_generics(&shaped, &local, arm_goal.as_ref(), fns);
            let shaped = if fns.is_empty() {
                shaped
            } else {
                replace_calls(
                    &shaped,
                    fns,
                    &smaller,
                    &h.rebound(&local, spec.params.len()),
                )?
            };
            let shaped = if fns.is_empty() {
                shaped
            } else {
                self.subst(&shaped, &h.x, &cval)
            };
            return Ok(lams(&binders, lams(&after, shaped)));
        }
        // The arm is written, and checked, with the fixed variables replaced.
        let mut sub_body = body.clone();
        for s in &sols {
            sub_body = self.subst(&sub_body, &s.f, &s.t);
        }
        let mut sub_local: Vec<(String, T)> = Vec::new();
        for (n, ty) in &local {
            if sols.iter().any(|s| s.f == *n) {
                continue;
            }
            let mut ty = ty.clone();
            for s in &sols {
                ty = self.subst(&ty, &s.f, &s.t);
            }
            sub_local.push((n.clone(), ty));
        }
        let sub_goal = arm_goal.map(|mut g| {
            for s in &sols {
                g = self.subst(&g, &s.f, &s.t);
            }
            g
        });
        let mut sub_cval = cval.clone();
        for s in &sols {
            sub_cval = self.subst(&sub_cval, &s.f, &s.t);
        }
        self.matched.push((h.x.clone(), sub_cval));
        let shaped = self.elaborate_at(&sub_body, &sub_local, sub_goal.as_ref());
        self.matched.pop();
        let shaped = shaped?;
        let shaped = self.with_generics(&shaped, &sub_local, sub_goal.as_ref(), fns);
        let shaped = if fns.is_empty() {
            shaped
        } else {
            replace_calls(
                &shaped,
                fns,
                &smaller,
                &h.rebound(&local, spec.params.len()),
            )?
        };

        // What is bound after a fixed variable and has a type that mentions
        // it (or mentions such a variable) is rebound inside the transport.
        let first = local
            .iter()
            .position(|(n, _)| sols.iter().any(|s| s.f == *n))
            .unwrap_or(0);
        let mut changed: Vec<String> = sols.iter().map(|s| s.f.clone()).collect();
        let mut dep: Vec<(String, T)> = Vec::new();
        for (n, ty) in &local[first..] {
            if *n == h.x || after.contains(n) || changed.contains(n) {
                continue;
            }
            if changed.iter().any(|c| occurs(ty, c)) {
                changed.push(n.clone());
                dep.push((n.clone(), ty.clone()));
            }
        }
        for s in &sols {
            if let Some((n, _)) = dep.iter().find(|(n, _)| occurs(&s.t, n)) {
                return err(msg!("kernel-unify-depends", name = &s.f, mentioned = n), sp);
            }
        }
        for (g, e) in h.general.iter().zip(&eqs) {
            dep.push((e.clone(), eq_ty(&g.ty, &idx[g.k], &g.arg)));
        }
        // The fixed variables are gone from the matched constructor too.
        let body0 = if fns.is_empty() {
            shaped
        } else {
            let mut cval = cval;
            for s in &sols {
                cval = self.subst(&cval, &s.f, &s.t);
            }
            self.subst(&shaped, &h.x, &cval)
        };
        let dep_names: Vec<String> = dep.iter().map(|(n, _)| n.clone()).collect();
        let inner = lams(&dep_names, lams(&after, body0));
        let full = pi_all(&dep, goal);
        let mut states = vec![full];
        for s in &sols {
            let next = self.subst(states.last().unwrap(), &s.f, &s.t);
            states.push(next);
        }
        let elim = if h.is_prop { "Eq::ind" } else { "Eq::rec" };
        let mut cur = inner;
        for (i, s) in sols.iter().enumerate().rev() {
            let y = self.fresh_name("y");
            let e2 = self.fresh_name("e");
            let motive_body = self.subst(&states[i], &s.f, &T::var(&y, sp));
            let motive = lam(&y, lam(&e2, motive_body));
            let sym = sym_proof(&s.ty, &T::var(&s.f, sp), &s.t, s.proof.clone());
            cur = app(
                T::var(elim, sp),
                vec![
                    s.ty.clone(),
                    s.t.clone(),
                    motive,
                    cur,
                    T::var(&s.f, sp),
                    sym,
                ],
            );
        }
        let applied = app(cur, dep_names.iter().map(|n| T::var(n, sp)).collect());
        Ok(lams(&binders, applied))
    }

    fn unify_indices(
        &mut self,
        ctx: &Ctx,
        solvable: &[String],
        mut work: Vec<Eqn>,
        goal: &T,
        family: &str,
        sp: tauto_parol::Span,
    ) -> Result<Plan, Diagnostic> {
        let mut sols: Vec<Sol> = Vec::new();
        // An equation between a stuck term and a constructor is set aside:
        // another equation may still show the case impossible.
        let mut stuck: Option<(T, T)> = None;
        while let Some(Eqn { l, r, ty, proof }) = work.pop() {
            let l = expand_numeral(self.whnf(ctx, &l));
            let r = expand_numeral(self.whnf(ctx, &r));
            if self.conv(ctx, &l, &r) {
                continue;
            }
            let pos = |n: &str| ctx.iter().rposition(|(m, _)| m == n);
            // A variable is fixed to a term that does not mention it; the term
            // may mention variables bound after it, as long as their types do
            // not depend on it (checked once all equations are solved).
            let fixable = |t: &T, other: &T, sols: &[Sol]| -> Option<String> {
                let TermKind::Var(f) = &*t.kind else {
                    return None;
                };
                pos(f)?;
                let scoped =
                    solvable.contains(f) && !sols.iter().any(|s| s.f == *f) && !occurs(other, f);
                scoped.then(|| f.clone())
            };
            // Between two variables, the one bound later is replaced.
            let later_is_r = matches!(
                (&*l.kind, &*r.kind),
                (TermKind::Var(a), TermKind::Var(b)) if pos(b) > pos(a)
            );
            if !later_is_r && let Some(f) = fixable(&l, &r, &sols) {
                sols.push(Sol { f, t: r, ty, proof });
                continue;
            }
            if let Some(f) = fixable(&r, &l, &sols) {
                let proof = sym_proof(&ty, &l, &r, proof);
                sols.push(Sol { f, t: l, ty, proof });
                continue;
            }
            if let Some(f) = fixable(&l, &r, &sols) {
                sols.push(Sol { f, t: r, ty, proof });
                continue;
            }
            let (Some((cl, al)), Some((cr, ar))) = (self.ctor_view(&l), self.ctor_view(&r)) else {
                stuck.get_or_insert((l, r));
                continue;
            };
            let (fam, jl) = self.ctors[&cl].clone();
            if self.ctors[&cr].0 != fam {
                return err(msg!("kernel-unify-different-types"), sp);
            }
            let ind = self.inds[&fam].clone();
            let noconf = format!("{fam}::noconf");
            if !self.globals.contains_key(&noconf) {
                return err(msg!("kernel-unify-no-confusion", name = &fam), sp);
            }
            let np = ind.params.len();
            let pargs = al[..np].to_vec();
            let mut head = pargs.clone();
            if cl != cr {
                head.extend([goal.clone(), l.clone(), r.clone(), proof]);
                return Ok(Plan::Impossible(app(T::var(&noconf, sp), head)));
            }
            let pnames: Vec<String> = ind.params.iter().map(|(n, _)| n.clone()).collect();
            let c = &ind.ctors[jl];
            let hs: Vec<String> = c.inj.iter().map(|i| format!("h'{i}")).collect();
            for (pos, &i) in c.inj.iter().enumerate() {
                let fty = self.instantiate(&c.args[i].1, &pnames, &pargs);
                let (a, b) = (al[np + i].clone(), ar[np + i].clone());
                let mut call = pargs.clone();
                call.extend([eq_ty(&fty, &a, &b), l.clone(), r.clone(), proof.clone()]);
                let pr = app(
                    app(T::var(&noconf, sp), call),
                    vec![lams(&hs, T::var(&hs[pos], sp))],
                );
                work.push(Eqn {
                    l: a,
                    r: b,
                    ty: fty,
                    proof: pr,
                });
            }
        }
        if let Some((l, r)) = stuck {
            return err(
                msg!(
                    "kernel-unify-index",
                    left = describe(&l),
                    right = describe(&r),
                    family = family
                ),
                sp,
            );
        }
        for s in &sols {
            if sols.iter().any(|o| occurs(&s.t, &o.f)) {
                return err(msg!("kernel-unify-cyclic"), sp);
            }
        }
        Ok(Plan::Solved(sols))
    }

    /// The names a constructor's argument types are written over and what
    /// they stand for: the family's parameters, or for a nested member the
    /// parameters of the type it stands for.
    fn ctor_binding(&self, ind: &Ind, pargs: &[T]) -> (Vec<String>, Vec<T>) {
        match &ind.alias {
            Some((j, args)) => (
                self.inds[j].params.iter().map(|(n, _)| n.clone()).collect(),
                args.clone(),
            ),
            None => (
                ind.params.iter().map(|(n, _)| n.clone()).collect(),
                pargs.to_vec(),
            ),
        }
    }

    /// The group member standing for `J<args>`, when a nested inductive type
    /// declared one.
    fn nested_member(&self, j: &str, args: &[T]) -> Option<String> {
        // The members were made over the types as the kernel reads them, a product as its
        // `Pair`; the arguments are compared so too.
        let key: Vec<String> = args
            .iter()
            .map(|a| describe(&self.kernel_products(a)))
            .collect();
        self.inds.iter().find_map(|(n, i)| match &i.alias {
            Some((j2, a2))
                if j2 == j
                    && a2
                        .iter()
                        .map(|a| describe(&self.kernel_products(a)))
                        .collect::<Vec<_>>()
                        == key =>
            {
                Some(n.clone())
            }
            _ => None,
        })
    }

    /// `t` with each product `Prod(A, B)` in it as the `Pair(A, B)` it is for the kernel.
    pub(super) fn kernel_products(&self, t: &T) -> T {
        let mut out = t.clone();
        crate::surface::walk::term(&mut out, &mut |t| {
            if self.product_parts(t).is_none() {
                return;
            }
            if let TermKind::App { function, .. } = std::sync::Arc::make_mut(&mut t.kind)
                && let TermKind::Var(f) = &*function.kind
            {
                let pair = format!("{}Pair", f.strip_suffix("Prod").unwrap_or(f));
                *function = Box::new(T::var(&pair, function.span));
            }
        });
        out
    }

    /// A constructor application: its name and arguments (parameters first).
    fn ctor_view(&self, t: &T) -> Option<(String, Vec<T>)> {
        match &*t.kind {
            TermKind::Var(n) if self.ctors.contains_key(n) => Some((n.clone(), vec![])),
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                TermKind::Var(n) if self.ctors.contains_key(n) => {
                    Some((n.clone(), arguments.clone()))
                }
                _ => None,
            },
            _ => None,
        }
    }
}

/// Whether `t` holds a `match` where `elaborate` compiles one: at its root,
/// or under applications, functions and other matches.
/// Whether `a` is the parameter `n` itself, or `n` η-expanded
/// (`x => n(x)`), as an implicit argument of a function type is filled in.
fn passes_unchanged(a: &T, n: &str) -> bool {
    match &*a.kind {
        TermKind::Var(v) => v == n,
        TermKind::Lam { params, body, .. } => match &*body.kind {
            TermKind::App {
                function,
                arguments,
            } => {
                matches!(&*function.kind, TermKind::Var(f) if f == n)
                    && !params.iter().any(|x| x == n)
                    && arguments.len() == params.len()
                    && arguments
                        .iter()
                        .zip(params)
                        .all(|(a, x)| matches!(&*a.kind, TermKind::Var(v) if v == x))
            }
            _ => false,
        },
        _ => false,
    }
}

pub(super) fn has_match(t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::Match { .. } | TermKind::Field { .. } | TermKind::Ascribe { .. } => true,
        TermKind::App { .. } => t.any_in_applications(|part, function| {
            function && matches!(&*part.kind, TermKind::Var(op) if op == "==" || op == "!=")
                || has_match(part)
        }),
        TermKind::Lam { body, .. } => has_match(body),
        TermKind::Pi { params, result, .. } => {
            params.iter().any(|(_, d)| has_match(d)) || has_match(result)
        }
        _ => false,
    }
}

/// Whether `t` has a `match` (or an `if`, which is one) written in it (not `==` or a
/// field, which `has_match` also counts).
pub(super) fn has_written_match(t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::Match { .. } | TermKind::If { .. } => true,
        TermKind::App { .. } => t.any_in_applications(|part, _| has_written_match(part)),
        TermKind::Lam { body, .. } => has_written_match(body),
        TermKind::Pi { params, result, .. } => {
            params.iter().any(|(_, d)| has_written_match(d)) || has_written_match(result)
        }
        _ => false,
    }
}

/// Whether `t` has `a == b` or `a != b` written in it, which a type reads as a body
/// does: by the equality of the type of `a`.
pub(super) fn has_equality(t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::App { .. } => t.any_in_applications(|part, function| {
            if function {
                matches!(&*part.kind, TermKind::Var(op) if op == "==" || op == "!=")
            } else {
                has_equality(part)
            }
        }),
        TermKind::Lam { body, .. } => has_equality(body),
        TermKind::Pi { params, result, .. } => {
            params.iter().any(|(_, d)| has_equality(d)) || has_equality(result)
        }
        TermKind::Exists { domain, body, .. } => has_equality(domain) || has_equality(body),
        _ => false,
    }
}

/// `ctx` with the variables before `x` whose types mention it, or one of the
/// variables `indices` that `x`'s type is indexed by (an earlier match put a
/// field of its own there), moved to the end, so that a match on `x`
/// generalizes them: in each arm their types have `x`'s constructor, and the
/// indices that the arm fixes.
fn depending_last(ctx: &[(String, T)], x: &str, indices: &[String]) -> Vec<(String, T)> {
    let Some(pos) = ctx.iter().rposition(|(n, _)| n == x) else {
        return ctx.to_vec();
    };
    let mut deps = vec![x.to_string()];
    deps.extend(indices.iter().cloned());
    let mut kept = Vec::new();
    let mut moved = Vec::new();
    for (n, d) in &ctx[..pos] {
        if deps.iter().any(|v| occurs(d, v)) {
            deps.push(n.clone());
            moved.push((n.clone(), d.clone()));
        } else {
            kept.push((n.clone(), d.clone()));
        }
    }
    kept.extend(ctx[pos..].iter().cloned());
    kept.extend(moved);
    kept
}

impl Kernel {
    /// The variables of `ctx` that are indices (not parameters) of the type of
    /// `x`, written as themselves.
    fn index_variables(&mut self, ctx: &[(String, T)], x: &str) -> Vec<String> {
        let Some(pos) = ctx.iter().rposition(|(n, _)| n == x) else {
            return Vec::new();
        };
        let before: Ctx = ctx[..pos].to_vec();
        let ty = self.whnf_pair(&before, &ctx[pos].1);
        let TermKind::App {
            function,
            arguments,
        } = &*ty.kind
        else {
            return Vec::new();
        };
        let TermKind::Var(family) = &*function.kind else {
            return Vec::new();
        };
        let Some(ind) = self.inds.get(family) else {
            return Vec::new();
        };
        arguments
            .iter()
            .skip(ind.params.len())
            .filter_map(|a| match &*a.kind {
                TermKind::Var(v) if v != x && ctx[..pos].iter().any(|(n, _)| n == v) => {
                    Some(v.clone())
                }
                _ => None,
            })
            .collect()
    }
}
