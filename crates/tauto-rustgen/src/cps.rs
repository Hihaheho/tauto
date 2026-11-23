//! Code of the M tier: continuation-passing style.
//!
//! A function of the M tier takes the handlers in place (`m`) and its own
//! continuation, and returns a `Step` for the trampoline. An expression that
//! cannot suspend is written as it is in the other tiers (`Gen::expr`) and
//! its value handed on; one that can is written with the rest of the
//! computation after it as a closure (`tauto_rt::cps::kont`) that is called
//! with the value. Such a closure may be called any number of times, so what
//! it uses is cloned in (it is a `Fn`): the names of the locals that can be
//! cloned are kept in `Mx::scope`, and the ones a closure's text mentions are
//! cloned at its start.

use std::collections::BTreeMap;

use proc_macro2::Ident;
use quote::quote;
use tauto_nir::*;

use crate::expr::{Fx, PatOut, clone_each, clone_each_mut, lid};
use crate::tok::{Rs, comma, id, is_simple, is_unit, mentioned, num, tuple};
use crate::{Gen, Pred};

pub(crate) struct Mx {
    /// The locals in scope that a continuation must own a copy of.
    pub scope: Vec<Ident>,
    /// The borrowed locals in scope whose value can be copied: a
    /// continuation that uses one owns a copy and borrows it again inside,
    /// since the borrow it was made from ends with the code that made it.
    pub refs: Vec<Ident>,
    /// The function's own continuation, which `return` calls.
    pub fk: Option<Ident>,
}

impl Mx {
    pub fn new(fk: Option<Ident>) -> Mx {
        Mx {
            scope: Vec::new(),
            refs: Vec::new(),
            fk,
        }
    }
}

/// The rest of the computation, as the generator knows it: a continuation
/// that is a name in the generated code, or code still to be written once the
/// value is known.
pub(crate) enum Kc<'a> {
    Var(Ident),
    /// A name of a `Kont<Payload>`: the target of a handler.
    Erased(Ident),
    Fn(Box<dyn FnOnce(&mut Gen<'a>, &mut Mx, Rs) -> Rs + 'a>),
}

impl<'a> Kc<'a> {
    pub fn new(f: impl FnOnce(&mut Gen<'a>, &mut Mx, Rs) -> Rs + 'a) -> Kc<'a> {
        Kc::Fn(Box::new(f))
    }

    fn dup(&self) -> Kc<'a> {
        match self {
            Kc::Var(n) => Kc::Var(n.clone()),
            Kc::Erased(n) => Kc::Erased(n.clone()),
            Kc::Fn(_) => panic!("tauto: a continuation written twice (a bug in the generator)"),
        }
    }
}

/// Whether a value of type `t` holds a function value in a member of an
/// option, a result or a pair.
fn fn_inside(t: &Ty) -> bool {
    match t {
        Ty::Fn(_) => true,
        Ty::Option(a) => fn_inside(a),
        Ty::Result(a, b) | Ty::Pair(a, b) => fn_inside(a) || fn_inside(b),
        _ => false,
    }
}

/// The arms of a handler of the M tier, the `direct` ones too: they are in
/// the handlers in place (`M::push_direct`), and code of the S tier inside
/// finds them through `tauto_rt::cps::bridge`.
fn m_arms(h: &HandleNode) -> impl Iterator<Item = &OpArm> {
    h.aborts.iter().chain(&h.susp).chain(&h.direct)
}

/// Whether the expression suspends (or returns), so it is written in
/// continuation-passing style.
pub(crate) fn susp(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Perform(p) => p.quant != Quant::Direct || p.args.iter().any(susp),
        ExprKind::Call(c) => {
            c.tier == Tier::M
                || o_callback_call(c)
                || matches!(c.callee, Callee::Cont(_))
                || matches!(&c.callee, Callee::Value(v) if susp(v))
                || c.args.iter().any(susp)
        }
        ExprKind::Handle(h) => h.m,
        ExprKind::Closure(_) => false,
        ExprKind::Budget(b) => b.m,
        ExprKind::Block(b) => b.stmts.iter().any(stmt_susp) || b.tail.as_deref().is_some_and(susp),
        ExprKind::Match(m) => {
            susp(&m.scrut)
                || m.arms
                    .iter()
                    .any(|a| a.guard.as_ref().is_some_and(susp) || susp(&a.body))
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => susp(cond) || susp(then) || otherwise.as_deref().is_some_and(susp),
        ExprKind::And(a, b) | ExprKind::Or(a, b) => susp(a) || susp(b),
        ExprKind::Ctor { fields, .. } => fields.iter().any(|(_, e)| susp(e)),
        ExprKind::Arith { args, .. } | ExprKind::Cmp { args, .. } | ExprKind::Eq { args, .. } => {
            args.iter().any(susp)
        }
        ExprKind::Not(a)
        | ExprKind::TempRef(a)
        | ExprKind::Shown(a)
        | ExprKind::Unreachable(a)
        | ExprKind::FnCast(a) => susp(a),
        ExprKind::Field { base, .. } => susp(base),
        ExprKind::Inject { value, .. }
        | ExprKind::Remap { value, .. }
        | ExprKind::Deref { value, .. } => susp(value),
        _ => false,
    }
}

/// A call of a function value of the O tier (one that may diverge under a
/// budget): in code of the M tier it is answered through the budgets in the
/// handlers in place, so it is written in continuation-passing style.
fn o_callback_call(c: &CallNode) -> bool {
    c.tier == Tier::O && matches!(&c.callee, Callee::Local(_) | Callee::Value(_))
}

fn stmt_susp(s: &Stmt) -> bool {
    match s {
        Stmt::Let { init, .. } | Stmt::Var { init, .. } => susp(init),
        Stmt::Assign { value, .. } => susp(value),
        Stmt::Expr(e) => susp(e),
        Stmt::While {
            cond, body, tick, ..
        } => {
            *tick == Tick::Budget
                || susp(cond)
                || body.stmts.iter().any(stmt_susp)
                || body.tail.as_deref().is_some_and(susp)
        }
        Stmt::Return { .. } => true,
    }
}

/// The join of the branches of an `if` or a `match`, and the `var`s it takes
/// with the value.
struct Join<'a> {
    kv: Kc<'a>,
    names: Vec<Ident>,
}

/// The `var`s a block assigns, by local number (a field of one counts).
fn assigned_vars(b: &Block, out: &mut BTreeMap<u32, Local>) {
    for s in &b.stmts {
        match s {
            Stmt::Let { init, .. } | Stmt::Var { init, .. } => assigned_vars_expr(init, out),
            Stmt::Assign { target, value, .. } => {
                out.insert(target.local.id, target.local.clone());
                assigned_vars_expr(value, out);
            }
            Stmt::Expr(e) => assigned_vars_expr(e, out),
            Stmt::While { cond, body, .. } => {
                assigned_vars_expr(cond, out);
                assigned_vars(body, out);
            }
            Stmt::Return { value, .. } => {
                if let Some(v) = value {
                    assigned_vars_expr(v, out);
                }
            }
        }
    }
    if let Some(t) = &b.tail {
        assigned_vars_expr(t, out);
    }
}

fn assigned_vars_expr(e: &Expr, out: &mut BTreeMap<u32, Local>) {
    e.walk(&mut |x| {
        if let ExprKind::Block(b) = &x.kind {
            for s in &b.stmts {
                if let Stmt::Assign { target, .. } = s {
                    out.insert(target.local.id, target.local.clone());
                }
            }
        }
    });
}

/// Whether the expression may leave with an `Abort` (it calls a function of
/// the A tier).
fn can_abort(e: &Expr) -> bool {
    let mut found = false;
    e.walk(&mut |x| {
        if let ExprKind::Call(c) = &x.kind
            && c.tier == Tier::A
        {
            found = true;
        }
    });
    found
}

fn pat_binds(p: &Pat, out: &mut Vec<(Local, Ty)>) {
    match p {
        Pat::Bind(l, t) => out.push((l.clone(), t.clone())),
        Pat::Ctor { fields, .. } => fields.iter().for_each(|f| pat_binds(f, out)),
        Pat::Variant { pat, .. } => pat_binds(pat, out),
        _ => {}
    }
}

impl<'a> Gen<'a> {
    /// A type as a closure's parameter or a `let` says it: what Rust cannot
    /// infer is `()`.
    fn ty_k(&mut self, t: &Ty) -> Rs {
        self.infer_unit.set(true);
        let s = self.ty(t);
        self.infer_unit.set(false);
        s
    }

    /// Whether a copy of the local is made for each continuation that uses
    /// it.
    fn dup_local(&self, l: &Local, t: &Ty) -> bool {
        if crate::expr::m_callback(l, t) {
            return true;
        }
        match l.repr {
            Repr::Ref if self.owned_refs.contains(&l.id) => true,
            Repr::SharedVar(true) | Repr::SharedVar(false) => true,
            Repr::Plain => self.ty_has(t, Pred::Clone),
            _ => false,
        }
    }

    fn add_local(&self, mx: &mut Mx, l: &Local, t: &Ty) {
        if self.dup_local(l, t) {
            mx.scope.push(lid(l));
        } else {
            self.add_ref(mx, l, t);
        }
    }

    /// A borrowed local whose value can be copied.
    fn add_ref(&self, mx: &mut Mx, l: &Local, t: &Ty) {
        if l.repr != Repr::Ref {
            return;
        }
        let pointee = match t {
            Ty::Ref(inner) => inner,
            t => t,
        };
        if !matches!(pointee, Ty::Fn(_)) && self.ty_has(pointee, Pred::Clone) {
            mx.refs.push(lid(l));
        }
    }

    fn add_pat(&self, mx: &mut Mx, p: &Pat) {
        let mut binds = Vec::new();
        pat_binds(p, &mut binds);
        for (l, t) in binds {
            self.add_local(mx, &l, &t);
        }
    }

    /// A closure that takes the value and writes `body` (the rest of the
    /// computation), as a continuation.
    fn kont_text(
        &mut self,
        mx: &mut Mx,
        arg: &str,
        arg_ty: &Rs,
        body: impl FnOnce(&mut Gen<'a>, &mut Mx) -> Rs,
    ) -> Rs {
        let visible = mx.scope.clone();
        let visible_refs = mx.refs.clone();
        let text = body(self, mx);
        mx.scope = visible.clone();
        mx.refs = visible_refs.clone();
        let used = mentioned(&visible, &text);
        let outer = clone_each(used.iter().cloned());
        let inner = clone_each_mut(used.iter().cloned());
        let used_refs = mentioned(&visible_refs, &text);
        let own_refs: Rs = used_refs
            .iter()
            .map(|x| quote!(let #x = (*#x).clone();))
            .collect();
        let borrow_refs: Rs = used_refs.iter().map(|x| quote!(let #x = &#x;)).collect();
        let arg = id(arg);
        quote!({
            #outer
            #own_refs
            tauto_rt::cps::kont(move |ev, m, #arg: #arg_ty| {
                #inner
                #borrow_refs
                #text
            })
        })
    }

    fn deliver(&mut self, mx: &mut Mx, k: Kc<'a>, v: Rs) -> Rs {
        match k {
            Kc::Var(n) => self.call_kont(mx, &n, &v, false),
            Kc::Erased(n) => self.call_kont(mx, &n, &v, true),
            Kc::Fn(f) => {
                if is_simple(&v) || is_unit(&v) {
                    f(self, mx, v)
                } else {
                    let t = self.tmp("v");
                    let rest = f(self, mx, quote!(#t));
                    quote!(let #t = #v; #rest)
                }
            }
        }
    }

    /// The continuation `n` called with `v`. The ones a function or a handler
    /// returns through are called with the stack unwound.
    fn call_kont(&self, mx: &Mx, n: &Ident, v: &Rs, erased: bool) -> Rs {
        let _ = mx;
        let v = if erased {
            quote!(Box::new(#v) as Payload)
        } else {
            v.clone()
        };
        let long = erased || n == "fk" || n.to_string().starts_with("kb") || n == "fin";
        if long {
            quote!(tauto_rt::cps::ret(&#n, m, #v))
        } else {
            quote!(#n(ev, m, #v))
        }
    }

    /// Code of the S tier in code of the M tier: its `direct` operations go
    /// to the `direct` arms of the handlers in place, then to `ev`, the
    /// handlers of the code that runs the computation now.
    pub(crate) fn bridged(&self, code: Rs, at: &impl quote::ToTokens) -> Rs {
        if mentioned(&[id("ev")], &code).is_empty() {
            return code;
        }
        quote!({ let ev = &tauto_rt::cps::bridge(ev, m, #at); #code })
    }

    /// A continuation that is used in more than one place, made a name.
    fn reify(&mut self, mx: &mut Mx, k: Kc<'a>, ty: &Ty) -> (Rs, Kc<'a>) {
        match k {
            Kc::Var(_) | Kc::Erased(_) => (Rs::new(), k),
            Kc::Fn(f) => {
                let name = self.tmp("kk");
                let t = self.ty_k(ty);
                let clos = self.kont_text(mx, "v", &t, move |this, mx| f(this, mx, quote!(v)));
                mx.scope.push(name.clone());
                (
                    quote!(let #name: tauto_rt::cps::Kont<'_, #t> = #clos;),
                    Kc::Var(name),
                )
            }
        }
    }

    /// Of the `var`s `found` assigns, the ones a continuation owns a copy of
    /// (declared outside, in scope, not shared), with their types.
    fn carried(&self, mx: &Mx, found: BTreeMap<u32, Local>) -> Vec<(Ident, Ty)> {
        found
            .into_values()
            .filter_map(|local| {
                let x = lid(&local);
                if local.repr != Repr::Plain || !mx.scope.contains(&x) {
                    return None;
                }
                self.var_tys.get(&local.id).map(|t| (x, t.clone()))
            })
            .collect()
    }

    /// `reify` for the join of the branches of an `if` or a `match`: when
    /// the branches assign `var`s from outside, the join takes their values
    /// with the branch's value, since a continuation made before the branches
    /// holds the values from before them.
    fn reify_join(
        &mut self,
        mx: &mut Mx,
        k: Kc<'a>,
        ty: &Ty,
        found: BTreeMap<u32, Local>,
    ) -> (Rs, Join<'a>) {
        let carried = match &k {
            Kc::Fn(_) => self.carried(mx, found),
            _ => Vec::new(),
        };
        if carried.is_empty() {
            let (pre, kv) = self.reify(mx, k, ty);
            return (
                pre,
                Join {
                    kv,
                    names: Vec::new(),
                },
            );
        }
        let Kc::Fn(f) = k else { unreachable!() };
        let name = self.tmp("kk");
        let t = self.ty_k(ty);
        let names: Vec<Ident> = carried.iter().map(|(x, _)| x.clone()).collect();
        let tys: Vec<Rs> = carried.iter().map(|(_, t)| self.ty_k(t)).collect();
        let jt = quote!((#t, #(#tys,)*));
        let unpack = quote!(#[allow(unused_mut)] let (v, #(mut #names,)*) = jv;);
        let clos = self.kont_text(mx, "jv", &jt, move |this, mx| {
            let rest = f(this, mx, quote!(v));
            quote!(#unpack #rest)
        });
        mx.scope.push(name.clone());
        (
            quote!(let #name: tauto_rt::cps::Kont<'_, #jt> = #clos;),
            Join {
                kv: Kc::Var(name),
                names,
            },
        )
    }

    /// The continuation one branch goes on with to the join.
    fn join_kc(&self, j: &Join<'a>) -> Kc<'a> {
        if j.names.is_empty() {
            return j.kv.dup();
        }
        let Kc::Var(n) = &j.kv else { unreachable!() };
        let (n, names) = (n.clone(), j.names.clone());
        Kc::new(move |this, mx, v| {
            this.call_kont(mx, &n, &quote!((#v, #(#names.clone(),)*)), false)
        })
    }

    /// The continuation as a `Kont<Payload>`: what `k(v)` of an arm and a
    /// handler's target take.
    fn payload_kont(&mut self, mx: &mut Mx, k: Kc<'a>, ty: &Ty) -> Rs {
        match k {
            Kc::Var(n) => quote!(tauto_rt::cps::erase(#n.clone())),
            Kc::Erased(n) => quote!(#n.clone()),
            Kc::Fn(f) => {
                let t = self.ty_k(ty);
                self.kont_text(mx, "p", &quote!(Payload), move |this, mx| {
                    let v = this.tmp("v");
                    let rest = f(this, mx, quote!(#v));
                    quote!(let #v: #t = tauto_rt::ev::answer::<#t>(p); #rest)
                })
            }
        }
    }

    fn typed_kont(&mut self, mx: &mut Mx, k: Kc<'a>, ty: &Ty) -> Rs {
        match k {
            Kc::Var(n) => quote!(#n.clone()),
            Kc::Fn(_) | Kc::Erased(_) => {
                let t = self.ty_k(ty);
                self.kont_text(mx, "v", &t, move |this, mx| this.deliver(mx, k, quote!(v)))
            }
        }
    }

    /// `e` written so that the continuation `k` is given its value.
    pub(crate) fn cps(&mut self, e: &Expr, mx: &mut Mx, k: Kc<'a>) -> Rs {
        let saved = mx.scope.clone();
        let out = self.cps_inner(e, mx, k);
        mx.scope = saved;
        out
    }

    fn cps_inner(&mut self, e: &Expr, mx: &mut Mx, k: Kc<'a>) -> Rs {
        if !susp(e) {
            return self.cps_direct(e, mx, k);
        }
        match &e.kind {
            ExprKind::Block(b) => self.cps_block(b.clone(), 0, mx, k),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                let (then, otherwise) = (then.clone(), otherwise.clone());
                let ty = e.ty.clone();
                self.cps(
                    cond,
                    mx,
                    Kc::new(move |this, mx, c| {
                        let mut found = BTreeMap::new();
                        assigned_vars_expr(&then, &mut found);
                        if let Some(o) = &otherwise {
                            assigned_vars_expr(o, &mut found);
                        }
                        let (pre, j) = this.reify_join(mx, k, &ty, found);
                        let tk = this.join_kc(&j);
                        let t = this.cps(&then, mx, tk);
                        let ok = this.join_kc(&j);
                        let o = match &otherwise {
                            Some(o) => this.cps(o, mx, ok),
                            None => this.deliver(mx, ok, quote!(())),
                        };
                        quote!(#pre if #c { #t } else { #o })
                    }),
                )
            }
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                let is_and = matches!(e.kind, ExprKind::And(..));
                let b = (**b).clone();
                let ty = e.ty.clone();
                self.cps(
                    a,
                    mx,
                    Kc::new(move |this, mx, av| {
                        let (pre, kv) = this.reify(mx, k, &ty);
                        let rhs = this.cps(&b, mx, kv.dup());
                        let short_v = if is_and { quote!(false) } else { quote!(true) };
                        let short = this.deliver(mx, kv.dup(), short_v);
                        if is_and {
                            quote!(#pre if #av { #rhs } else { #short })
                        } else {
                            quote!(#pre if #av { #short } else { #rhs })
                        }
                    }),
                )
            }
            ExprKind::Match(m) => {
                let m = (**m).clone();
                let ty = e.ty.clone();
                let scrut = m.scrut.clone();
                self.cps(
                    &scrut,
                    mx,
                    Kc::new(move |this, mx, s| this.cps_match(m, ty, s, mx, k)),
                )
            }
            ExprKind::Handle(h) => self.cps_handle(h, &e.ty, mx, k),
            ExprKind::Budget(b) => self.cps_budget(b, &e.ty, mx, k),
            _ => self.cps_node(e, mx, k),
        }
    }

    /// An expression that cannot suspend: written as it is, and its value
    /// given on. An abort leaves through the handlers.
    fn cps_direct(&mut self, e: &Expr, mx: &mut Mx, k: Kc<'a>) -> Rs {
        let abort = can_abort(e);
        let mut fx = Fx::new(abort);
        fx.m = true;
        self.m_scope = mx.scope.clone();
        let mut code = self.expr(e, &mut fx);
        let at = self.loc(e.span);
        code = self.bridged(code, &at);
        // A closure that goes into a `Payload` is boxed as its own type
        // unless it is given the type of the function value first.
        // So is one inside a value (`Some(f)`), which is boxed when it is
        // handed to a continuation of the M tier (`k(Some(f))`).
        let inside = !matches!(e.ty, Ty::Fn(_)) && fn_inside(&e.ty) && !e.ty.has_arm_generic();
        // A value with type parameters (`Ran(n)` of `Out(T)`) boxed for a
        // handler's target is written at its type, too: nothing else there
        // fixes its parameters.
        let generic = matches!(k, Kc::Erased(_))
            && matches!(e.ty, Ty::Data(_, ref args) if !args.is_empty())
            && !e.ty.has_arm_generic();
        if matches!(k, Kc::Erased(_)) && matches!(e.ty, Ty::Fn(_))
            || ((inside || generic) && !abort)
        {
            let t = self.ty(&e.ty);
            code = quote!({ let f: #t = #code; f });
        }
        if abort {
            let t = self.tmp("v");
            let ok = self.deliver(mx, k, quote!(#t));
            quote!(
                match (|| -> Result<_, Abort> { Ok(#code) })() {
                    Ok(#t) => { #ok }
                    Err(a) => tauto_rt::cps::abort(ev, m, a),
                }
            )
        } else {
            self.deliver(mx, k, code)
        }
    }

    fn cps_match(&mut self, m: MatchNode, ty: Ty, scrut: Rs, mx: &mut Mx, k: Kc<'a>) -> Rs {
        let mut found = BTreeMap::new();
        for arm in &m.arms {
            assigned_vars_expr(&arm.body, &mut found);
        }
        let (pre, j) = self.reify_join(mx, k, &ty, found);
        let scrut = crate::expr::cell_free_scrutinee(&m, scrut);
        let mut arms = Vec::new();
        for arm in &m.arms {
            let saved = mx.scope.clone();
            let mut out = PatOut::default();
            let pat = self.pat(&arm.pat, m.by_ref, &mut out);
            if !m.by_ref {
                self.add_pat(mx, &arm.pat);
            } else {
                let mut binds = Vec::new();
                pat_binds(&arm.pat, &mut binds);
                for (l, t) in binds {
                    self.add_ref(mx, &l, &t);
                }
            }
            let mut guards = out.guards.clone();
            if let Some(g) = &arm.guard {
                let g = self.expr(g, &mut Fx::new(false));
                guards.push(out.user_guard(g));
            }
            let guard = PatOut::guard_clause(&guards);
            let ak = self.join_kc(&j);
            let body = self.cps(&arm.body, mx, ak);
            let prologue = out.prologue();
            arms.push(quote!(#pat #guard => { #prologue #body }));
            mx.scope = saved;
        }
        if !m.exhaustive {
            let at = self.loc(m.span);
            arms.push(quote!(_ => tauto_rt::no_arm(#at)));
        }
        let arms = comma(arms);
        quote!(#pre match #scrut { #arms })
    }

    /// A node whose operands are evaluated first, in order, the ones up to
    /// the last that suspends bound to names.
    fn cps_node(&mut self, e: &Expr, mx: &mut Mx, k: Kc<'a>) -> Rs {
        let mut e2 = e.clone();
        let n = e2.operands_mut().len();
        let all = match &e.kind {
            ExprKind::Perform(_) => true,
            ExprKind::Call(c) => {
                c.tier == Tier::M || o_callback_call(c) || matches!(c.callee, Callee::Cont(_))
            }
            _ => false,
        };
        let last = if all {
            n.checked_sub(1)
        } else {
            let mut last = None;
            for (i, o) in e2.clone().operands_mut().into_iter().enumerate() {
                if susp(o) {
                    last = Some(i);
                }
            }
            last
        };
        self.bind_operands(
            e2,
            0,
            last,
            mx,
            Box::new(move |this, mx, e3| this.finish_node(e3, mx, k)),
        )
    }

    #[allow(clippy::type_complexity)]
    fn bind_operands(
        &mut self,
        e: Expr,
        i: usize,
        last: Option<usize>,
        mx: &mut Mx,
        done: Box<dyn FnOnce(&mut Gen<'a>, &mut Mx, Expr) -> Rs + 'a>,
    ) -> Rs {
        let Some(l) = last else {
            return done(self, mx, e);
        };
        if i > l {
            return done(self, mx, e);
        }
        let child = e.clone().operands_mut()[i].clone();
        self.next_tmp += 1;
        let local = Local {
            id: 1_000_000 + self.next_tmp,
            name: "t".into(),
            repr: Repr::Plain,
        };
        let ty = child.ty.clone();
        let span = child.span;
        self.cps(
            &child,
            mx,
            Kc::new(move |this, mx, v| {
                this.add_local(mx, &local, &ty);
                let mut e3 = e;
                *e3.operands_mut()[i] = Expr {
                    kind: ExprKind::Read {
                        local: local.clone(),
                        how: Use::Move,
                    },
                    ty,
                    span,
                };
                let rest = this.bind_operands(e3, i + 1, last, mx, done);
                let x = lid(&local);
                quote!(let mut #x = #v; #rest)
            }),
        )
    }

    fn finish_node(&mut self, e: Expr, mx: &mut Mx, k: Kc<'a>) -> Rs {
        match &e.kind {
            // A `direct` operation whose arguments are bound is answered in
            // place, as one whose arguments do not suspend is.
            ExprKind::Perform(p) if p.quant == Quant::Direct => self.cps_direct(&e, mx, k),
            ExprKind::Perform(p) => self.cps_perform(p, &e, mx, k),
            ExprKind::Call(c)
                if c.tier == Tier::M
                    || o_callback_call(c)
                    || matches!(c.callee, Callee::Cont(_)) =>
            {
                self.cps_call(c, &e, mx, k)
            }
            _ => self.cps_direct(&e, mx, k),
        }
    }

    fn cps_perform(&mut self, p: &PerformNode, e: &Expr, mx: &mut Mx, k: Kc<'a>) -> Rs {
        let opc = crate::expr::op_const(&self.pkg.ops[p.op]);
        let at = self.loc(p.span);
        let mut fx = Fx::new(false);
        fx.m = true;
        let args: Vec<Rs> = p
            .args
            .iter()
            .map(|a| {
                let a = self.expr(a, &mut fx);
                self.bridged(a, &at)
            })
            .collect();
        let payload = self.boxed_payload(&p.args, &args);
        if p.quant == Quant::Zero {
            return quote!(
                tauto_rt::cps::abort(ev, m, Abort { op: #opc, args: #payload, at: #at })
            );
        }
        let r = self.ty_k(&e.ty);
        let kont = if p.result == Ty::Never {
            quote!(tauto_rt::cps::kont(move |_, _, _p: Payload| panic!(
                "tauto: a Never was answered"
            )))
        } else {
            self.payload_kont_raw(mx, k, &r)
        };
        quote!(tauto_rt::cps::perform(ev, m, #opc, #payload, #at, #kont))
    }

    /// The continuation of a `perform`, which takes the answer's `Payload`.
    fn payload_kont_raw(&mut self, mx: &mut Mx, k: Kc<'a>, r: &Rs) -> Rs {
        let r = r.clone();
        self.kont_text(mx, "p", &quote!(Payload), move |this, mx| {
            let v = this.tmp("v");
            let rest = this.deliver(mx, k, quote!(#v));
            quote!(let #v: #r = tauto_rt::ev::answer::<#r>(p); #rest)
        })
    }

    fn cps_call(&mut self, c: &CallNode, e: &Expr, mx: &mut Mx, k: Kc<'a>) -> Rs {
        let mut fx = Fx::new(false);
        fx.m = true;
        let call_at = self.loc(c.span);
        let mut args: Vec<Rs> = c
            .args
            .iter()
            .map(|a| {
                let a = self.expr(a, &mut fx);
                self.bridged(a, &call_at)
            })
            .collect();
        // A borrowed duplicable argument the callee takes as an owned copy.
        if let Callee::Inst(i) = &c.callee {
            let f = &self.pkg.fns[*i];
            for (n, a) in args.iter_mut().enumerate() {
                if self.m_owned_param(f, n) {
                    *a = quote!((*(#a)).clone());
                }
            }
        }
        match &c.callee {
            Callee::Cont(l) => {
                let target = self.payload_kont(mx, k, &e.ty);
                let (x, a0) = (lid(l), &args[0]);
                quote!(#x.call(ev, m, Box::new(#a0), #target))
            }
            Callee::Inst(i) => {
                let name = id(&self.fn_names[*i]);
                let turbofish = if c.targs.is_empty() {
                    Rs::new()
                } else {
                    let ts = comma(c.targs.iter().map(|t| self.ty(t)));
                    quote!(::<#ts>)
                };
                let ty = e.ty.clone();
                // A budget's step is charged after the arguments are
                // evaluated: they are bound before the tick.
                let mut bound = Rs::new();
                if c.tick == Tick::Budget {
                    for (n, a) in args.iter_mut().enumerate() {
                        let t = id(&format!("__ba{n}"));
                        bound.extend(quote!(let #t = #a;));
                        // The tick's continuation may run more than once
                        // (an `Fn`): each run passes a copy on.
                        *a = quote!(#t.clone());
                    }
                }
                let call = move |this: &mut Gen<'a>, mx: &mut Mx| {
                    let kont = this.typed_kont(mx, k, &ty);
                    let all = comma(
                        [quote!(ev), quote!(m)]
                            .into_iter()
                            .chain(args)
                            .chain([kont]),
                    );
                    quote!(#name #turbofish(#all))
                };
                match c.tick {
                    Tick::Host => {
                        let at = self.loc(c.span);
                        let call = call(self, mx);
                        quote!(tauto_rt::host_tick(#at); #call)
                    }
                    Tick::Budget => {
                        let at = self.loc(c.span);
                        let inner = self.kont_text(mx, "_t", &quote!(()), call);
                        quote!({ #bound tauto_rt::cps::tick(ev, m, #at, #inner) })
                    }
                    Tick::None => call(self, mx),
                }
            }
            Callee::Local(l)
                if o_callback_call(c) && matches!(l.repr, Repr::FnRef | Repr::BorrowClosure) =>
            {
                let kont = self.typed_kont(mx, k, &e.ty);
                let (x, at) = (lid(l), self.loc(c.span));
                let args = tuple(&args);
                quote!(tauto_rt::cps::call_o(m, #at, &#x, #args, #kont))
            }
            Callee::Local(_) | Callee::Value(_) if o_callback_call(c) => {
                let kont = self.typed_kont(mx, k, &e.ty);
                let at = self.loc(c.span);
                let function = match &c.callee {
                    Callee::Local(local) => {
                        let name = lid(local);
                        quote!(#name)
                    }
                    Callee::Value(value) => {
                        let v = self.expr(value, &mut fx);
                        self.bridged(v, &at)
                    }
                    _ => unreachable!(),
                };
                // The driver makes the call, with the handlers it runs the
                // computation under: the function and its arguments wait in
                // the step.
                let names: Vec<Ident> = (0..args.len()).map(|n| id(&format!("__oa{n}"))).collect();
                // The continuation takes its copies first: the step owns
                // the function and the arguments from here on.
                quote!({
                    let __ok = #kont;
                    let __of = #function;
                    #(let #names = #args;)*
                    tauto_rt::cps::call_o_future(
                        m,
                        #at,
                        move |ev| (__of)(ev, #(#names),*),
                        __ok,
                    )
                })
            }
            Callee::Local(l) => {
                let kont = self.typed_kont(mx, k, &e.ty);
                let x = lid(l);
                let all = comma(
                    [quote!(ev), quote!(m)]
                        .into_iter()
                        .chain(args)
                        .chain([kont]),
                );
                quote!(#x(#all))
            }
            _ => panic!(
                "tauto: a call of the M tier that is not to a function (a bug in the generator)"
            ),
        }
    }

    fn cps_block(&mut self, b: Block, i: usize, mx: &mut Mx, k: Kc<'a>) -> Rs {
        if i == b.stmts.len() {
            return match &b.tail {
                Some(t) => self.cps(t, mx, k),
                None => self.deliver(mx, k, quote!(())),
            };
        }
        let s = b.stmts[i].clone();
        match s {
            Stmt::Let {
                stack: _,
                local,
                ty,
                init,
                span,
            }
            | Stmt::Var {
                local,
                ty,
                init,
                span,
            } if !stmt_susp(&Stmt::Expr(init.clone()))
                && matches!(
                    (&init.kind, local.repr),
                    (ExprKind::Closure(_), Repr::BorrowClosure)
                ) =>
            {
                let _ = span;
                let mut fx = Fx::new(false);
                let text = self.stmt(
                    &Stmt::Let {
                        stack: false,
                        local: local.clone(),
                        ty: ty.clone(),
                        init,
                        span,
                    },
                    &mut fx,
                );
                self.add_local(mx, &local, &ty);
                let rest = self.cps_block(b, i + 1, mx, k);
                quote!(#text #rest)
            }
            Stmt::Let {
                local, ty, init, ..
            } => {
                let var = false;
                self.cps(
                    &init.clone(),
                    mx,
                    Kc::new(move |this, mx, v| {
                        this.add_local(mx, &local, &ty);
                        this.note_fn_local(&local, &ty);
                        let text = this.let_text(&local, &ty, &v, var);
                        let rest = this.cps_block(b, i + 1, mx, k);
                        quote!(#text #rest)
                    }),
                )
            }
            Stmt::Var {
                local, ty, init, ..
            } => self.cps(
                &init.clone(),
                mx,
                Kc::new(move |this, mx, v| {
                    this.add_local(mx, &local, &ty);
                    this.var_tys.insert(local.id, ty.clone());
                    let text = this.let_text(&local, &ty, &v, true);
                    let rest = this.cps_block(b, i + 1, mx, k);
                    quote!(#text #rest)
                }),
            ),
            Stmt::Assign { target, value, .. } => self.cps(
                &value.clone(),
                mx,
                Kc::new(move |this, mx, v| {
                    let x = lid(&target.local);
                    let text = match target.local.repr {
                        Repr::SharedVar(true) if target.path.is_empty() => quote!(#x.set(#v);),
                        Repr::SharedVar(false) if target.path.is_empty() => {
                            // The value's temporaries (a `borrow()` of the same
                            // cell) end before the cell is borrowed to write.
                            quote!({ let v = #v; *#x.borrow_mut() = v; })
                        }
                        _ => {
                            let place = this.place_mut(&target);
                            quote!(#place = #v;)
                        }
                    };
                    let rest = this.cps_block(b, i + 1, mx, k);
                    quote!(#text #rest)
                }),
            ),
            Stmt::Expr(e) => self.cps(
                &e.clone(),
                mx,
                Kc::new(move |this, mx, v| {
                    let rest = this.cps_block(b, i + 1, mx, k);
                    quote!(let _ = #v; #rest)
                }),
            ),
            Stmt::Return { value, .. } => {
                let fk = mx.fk.clone().expect("a function continuation");
                match value {
                    Some(v) => self.cps(&v, mx, Kc::Var(fk)),
                    None => quote!(#fk(m, ())),
                }
            }
            Stmt::While {
                cond,
                body,
                tick,
                span,
            } => {
                if !stmt_susp(&Stmt::While {
                    cond: cond.clone(),
                    body: body.clone(),
                    tick,
                    span,
                }) {
                    let w = Stmt::While {
                        cond,
                        body,
                        tick,
                        span,
                    };
                    let as_expr = Expr {
                        kind: ExprKind::Block(Block {
                            stmts: vec![w],
                            tail: None,
                        }),
                        ty: Ty::Unit,
                        span,
                    };
                    return self.cps(
                        &as_expr,
                        mx,
                        Kc::new(move |this, mx, _| this.cps_block(b, i + 1, mx, k)),
                    );
                }
                let rest_k = Kc::new(move |this, mx, _| this.cps_block(b, i + 1, mx, k));
                self.cps_while(cond, body, tick, span, mx, rest_k)
            }
        }
    }

    /// `let x = v;` and the like, as `Gen::stmt` writes them.
    fn let_text(&mut self, local: &Local, ty: &Ty, v: &Rs, var: bool) -> Rs {
        let x = lid(local);
        let annot = if ty.has_arm_generic() || (!var && local.repr != Repr::Plain) {
            Rs::new()
        } else {
            let t = self.ty(ty);
            quote!(: #t)
        };
        match (var, local.repr) {
            (true, Repr::SharedVar(true)) => quote!(let #x = Rc::new(Cell::new(#v));),
            (true, Repr::SharedVar(false)) => quote!(let #x = Rc::new(RefCell::new(#v));),
            _ => quote!(let mut #x #annot = #v;),
        }
    }

    /// A `while` that suspends: each round is a continuation that calls
    /// itself.
    fn cps_while(
        &mut self,
        cond: Expr,
        body: Block,
        tick: Tick,
        span: Span,
        mx: &mut Mx,
        k: Kc<'a>,
    ) -> Rs {
        // The `var`s declared outside the loop that its body assigns: a
        // continuation owns a copy of each, so the round that comes next and
        // the code after the loop take the values the round left, not the
        // ones from where the loop was written.
        let carried = {
            let mut found = BTreeMap::new();
            assigned_vars(&body, &mut found);
            assigned_vars_expr(&cond, &mut found);
            self.carried(mx, found)
        };
        if !carried.is_empty() {
            return self.cps_while_carrying(cond, body, tick, span, mx, k, carried);
        }
        let (pre, kv) = self.reify(mx, k, &Ty::Unit);
        let (pre, after) = match kv {
            Kc::Var(n) => (pre, n),
            other => {
                // A handler's target: the loop's exit is a continuation of its own.
                let name = self.tmp("kk");
                let clos = self.kont_text(mx, "v", &quote!(()), move |this, mx| {
                    this.deliver(mx, other, quote!(v))
                });
                (
                    quote!(#pre let #name: tauto_rt::cps::Kont<'_, ()> = #clos;),
                    name,
                )
            }
        };
        let lp = self.tmp("lp");
        let round = self.tmp("round");
        mx.scope.push(after.clone());
        mx.scope.push(lp.clone());
        let tick_text = match tick {
            Tick::Host => {
                let at = self.loc(span);
                quote!(tauto_rt::host_tick(#at);)
            }
            _ => Rs::new(),
        };
        let budget_at = (tick == Tick::Budget).then(|| self.loc(span));
        let lp2 = lp.clone();
        let after2 = after.clone();
        let step = self.kont_text(mx, "_u", &quote!(()), move |this, mx| {
            let again = quote!({
                let again = #lp2.borrow().as_ref().expect("a round").clone();
                let m2 = m.clone();
                tauto_rt::cps::more(move |ev| again(ev, &m2, ()))
            });
            let body_expr = Expr {
                kind: ExprKind::Block(body),
                ty: Ty::Unit,
                span,
            };
            let round = move |this: &mut Gen<'a>, mx: &mut Mx| {
                let then = this.cps(&body_expr, mx, Kc::new(move |_, _, _| again));
                let exit = quote!(#after2(ev, m, ()));
                this.cps(
                    &cond,
                    mx,
                    Kc::new(move |_, _, c| quote!(if #c { #then } else { #exit })),
                )
            };
            match budget_at {
                // The round goes on when the budgets in place have a step.
                Some(at) => {
                    let inner = this.kont_text(mx, "_t", &quote!(()), round);
                    quote!(tauto_rt::cps::tick(ev, m, #at, #inner))
                }
                None => {
                    let r = round(this, mx);
                    quote!(#tick_text #r)
                }
            }
        });
        quote!(
            #pre
            let #lp: Rc<RefCell<Option<tauto_rt::cps::Kont<'_, ()>>>> = Rc::new(RefCell::new(None));
            let #round = #step;
            *#lp.borrow_mut() = Some(#round.clone());
            #round(ev, m, ())
        )
    }

    /// A `while` that suspends and assigns `var`s from outside it: each round
    /// is a continuation that takes the values of those `var`s, and the code
    /// after the loop is written where the last round ends, with the values
    /// it left.
    #[allow(clippy::too_many_arguments)]
    fn cps_while_carrying(
        &mut self,
        cond: Expr,
        body: Block,
        tick: Tick,
        span: Span,
        mx: &mut Mx,
        k: Kc<'a>,
        carried: Vec<(Ident, Ty)>,
    ) -> Rs {
        let names: Vec<Ident> = carried.iter().map(|(x, _)| x.clone()).collect();
        let tys: Vec<Rs> = carried.iter().map(|(_, t)| self.ty_k(t)).collect();
        let st_ty = quote!((#(#tys,)*));
        let pack = {
            let names = names.clone();
            move || quote!((#(#names.clone(),)*))
        };
        let unpack = quote!(#[allow(unused_mut)] let (#(mut #names,)*) = st;);
        let lp = self.tmp("lp");
        let round = self.tmp("round");
        mx.scope.push(lp.clone());
        let tick_text = match tick {
            Tick::Host => {
                let at = self.loc(span);
                quote!(tauto_rt::host_tick(#at);)
            }
            _ => Rs::new(),
        };
        let budget_at = (tick == Tick::Budget).then(|| self.loc(span));
        let lp2 = lp.clone();
        let pack2 = pack.clone();
        let step = self.kont_text(mx, "st", &st_ty, move |this, mx| {
            let st = pack2();
            let again = quote!({
                let again = #lp2.borrow().as_ref().expect("a round").clone();
                let m2 = m.clone();
                let st = #st;
                tauto_rt::cps::more(move |ev| again(ev, &m2, st))
            });
            let body_expr = Expr {
                kind: ExprKind::Block(body),
                ty: Ty::Unit,
                span,
            };
            let round = move |this: &mut Gen<'a>, mx: &mut Mx| {
                let then = this.cps(&body_expr, mx, Kc::new(move |_, _, _| again));
                let exit = this.deliver(mx, k, quote!(()));
                this.cps(
                    &cond,
                    mx,
                    Kc::new(move |_, _, c| quote!(if #c { #then } else { #exit })),
                )
            };
            match budget_at {
                // The round goes on when the budgets in place have a step.
                Some(at) => {
                    let inner = this.kont_text(mx, "_t", &quote!(()), round);
                    quote!(#unpack tauto_rt::cps::tick(ev, m, #at, #inner))
                }
                None => {
                    let r = round(this, mx);
                    quote!(#unpack #tick_text #r)
                }
            }
        });
        let st0 = pack();
        quote!(
            let #lp: Rc<RefCell<Option<tauto_rt::cps::Kont<'_, #st_ty>>>> = Rc::new(RefCell::new(None));
            let #round = #step;
            *#lp.borrow_mut() = Some(#round.clone());
            #round(ev, m, #st0)
        )
    }

    /// A `budget` in code of the M tier: a frame among the handlers in place
    /// that the steps are counted in, left where the body ends.
    fn cps_budget(&mut self, b: &BudgetNode, ty: &Ty, mx: &mut Mx, k: Kc<'a>) -> Rs {
        let bid = num(b.id as u64);
        let outside = mx.scope.clone();
        let (pre_k, kv) = self.reify(mx, k, ty);
        let erased_target = match kv {
            Kc::Var(n) => quote!(tauto_rt::cps::erase(#n.clone())),
            Kc::Erased(n) => quote!(#n.clone()),
            Kc::Fn(_) => unreachable!(),
        };
        let bty = self.ty_k(ty);
        let (kb, target, steps, tgt) = (
            id(&format!("kb{}", b.id)),
            id(&format!("target{}", b.id)),
            id(&format!("steps{}", b.id)),
            id(&format!("tgt{}", b.id)),
        );
        let kb_text = {
            let tgt = tgt.clone();
            self.kont_text(mx, "v", &bty, move |this, mx| {
                mx.scope.push(tgt.clone());
                let inner = this.deliver(mx, Kc::Erased(tgt.clone()), quote!(v));
                quote!(let (mo, #tgt) = m.pop(); let m = &mo; #inner)
            })
        };
        let body = b.body.clone();
        let steps_e = b.steps.clone();
        let push = if b.memory {
            id("push_budget_memory")
        } else {
            id("push_budget")
        };
        mx.scope.push(kb.clone());
        mx.scope.push(steps.clone());
        let body_text = self.cps(&body, mx, Kc::Var(kb.clone()));
        let rest = quote!(
            #pre_k
            let #target: tauto_rt::cps::Kont<'_, Payload> = #erased_target;
            let #kb = #kb_text;
            let mb = m.#push::<#bty>(#bid, #steps, #target);
            let m = &mb;
            #body_text
        );
        // The steps are given before the body starts; they are a value of the
        // surrounding code, where the names above are not yet bound.
        mx.scope = outside;
        let name = steps.clone();
        self.cps(
            &steps_e,
            mx,
            Kc::new(move |_, _, v| quote!(let #name = #v; #rest)),
        )
    }

    /// A `handle` whose body may resume more than once.
    fn cps_handle(&mut self, h: &HandleNode, ty: &Ty, mx: &mut Mx, k: Kc<'a>) -> Rs {
        let hid = h.id;
        let (pre_k, kv) = self.reify(mx, k, ty);
        let erased_target = match kv {
            Kc::Var(n) => quote!(tauto_rt::cps::erase(#n.clone())),
            Kc::Erased(n) => quote!(#n.clone()),
            Kc::Fn(_) => unreachable!(),
        };
        let target = id(&format!("target{hid}"));
        let kb = id(&format!("kb{hid}"));
        let armn = id(&format!("arm{hid}"));
        let mn = id(&format!("m{hid}"));

        // The arm of the return clause, run where the body ends.
        let bty = self.ty_k(&h.body_ty);
        let ret = h.ret.clone();
        let (body_ty, h_span) = (h.body_ty.clone(), h.span);
        let tgt = id(&format!("tgt{hid}"));
        let mo = id(&format!("mo{hid}"));
        let kb_text = {
            let (tgt, mo) = (tgt.clone(), mo.clone());
            self.kont_text(mx, "v", &bty, move |this, mx| {
                mx.scope.push(tgt.clone());
                let reply = Kc::Erased(tgt.clone());
                let inner = if body_ty == Ty::Never {
                    quote!(match v {})
                } else {
                    match &ret {
                        None => this.deliver(mx, reply, quote!(v)),
                        Some(arm) => {
                            this.add_pat(mx, &arm.pat);
                            let mut out = PatOut::default();
                            let pat = this.pat(&arm.pat, false, &mut out);
                            let guard = PatOut::guard_clause(&out.guards);
                            let at = this.loc(h_span);
                            let body = this.cps(&arm.body, mx, reply);
                            let prologue = out.prologue();
                            quote!(match v { #pat #guard => { #prologue #body }, _ => tauto_rt::no_arm(#at) })
                        }
                    }
                };
                quote!(let (#mo, #tgt) = m.pop(); let m = &#mo; #inner)
            })
        };
        // `m` inside the closure above is the chain with the handler on top.
        let arm_text = self.arm_text(h, ty, mx);

        let mut ops: Vec<usize> = Vec::new();
        for a in m_arms(h) {
            if !ops.contains(&a.op) {
                ops.push(a.op);
            }
        }
        let ids = comma(ops.iter().map(|o| {
            let n = num(self.pkg.ops[*o].id as u64);
            quote!(#n)
        }));

        mx.scope.push(kb.clone());
        let adapt = if !h.direct.is_empty() {
            let a = self.direct_adapt(&h.direct);
            quote!(Some(#a))
        } else {
            quote!(None)
        };
        let body = self.cps(&h.body, mx, Kc::Var(kb.clone()));
        quote!(
            #pre_k
            let #target: tauto_rt::cps::Kont<'_, Payload> = #erased_target;
            let #kb = #kb_text;
            let #armn = #arm_text;
            let #mn = m.push_direct(&[#ids], #armn, #target, #adapt);
            let m = &#mn;
            #body
        )
    }

    /// The [`tauto_rt::cps::Adapt`] of a handler's `direct` arms, in code
    /// that holds no `direct` handler from around it: an operation a
    /// function value performs with its arguments of their types goes to
    /// the arms boxed, and the answer comes back of its type.
    fn direct_adapt(&mut self, arms: &[OpArm]) -> Rs {
        let mut ops: Vec<usize> = Vec::new();
        for a in arms {
            if !ops.contains(&a.op) {
                ops.push(a.op);
            }
        }
        let mut body = Rs::new();
        for op in &ops {
            let opc = crate::expr::op_const(&self.pkg.ops[*op]);
            let mine: Vec<&OpArm> = arms.iter().filter(|a| a.op == *op).collect();
            for (params, group) in self.arm_groups(*op, &mine) {
                let tup = self.payload_ty(&params);
                let r = match group.first() {
                    Some(a) => self.answer_ty(&a.body.ty),
                    None => quote!(_),
                };
                body.extend(quote!(
                    if op == #opc.id {
                        if let Some(io) = io.downcast_mut::<tauto_rt::ev::Io<#tup, #r>>() {
                            if let Some(a) = io.take_args() {
                                match run(#opc, Box::new(a)) {
                                    Ok(r) => {
                                        *io = tauto_rt::ev::Io::Answer(tauto_rt::ev::answer::<#r>(r));
                                        return true;
                                    }
                                    Err(a) => { *io = tauto_rt::ev::Io::Args(tauto_rt::ev::answer::<#tup>(a)); }
                                }
                            }
                        } else if let Some(io) = io.downcast_mut::<tauto_rt::ev::Io<Payload, Payload>>() {
                            if let Some(a) = io.take_args() {
                                match run(#opc, a) {
                                    Ok(r) => { *io = tauto_rt::ev::Io::Answer(r); return true; }
                                    Err(a) => { *io = tauto_rt::ev::Io::Args(a); }
                                }
                            }
                        }
                    }
                ));
            }
        }
        quote!({
            let adapt: std::rc::Rc<tauto_rt::cps::Adapt> = std::rc::Rc::new(
                |op: u32, io: &mut dyn std::any::Any, run: &mut dyn FnMut(tauto_rt::Op, Payload) -> Result<Payload, Payload>| -> bool {
                    #body
                    false
                },
            );
            adapt
        })
    }

    /// The closure that runs the arm of an operation the handler takes.
    fn arm_text(&mut self, h: &HandleNode, ty: &Ty, mx: &mut Mx) -> Rs {
        let hid = h.id;
        let tgt = id(&format!("tgt{hid}"));
        let res = id(&format!("res{hid}"));
        let mo = id(&format!("mo{hid}"));
        let visible = mx.scope.clone();
        let saved = mx.scope.clone();
        mx.scope.push(tgt.clone());
        mx.scope.push(res.clone());
        let mut ops: Vec<usize> = Vec::new();
        for a in m_arms(h) {
            if !ops.contains(&a.op) {
                ops.push(a.op);
            }
        }
        let _ = ty;
        let mut groups = Rs::new();
        for op in &ops {
            let opc = crate::expr::op_const(&self.pkg.ops[*op]);
            let mine: Vec<OpArm> = m_arms(h).filter(|a| a.op == *op).cloned().collect();
            let refs: Vec<&OpArm> = mine.iter().collect();
            for (params, group) in self.arm_groups(*op, &refs) {
                let tup = self.payload_ty(&params);
                let mut tries = Rs::new();
                for arm in group {
                    let inner_saved = mx.scope.clone();
                    let mut out = PatOut::default();
                    let pats: Vec<Rs> = arm
                        .pats
                        .iter()
                        .map(|p| self.pat(p, false, &mut out))
                        .collect();
                    for p in &arm.pats {
                        self.add_pat(mx, p);
                    }
                    let pat = tuple(&pats);
                    let mut guards = out.guards.clone();
                    if let Some(gd) = &arm.guard {
                        let gd = self.expr(gd, &mut Fx::new(false));
                        let gd = self.bridged(gd, &quote!(at));
                        guards.push(out.user_guard(gd));
                    }
                    let guard = PatOut::guard_clause(&guards);
                    let kdef = match &arm.k {
                        Some(k) => {
                            mx.scope.push(lid(k));
                            self.conts.insert(k.id);
                            let k = lid(k);
                            quote!(let #k = #res.clone();)
                        }
                        None => Rs::new(),
                    };
                    // A `direct` arm's value is the answer: `k(e)` without the
                    // `k`.
                    let reply = if h.direct.iter().any(|d| d.op == arm.op) {
                        let (res, tgt) = (res.clone(), tgt.clone());
                        Kc::new(
                            move |_, _, v| quote!(#res.call(ev, m, Box::new(#v) as Payload, #tgt.clone())),
                        )
                    } else {
                        Kc::Erased(tgt.clone())
                    };
                    let code = self.cps(&arm.body, mx, reply);
                    let prologue = out.prologue();
                    tries.extend(quote!(
                        match a {
                            #pat #guard => {
                                #prologue
                                #kdef
                                return { #code };
                            }
                            other => { a = other; }
                        }
                    ));
                    mx.scope = inner_saved;
                }
                groups.extend(quote!(
                    if op.id == #opc.id {
                        match args.downcast::<#tup>() {
                            Ok(b) => {
                                let mut a = *b;
                                #tries
                                args = Box::new(a);
                            }
                            Err(b) => { args = b; }
                        }
                    }
                ));
            }
        }
        let text = quote!(#groups tauto_rt::cps::Step::NoMatch(args));
        mx.scope = saved;
        let used = mentioned(&visible, &text);
        let outer = clone_each(used.iter().cloned());
        let inner = clone_each_mut(used.iter().cloned());
        quote!({
            #outer
            tauto_rt::cps::arm(move |ev, #mo, #tgt, op, mut args, at, #res| {
                let m = #mo;
                #inner
                #text
            })
        })
    }

    /// A `handle` in a function of another tier: the computation is run by a
    /// driver.
    pub(crate) fn handle_host_m(&mut self, h: &HandleNode, fx: &mut Fx) -> Rs {
        self.without_evd(|g| g.handle_host_m_inner(h, fx))
    }

    pub(crate) fn handle_host_m_inner(&mut self, h: &HandleNode, fx: &mut Fx) -> Rs {
        let mut mx = Mx::new(None);
        mx.scope = h.clones.iter().map(lid).collect();
        let ty = h.result.clone();
        // A `return` inside ends the driver with the function's value
        // through `fret`, which drops the rest of the computation.
        if h.host_ret.is_some() {
            mx.fk = Some(id("fret"));
            mx.scope.push(id("fret"));
        }
        let body = self.cps_handle(h, &ty, &mut mx, Kc::Var(id("fin")));
        let r = self.ty_k(&h.result);
        let ks = if h.host_ret.is_some() {
            quote!(fin, fret)
        } else {
            quote!(fin)
        };
        let (run, run_a, run_o) = if h.host_ret.is_some() {
            ("run_r", "run_ar", "run_or")
        } else {
            ("run", "run_a", "run_o")
        };
        // The computation runs with the handlers of this code; a kept `k`
        // takes the handlers of whoever resumes it.
        let driver = |name: &str| {
            let name = id(&format!("{name}_in"));
            quote!(tauto_rt::cps::#name(ev, |ev, m, #ks| { #body }))
        };
        let call = if fx.o {
            let d = driver(run_o);
            quote!(#d.await)
        } else if fx.ret_a || !fx.targets.is_empty() {
            self.take_result(driver(run_a), fx)
        } else {
            driver(run)
        };
        match &h.host_ret {
            Some(rt) => {
                let rt = self.ty_k(rt);
                let leave = if fx.ret_a {
                    quote!(return Ok(r))
                } else {
                    quote!(return r)
                };
                quote!(match #call {
                    tauto_rt::cps::Flow::Value(v) => v,
                    tauto_rt::cps::Flow::Return(r) => { let r: #rt = r; #leave }
                })
            }
            None => quote!({ let r: #r = #call; r }),
        }
    }

    pub(crate) fn fn_def_m(
        &mut self,
        f: &FnInst,
        name: &str,
        gens: &Rs,
        params: &[Rs],
        ret: &Rs,
    ) -> Rs {
        let mut mx = Mx::new(Some(id("fk")));
        mx.scope.push(id("fk"));
        for p in &f.params {
            self.add_local(&mut mx, &p.local, &p.ty);
        }
        let body = self.cps(&f.body, &mut mx, Kc::Var(id("fk")));
        let mut ps = vec![quote!(ev: &Ev<'_>), quote!(m: &tauto_rt::cps::M<'a>)];
        ps.extend(params.iter().cloned());
        ps.push(quote!(fk: tauto_rt::cps::Kont<'a, #ret>));
        let ps = comma(ps);
        let (doc, name) = (crate::tok::doc(&f.source), id(name));
        quote!(
            #doc
            pub fn #name #gens(#ps) -> tauto_rt::cps::Step<'a> {
                let m_o = m.clone();
                tauto_rt::cps::more(move |ev| {
                    let m = &m_o;
                    #body
                })
            }
        )
    }
}

impl<'a> Gen<'a> {
    /// A closure of the M tier: a function of the handlers in place and its
    /// own continuation.
    pub(crate) fn closure_m(&mut self, c: &ClosureNode) -> Rs {
        let outer = self.m_scope.clone();
        let mut mx = Mx::new(Some(id("fk")));
        mx.scope = outer.clone();
        mx.scope.push(id("fk"));
        let mut params = vec![quote!(ev), quote!(m)];
        for (l, t) in &c.params {
            self.add_local(&mut mx, l, t);
            self.note_fn_local(l, t);
            let (x, t) = (lid(l), self.ty(t));
            params.push(quote!(#x: #t));
        }
        params.push(quote!(fk));
        let params = comma(params);
        let body = self.cps(&c.body, &mut mx, Kc::Var(id("fk")));
        // The closure's own `fk` shadows any outer one: it is not captured,
        // and a closure made outside the M tier has none to capture.
        let own = id("fk");
        let outer: Vec<Ident> = outer.into_iter().filter(|n| *n != own).collect();
        let mut used = mentioned(&outer, &body);
        // Made outside the M tier, the closure has no chain in scope: what
        // it captures is what the closure node says, cloned as in
        // `closure_raw` (`ClosureNode::clones`).
        for l in &c.clones {
            let x = lid(l);
            if !used.contains(&x) {
                used.push(x);
            }
        }
        let inner = clone_each_mut(used.iter().cloned());
        let outer_clones = clone_each(used.iter().cloned());
        let kind = if c.fn_ty.kind.dup() { "rc" } else { "box" };
        let helper = id(&format!("mfn_{kind}{}", c.params.len()));
        quote!({
            #outer_clones
            tauto_rt::cps::#helper(move |#params| {
                #inner
                #body
            })
        })
    }
}
