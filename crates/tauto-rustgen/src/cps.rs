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

use proc_macro2::Ident;
use quote::quote;
use tauto_nir::*;

use crate::expr::{Fx, PatOut, clone_each, clone_each_mut, lid};
use crate::tok::{Rs, comma, id, is_simple, is_unit, mentioned, num, tuple};
use crate::{Gen, Pred};

pub(crate) struct Mx {
    /// The locals in scope that a continuation must own a copy of.
    pub scope: Vec<Ident>,
    /// The function's own continuation, which `return` calls.
    pub fk: Option<Ident>,
}

impl Mx {
    pub fn new(fk: Option<Ident>) -> Mx {
        Mx {
            scope: Vec::new(),
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

/// The arms of a handler of the M tier: the `direct` ones too, where the
/// code holds no `direct` handler (`HandleNode::detached`).
fn m_arms(h: &HandleNode) -> impl Iterator<Item = &OpArm> {
    let direct: &[OpArm] = if h.detached { &h.direct } else { &[] };
    h.aborts.iter().chain(&h.susp).chain(direct)
}

/// Whether the expression suspends (or returns), so it is written in
/// continuation-passing style.
pub(crate) fn susp(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Perform(p) => p.quant != Quant::Direct || p.detached || p.args.iter().any(susp),
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
        ExprKind::Product { members, .. } => members.iter().any(susp),
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
        | ExprKind::Member { value, .. }
        | ExprKind::Deref { value, .. } => susp(value),
        _ => false,
    }
}

/// A call of a borrowed function of the O tier (one that may diverge under a
/// budget): in code of the M tier it is answered through the budgets in the
/// handlers in place, so it is written in continuation-passing style.
fn o_callback_call(c: &CallNode) -> bool {
    c.tier == Tier::O
        && matches!(&c.callee, Callee::Local(l) if matches!(l.repr, Repr::FnRef | Repr::BorrowClosure))
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
        if crate::expr::m_o_callback(l, t) {
            return true;
        }
        match l.repr {
            Repr::SharedVar(true) | Repr::SharedVar(false) => true,
            Repr::Plain => self.ty_has(t, Pred::Clone),
            _ => false,
        }
    }

    fn add_local(&self, mx: &mut Mx, l: &Local, t: &Ty) {
        if self.dup_local(l, t) {
            mx.scope.push(lid(l));
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
        let text = body(self, mx);
        mx.scope = visible.clone();
        let used = mentioned(&visible, &text);
        let outer = clone_each(used.iter().cloned());
        let inner = clone_each_mut(used.iter().cloned());
        let arg = id(arg);
        quote!({
            let ev_o = ev_o.clone();
            #outer
            tauto_rt::cps::kont(move |m, #arg: #arg_ty| {
                let ev = &ev_o;
                #inner
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
            quote!(#n(m, #v))
        }
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
                        let (pre, kv) = this.reify(mx, k, &ty);
                        let t = this.cps(&then, mx, kv.dup());
                        let o = match &otherwise {
                            Some(o) => this.cps(o, mx, kv.dup()),
                            None => this.deliver(mx, kv.dup(), quote!(())),
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
        // A closure that goes into a `Payload` is boxed as its own type
        // unless it is given the type of the function value first.
        if matches!(k, Kc::Erased(_)) && matches!(e.ty, Ty::Fn(_)) && !abort {
            let t = self.ty(&e.ty);
            code = quote!({ let f: #t = #code; f });
        }
        if abort {
            let t = self.tmp("v");
            let ok = self.deliver(mx, k, quote!(#t));
            quote!(
                match (|| -> Result<_, Abort> { Ok(#code) })() {
                    Ok(#t) => { #ok }
                    Err(a) => tauto_rt::cps::abort(m, a),
                }
            )
        } else {
            self.deliver(mx, k, code)
        }
    }

    fn cps_match(&mut self, m: MatchNode, ty: Ty, scrut: Rs, mx: &mut Mx, k: Kc<'a>) -> Rs {
        let (pre, kv) = self.reify(mx, k, &ty);
        let scrut = crate::expr::cell_free_scrutinee(&m, scrut);
        let mut arms = Vec::new();
        for arm in &m.arms {
            let saved = mx.scope.clone();
            let mut out = PatOut::default();
            let pat = self.pat(&arm.pat, m.by_ref, &mut out);
            if !m.by_ref {
                self.add_pat(mx, &arm.pat);
            }
            let mut guards = out.guards.clone();
            if let Some(g) = &arm.guard {
                let g = self.expr(g, &mut Fx::new(false));
                guards.push(out.user_guard(g));
            }
            let guard = PatOut::guard_clause(&guards);
            let body = self.cps(&arm.body, mx, kv.dup());
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
        let opc = id(&format!("OP_{}", self.pkg.ops[p.op].name));
        let at = self.loc(p.span);
        let mut fx = Fx::new(false);
        fx.m = true;
        let args: Vec<Rs> = p.args.iter().map(|a| self.expr(a, &mut fx)).collect();
        let payload = self.boxed_payload(&p.args, &args);
        if p.quant == Quant::Zero {
            return quote!(
                tauto_rt::cps::abort(m, Abort { op: #opc, args: #payload, at: #at })
            );
        }
        let r = self.ty_k(&e.ty);
        let kont = if p.result == Ty::Never {
            quote!(tauto_rt::cps::kont(move |m, p: Payload| panic!(
                "tauto: a Never was answered"
            )))
        } else {
            self.payload_kont_raw(mx, k, &r)
        };
        if p.detached {
            return quote!(tauto_rt::cps::perform_direct(ev, m, #opc, #payload, #at, #kont));
        }
        quote!(tauto_rt::cps::perform(m, #opc, #payload, #at, #kont))
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
        let args: Vec<Rs> = c.args.iter().map(|a| self.expr(a, &mut fx)).collect();
        match &c.callee {
            Callee::Cont(l) => {
                let target = self.payload_kont(mx, k, &e.ty);
                let (x, a0) = (lid(l), &args[0]);
                quote!(#x.call(m, Box::new(#a0), #target))
            }
            Callee::Inst(i) => {
                let f = &self.pkg.fns[*i];
                let name = id(&f.rust_name);
                let turbofish = if c.targs.is_empty() {
                    Rs::new()
                } else {
                    let ts = comma(c.targs.iter().map(|t| self.ty(t)));
                    quote!(::<#ts>)
                };
                let ty = e.ty.clone();
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
                        quote!(tauto_rt::cps::tick(m, #at, #inner))
                    }
                    Tick::None => call(self, mx),
                }
            }
            Callee::Local(l) if o_callback_call(c) => {
                let kont = self.typed_kont(mx, k, &e.ty);
                let (x, at) = (lid(l), self.loc(c.span));
                let args = tuple(&args);
                quote!(tauto_rt::cps::call_o(ev, m, #at, &#x, #args, #kont))
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
        let annot = if ty.has_infer() || (!var && local.repr != Repr::Plain) {
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
                tauto_rt::cps::more(move || again(&m2, ()))
            });
            let body_expr = Expr {
                kind: ExprKind::Block(body),
                ty: Ty::Unit,
                span,
            };
            let round = move |this: &mut Gen<'a>, mx: &mut Mx| {
                let then = this.cps(&body_expr, mx, Kc::new(move |_, _, _| again));
                let exit = quote!(#after2(m, ()));
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
                    quote!(tauto_rt::cps::tick(m, #at, #inner))
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
            #round(m, ())
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
            let mb = m.#push::<#bty>(#bid, u64::try_from(#steps).unwrap_or(0), #target);
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
        let direct = if h.direct.is_empty() || h.detached {
            Rs::new()
        } else {
            let names = mx.scope.clone();
            self.direct_handler(&h.direct, Some(&names))
        };
        let body = self.cps(&h.body, mx, Kc::Var(kb.clone()));
        quote!(
            #pre_k
            let #target: tauto_rt::cps::Kont<'_, Payload> = #erased_target;
            let #kb = #kb_text;
            let #armn = #arm_text;
            let #mn = m.push(&[#ids], #armn, #target);
            #direct
            let m = &#mn;
            #body
        )
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
            let opc = id(&format!("OP_{}", self.pkg.ops[*op].name));
            let mine: Vec<OpArm> = m_arms(h).filter(|a| a.op == *op).cloned().collect();
            let tup = self.payload_ty(&mine[0].params);
            let mut tries = Rs::new();
            for arm in &mine {
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
                let reply = if h.detached && h.direct.iter().any(|d| d.op == arm.op) {
                    let (res, tgt) = (res.clone(), tgt.clone());
                    Kc::new(
                        move |_, _, v| quote!(#res.call(m, Box::new(#v) as Payload, #tgt.clone())),
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
        let text = quote!(#groups tauto_rt::cps::Step::NoMatch(args));
        mx.scope = saved;
        let used = mentioned(&visible, &text);
        let outer = clone_each(used.iter().cloned());
        let inner = clone_each_mut(used.iter().cloned());
        quote!({
            let ev_o = ev_o.clone();
            #outer
            tauto_rt::cps::arm(move |#mo, #tgt, op, mut args, at, #res| {
                let ev = &ev_o;
                let m = #mo;
                #inner
                #text
            })
        })
    }

    /// A `handle` in a function of another tier: the computation is run by a
    /// driver.
    pub(crate) fn handle_host_m(&mut self, h: &HandleNode, fx: &mut Fx) -> Rs {
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
        // The continuation of a kept `k` holds no handler from here: the
        // driver answers the `direct` operations, with the handlers of
        // whoever runs it.
        let kept = h.kept;
        let driver = |name: &str| {
            if kept {
                let name = id(&format!("{name}_in"));
                quote!(
                    tauto_rt::cps::#name(ev, |m, #ks| {
                        let ev_o = Ev::empty();
                        let ev = &ev_o;
                        #body
                    })
                )
            } else {
                let name = id(name);
                quote!(
                    tauto_rt::cps::#name(|m, #ks| {
                        let ev_o = ev.clone();
                        let ev = &ev_o;
                        #body
                    })
                )
            }
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

    pub(crate) fn fn_def_m(&mut self, f: &FnInst, gens: &Rs, params: &[Rs], ret: &Rs) -> Rs {
        let mut mx = Mx::new(Some(id("fk")));
        mx.scope.push(id("fk"));
        for p in &f.params {
            self.add_local(&mut mx, &p.local, &p.ty);
        }
        let body = self.cps(&f.body, &mut mx, Kc::Var(id("fk")));
        let mut ps = vec![quote!(ev: &Ev<'a>), quote!(m: &tauto_rt::cps::M<'a>)];
        ps.extend(params.iter().cloned());
        ps.push(quote!(fk: tauto_rt::cps::Kont<'a, #ret>));
        let ps = comma(ps);
        let (doc, name) = (crate::tok::doc(&f.source), id(&f.rust_name));
        quote!(
            #doc
            pub fn #name #gens(#ps) -> tauto_rt::cps::Step<'a> {
                let ev_o = ev.clone();
                let m_o = m.clone();
                tauto_rt::cps::more(move || {
                    let ev = &ev_o;
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
            let (x, t) = (lid(l), self.ty(t));
            params.push(quote!(#x: #t));
        }
        params.push(quote!(fk));
        let params = comma(params);
        let body = self.cps(&c.body, &mut mx, Kc::Var(id("fk")));
        let used = mentioned(&outer, &body);
        let inner = clone_each_mut(used.iter().cloned());
        let outer_clones = clone_each(used.iter().cloned());
        let kind = if c.fn_ty.kind.dup() { "rc" } else { "box" };
        let helper = id(&format!("mfn_{kind}{}", c.params.len()));
        quote!({
            #outer_clones
            tauto_rt::cps::#helper(move |#params| {
                let ev_o = ev.clone();
                let ev = &ev_o;
                #inner
                #body
            })
        })
    }
}
