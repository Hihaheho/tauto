use crate::types::{Quant, Ty as TTy};
use tauto_surface::surface::{Handler, SurfaceTerm, TermKind};

use super::*;

/// The continuation of a `direct` arm: every path ends in `k(e)`, and the
/// arm's value is the `e`.
pub(crate) struct TailK {
    pub k: Name,
    pub ans: TTy,
}

impl<'a> Lowerer<'a> {
    fn operation_instance(
        &mut self,
        checked: &crate::types::CheckedOperationInstance,
    ) -> OperationInstance {
        OperationInstance {
            type_args: checked.type_args.iter().map(|t| self.conv(t)).collect(),
            params: checked.params.iter().map(|t| self.conv(t)).collect(),
            answer: self.conv(&checked.answer),
            admission: checked.admission,
        }
    }

    /// The type the declaration of `effect` writes for its `i`th parameter.
    pub(crate) fn effect_param_written(&self, effect: &Name, i: usize) -> Option<SurfaceTerm> {
        self.effect_decls.get(effect)?.params.get(i)?.clone()
    }

    /// The tier a function passed for the `i`th parameter of `effect` is
    /// made at: the one the row written on the declared parameter gives,
    /// whatever its own body performs, as the arms take it
    /// (`effect_param_written`).
    fn performed_tier(&self, cx: &Cx, effect: &Name, i: usize) -> Option<(SurfaceTerm, Tier)> {
        let w = self.effect_param_written(effect, i)?;
        let effects = pi_effects(&w)?;
        let tier = self.value_tier_in(&effects.into_iter().collect(), cx);
        Some((w, tier))
    }

    /// The index of the operation `effect` in the package, declared on first
    /// use.
    pub fn op_index(&mut self, effect: &Name) -> usize {
        if let Some(i) = self.op_ids.get(effect) {
            return *i;
        }
        let sig = self.types.effects.get(effect).cloned();
        let (generics, params, result) = match sig {
            Some(sig) => {
                let g = sig.generics.iter().map(|p| p.name().to_string()).collect();
                let params = sig.params.iter().map(|p| self.conv(p)).collect();
                let result = self.conv(&sig.result);
                (g, params, result)
            }
            None => (Vec::new(), Vec::new(), Ty::Unit),
        };
        let quant = self.quant(effect);
        // `show` is 0 and the budget's `exceeded` is 1 (`tauto_rt::budget`).
        let id = match effect {
            name if tauto_surface::bindings::is_library(name, "show") => 0,
            name if tauto_surface::bindings::is_library(name, "exceeded") => 1,
            _ => {
                self.ops
                    .iter()
                    .filter(|o| {
                        !tauto_surface::bindings::is_library(&o.name, "show")
                            && !tauto_surface::bindings::is_library(&o.name, "exceeded")
                    })
                    .count() as u32
                    + 2
            }
        };
        self.ops.push(OpDef {
            id,
            name: effect.clone(),
            quant,
            generics,
            params,
            result,
        });
        let i = self.ops.len() - 1;
        self.op_ids.insert(effect.clone(), i);
        i
    }

    /// `perform spawn(f)` is `Task { result: pending_spawn(f) }`: where the
    /// body runs is the host's to choose (`tauto_rt::exec`). The arms of
    /// a handler for `spawn` are not lowered.
    fn spawn(&mut self, cx: &mut Cx, t: &SurfaceTerm, f: &SurfaceTerm) -> R<Expr> {
        let span = t.span;
        self.spawns = true;
        let Some(ctor) = self.ctor_ref(&tauto_surface::bindings::library_name("Task::Mk")) else {
            return unsupported(msg!("nir-spawn-without-the-std-task"), span);
        };
        let ret = match self.types.term(f).map(|t| t.unborrowed().clone()) {
            Some(TTy::Fn(_, r, _)) => *r,
            _ => return unsupported(msg!("nir-a-spawn-of-a-value-that"), span),
        };
        let mut body = self.expr(cx, f)?;
        // A name's type does not say whether calling it may suspend; its row
        // does, and a body that may wait is spawned as a future.
        let row = self.value_row(cx, f);
        if let (Some(row), Ty::Fn(ft)) = (&row, &mut body.ty) {
            ft.tier = ft.tier.max(self.row_tier_in(row, cx));
        }
        // A task runs apart from the handlers around its `spawn`: the host
        // answers what it asks, as it does at the top level.
        if self.hosted() && self.rows.target != Target::Llvm {
            // The arms of what the task's row says it performs, or all of
            // them when the row is open.
            let answered: Option<BTreeSet<String>> = row.as_ref().and_then(|r| {
                r.iter()
                    .all(|e| e.row_variable().is_none() && !e.starts_with('?'))
                    .then(|| r.iter().map(|e| e.to_string()).collect())
            });
            body = self.task_under_host(cx, body, answered.as_ref())?;
        }
        let result = self.conv(&ret);
        let pending = Expr {
            ty: Ty::Std(tauto_nir::StdType::Pending, vec![result]),
            kind: ExprKind::Call(Box::new(CallNode {
                callee: Callee::Builtin("pending_spawn".into()),
                args: vec![body],
                tier: Tier::S,
                targs: Vec::new(),
                tick: Tick::None,
                recur: false,
                unwind: Vec::new(),
                span,
            })),
            span,
        };
        let ty = self.ety(t);
        Ok(Expr {
            kind: ExprKind::Ctor {
                ctor,
                fields: vec![(Some("result".to_string()), pending)],
            },
            ty,
            span,
        })
    }

    pub fn perform(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        effect: &Name,
        args: &[SurfaceTerm],
    ) -> R<Expr> {
        let span = t.span;
        if tauto_surface::bindings::is_library(&effect, "spawn") && args.len() == 1 {
            return self.spawn(cx, t, &args[0]);
        }
        let quant = if tauto_surface::bindings::is_library(&effect, "show") {
            Quant::Direct
        } else {
            self.quant(effect)
        };
        let op = self.op_index(effect);
        let ty = self.ety(t);
        let checked = self
            .operation_facts
            .and_then(|facts| facts.perform(t.id()))
            .cloned();
        let instance = checked
            .as_ref()
            .map(|instance| self.operation_instance(instance));
        let mut out = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let written = self.performed_tier(cx, effect, i);
            let lam_params = match (&*a.kind, self.types.term(a).map(|t| t.unborrowed().clone())) {
                (TermKind::Lam { .. }, Some(TTy::Fn(ps, ..))) => Some(ps),
                _ => None,
            };
            let e = match (&written, lam_params) {
                // A closure literal is made for the declared tier, as one
                // passed to a function's parameter is (`call_args`).
                (Some((_, tier)), Some(ps)) => {
                    self.closure(cx, a, Some(*tier), false, Some(&ps))?
                }
                _ => match checked
                    .as_ref()
                    .filter(|instance| instance.admission == OperationAdmission::Unique)
                {
                    Some(instance) => match instance.params.get(i) {
                        Some(formal) => self.expr_expect(cx, a, formal)?,
                        None => self.expr(cx, a)?,
                    },
                    None => self.expr(cx, a)?,
                },
            };
            let mut e = self.deref_if_ref(e);
            // Passed as the arms take it: of the kind and the tier the
            // declaration writes.
            let declared = self
                .types
                .effects
                .get(effect)
                .and_then(|s| s.params.get(i))
                .cloned();
            if let (Some((w, _)), Ty::Fn(_), Some(TTy::Fn(_, _, kind))) =
                (&written, &e.ty, declared.as_ref().map(|d| d.unborrowed()))
            {
                let mut to = e.ty.clone();
                if let Ty::Fn(f) = &mut to {
                    f.kind = *kind;
                }
                self.written_tiers(&mut to, w, cx);
                e = self.coerce(e, &to);
            }
            if tauto_surface::bindings::is_library(&effect, "show") && i == 1 {
                // What an arm of `show` was given is shown already: it is
                // passed on as it is, not shown again.
                if let ExprKind::Read { local, .. } = &e.kind
                    && self.shown_locals.contains(&local.id)
                {
                    out.push(Expr {
                        kind: ExprKind::Read {
                            local: local.clone(),
                            how: Use::Clone,
                        },
                        ty: Ty::Shown,
                        span: e.span,
                    });
                    continue;
                }
                let ety = e.ty.clone();
                self.need(cx, &ety, Bound::Show);
                out.push(Expr {
                    span: e.span,
                    ty: Ty::Shown,
                    kind: ExprKind::Shown(Box::new(e)),
                });
            } else {
                out.push(e);
            }
        }
        Ok(Expr {
            kind: ExprKind::Perform(Box::new(PerformNode {
                op,
                instance,
                quant,
                detached: cx.detached && quant == Quant::Direct,
                unwind: Vec::new(),
                args: out,
                result: ty.clone(),
                span,
            })),
            ty,
            span,
        })
    }

    pub fn handle_expr(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        body: &SurfaceTerm,
        handlers: &[Handler],
    ) -> R<Expr> {
        let result_t = self.types.term(t).cloned().unwrap_or(TTy::Var(0));
        let body_t = self.types.term(body).cloned().unwrap_or(TTy::Var(0));
        let mut result = self.conv(&result_t);
        // A function the `handle` gives is held at the tier of the row row
        // checking found for it, as a `let` of it is: an arm's closure that
        // resumes `k` may perform what the body does.
        if let Some(row) = self.value_row(cx, t)
            && let Ty::Fn(f) = &result
            && f.tier < self.value_tier_in(&row, cx)
        {
            let tier = self.value_tier_in(&row, cx);
            super::ty::set_fn_tier(&mut result, tier);
        }
        let id = self.next_handle;
        self.next_handle += 1;
        let body_tier = self.row_tier(&self.term_row(body), &cx.rowvars);
        // A continuation kept as a value is written in continuation-passing
        // style, which can be called after the `handle` has ended.
        let kept = crate::lin::kept_continuation(handlers);
        if let Some(at) = kept
            && cx.tier == Tier::M
            && !cx.detached
        {
            self.rust_unsupported
                .borrow_mut()
                .get_or_insert_with(|| Unsupported {
                    what: msg!("nir-kept-continuation-multi-shot"),
                    span: Some(at),
                });
        }
        let kept = kept.is_some();
        // A body that may resume more than once, or that suspends inside code
        // that does, is written in continuation-passing style.
        let m = kept
            || cx.detached
            || body_tier == Tier::M
            || (cx.tier == Tier::M && body_tier >= Tier::O);
        let (outer_tier, outer_host) = (cx.tier, cx.host_m);
        // The driver of a handle that starts the M tier in a function of
        // another tier ends the function when the code `return`s.
        let host = m && cx.tier != Tier::M;
        let outer_ret = cx.host_ret;
        let outer_detached = cx.detached;
        cx.detached |= kept;
        let detached = cx.detached;
        if m {
            cx.host_m |= host;
            cx.tier = Tier::M;
        }
        if host {
            cx.host_ret = false;
        }
        let r = self.handle_inner(
            cx, t, body, handlers, m, body_tier, id, &result_t, &body_t, result,
        );
        let returns = host && cx.host_ret;
        cx.host_ret = if host { outer_ret } else { cx.host_ret };
        cx.tier = outer_tier;
        cx.host_m = outer_host;
        cx.detached = outer_detached;
        let mut r = r?;
        if let ExprKind::Handle(h) = &mut r.kind {
            h.kept = kept;
            h.detached = detached;
            if returns {
                h.host_ret = Some(self.conv(&cx.ret));
            }
        }
        Ok(r)
    }

    #[allow(clippy::too_many_arguments)]
    fn handle_inner(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        body: &SurfaceTerm,
        handlers: &[Handler],
        m: bool,
        body_tier: Tier,
        id: u32,
        result_t: &TTy,
        body_t: &TTy,
        result: Ty,
    ) -> R<Expr> {
        let span = t.span;
        let (result_t, body_t) = (result_t.clone(), body_t.clone());
        // The continuations of an `m` handle run after the statement that
        // starts them has ended: what the body mentions is captured, too.
        if m {
            cx.frames.push(CFrame {
                base: cx.bindings.len(),
                captures: Vec::new(),
            });
        }
        let mut body_e = self.expr(cx, body)?;
        // The arms may run when the `handle` has ended (a `k` that escapes):
        // what they mention is captured, as a closure's is.
        if !m {
            cx.frames.push(CFrame {
                base: cx.bindings.len(),
                captures: Vec::new(),
            });
        }
        self.handle_results.push(result.clone());
        let arms = self.arms(cx, handlers, &result_t, &body_t, &body_e);
        self.handle_results.pop();
        let (mut ret, direct, aborts, susp) = arms?;
        // The `return` arm's function is lifted to the tier the `handle`
        // holds what it gives at, as an arm that resumes `k` gives.
        if let Some(r) = &mut ret
            && let (Ty::Fn(made), Ty::Fn(held)) = (&r.body.ty, &result)
            && made.tier < held.tier
        {
            let unit = Expr {
                kind: ExprKind::Unit,
                ty: Ty::Unit,
                span: r.body.span,
            };
            let b = std::mem::replace(&mut r.body, unit);
            r.body = self.coerce(b, &result);
        }
        let frame = cx.frames.pop().expect("a frame");
        let mut clones = Vec::new();
        for c in &frame.captures {
            match c.repr {
                Repr::SharedVar(true) | Repr::SharedVar(false) => clones.push(c.clone()),
                Repr::Plain => {
                    let Some(b) = cx.bindings.iter().find(|b| b.local.id == c.id) else {
                        continue;
                    };
                    let bty = b.ty.clone();
                    let nty = self.conv(&bty);
                    if self.dup_use(&nty) == Some(Use::Clone) {
                        clones.push(c.clone());
                    }
                }
                _ => {}
            }
        }
        if ret.is_none() {
            body_e = self.coerce(body_e, &result);
        }
        let body_ty = body_e.ty.clone();
        Ok(Expr {
            kind: ExprKind::Handle(Box::new(HandleNode {
                id,
                body: body_e,
                body_ty,
                result: result.clone(),
                ret,
                direct,
                aborts,
                susp,
                captures: frame.captures,
                clones,
                body_tier,
                m,
                host_ret: None,
                kept: false,
                detached: false,
                span,
            })),
            ty: result,
            span,
        })
    }

    /// Whether the program runs under the host's handler: it has standard
    /// effects other than `wait` for it to answer, at its top level or in a
    /// task, or entries whose bodies may perform them. The LLVM backend
    /// answers them where they are performed.
    pub(crate) fn hosted(&self) -> bool {
        if self.rows.target == Target::Llvm {
            // The LLVM backend answers `main`, `exit` (an arm that does not
            // resume) and `fs_read` where they are performed (`tauto_llvm`),
            // and everything in a program of entries.
            return !self.rows.entries
                && self
                    .rows
                    .host_effects
                    .iter()
                    .any(|e| Self::llvm_hosted(&Name::from(e.as_str())));
        }
        self.rows.entries || self.rows.host_effects.iter().any(|e| e.as_str() != "wait")
    }

    /// Whether the LLVM backend has the host's handler answer `effect`.
    pub(crate) fn llvm_hosted(effect: &Name) -> bool {
        ["stdout", "stderr", "stdout_flush", "argv"]
            .iter()
            .any(|l| tauto_surface::bindings::is_library(effect, l))
    }

    /// Whether `effect` is one the host answers (other than `wait`, which
    /// the driver that runs the task answers).
    pub(crate) fn is_host_effect(&self, effect: &Name) -> bool {
        crate::host::HOST_EFFECTS
            .iter()
            .any(|l| *l != "wait" && tauto_surface::bindings::is_library(effect, l))
    }

    /// The function a task runs, with its body under the host.
    fn task_under_host(
        &mut self,
        cx: &mut Cx,
        mut f: Expr,
        answered: Option<&BTreeSet<String>>,
    ) -> R<Expr> {
        if !matches!(f.kind, ExprKind::Closure(_)) {
            return self.task_value_under_host(cx, f, answered);
        }
        let ExprKind::Closure(c) = &mut f.kind else {
            unreachable!()
        };
        let outer = cx.tier;
        c.fn_ty.tier = c.fn_ty.tier.max(Tier::O);
        if let Ty::Fn(ft) = &mut f.ty {
            ft.tier = ft.tier.max(Tier::O);
        }
        let ExprKind::Closure(c) = &mut f.kind else {
            unreachable!()
        };
        cx.tier = c.fn_ty.tier;
        let body = std::mem::replace(
            &mut c.body,
            Expr {
                kind: ExprKind::Unit,
                ty: Ty::Unit,
                span: f.span,
            },
        );
        let ret = c.ret.clone();
        let r = self.host_handle_typed(cx, body, ret, answered);
        cx.tier = outer;
        c.body = r?;
        Ok(f)
    }

    /// A task's function given as a value `f`: `{ let g = f; () => handle { g() } }`
    /// with the host's handler.
    fn task_value_under_host(
        &mut self,
        cx: &mut Cx,
        f: Expr,
        answered: Option<&BTreeSet<String>>,
    ) -> R<Expr> {
        let span = f.span;
        let Ty::Fn(fty) = f.ty.clone() else {
            return unsupported(msg!("nir-a-spawn-of-a-value-that"), span);
        };
        let mut task_ty = (*fty).clone();
        task_ty.tier = task_ty.tier.max(Tier::O);
        let g = self.fresh_local(&Name::from("task"), Repr::Plain);
        let call = Expr {
            ty: fty.ret.clone(),
            kind: ExprKind::Call(Box::new(CallNode {
                callee: Callee::Local(g.clone()),
                args: Vec::new(),
                tier: fty.tier,
                targs: Vec::new(),
                tick: Tick::None,
                recur: false,
                unwind: Vec::new(),
                span,
            })),
            span,
        };
        let outer = cx.tier;
        cx.tier = task_ty.tier;
        let body = self.host_handle_typed(cx, call, fty.ret.clone(), answered);
        cx.tier = outer;
        let closure = Expr {
            ty: Ty::Fn(Box::new(task_ty.clone())),
            kind: ExprKind::Closure(Box::new(ClosureNode {
                params: Vec::new(),
                ret: fty.ret.clone(),
                body: body?,
                fn_ty: task_ty.clone(),
                borrowed: false,
                clones: if fty.kind.dup() {
                    vec![g.clone()]
                } else {
                    Vec::new()
                },
                pure: false,
                refs: Vec::new(),
                owned_refs: Vec::new(),
                span,
            })),
            span,
        };
        Ok(Expr {
            ty: Ty::Fn(Box::new(task_ty)),
            kind: ExprKind::Block(Block {
                stmts: vec![tauto_nir::Stmt::Let {
                    local: g,
                    ty: f.ty.clone(),
                    init: f,
                    span,
                    stack: false,
                }],
                tail: Some(Box::new(closure)),
            }),
            span,
        })
    }

    /// `body_e` run under the host: the handler the language puts outside
    /// every program, whose direct arms answer the standard effects that
    /// reach it. Nothing is written around the program for it; the arms are
    /// the host's, read from the prelude once it is checked.
    pub(crate) fn host_handle(
        &mut self,
        cx: &mut Cx,
        body_e: Expr,
        answered: Option<&BTreeSet<String>>,
    ) -> R<Expr> {
        self.host_handle_typed(cx, body_e, Ty::Unit, answered)
    }

    /// The host's handler around `body_e`, with the arms of the effects in
    /// `answered` (every arm when `None`: a row the lowering cannot list,
    /// such as one with a row variable).
    fn host_handle_typed(
        &mut self,
        cx: &mut Cx,
        body_e: Expr,
        result: Ty,
        answered: Option<&BTreeSet<String>>,
    ) -> R<Expr> {
        let name: Name = tauto_surface::bindings::library_name("Host::run").into();
        let Some(decl) = self.fns.get(&name).map(|f| f.decl) else {
            return Ok(body_e);
        };
        let Some(handlers) = host_handlers(&decl.body) else {
            return Ok(body_e);
        };
        let handlers: Vec<Handler> = handlers
            .iter()
            .filter(|h| match (h, answered) {
                (Handler::Operation { effect, .. }, Some(set)) => set.contains(&effect.to_string()),
                _ => true,
            })
            .cloned()
            .collect();
        let handlers = &handlers[..];
        let saved = std::mem::take(&mut self.param_values);
        if let Some(scheme) = self.types.scheme(&name) {
            for (g, _) in &scheme.generics {
                self.param_values.insert(g.id().clone(), result.clone());
            }
        }
        // An arm for every instance (`∀ A. ref_new<A>(v)`) has the
        // operation's generic as a type parameter of its own, which
        // `tauto_nir::arms::instantiate` writes at each type performed.
        let outer_skolems = self.host_skolems.replace(HashMap::new());
        let r = self.host_handle_arms(cx, body_e, handlers, result);
        self.host_skolems = outer_skolems;
        self.param_values = saved;
        r
    }

    fn host_handle_arms(
        &mut self,
        cx: &mut Cx,
        body_e: Expr,
        handlers: &[Handler],
        result: Ty,
    ) -> R<Expr> {
        let span = body_e.span;
        let id = self.next_handle;
        self.next_handle += 1;
        let body_tier = cx.tier;
        cx.frames.push(CFrame {
            base: cx.bindings.len(),
            captures: Vec::new(),
        });
        let (ret, direct, aborts, susp) =
            self.arms(cx, handlers, &TTy::Unit, &TTy::Unit, &body_e)?;
        let frame = cx.frames.pop().expect("a frame");
        let body_ty = body_e.ty.clone();
        Ok(Expr {
            kind: ExprKind::Handle(Box::new(HandleNode {
                id,
                body: body_e,
                body_ty,
                result: result.clone(),
                ret,
                direct,
                aborts,
                susp,
                captures: frame.captures,
                clones: Vec::new(),
                body_tier,
                m: false,
                host_ret: None,
                kept: false,
                detached: false,
                span,
            })),
            ty: result,
            span,
        })
    }

    /// The arms of a `handle` whose body lowers to `body_e`.
    #[allow(clippy::type_complexity)]
    fn arms(
        &mut self,
        cx: &mut Cx,
        handlers: &[Handler],
        result_t: &TTy,
        body_t: &TTy,
        body_e: &Expr,
    ) -> R<(Option<ReturnArm>, Vec<OpArm>, Vec<OpArm>, Vec<OpArm>)> {
        let (result_t, body_t) = (result_t.clone(), body_t.clone());
        let mut ret = None;
        let mut direct = Vec::new();
        let mut aborts = Vec::new();
        let mut susp = Vec::new();
        for h in handlers {
            match h {
                Handler::Return { pattern, body } => {
                    let mark = cx.bindings.len();
                    let pat = self.pattern(cx, pattern, &body_t, body.id(), false)?;
                    let e = self.expr_expect(cx, body, &result_t)?;
                    cx.bindings.truncate(mark);
                    ret = Some(ReturnArm { pat, body: e });
                }
                Handler::Operation {
                    effect,
                    patterns,
                    cont,
                    guard,
                    body,
                    ..
                } => {
                    if tauto_surface::bindings::is_library(&effect, "spawn") {
                        continue;
                    }
                    if tauto_surface::bindings::is_library(&effect, "exceeded") {
                        let arm =
                            self.exceeded_arm(cx, patterns, cont, guard, body, &result_t, body_e)?;
                        susp.push(arm);
                        continue;
                    }
                    let quant = if tauto_surface::bindings::is_library(&effect, "show") {
                        Quant::Direct
                    } else {
                        self.quant(effect)
                    };
                    let op = self.op_index(effect);
                    let sig = self.types.effects.get(effect).cloned();
                    let checked = self
                        .operation_facts
                        .and_then(|facts| facts.arm(body.id()))
                        .cloned();
                    let instance = checked
                        .as_ref()
                        .map(|instance| self.operation_instance(instance));
                    let admitted = checked
                        .as_ref()
                        .filter(|instance| instance.admission == OperationAdmission::Unique);
                    let mark = cx.bindings.len();
                    let mut pats = Vec::new();
                    let mut params = Vec::new();
                    for (i, p) in patterns.iter().enumerate() {
                        let declared = sig
                            .as_ref()
                            .and_then(|s| s.params.get(i))
                            .cloned()
                            .unwrap_or(TTy::Var(0));
                        // The parameter's type as the declaration writes it: a
                        // function in it is taken at the tier its row gives, as
                        // the `perform` passes it.
                        let written = self.effect_param_written(effect, i);
                        let (pty, nty) = if tauto_surface::bindings::is_library(&effect, "show")
                            && i == 1
                        {
                            (TTy::Var(0), Ty::Shown)
                        } else {
                            let pty = match admitted.and_then(|instance| instance.params.get(i)) {
                                Some(formal) => formal.clone(),
                                None => match p {
                                    tauto_surface::surface::Pattern::Bind { name: n, .. } => {
                                        self.local_ty(n, body.id(), Some(&declared))
                                    }
                                    _ => declared,
                                },
                            };
                            let mut n = self.conv(&pty);
                            if let Some(w) = written.as_ref() {
                                self.written_tiers(&mut n, w, cx);
                            }
                            (pty, n)
                        };
                        let pat = if tauto_surface::bindings::is_library(&effect, "show") && i == 1
                        {
                            self.show_pattern(cx, p, body.id())
                        } else {
                            self.pattern_written(cx, p, &pty, body.id(), false, written.as_ref())?
                        };
                        pats.push(pat);
                        params.push(nty);
                    }
                    let guard_e = match guard {
                        Some(g) => Some(self.expr_expect(cx, g, &TTy::Bool)?),
                        None => None,
                    };
                    let mut k_local = None;
                    let mut k_ans = Ty::Unit;
                    let body_e = if matches!(quant, Quant::AtMostOne | Quant::One | Quant::Many) {
                        let Some(k) = cont else {
                            return unsupported(
                                msg!("nir-an-arm-that-resumes-without-k"),
                                body.span,
                            );
                        };
                        let kty = self
                            .types
                            .local(k, body.id())
                            .cloned()
                            .unwrap_or(TTy::Var(0));
                        let local = self.fresh_local(k, Repr::Plain);
                        cx.bindings.push(Binding {
                            name: k.clone(),
                            local: local.clone(),
                            ty: kty,
                            mode: Mode::Cont,
                            fn_row: None,
                            budgeted: cx.under_budget,
                            celled: false,
                        });
                        if let Some(r) = self.handle_results.last() {
                            self.cont_results.insert(local.id, r.clone());
                        }
                        k_local = Some(local);
                        k_ans = match admitted {
                            Some(instance) => self.conv(&instance.answer),
                            None => match self.types.local(k, body.id()) {
                                Some(TTy::Fn(ps, _, _)) => {
                                    let a = ps.first().cloned().unwrap_or(TTy::Unit);
                                    self.conv(&a)
                                }
                                _ => Ty::Unit,
                            },
                        };
                        self.expr_expect(cx, body, &result_t)?
                    } else if quant == Quant::Direct {
                        let Some(k) = cont else {
                            return unsupported(msg!("nir-a-direct-arm-without-k"), body.span);
                        };
                        let ans = match self.types.local(k, body.id()) {
                            Some(TTy::Fn(ps, _, _)) => ps.first().cloned().unwrap_or(TTy::Unit),
                            _ => TTy::Unit,
                        };
                        let tk = TailK { k: k.clone(), ans };
                        self.expr_tail(cx, body, &tk)?
                    } else {
                        self.expr_expect(cx, body, &result_t)?
                    };
                    cx.bindings.truncate(mark);
                    let arm = OpArm {
                        op,
                        instance,
                        params,
                        pats,
                        guard: guard_e,
                        body: body_e,
                        k: k_local,
                        k_ans,
                        instantiated: false,
                        span: body.span,
                    };
                    match quant {
                        Quant::Direct => direct.push(arm),
                        Quant::Zero => aborts.push(arm),
                        _ => susp.push(arm),
                    }
                }
            }
        }
        Ok((ret, direct, aborts, susp))
    }

    /// An arm of `exceeded(info), k`: `info`
    /// holds the stopped body, `k` takes a `BudgetAnswer`.
    fn exceeded_arm(
        &mut self,
        cx: &mut Cx,
        patterns: &[tauto_surface::surface::Pattern],
        cont: &Option<Name>,
        guard: &Option<SurfaceTerm>,
        body: &SurfaceTerm,
        result_t: &TTy,
        handled: &Expr,
    ) -> R<OpArm> {
        let at = body.id();
        let (Some(k), [pattern]) = (cont, patterns) else {
            return unsupported(msg!("nir-an-exceeded-arm-without-k"), body.span);
        };
        if guard.is_some() {
            return unsupported(msg!("nir-a-guard-on-an-exceeded-arm"), body.span);
        }
        let op = self.op_index(&tauto_surface::bindings::library_name("exceeded"));
        let kty = self.types.local(k, at).cloned().unwrap_or(TTy::Var(0));
        let budget_ty = match &kty {
            TTy::Fn(ps, _, _) => self.conv(ps.first().unwrap_or(&TTy::Unit)),
            _ => Ty::Unit,
        };
        // The type of the budgets written in the body, when the checker's
        // record of `k` has not settled it.
        let mut budget_ty = budget_ty;
        if budget_ty == Ty::Never {
            handled.walk(&mut |x| {
                if matches!(&x.kind, ExprKind::Budget(_))
                    && budget_ty == Ty::Never
                    && x.ty != Ty::Never
                {
                    budget_ty = x.ty.clone();
                }
            });
        }
        // A budget the handler never meets has no type to speak of.
        let budget_ty = if budget_ty == Ty::Never {
            Ty::Unit
        } else {
            budget_ty
        };
        let mark = cx.bindings.len();
        let info_ty = Ty::Info(Box::new(budget_ty.clone()));
        let pat = match pattern {
            tauto_surface::surface::Pattern::Bind { name: n, .. } => {
                let bound = self.local_ty(n, at, None);
                let local = self.fresh_local(n, Repr::Plain);
                cx.bindings.push(Binding {
                    name: n.clone(),
                    local: local.clone(),
                    ty: bound,
                    mode: Mode::Owned,
                    fn_row: None,
                    budgeted: cx.under_budget,
                    celled: false,
                });
                Pat::Bind(local, info_ty.clone())
            }
            _ => Pat::Wild,
        };
        let klocal = self.fresh_local(k, Repr::Plain);
        cx.bindings.push(Binding {
            name: k.clone(),
            local: klocal.clone(),
            ty: kty,
            mode: Mode::ContBudget,
            fn_row: None,
            budgeted: cx.under_budget,
            celled: false,
        });
        let body_e = self.expr_expect(cx, body, result_t)?;
        cx.bindings.truncate(mark);
        Ok(OpArm {
            op,
            instance: None,
            params: vec![info_ty],
            pats: vec![pat],
            guard: None,
            body: body_e,
            k: Some(klocal),
            k_ans: Ty::BudgetAnswer(Box::new(budget_ty)),
            instantiated: false,
            span: body.span,
        })
    }

    /// The pattern for the shown value in a `show` arm: a name, bound to the
    /// `Shown` value.
    fn show_pattern(
        &mut self,
        cx: &mut Cx,
        p: &tauto_surface::surface::Pattern,
        _at: tauto_surface::surface::TermId,
    ) -> Pat {
        match p {
            tauto_surface::surface::Pattern::Bind { name: n, .. } => {
                let local = self.fresh_local(n, Repr::Plain);
                cx.bindings.push(Binding {
                    name: n.clone(),
                    local: local.clone(),
                    ty: TTy::Var(0),
                    mode: Mode::Owned,
                    fn_row: None,
                    budgeted: cx.under_budget,
                    celled: false,
                });
                self.shown_locals.insert(local.id);
                Pat::Bind(local, Ty::Shown)
            }
            _ => Pat::Wild,
        }
    }

    /// A direct arm's body, with each `k(e)` replaced by `e`.
    pub fn expr_tail(&mut self, cx: &mut Cx, t: &SurfaceTerm, tk: &TailK) -> R<Expr> {
        let span = t.span;
        let ty = self.conv(&tk.ans);
        match &*t.kind {
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(n) if *n == tk.k)
                && arguments.len() == 1 =>
            {
                self.expr_expect(cx, &arguments[0], &tk.ans)
            }
            TermKind::Block(stmts) => {
                let refs: Vec<&tauto_surface::surface::Stmt> = stmts.iter().collect();
                let b = self.block_with(cx, &refs, false, &tk.ans, Some(tk))?;
                Ok(Expr {
                    kind: ExprKind::Block(b),
                    ty,
                    span,
                })
            }
            TermKind::If {
                condition,
                then,
                otherwise: Some(o),
            } => {
                let cond = self.expr_expect(cx, condition, &TTy::Bool)?;
                let then = self.expr_tail(cx, then, tk)?;
                let o = self.expr_tail(cx, o, tk)?;
                Ok(Expr {
                    kind: ExprKind::If {
                        cond: Box::new(cond),
                        then: Box::new(then),
                        otherwise: Some(Box::new(o)),
                    },
                    ty,
                    span,
                })
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => self.match_with(cx, t, scrutinee, arms, Some(tk)),
            _ => unsupported(msg!("nir-a-direct-arm-that-does-not"), span),
        }
    }
}

/// Where the type parameters of the host's arms for every instance are
/// numbered from: past any the checker gives.
pub(crate) const HOST_SKOLEM_BASE: usize = 1 << 40;

/// The arms of the host's handler: the `handle` that is the body of the
/// prelude's `Host::run`.
fn host_handlers(body: &SurfaceTerm) -> Option<&[Handler]> {
    match &*body.kind {
        TermKind::Handle { handlers, .. } => Some(handlers),
        TermKind::Block(stmts) => match stmts.as_slice() {
            [Stmt::Expr(e)] => host_handlers(e),
            _ => None,
        },
        _ => None,
    }
}
