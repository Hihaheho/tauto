use tauto::surface::{Handler, SurfaceTerm, TermKind};
use tauto::types::{Quant, Ty as TTy};

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
        checked: &tauto::types::CheckedOperationInstance,
    ) -> OperationInstance {
        OperationInstance {
            type_args: checked.type_args.iter().map(|t| self.conv(t)).collect(),
            params: checked.params.iter().map(|t| self.conv(t)).collect(),
            answer: self.conv(&checked.answer),
            admission: checked.admission,
        }
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
            name if tauto::bindings::is_library(name, "show") => 0,
            name if tauto::bindings::is_library(name, "exceeded") => 1,
            _ => {
                self.ops
                    .iter()
                    .filter(|o| {
                        !tauto::bindings::is_library(&o.name, "show")
                            && !tauto::bindings::is_library(&o.name, "exceeded")
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
        let Some(ctor) = self.ctor_ref(&tauto::bindings::library_name("Task::Mk")) else {
            return unsupported(msg!("nir-spawn-without-the-std-task"), span);
        };
        let ret = match self.types.term(f).map(|t| t.unborrowed().clone()) {
            Some(TTy::Fn(_, r, _)) => *r,
            _ => return unsupported(msg!("nir-a-spawn-of-a-value-that"), span),
        };
        let mut body = self.expr(cx, f)?;
        // A name's type does not say whether calling it may suspend; its row
        // does, and a body that may wait is spawned as a future.
        if let (Some(row), Ty::Fn(ft)) = (self.value_row(cx, f), &mut body.ty) {
            ft.tier = ft.tier.max(self.row_tier_in(&row, cx));
        }
        let result = self.conv(&ret);
        let pending = Expr {
            ty: Ty::Std(crate::StdType::Pending, vec![result]),
            kind: ExprKind::Call(Box::new(CallNode {
                callee: Callee::Builtin("pending_spawn".into()),
                args: vec![body],
                tier: Tier::S,
                targs: Vec::new(),
                tick: Tick::None,
                recur: false,
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
        if tauto::bindings::is_library(&effect, "spawn") && args.len() == 1 {
            return self.spawn(cx, t, &args[0]);
        }
        let quant = if tauto::bindings::is_library(&effect, "show") {
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
            let e = match checked
                .as_ref()
                .filter(|instance| instance.admission == OperationAdmission::Unique)
            {
                Some(instance) => match instance.params.get(i) {
                    Some(formal) => self.expr_expect(cx, a, formal)?,
                    None => self.expr(cx, a)?,
                },
                None => self.expr(cx, a)?,
            };
            let e = self.deref_if_ref(e);
            if tauto::bindings::is_library(&effect, "show") && i == 1 {
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
        let result = self.conv(&result_t);
        let id = self.next_handle;
        self.next_handle += 1;
        let body_tier = self.row_tier(&self.term_row(body), &cx.rowvars);
        // A continuation kept as a value is written in continuation-passing
        // style, which can be called after the `handle` has ended.
        let kept = tauto::lin::kept_continuation(handlers);
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
        let mut ret = None;
        let mut direct = Vec::new();
        let mut aborts = Vec::new();
        let mut susp = Vec::new();
        // The arms may run when the `handle` has ended (a `k` that escapes):
        // what they mention is captured, as a closure's is.
        if !m {
            cx.frames.push(CFrame {
                base: cx.bindings.len(),
                captures: Vec::new(),
            });
        }
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
                    if tauto::bindings::is_library(&effect, "spawn") {
                        continue;
                    }
                    if tauto::bindings::is_library(&effect, "exceeded") {
                        let arm =
                            self.exceeded_arm(cx, patterns, cont, guard, body, &result_t, &body_e)?;
                        susp.push(arm);
                        continue;
                    }
                    let quant = if tauto::bindings::is_library(&effect, "show") {
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
                        let (pty, nty) = if tauto::bindings::is_library(&effect, "show") && i == 1 {
                            (TTy::Var(0), Ty::Shown)
                        } else {
                            let pty = match admitted.and_then(|instance| instance.params.get(i)) {
                                Some(formal) => formal.clone(),
                                None => match p {
                                    tauto::surface::Pattern::Bind(n) => {
                                        self.local_ty(n, body.id(), Some(&declared))
                                    }
                                    _ => declared,
                                },
                            };
                            let n = self.conv(&pty);
                            (pty, n)
                        };
                        let pat = if tauto::bindings::is_library(&effect, "show") && i == 1 {
                            self.show_pattern(cx, p, body.id())
                        } else {
                            self.pattern(cx, p, &pty, body.id(), false)?
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

    /// An arm of `exceeded(info), k`: `info`
    /// holds the stopped body, `k` takes a `BudgetAnswer`.
    fn exceeded_arm(
        &mut self,
        cx: &mut Cx,
        patterns: &[tauto::surface::Pattern],
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
        let op = self.op_index(&tauto::bindings::library_name("exceeded"));
        let kty = self.types.local(k, at).cloned().unwrap_or(TTy::Var(0));
        let budget_ty = match &kty {
            TTy::Fn(ps, _, _) => self.conv(ps.first().unwrap_or(&TTy::Unit)),
            _ => Ty::Unit,
        };
        // The type of the budgets written in the body, when the checker's
        // record of `k` has not settled it.
        let mut budget_ty = budget_ty;
        if budget_ty.has_infer() {
            handled.walk(&mut |x| {
                if matches!(&x.kind, ExprKind::Budget(_))
                    && budget_ty.has_infer()
                    && !x.ty.has_infer()
                {
                    budget_ty = x.ty.clone();
                }
            });
        }
        // A budget the handler never meets has no type to speak of.
        let budget_ty = if budget_ty.has_infer() {
            Ty::Unit
        } else {
            budget_ty
        };
        let mark = cx.bindings.len();
        let info_ty = Ty::Info(Box::new(budget_ty.clone()));
        let pat = match pattern {
            tauto::surface::Pattern::Bind(n) => {
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
            span: body.span,
        })
    }

    /// The pattern for the shown value in a `show` arm: a name, bound to the
    /// `Shown` value.
    fn show_pattern(
        &mut self,
        cx: &mut Cx,
        p: &tauto::surface::Pattern,
        _at: tauto::surface::TermId,
    ) -> Pat {
        match p {
            tauto::surface::Pattern::Bind(n) => {
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
                let refs: Vec<&tauto::surface::Stmt> = stmts.iter().collect();
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
