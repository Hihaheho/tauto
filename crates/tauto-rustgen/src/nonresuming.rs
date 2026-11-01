//! Synchronous bodies whose budget handler discards the continuation.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use tauto_message::{Message, msg};
use tauto_nir::*;

use crate::Gen;

/// A reason a budget keeps the ordinary Future path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BudgetReason {
    /// A stable, machine-readable category.
    pub code: &'static str,
    /// The source function containing the rejected expression.
    pub function: String,
    pub span: Span,
    pub message: String,
}

/// Static eligibility of one budget in one lowered function instance.
/// An empty reason list still requires the runtime stack and sync-feature guards.
#[derive(Debug, Clone)]
pub struct BudgetDiagnostic {
    pub budget_id: u32,
    pub function: String,
    pub span: Span,
    pub reasons: Vec<BudgetReason>,
    /// Ordinary source instance or an explicitly named host-contract facade.
    pub variant: String,
    /// Caller assertions, never compiler or kernel proofs.
    pub assumptions: Vec<crate::HostAssumption>,
}

impl BudgetDiagnostic {
    pub fn eligible(&self) -> bool {
        self.reasons.is_empty()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Mode {
    Body,
    Observer,
    Callback,
}

#[derive(Clone, Default)]
struct ProofContext {
    callbacks: BTreeSet<u32>,
    types: BTreeMap<String, Ty>,
}

impl ProofContext {
    fn resolve(&self, ty: &Ty) -> Ty {
        self.resolve_bounded(ty, &mut 4096, 0)
    }

    fn resolve_bounded(&self, ty: &Ty, left: &mut usize, depth: usize) -> Ty {
        if *left == 0 || depth >= 128 {
            return Ty::Infer;
        }
        *left -= 1;
        let mut resolve = |t: &Ty| self.resolve_bounded(t, left, depth + 1);
        match ty {
            Ty::Param(name) => self
                .types
                .get(name)
                .map(&mut resolve)
                .unwrap_or_else(|| ty.clone()),
            Ty::Vec(t) => Ty::Vec(Box::new(resolve(t))),
            Ty::Array(t) => Ty::Array(Box::new(resolve(t))),
            Ty::Slice(t) => Ty::Slice(Box::new(resolve(t))),
            Ty::Option(t) => Ty::Option(Box::new(resolve(t))),
            Ty::Ref(t) => Ty::Ref(Box::new(resolve(t))),
            Ty::RefMut(t) => Ty::RefMut(Box::new(resolve(t))),
            Ty::SharedVar(true, t) => Ty::SharedVar(true, Box::new(resolve(t))),
            Ty::SharedVar(false, t) => Ty::SharedVar(false, Box::new(resolve(t))),
            Ty::Info(t) => Ty::Info(Box::new(resolve(t))),
            Ty::BudgetAnswer(t) => Ty::BudgetAnswer(Box::new(resolve(t))),
            Ty::HashMap(a, b) => Ty::HashMap(Box::new(resolve(a)), Box::new(resolve(b))),
            Ty::Result(a, b) => Ty::Result(Box::new(resolve(a)), Box::new(resolve(b))),
            Ty::Pair(a, b) => Ty::Pair(Box::new(resolve(a)), Box::new(resolve(b))),
            Ty::Product(ms) => {
                Ty::Product(ms.iter().map(|(k, m)| (k.clone(), resolve(m))).collect())
            }
            Ty::Data(name, args) => Ty::Data(name.clone(), args.iter().map(&mut resolve).collect()),
            Ty::Std(name, args) => Ty::Std(name.clone(), args.iter().map(&mut resolve).collect()),
            Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
                params: f.params.iter().map(&mut resolve).collect(),
                ret: resolve(&f.ret),
                kind: f.kind,
                tier: f.tier,
            })),
            _ => ty.clone(),
        }
    }
}

type Visit = (InstId, Vec<Ty>, Vec<bool>, Mode);

#[derive(Default)]
struct Check {
    calls: BTreeSet<InstId>,
    visited: BTreeSet<Visit>,
    reasons: Vec<BudgetReason>,
    aborts: Vec<(OpIndex, Vec<Ty>, Span, String)>,
    assumptions: BTreeSet<crate::HostAssumption>,
}

impl Check {
    fn enter(&mut self, visit: Visit, function: &str, span: Span) -> bool {
        if self.visited.contains(&visit) {
            return false;
        }
        // A changing generic recursion must fail closed instead of expanding
        // an unbounded collection of proof contexts.
        if self.visited.len() >= 256 {
            self.reject(
                "analysis-limit",
                function,
                span,
                msg!("rustgen-budget-analysis-limit"),
            );
            return false;
        }
        self.visited.insert(visit)
    }

    fn reject(&mut self, code: &'static str, function: &str, span: Span, message: Message) {
        let reason = BudgetReason {
            code,
            function: function.into(),
            span,
            message: message.to_string(),
        };
        if !self.reasons.contains(&reason) {
            self.reasons.push(reason);
        }
    }
}

/// Explain the same static checks used by synchronous budget emission.
/// This does not execute the program or predict the runtime stack guard.
pub fn budget_diagnostics(
    pkg: &Package,
    sources: &crate::Sources<'_>,
    bindings: &crate::Bindings,
) -> Vec<BudgetDiagnostic> {
    let mut generator = Gen::new(pkg, sources, bindings);
    let mut out = Vec::new();
    for f in &pkg.fns {
        explain_function(&generator, f, "ordinary", &mut out);
    }
    for (facade, contract) in &bindings.nonresuming_entries {
        let Some(export) = pkg.exports.iter().find(|e| e.name == contract.function) else {
            continue;
        };
        if generator.export_issue(export).is_some() {
            continue;
        }
        generator.trusted_budget_host = Some(crate::HostAssumption {
            kind: "embedding",
            name: facade.clone(),
            at: contract.at.clone(),
            contract: "closed-host-v1",
        });
        generator.trusted_budget_callbacks = generator.contract_context(contract);
        explain_function(&generator, &pkg.fns[export.inst], facade, &mut out);
    }
    out
}

fn explain_function(
    generator: &Gen<'_>,
    f: &FnInst,
    variant: &str,
    out: &mut Vec<BudgetDiagnostic>,
) {
    let mut budgets = Vec::new();
    let mut checked = BTreeSet::new();
    walk_all(&f.body, &mut |e| {
        if let ExprKind::Budget(b) = &e.kind {
            budgets.push((b.id, b.span));
        }
        if let ExprKind::Handle(h) = &e.kind {
            if let Some(b) = immediate_budget(&h.body) {
                let check = generator.check_budget(h, &f.source);
                checked.insert(b.id);
                out.push(BudgetDiagnostic {
                    budget_id: b.id,
                    function: f.source.clone(),
                    span: b.span,
                    reasons: check.reasons,
                    variant: variant.into(),
                    assumptions: check.assumptions.into_iter().collect(),
                });
            }
        }
    });
    for (budget_id, span) in budgets {
        if !checked.contains(&budget_id) {
            out.push(BudgetDiagnostic {
                budget_id,
                function: f.source.clone(),
                span,
                variant: variant.into(),
                assumptions: Vec::new(),
                reasons: vec![BudgetReason {
                    code: "no-immediate-handler",
                    function: f.source.clone(),
                    span,
                    message: msg!("rustgen-budget-no-immediate-handler").to_string(),
                }],
            });
        }
    }
}

fn walk_all(e: &Expr, visit: &mut impl FnMut(&Expr)) {
    e.walk(&mut |node| {
        visit(node);
        if let ExprKind::Handle(h) = &node.kind {
            for a in &h.susp {
                if let Some(g) = &a.guard {
                    walk_all(g, visit);
                }
                walk_all(&a.body, visit);
            }
        }
    });
}

impl Gen<'_> {
    /// Keep the original O handler and use only statically checked bodies.
    pub(crate) fn nonresuming_budget(&mut self, h: &HandleNode) -> Option<u32> {
        let budget = immediate_budget(&h.body)?;
        let check = self.check_budget(h, "<budget>");
        if !check.reasons.is_empty() {
            return None;
        }
        self.sync_budget_fns.extend(
            check
                .calls
                .into_iter()
                .filter(|i| self.pkg.fns[*i].tier == Tier::O),
        );
        Some(budget.id)
    }

    fn check_budget(&self, h: &HandleNode, function: &str) -> Check {
        let mut check = Check::default();
        check
            .assumptions
            .extend(self.trusted_budget_host.iter().cloned());
        check
            .assumptions
            .extend(self.trusted_budget_callbacks.values().cloned());
        let root_callbacks = ProofContext {
            callbacks: self.trusted_budget_callbacks.keys().copied().collect(),
            types: BTreeMap::new(),
        };
        let Some(budget) = immediate_budget(&h.body) else {
            return check;
        };
        if self.pkg.sync {
            check.reject(
                "concurrent-observer",
                function,
                budget.span,
                msg!("rustgen-budget-concurrent-observer"),
            );
        }
        if h.m || budget.m {
            check.reject(
                "multishot",
                function,
                budget.span,
                msg!("rustgen-budget-multishot"),
            );
        }
        if !h.direct.is_empty() || h.susp.len() != 1 {
            check.reject(
                "handler-shape",
                function,
                budget.span,
                msg!("rustgen-budget-handler-shape"),
            );
        }
        if let Some(arm) = h.susp.first() {
            if self.pkg.ops[arm.op].name != "exceeded"
                || arm.guard.is_some()
                || arm.params != [Ty::Info(Box::new(budget.body.ty.clone()))]
                || !matches!(arm.pats.as_slice(), [Pat::Wild | Pat::Bind(_, _)])
            {
                check.reject(
                    "exceeded-not-total",
                    function,
                    budget.span,
                    msg!("rustgen-budget-exceeded-not-total"),
                );
            }
            if arm.k.as_ref().is_none_or(|k| mentions(&arm.body, k.id)) {
                check.reject(
                    "continuation-used",
                    function,
                    budget.span,
                    msg!("rustgen-budget-continuation-used"),
                );
            }
        }
        self.tick_only(
            &budget.body,
            false,
            Mode::Body,
            &root_callbacks,
            function,
            &mut check,
        );
        for (op, payload, span, caller) in check.aborts.clone() {
            let caught = h.aborts.iter().any(|arm| {
                arm.op == op
                    && arm.params == payload
                    && arm.guard.is_none()
                    && arm
                        .pats
                        .iter()
                        .all(|p| matches!(p, Pat::Wild | Pat::Bind(_, _)))
                    && arm.pats.len() == payload.len()
                    && arm.k.is_none()
            });
            if !caught {
                check.reject(
                    "abort-not-locally-total",
                    &caller,
                    span,
                    msg!(
                        "rustgen-budget-abort-not-locally-total",
                        op = &self.pkg.ops[op].name
                    ),
                );
            }
        }
        // Even values without custom destructors can expose reference counts
        // to Rust. The original Future retains them until its handler returns.
        // No host observer may run during that interval on the synchronous path.
        let mut observers = Check::default();
        let context = msg!("rustgen-budget-handler-of", function = function).to_string();
        for arm in h.aborts.iter().chain(&h.susp).chain(&h.direct) {
            if let Some(guard) = &arm.guard {
                self.tick_only(
                    guard,
                    true,
                    Mode::Observer,
                    &root_callbacks,
                    &context,
                    &mut observers,
                );
            }
            if arm.params.iter().any(|ty| {
                !matches!(ty, Ty::Info(_))
                    && !self.inert_drop(ty, &HashSet::new(), &mut HashSet::new())
            }) {
                observers.reject(
                    "unproven-payload",
                    &context,
                    arm.span,
                    msg!("rustgen-budget-unproven-payload"),
                );
            }
            self.tick_only(
                &arm.body,
                true,
                Mode::Observer,
                &root_callbacks,
                &context,
                &mut observers,
            );
        }
        if let Some(ret) = &h.ret {
            self.tick_only(
                &ret.body,
                true,
                Mode::Observer,
                &root_callbacks,
                &context,
                &mut observers,
            );
        }
        if !observers.reasons.is_empty() {
            check.reject(
                "observable-handler",
                function,
                budget.span,
                msg!("rustgen-budget-observable-handler"),
            );
            check.reasons.extend(observers.reasons);
        }
        check.assumptions.extend(observers.assumptions);
        check
    }

    fn tick_only(
        &self,
        e: &Expr,
        returns: bool,
        mode: Mode,
        context: &ProofContext,
        function: &str,
        check: &mut Check,
    ) {
        self.check_expr(e, returns, mode, context, function, check, false);
    }

    fn check_expr(
        &self,
        e: &Expr,
        returns: bool,
        mode: Mode,
        context: &ProofContext,
        function: &str,
        check: &mut Check,
        borrowed_position: bool,
    ) {
        let aborts = mode == Mode::Body;
        let x = e;
        let mut borrowed_args = BTreeSet::new();
        let borrowed_callable = match &x.kind {
            ExprKind::Read { local, .. } => {
                borrowed_position && context.callbacks.contains(&local.id)
            }
            ExprKind::Ref(place) => {
                borrowed_position
                    && place.path.is_empty()
                    && context.callbacks.contains(&place.local.id)
            }
            ExprKind::Closure(_) | ExprKind::FnValue { .. } | ExprKind::TempRef(_) => {
                borrowed_position
            }
            _ => false,
        };
        if !borrowed_callable && !self.inert_at(&x.ty, context) {
            check.reject(
                "unproven-lifetime",
                function,
                x.span,
                msg!(
                    "rustgen-budget-unproven-lifetime-value",
                    ty = self.ty(&context.resolve(&x.ty)).to_string()
                ),
            );
        }
        if mode == Mode::Observer {
            match &x.kind {
                ExprKind::Arith { op, .. }
                    if (!matches!(x.ty, Ty::Float | Ty::Float32) || *op == Arith::Div)
                        && constant_integer(x).is_none() =>
                {
                    check.reject(
                        "handler-may-panic",
                        function,
                        x.span,
                        msg!("rustgen-budget-handler-may-panic"),
                    );
                }
                ExprKind::Match(_) => {
                    check.reject(
                        "handler-may-panic",
                        function,
                        x.span,
                        msg!("rustgen-budget-handler-may-panic-2"),
                    );
                }
                ExprKind::Call(c) if c.tick != Tick::None => {
                    check.reject(
                        "handler-may-panic",
                        function,
                        c.span,
                        msg!("rustgen-budget-handler-may-panic-3"),
                    );
                }
                ExprKind::Block(b) if b.stmts.iter().any(|s| matches!(s, Stmt::While { .. })) => {
                    check.reject(
                        "handler-may-panic",
                        function,
                        x.span,
                        msg!("rustgen-budget-handler-may-panic-4"),
                    );
                }
                _ => {}
            }
        }
        match &x.kind {
            ExprKind::Read { local, .. } if local.repr == Repr::SharedVar(false) => {
                check.reject(
                    "refcell-guard",
                    function,
                    x.span,
                    msg!("rustgen-budget-refcell-guard"),
                );
            }
            ExprKind::RefMut(_) if mode == Mode::Callback => {
                check.reject(
                    "callback-mutation",
                    function,
                    x.span,
                    msg!("rustgen-budget-callback-mutation"),
                );
            }
            ExprKind::Ref(p) | ExprKind::RefMut(p) if p.local.repr == Repr::SharedVar(false) => {
                check.reject(
                    "refcell-guard",
                    function,
                    x.span,
                    msg!("rustgen-budget-refcell-guard"),
                );
            }
            ExprKind::Handle(_) => check.reject(
                "nested-handler",
                function,
                x.span,
                msg!("rustgen-budget-nested-handler"),
            ),
            ExprKind::Budget(_) => check.reject(
                "nested-budget",
                function,
                x.span,
                msg!("rustgen-budget-nested-budget"),
            ),
            ExprKind::Perform(p) if aborts && p.quant == Quant::Zero => {
                check.aborts.push((
                    p.op,
                    p.args.iter().map(|a| context.resolve(&a.ty)).collect(),
                    p.span,
                    function.into(),
                ));
            }
            ExprKind::Perform(_) => check.reject(
                "effect-operation",
                function,
                x.span,
                msg!("rustgen-budget-effect-operation"),
            ),
            ExprKind::Closure(_) | ExprKind::FnValue { .. } if !borrowed_callable => {
                check.reject(
                    "unproven-callable",
                    function,
                    x.span,
                    msg!(
                        "rustgen-budget-unproven-callable",
                        origin = self.callable_origin(x, context)
                    ),
                );
            }
            ExprKind::FnCast(_) => check.reject(
                "unproven-callable",
                function,
                x.span,
                msg!(
                    "rustgen-budget-unproven-callable-cast",
                    origin = self.callable_origin(x, context)
                ),
            ),
            ExprKind::Block(b) => {
                for s in &b.stmts {
                    match s {
                        Stmt::While { span, .. } if mode == Mode::Callback => {
                            check.reject(
                                "callback-effect",
                                function,
                                *span,
                                msg!("rustgen-budget-callback-effect"),
                            );
                        }
                        Stmt::Return { span, .. } if !returns => check.reject(
                            "body-return",
                            function,
                            *span,
                            msg!("rustgen-budget-body-return"),
                        ),
                        Stmt::Assign { span, .. } if mode == Mode::Callback => {
                            check.reject(
                                "callback-mutation",
                                function,
                                *span,
                                msg!("rustgen-budget-callback-mutation-2"),
                            );
                        }
                        Stmt::Assign { target, span, .. }
                            if target.local.repr == Repr::SharedVar(false) =>
                        {
                            check.reject(
                                "refcell-guard",
                                function,
                                *span,
                                msg!("rustgen-budget-refcell-guard-2"),
                            );
                        }
                        _ => {}
                    }
                }
            }
            ExprKind::Call(c) => {
                if mode == Mode::Callback && (c.tier != Tier::S || c.tick != Tick::None) {
                    check.reject(
                        "callback-effect",
                        function,
                        c.span,
                        msg!("rustgen-budget-callback-effect-2"),
                    );
                }
                if c.tier == Tier::M || (!aborts && c.tier == Tier::A) {
                    check.reject(
                        "call-tier",
                        function,
                        c.span,
                        msg!("rustgen-budget-call-tier"),
                    );
                }
                match &c.callee {
                    Callee::Inst(i) => {
                        let f = &self.pkg.fns[*i];
                        let targs: Vec<_> = c.targs.iter().map(|t| context.resolve(t)).collect();
                        let mut proven = ProofContext::default();
                        if self.trusted_budget_host.is_some() && !f.generics.is_empty() {
                            if targs.len() == f.generics.len()
                                && targs
                                    .iter()
                                    .all(|t| self.concrete_type(t, &mut BTreeSet::new()))
                            {
                                proven.types.extend(
                                    f.generics
                                        .iter()
                                        .zip(&targs)
                                        .map(|((name, _), ty)| (name.clone(), ty.clone())),
                                );
                            } else {
                                check.reject(
                                    "unproven-type-arguments",
                                    function,
                                    c.span,
                                    msg!(
                                        "rustgen-budget-unproven-type-arguments",
                                        function = &f.source,
                                        generics = format!(
                                            "{:?}",
                                            f.generics
                                                .iter()
                                                .map(|(name, _)| name)
                                                .collect::<Vec<_>>()
                                        ),
                                        found = format!("{targs:?}")
                                    ),
                                );
                            }
                        }
                        let mut obligations = Vec::new();
                        for (index, param) in f.params.iter().enumerate() {
                            let ty = proven.resolve(&param.ty);
                            if shared_callback(&ty)
                                || (self.trusted_budget_host.is_some() && owned_callback(&ty))
                            {
                                let safe = c.args.get(index).is_some_and(|arg| {
                                    self.prove_callback(
                                        arg,
                                        context,
                                        callback_mode(mode),
                                        function,
                                        check,
                                    )
                                });
                                obligations.push(safe);
                                if safe {
                                    proven.callbacks.insert(param.local.id);
                                    borrowed_args.insert(index);
                                } else {
                                    check.reject(
                                        "unknown-callback",
                                        function,
                                        c.span,
                                        msg!(
                                            "rustgen-budget-unknown-callback",
                                            index = index + 1,
                                            name = &param.local.name,
                                            function = &f.source,
                                            ty = self.ty(&ty).to_string(),
                                            origin = c
                                                .args
                                                .get(index)
                                                .map(|arg| self.callable_origin(arg, context))
                                                .unwrap_or_else(|| msg!(
                                                    "rustgen-budget-missing-argument"
                                                ))
                                        ),
                                    );
                                }
                            } else if !self.inert_at(&param.ty, &proven) {
                                check.reject(
                                    "unproven-parameter",
                                    function,
                                    c.span,
                                    msg!(
                                        "rustgen-budget-unproven-parameter",
                                        index = index + 1,
                                        name = &param.local.name,
                                        function = &f.source,
                                        ty = self.ty(&ty).to_string(),
                                        from = self.ty(&param.ty).to_string()
                                    ),
                                );
                            }
                        }
                        if !self.inert_at(&f.ret, &proven) {
                            check.reject(
                                "unproven-result",
                                function,
                                c.span,
                                msg!(
                                    "rustgen-budget-unproven-result",
                                    function = &f.source,
                                    ty = self.ty(&proven.resolve(&f.ret)).to_string()
                                ),
                            );
                        }
                        check.calls.insert(*i);
                        if check.enter((*i, targs, obligations, mode), &f.source, f.span) {
                            if f.tier == Tier::M || (!aborts && f.tier == Tier::A) {
                                check.reject(
                                    "call-tier",
                                    &f.source,
                                    f.span,
                                    msg!("rustgen-budget-call-tier-2"),
                                );
                            }
                            self.tick_only(&f.body, true, mode, &proven, &f.source, check);
                        }
                    }
                    Callee::Local(local)
                        if c.tier == Tier::S && context.callbacks.contains(&local.id) => {}
                    Callee::Builtin(name) if c.tier == Tier::S => {
                        if mode == Mode::Callback
                            && !matches!(
                                name.as_str(),
                                "clone"
                                    | "Text::of_i64"
                                    | "Text::of_u64"
                                    | "Text::len"
                                    | "Text::compare"
                                    | "Text::byte"
                                    | "Text::slice"
                                    | "Text::of_code_point"
                                    | "Array::len"
                                    | "Array::get"
                                    | "Bytes::len"
                                    | "Bytes::get"
                                    | "Vec::len"
                                    | "Vec::get"
                                    | "div"
                                    | "mod"
                                    | "concat"
                                    | "Buf::clone"
                            )
                        {
                            check.reject(
                                "callback-builtin",
                                function,
                                c.span,
                                msg!("rustgen-budget-callback-builtin", name = name),
                            );
                        }
                        if mode == Mode::Observer
                            && !matches!(
                                name.as_str(),
                                "clone"
                                    | "Text::of_i64"
                                    | "Text::of_u64"
                                    | "Text::len"
                                    | "Text::compare"
                                    | "Array::len"
                                    | "Array::get"
                                    | "Bytes::len"
                                    | "Bytes::get"
                                    | "Vec::len"
                                    | "Vec::get"
                            )
                        {
                            check.reject(
                                "handler-may-panic",
                                function,
                                c.span,
                                msg!("rustgen-budget-builtin-may-panic", name = name),
                            );
                        }
                    }
                    Callee::Extern(name) => {
                        if let Some(contract) = self
                            .bindings
                            .nonresuming_externs
                            .get(name)
                            .filter(|_| self.trusted_budget_host.is_some())
                        {
                            let mut signature_ok = c.tier == Tier::S;
                            if c.tier != Tier::S {
                                check.reject(
                                    "extern-signature",
                                    function,
                                    c.span,
                                    msg!(
                                        "rustgen-budget-extern-tier",
                                        name = name,
                                        tier = format!("{:?}", c.tier)
                                    ),
                                );
                            }
                            let result = context.resolve(&x.ty);
                            if !host_result(&result) {
                                signature_ok = false;
                                check.reject(
                                    "extern-signature",
                                    function,
                                    c.span,
                                    msg!(
                                        "rustgen-budget-extern-result",
                                        name = name,
                                        ty = self.ty(&result).to_string()
                                    ),
                                );
                            }
                            for (index, arg) in c.args.iter().enumerate() {
                                let ty = context.resolve(&arg.ty);
                                if !host_argument(&ty) {
                                    signature_ok = false;
                                    check.reject(
                                        "extern-signature",
                                        function,
                                        arg.span,
                                        msg!(
                                            "rustgen-budget-extern-argument",
                                            name = name,
                                            index = index + 1,
                                            ty = self.ty(&ty).to_string()
                                        ),
                                    );
                                }
                            }
                            if signature_ok {
                                check.assumptions.insert(contract.assumption(name));
                            }
                        } else {
                            check.reject(
                                "extern-contract",
                                function,
                                c.span,
                                msg!("rustgen-budget-extern-contract", name = name),
                            );
                        }
                    }
                    _ => {
                        let target = match &c.callee {
                            Callee::Local(local) => {
                                msg!("rustgen-budget-origin-local", name = &local.name)
                            }
                            Callee::Cont(local) => {
                                msg!("rustgen-budget-origin-continuation", name = &local.name)
                            }
                            Callee::Value(value) => msg!(
                                "rustgen-budget-origin-computed-callable",
                                ty = self.ty(&context.resolve(&value.ty)).to_string()
                            ),
                            Callee::Builtin(name) | Callee::Extern(name) => Message::text(name),
                            Callee::Inst(inst) => Message::text(&self.pkg.fns[*inst].source),
                        };
                        check.reject(
                            "unknown-call",
                            function,
                            c.span,
                            msg!("rustgen-budget-unknown-call", target = target),
                        );
                    }
                }
            }
            _ => {}
        }
        self.check_children(
            e,
            returns,
            mode,
            context,
            function,
            check,
            &borrowed_args,
            borrowed_position,
        );
    }

    // Borrowed callable evidence is tied to the actual argument position of
    // this call, never to source spans shared by other lowered instances.
    fn check_children(
        &self,
        e: &Expr,
        returns: bool,
        mode: Mode,
        context: &ProofContext,
        function: &str,
        check: &mut Check,
        borrowed_args: &BTreeSet<usize>,
        borrowed_position: bool,
    ) {
        let mut child = |value: &Expr, borrowed| {
            self.check_expr(value, returns, mode, context, function, check, borrowed)
        };
        match &e.kind {
            ExprKind::Call(call) => {
                if let Callee::Value(value) = &call.callee {
                    child(value, false);
                }
                for (index, arg) in call.args.iter().enumerate() {
                    child(arg, borrowed_args.contains(&index));
                }
            }
            ExprKind::TempRef(value) => {
                // This wrapper has exactly the same proven borrowed origin.
                child(value, borrowed_position);
            }
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => {
                for arg in args {
                    child(arg, false);
                }
            }
            ExprKind::Not(value)
            | ExprKind::Shown(value)
            | ExprKind::Unreachable(value)
            | ExprKind::Inject { value, .. }
            | ExprKind::Remap { value, .. }
            | ExprKind::Member { value, .. }
            | ExprKind::Deref { value, .. } => child(value, false),
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                child(a, false);
                child(b, false);
            }
            ExprKind::Ctor { fields, .. } => {
                for (_, value) in fields {
                    child(value, false);
                }
            }
            ExprKind::Product { members, .. } => {
                for value in members {
                    child(value, false);
                }
            }
            ExprKind::Field { base, .. } => child(base, false),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                child(cond, false);
                child(then, false);
                if let Some(value) = otherwise {
                    child(value, false);
                }
            }
            ExprKind::Match(m) => {
                child(&m.scrut, false);
                for arm in &m.arms {
                    if let Some(guard) = &arm.guard {
                        child(guard, false);
                    }
                    child(&arm.body, false);
                }
            }
            ExprKind::Block(block) => {
                self.check_block(block, returns, mode, context, function, check);
            }
            ExprKind::Perform(p) => {
                for arg in &p.args {
                    child(arg, false);
                }
            }
            // A valid borrowed closure was already checked in its own callback
            // context. All other closures/handlers/casts/budgets were rejected.
            ExprKind::Closure(_)
            | ExprKind::FnValue { .. }
            | ExprKind::FnCast(_)
            | ExprKind::Handle(_)
            | ExprKind::Budget(_)
            | ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Text(_)
            | ExprKind::Read { .. }
            | ExprKind::Ref(_)
            | ExprKind::RefMut(_) => {}
        }
    }

    fn check_block(
        &self,
        block: &Block,
        returns: bool,
        mode: Mode,
        context: &ProofContext,
        function: &str,
        check: &mut Check,
    ) {
        let mut local_context = context.clone();
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let {
                    local,
                    ty,
                    init,
                    span,
                } => {
                    let resolved = local_context.resolve(ty);
                    let callable = self.trusted_budget_host.is_some()
                        && (owned_callback(&resolved) || shared_callback(&resolved))
                        && self.prove_callback(
                            init,
                            &local_context,
                            callback_mode(mode),
                            function,
                            check,
                        );
                    if !callable && !self.inert_at(ty, &local_context) {
                        check.reject(
                            "unproven-lifetime",
                            function,
                            *span,
                            msg!(
                                "rustgen-budget-unproven-lifetime-local",
                                name = &local.name,
                                ty = self.ty(&resolved).to_string()
                            ),
                        );
                    }
                    self.check_expr(
                        init,
                        returns,
                        mode,
                        &local_context,
                        function,
                        check,
                        callable,
                    );
                    if callable {
                        local_context.callbacks.insert(local.id);
                    }
                }
                Stmt::Var {
                    local,
                    ty,
                    init,
                    span,
                } => {
                    if !self.inert_at(ty, &local_context) {
                        check.reject(
                            "unproven-lifetime",
                            function,
                            *span,
                            msg!(
                                "rustgen-budget-unproven-lifetime-var",
                                name = &local.name,
                                ty = self.ty(&local_context.resolve(ty)).to_string()
                            ),
                        );
                    }
                    self.check_expr(init, returns, mode, &local_context, function, check, false);
                }
                Stmt::Assign {
                    target,
                    value,
                    span,
                } => {
                    if local_context.callbacks.remove(&target.local.id) {
                        check.reject(
                            "unproven-callable",
                            function,
                            *span,
                            msg!(
                                "rustgen-budget-assignment-invalidates",
                                name = &target.local.name
                            ),
                        );
                    }
                    self.check_expr(value, returns, mode, &local_context, function, check, false);
                }
                Stmt::Expr(value) => {
                    self.check_expr(value, returns, mode, &local_context, function, check, false);
                }
                Stmt::While {
                    cond, body, span, ..
                } => {
                    self.check_expr(cond, returns, mode, &local_context, function, check, false);
                    self.check_expr(
                        &Expr {
                            kind: ExprKind::Block(body.clone()),
                            ty: Ty::Unit,
                            span: *span,
                        },
                        returns,
                        mode,
                        &local_context,
                        function,
                        check,
                        false,
                    );
                }
                Stmt::Return { value, .. } => {
                    if let Some(value) = value {
                        self.check_expr(
                            value,
                            returns,
                            mode,
                            &local_context,
                            function,
                            check,
                            false,
                        );
                    }
                }
            }
        }
        if let Some(tail) = &block.tail {
            self.check_expr(tail, returns, mode, &local_context, function, check, false);
        }
    }

    /// A borrowed callback is safe only from an actual closed origin. The
    /// effect row and Rust Fn ABI never establish this property on their own.
    fn prove_callback(
        &self,
        e: &Expr,
        context: &ProofContext,
        mode: Mode,
        function: &str,
        check: &mut Check,
    ) -> bool {
        let before = check.reasons.len();
        let valid = match &e.kind {
            ExprKind::TempRef(inner) => self.prove_callback(inner, context, mode, function, check),
            ExprKind::Ref(place) => {
                place.path.is_empty() && context.callbacks.contains(&place.local.id)
            }
            ExprKind::Read { local, .. } => context.callbacks.contains(&local.id),
            ExprKind::Closure(c)
                if c.fn_ty.tier == Tier::S
                    && c.fn_ty.kind.dup()
                    && (c.borrowed
                        || (self.trusted_budget_host.is_some()
                            && c.pure
                            && c.refs.is_empty()
                            && c.clones.is_empty())) =>
            {
                let inert = c.params.iter().all(|(_, ty)| self.inert_at(ty, context))
                    && self.inert_at(&c.ret, context);
                if inert {
                    self.tick_only(&c.body, true, mode, context, function, check);
                }
                inert
            }
            ExprKind::FnValue { inst, .. } => {
                let f = &self.pkg.fns[*inst];
                let inert = f.tier == Tier::S
                    && f.generics.is_empty()
                    && f.params
                        .iter()
                        .all(|p| self.inert_drop(&p.ty, &HashSet::new(), &mut HashSet::new()))
                    && self.inert_drop(&f.ret, &HashSet::new(), &mut HashSet::new());
                if inert && check.enter((*inst, Vec::new(), Vec::new(), mode), &f.source, f.span) {
                    self.tick_only(
                        &f.body,
                        true,
                        mode,
                        &ProofContext::default(),
                        &f.source,
                        check,
                    );
                }
                inert
            }
            _ => false,
        };
        let valid = valid && check.reasons.len() == before;
        valid
    }

    fn callable_origin(&self, expr: &Expr, context: &ProofContext) -> Message {
        match &expr.kind {
            ExprKind::FnValue { inst, .. } => msg!(
                "rustgen-budget-origin-function",
                name = &self.pkg.fns[*inst].source
            ),
            ExprKind::Read { local, .. } => msg!("rustgen-budget-origin-local", name = &local.name),
            ExprKind::Ref(place) | ExprKind::RefMut(place) => {
                msg!("rustgen-budget-origin-borrow", name = &place.local.name)
            }
            ExprKind::Closure(closure) => msg!(if closure.borrowed {
                "rustgen-budget-origin-borrowed-closure"
            } else if closure.pure {
                "rustgen-budget-origin-capture-free-closure"
            } else {
                "rustgen-budget-origin-captured-closure"
            }),
            ExprKind::TempRef(value) => self.callable_origin(value, context),
            ExprKind::FnCast(value) => msg!(
                "rustgen-budget-origin-cast",
                origin = self.callable_origin(value, context)
            ),
            _ => msg!(
                "rustgen-budget-origin-computed-value",
                ty = self.ty(&context.resolve(&expr.ty)).to_string()
            ),
        }
    }

    fn inert_at(&self, ty: &Ty, context: &ProofContext) -> bool {
        self.inert_drop(&context.resolve(ty), &HashSet::new(), &mut HashSet::new())
    }

    fn concrete_type(&self, ty: &Ty, unions: &mut BTreeSet<UnionId>) -> bool {
        match ty {
            Ty::Param(_) | Ty::Infer => false,
            Ty::Vec(t)
            | Ty::Array(t)
            | Ty::Slice(t)
            | Ty::Option(t)
            | Ty::Ref(t)
            | Ty::RefMut(t)
            | Ty::SharedVar(true, t)
            | Ty::SharedVar(false, t)
            | Ty::Info(t)
            | Ty::BudgetAnswer(t) => self.concrete_type(t, unions),
            Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => {
                self.concrete_type(a, unions) && self.concrete_type(b, unions)
            }
            Ty::Product(ms) => ms.iter().all(|(_, m)| self.concrete_type(m, unions)),
            Ty::Data(_, args) | Ty::Std(_, args) => {
                args.iter().all(|t| self.concrete_type(t, unions))
            }
            Ty::Fn(f) => {
                f.params.iter().all(|t| self.concrete_type(t, unions))
                    && self.concrete_type(&f.ret, unions)
            }
            Ty::Union(i) => {
                if !unions.insert(*i) {
                    return false;
                }
                let concrete = self.pkg.unions[*i]
                    .members
                    .iter()
                    .all(|t| self.concrete_type(t, unions));
                unions.remove(i);
                concrete
            }
            Ty::Int(_)
            | Ty::Bool
            | Ty::Text
            | Ty::Unit
            | Ty::Never
            | Ty::Float
            | Ty::Float32
            | Ty::Buf
            | Ty::Shown => true,
        }
    }

    /// Early exhaustion must not change an observable destructor's timing.
    /// Unknown type parameters, function values and host-owned types stay on
    /// the resumable path, including when nested in generated containers.
    fn inert_drop(&self, ty: &Ty, params: &HashSet<String>, seen: &mut HashSet<String>) -> bool {
        match ty {
            Ty::Int(_)
            | Ty::Bool
            | Ty::Text
            | Ty::Unit
            | Ty::Never
            | Ty::Float
            | Ty::Float32
            | Ty::Buf => true,
            Ty::Shown => self.trusted_budget_host.is_some(),
            Ty::Vec(t)
            | Ty::Array(t)
            | Ty::Slice(t)
            | Ty::Option(t)
            | Ty::Ref(t)
            | Ty::RefMut(t)
            | Ty::SharedVar(true, t) => self.inert_drop(t, params, seen),
            Ty::HashMap(a, b) | Ty::Result(a, b) | Ty::Pair(a, b) => {
                self.inert_drop(a, params, seen) && self.inert_drop(b, params, seen)
            }
            Ty::Product(ms) => ms.iter().all(|(_, m)| self.inert_drop(m, params, seen)),
            Ty::Param(p) => params.contains(p),
            Ty::Data(name, args) => {
                if self.bindings.types.contains_key(name)
                    || !args.iter().all(|a| self.inert_drop(a, params, seen))
                {
                    return false;
                }
                let Some(d) = self.data(name) else {
                    return false;
                };
                if d.linear || d.generics.len() != args.len() {
                    return false;
                }
                // Included generated types are local to the embedding crate.
                // A host can add Drop to non-Copy data unless it asserts the
                // whole-embedding contract at a separate qualified entry.
                if self.trusted_budget_host.is_none()
                    && !(d.copy && self.flags[self.data_index[name.as_str()]][0])
                {
                    return false;
                }
                if !seen.insert(name.clone()) {
                    return true;
                }
                let ps = d.generics.iter().cloned().collect();
                let safe = d
                    .ctors
                    .iter()
                    .all(|c| c.fields.iter().all(|f| self.inert_drop(&f.ty, &ps, seen)));
                seen.remove(name);
                safe
            }
            Ty::Union(i) => {
                self.trusted_budget_host.is_some()
                    && self.pkg.unions[*i]
                        .members
                        .iter()
                        .all(|t| self.inert_drop(t, params, seen))
            }
            Ty::Std(_, _)
            | Ty::Fn(_)
            | Ty::Info(_)
            | Ty::BudgetAnswer(_)
            | Ty::Infer
            | Ty::SharedVar(false, _) => false,
        }
    }
}

fn host_scalar(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Int(_) | Ty::Bool | Ty::Unit | Ty::Never | Ty::Float | Ty::Float32
    ) && !matches!(ty, Ty::Int(Width::Nat))
}

fn host_argument(ty: &Ty) -> bool {
    host_scalar(ty) || matches!(ty, Ty::Text) || matches!(ty, Ty::Ref(inner) if **inner == Ty::Text)
}

fn host_result(ty: &Ty) -> bool {
    host_scalar(ty)
        || matches!(ty, Ty::Text)
        || matches!(ty, Ty::Option(inner) if **inner == Ty::Text)
}

fn shared_callback(ty: &Ty) -> bool {
    matches!(ty, Ty::Ref(inner) if matches!(&**inner, Ty::Fn(f) if f.tier == Tier::S && f.kind.dup()))
}

fn owned_callback(ty: &Ty) -> bool {
    matches!(ty, Ty::Fn(f) if f.tier == Tier::S && f.kind.dup())
}

fn callback_mode(mode: Mode) -> Mode {
    if mode == Mode::Observer {
        Mode::Observer
    } else {
        Mode::Callback
    }
}

// Integer literals and fully checked constant arithmetic cannot enter a host
// panic hook. Keep width checks identical to the generated checked operations.
fn constant_integer(e: &Expr) -> Option<i128> {
    match &e.kind {
        ExprKind::Int(value) => Some(i128::from(*value)),
        ExprKind::Arith { op, args, width } => {
            let a = constant_integer(args.first()?)?;
            let value = match op {
                Arith::Neg => a.checked_neg()?,
                Arith::Add => a.checked_add(constant_integer(args.get(1)?)?)?,
                Arith::Sub => a.checked_sub(constant_integer(args.get(1)?)?)?,
                Arith::Mul => a.checked_mul(constant_integer(args.get(1)?)?)?,
                Arith::Div => return None,
            };
            let (min, max) = match width {
                Width::W32 => (i128::from(i32::MIN), i128::from(i32::MAX)),
                Width::W64 => (i128::from(i64::MIN), i128::from(i64::MAX)),
                Width::U8 => (0, i128::from(u8::MAX)),
                Width::U32 => (0, i128::from(u32::MAX)),
                Width::U64 => (0, i128::from(u64::MAX)),
                Width::Nat => (0, i128::MAX),
            };
            (min..=max).contains(&value).then_some(value)
        }
        _ => None,
    }
}

fn immediate_budget(e: &Expr) -> Option<&BudgetNode> {
    match &e.kind {
        // A memory budget's count is the cells charged on the thread, which
        // the synchronous fuel does not see: it always runs resumably.
        ExprKind::Budget(b) if !b.memory => Some(b),
        ExprKind::Block(b) if b.stmts.is_empty() => immediate_budget(b.tail.as_deref()?),
        _ => None,
    }
}

/// Include nested suspending arms, which the general NIR walk omits, as well
/// as places and closure captures that need not occur as a plain read.
fn mentions(e: &Expr, id: u32) -> bool {
    let mut found = false;
    e.walk(&mut |x| {
        found |= match &x.kind {
            ExprKind::Read { local, .. } => local.id == id,
            ExprKind::Ref(p) | ExprKind::RefMut(p) => p.local.id == id,
            ExprKind::Call(c) => {
                matches!(&c.callee, Callee::Cont(l) | Callee::Local(l) if l.id == id)
            }
            ExprKind::Closure(c) => {
                c.clones.iter().any(|l| l.id == id) || c.refs.iter().any(|r| r.outer.id == id)
            }
            ExprKind::Handle(h) => {
                h.captures.iter().chain(&h.clones).any(|l| l.id == id)
                    || h.susp.iter().any(|a| {
                        a.guard.as_ref().is_some_and(|g| mentions(g, id)) || mentions(&a.body, id)
                    })
            }
            _ => false,
        };
    });
    found
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn continuation_aliases_places_and_nested_suspending_arms_are_not_missed() {
        let pkg = tauto_nir::compile(
            r#"let result := handle { budget(steps: 0) { 1 } } with { exceeded(info), k => 0 }"#,
        )
        .unwrap();
        let mut handler = None;
        for f in &pkg.fns {
            f.body.walk(&mut |e| {
                if let ExprKind::Handle(h) = &e.kind {
                    handler = Some((**h).clone());
                }
            });
        }
        let mut handler = handler.unwrap();
        let k = handler.susp[0].k.clone().unwrap();
        let mut read = handler.susp[0].body.clone();
        read.kind = ExprKind::Read {
            local: k.clone(),
            how: Use::Move,
        };
        assert!(mentions(&read, k.id));
        let mut alias = read.clone();
        alias.kind = ExprKind::Block(Block {
            stmts: vec![Stmt::Let {
                local: Local {
                    id: k.id + 1000,
                    name: "alias".into(),
                    repr: Repr::Plain,
                },
                ty: read.ty.clone(),
                init: read.clone(),
                span: read.span,
            }],
            tail: None,
        });
        assert!(mentions(&alias, k.id));
        let mut place = read.clone();
        place.kind = ExprKind::Ref(Place {
            local: k.clone(),
            path: Vec::new(),
            ty: read.ty.clone(),
        });
        assert!(mentions(&place, k.id));
        handler.captures.clear();
        handler.clones.clear();
        handler.susp[0].body = read.clone();
        let mut nested = read;
        nested.kind = ExprKind::Handle(Box::new(handler));
        assert!(mentions(&nested, k.id));
    }
}
