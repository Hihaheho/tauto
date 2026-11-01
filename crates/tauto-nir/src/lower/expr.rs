//! Statements and expressions.

use std::collections::{BTreeMap, HashMap};

use tauto::surface::{DataDecl, FnDecl, Stmt, SurfaceTerm, TermId, TermKind};
use tauto::types::{Kind, Ty as TTy};

use super::ty::{set_fn_tier, set_written_tiers, set_written_tiers_in_args};
use super::*;

const OPERATORS: &[&str] = &[
    "+", "-", "*", "/", "==", "!=", "<", ">", "<=", ">=", "&&", "||",
];

fn expr_of(kind: ExprKind, ty: Ty, span: Span) -> Expr {
    Expr { kind, ty, span }
}

/// A lifted call borrows its captures until the call returns, including
/// while evaluating its explicit arguments. Keep the clones of those
/// locals explicit: last-use elision visits the arguments backwards and
/// cannot otherwise see the lifetime of an earlier capture argument.
fn keep_capture_clones(e: &mut Expr, borrowed: &[u32]) {
    if let ExprKind::Read {
        local,
        how: Use::Clone,
    } = &e.kind
        && local.repr == Repr::Plain
        && borrowed.contains(&local.id)
    {
        let place = Place {
            local: local.clone(),
            path: Vec::new(),
            ty: e.ty.clone(),
        };
        e.kind = ExprKind::Deref {
            value: Box::new(expr_of(
                ExprKind::Ref(place),
                Ty::Ref(Box::new(e.ty.clone())),
                e.span,
            )),
            how: Use::Clone,
        };
        return;
    }
    match &mut e.kind {
        ExprKind::Block(b) => keep_block_capture_clones(b, borrowed),
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            keep_capture_clones(cond, borrowed);
            keep_capture_clones(then, borrowed);
            if let Some(otherwise) = otherwise {
                keep_capture_clones(otherwise, borrowed);
            }
        }
        ExprKind::And(a, b) | ExprKind::Or(a, b) => {
            keep_capture_clones(a, borrowed);
            keep_capture_clones(b, borrowed);
        }
        ExprKind::Match(m) => {
            keep_capture_clones(&mut m.scrut, borrowed);
            for arm in &mut m.arms {
                if let Some(guard) = &mut arm.guard {
                    keep_capture_clones(guard, borrowed);
                }
                keep_capture_clones(&mut arm.body, borrowed);
            }
        }
        // These are opaque to last-use elision, so their existing clones
        // already survive. In particular, do not alter closure ownership.
        ExprKind::Closure(_) | ExprKind::Handle(_) | ExprKind::Budget(_) => {}
        _ => {
            for operand in e.operands_mut() {
                keep_capture_clones(operand, borrowed);
            }
        }
    }
}

fn keep_block_capture_clones(b: &mut Block, borrowed: &[u32]) {
    for stmt in &mut b.stmts {
        match stmt {
            crate::Stmt::Let { init, .. } | crate::Stmt::Var { init, .. } => {
                keep_capture_clones(init, borrowed)
            }
            crate::Stmt::Assign { value, .. } | crate::Stmt::Expr(value) => {
                keep_capture_clones(value, borrowed)
            }
            crate::Stmt::While { cond, body, .. } => {
                keep_capture_clones(cond, borrowed);
                keep_block_capture_clones(body, borrowed);
            }
            crate::Stmt::Return { value, .. } => {
                if let Some(value) = value {
                    keep_capture_clones(value, borrowed);
                }
            }
        }
    }
    if let Some(tail) = &mut b.tail {
        keep_capture_clones(tail, borrowed);
    }
}

impl<'a> Lowerer<'a> {
    // ---- scopes --------------------------------------------------------

    pub fn find(&self, cx: &Cx, name: &str) -> Option<usize> {
        cx.bindings
            .iter()
            .rposition(|b| b.name == name && !cx.hidden_bindings.contains(&b.local.id))
    }

    fn find_capture(&self, cx: &Cx, key: &CaptureKey) -> Option<usize> {
        cx.capture_bindings
            .iter()
            .rev()
            .find(|(candidate, _)| candidate == key)
            .map(|(_, binding)| *binding)
            .filter(|binding| *binding < cx.bindings.len())
    }

    /// Records that the closures being lowered use binding `i`, when it
    /// lies outside them.
    pub fn note_capture(&self, cx: &mut Cx, i: usize) {
        let local = cx.bindings[i].local.clone();
        for f in cx.frames.iter_mut() {
            if i < f.base && !f.captures.iter().any(|c| c.id == local.id) {
                f.captures.push(local.clone());
            }
        }
    }

    pub fn local_ty(&self, name: &str, at: tauto::surface::TermId, fallback: Option<&TTy>) -> TTy {
        self.types
            .local(name, at)
            .cloned()
            .or_else(|| fallback.cloned())
            .unwrap_or(TTy::Var(0))
    }

    // ---- blocks and statements ----------------------------------------

    pub fn block_of(
        &mut self,
        cx: &mut Cx,
        stmts: &[&Stmt],
        root: bool,
        expected: &TTy,
    ) -> R<Block> {
        self.block_with(cx, stmts, root, expected, None)
    }

    pub(crate) fn block_with(
        &mut self,
        cx: &mut Cx,
        stmts: &[&Stmt],
        root: bool,
        expected: &TTy,
        tail_k: Option<&super::handle::TailK>,
    ) -> R<Block> {
        let mark = cx.bindings.len();
        let capture_mark = cx.capture_bindings.len();
        let mut out: Vec<crate::Stmt> = Vec::new();
        let mut tail: Option<Box<Expr>> = None;
        for (i, s) in stmts.iter().enumerate() {
            let last = i + 1 == stmts.len();
            match s {
                Stmt::Expr(e) if last => {
                    tail = Some(Box::new(match tail_k {
                        Some(tk) => self.expr_tail(cx, e, tk)?,
                        None => self.expr_expect(cx, e, expected)?,
                    }));
                }
                Stmt::Expr(e) => out.push(crate::Stmt::Expr(self.expr(cx, e)?)),
                Stmt::Let {
                    name,
                    ty,
                    value,
                    borrow,
                    ..
                } => {
                    let s = self.let_stmt(cx, name, ty.as_ref(), value, *borrow)?;
                    out.push(s);
                }
                Stmt::Var { name, value, .. } => {
                    let rest = &stmts[i + 1..];
                    let s = self.var_stmt(cx, name, value, rest)?;
                    out.push(s);
                }
                Stmt::Assign { name, place, value } => {
                    let s = self.assign_stmt(cx, name, place.as_ref(), value)?;
                    out.push(s);
                }
                Stmt::While { condition, body } => {
                    let cond = self.expr_expect(cx, condition, &TTy::Bool)?;
                    let body = self.body_block(cx, body)?;
                    out.push(crate::Stmt::While {
                        cond,
                        body,
                        tick: if cx.under_budget {
                            Tick::Budget
                        } else {
                            Tick::Host
                        },
                        span: condition.span,
                    });
                }
                Stmt::Return(value) => {
                    cx.host_ret |= cx.host_m;
                    let ret = cx.ret.clone();
                    let value = match value {
                        Some(v) => Some(self.expr_expect(cx, v, &ret)?),
                        None => None,
                    };
                    let span = value.as_ref().map(|v| v.span).unwrap_or(Span::new(0, 0));
                    out.push(crate::Stmt::Return { value, span });
                }
                Stmt::Fn(f) => {
                    let hoisted = self
                        .fns
                        .get(&f.name)
                        .is_some_and(|src| std::ptr::eq(src.decl, f));
                    if !root && !hoisted {
                        return unsupported(
                            msg!("nir-the-local-function", f = f.name.to_string()),
                            f.span,
                        );
                    }
                    if hoisted && self.nested_fns.contains(&f.name) {
                        out.extend(self.lift_captures(cx, f)?);
                    }
                }
                Stmt::Effect(_)
                | Stmt::Struct(_)
                | Stmt::Enum(_)
                | Stmt::Extern { .. }
                | Stmt::Class(_)
                | Stmt::Instance(_)
                | Stmt::Theorem(_)
                | Stmt::Def(_)
                | Stmt::Import { .. }
                | Stmt::Module { .. }
                | Stmt::Mutual { .. }
                | Stmt::Attributed { .. }
                | Stmt::Called { .. }
                | Stmt::Syntax { .. }
                | Stmt::Macro { .. }
                | Stmt::Inductive(_) => {}
                Stmt::Other(what, span) => {
                    return unsupported(msg!("nir-the-statement", what = what.to_string()), *span);
                }
            }
        }
        cx.bindings.truncate(mark);
        cx.capture_bindings.truncate(capture_mark);
        Ok(Block { stmts: out, tail })
    }

    /// A loop body or a branch: a block term as a block.
    pub fn body_block(&mut self, cx: &mut Cx, body: &SurfaceTerm) -> R<Block> {
        match &*body.kind {
            TermKind::Block(stmts) => {
                let refs: Vec<&Stmt> = stmts.iter().collect();
                self.block_of(cx, &refs, false, &TTy::Unit)
            }
            _ => {
                let e = self.expr_expect(cx, body, &TTy::Unit)?;
                Ok(Block {
                    stmts: Vec::new(),
                    tail: Some(Box::new(e)),
                })
            }
        }
    }

    fn let_stmt(
        &mut self,
        cx: &mut Cx,
        name: &str,
        declared: Option<&SurfaceTerm>,
        value: &SurfaceTerm,
        borrow: bool,
    ) -> R<crate::Stmt> {
        let fallback = self.types.term(value).cloned();
        let is_lam = matches!(
            &*value.kind,
            TermKind::Lam { .. } | TermKind::BorrowLam { .. }
        );
        // A closure literal's own type has the kind its captures give it; the
        // name's recorded type may not.
        let lty = match (&fallback, is_lam) {
            (Some(t @ TTy::Fn(..)), true) => t.clone(),
            _ => self.local_ty(name, value.id(), fallback.as_ref()),
        };
        let borrow_closure = is_lam && self.lam_borrows(cx, value);
        let init = if is_lam {
            self.closure(cx, value, None, borrow_closure, None)?
        } else if borrow || matches!(lty, TTy::Borrow(..)) {
            self.expr(cx, value)?
        } else {
            self.expr_expect(cx, value, &lty)?
        };
        let repr = match &lty {
            _ if borrow_closure => Repr::BorrowClosure,
            TTy::Borrow(inner, _) if matches!(**inner, TTy::Fn(..)) => Repr::FnRef,
            TTy::Borrow(_, false) => Repr::Ref,
            TTy::Borrow(_, true) => Repr::RefMut,
            _ => Repr::Plain,
        };
        // `let &y = x` of a borrowed `x` rebinds the borrow: reading `x`
        // for its value (a copy or a clone) would give `y` the value where
        // it holds a borrow.
        let mut init = init;
        if repr == Repr::Ref
            && let ExprKind::Read { local, how } = &mut init.kind
            && local.repr == Repr::Ref
            && matches!(how, Use::Copy | Use::Clone)
        {
            *how = Use::Move;
        }
        let local = self.fresh_local(name, repr);
        // A written function type's row is the one the value is held at,
        // unless the value says its own.
        let written = declared
            .and_then(pi_effects)
            .map(|e| e.into_iter().collect::<Row>());
        let fn_row = self.value_row(cx, value).or(written.clone());
        // A view (`Option(&A)`) keeps the borrow its value has, even when the
        // checker took it for the value (`&A ≡ A`).
        // A function item is held at the tier of its own row, as a closure
        // literal is.
        let item = matches!(init.kind, ExprKind::FnValue { .. }) && written.is_none();
        let ty = if is_lam || item || (!borrow && holds_ref(&init.ty)) {
            init.ty.clone()
        } else {
            let mut ty = self.conv(&lty);
            // A function read from a field is held at the tier of the
            // field's row, as a written row would make it.
            let from_field = matches!(&*value.kind, TermKind::Field { .. });
            if let (true, Some(row)) = (written.is_some() || from_field, &fn_row) {
                super::ty::set_fn_tier(&mut ty, self.row_tier_in(row, cx));
            }
            ty
        };
        if (is_lam || item) && matches!(ty, Ty::Fn(_)) {
            cx.held.insert(local.id, ty.clone());
        }
        cx.bindings.push(Binding {
            name: name.to_string(),
            local: local.clone(),
            ty: lty.clone(),
            mode: match &lty {
                TTy::Borrow(_, m) => Mode::Borrow(*m),
                _ if borrow_closure => Mode::BorrowClosure,
                _ => Mode::Owned,
            },
            fn_row,
            budgeted: cx.under_budget,
            celled: false,
        });
        Ok(crate::Stmt::Let {
            local,
            ty,
            init,
            span: value.span,
        })
    }

    fn var_stmt(
        &mut self,
        cx: &mut Cx,
        name: &str,
        value: &SurfaceTerm,
        rest: &[&Stmt],
    ) -> R<crate::Stmt> {
        let fallback = self.types.term(value).cloned();
        let lty = self.local_ty(name, value.id(), fallback.as_ref());
        let init = self.expr_expect(cx, value, &lty)?;
        self.m_hit.set(false);
        let celled = self.escaping_capture(cx, rest, name)
            || ((cx.tier == Tier::M || self.m_hit.get()) && self.kind_of(&lty).dup());
        let repr = if celled {
            if self.kind_of(&lty) == Kind::Copy {
                Repr::SharedVar(true)
            } else if self.kind_of(&lty).dup() {
                Repr::SharedVar(false)
            } else {
                return unsupported(
                    msg!("nir-the-affine-var-captured-by-a", name = name.to_string()),
                    value.span,
                );
            }
        } else {
            Repr::Plain
        };
        let local = self.fresh_local(name, repr);
        let ty = self.conv(&lty);
        let fn_row = self.value_row(cx, value);
        cx.bindings.push(Binding {
            name: name.to_string(),
            local: local.clone(),
            ty: lty,
            mode: Mode::Var,
            fn_row,
            budgeted: cx.under_budget,
            celled,
        });
        Ok(crate::Stmt::Var {
            local,
            ty,
            init,
            span: value.span,
        })
    }

    fn assign_stmt(
        &mut self,
        cx: &mut Cx,
        name: &str,
        place: Option<&SurfaceTerm>,
        value: &SurfaceTerm,
    ) -> R<crate::Stmt> {
        if let Some(place) = place {
            let Some(target) = self.place(cx, place)? else {
                return unsupported(
                    msg!("nir-assignment-to-a-field-of", name = name.to_string()),
                    place.span,
                );
            };
            let inner = self.types.term(place).map(|t| t.unborrowed().clone());
            let v = match inner {
                Some(inner) => self.expr_expect(cx, value, &inner)?,
                None => self.expr(cx, value)?,
            };
            return Ok(crate::Stmt::Assign {
                target,
                value: v,
                span: value.span,
            });
        }
        let Some(i) = self.find(cx, name) else {
            return unsupported(
                msg!("nir-assignment-to-which-is-not-a", name = name.to_string()),
                value.span,
            );
        };
        self.note_capture(cx, i);
        let b = cx.bindings[i].clone();
        let inner = b.ty.unborrowed().clone();
        let v = self.expr_expect(cx, value, &inner)?;
        let ty = self.conv(&inner);
        Ok(crate::Stmt::Assign {
            target: Place {
                local: b.local,
                path: Vec::new(),
                ty,
            },
            value: v,
            span: value.span,
        })
    }

    /// The names a term uses from outside, with those the local functions
    /// it calls use from the body around them.
    pub fn free_names(&self, t: &SurfaceTerm) -> Vec<String> {
        let mut out = tauto::lin::free_vars(t);
        let mut i = 0;
        while i < out.len() {
            let n = out[i].clone();
            i += 1;
            if !self.nested_fns.contains(&n) {
                continue;
            }
            let g = self.fns[&n].decl;
            for m in tauto::lin::free_vars(&g.body) {
                if !g.params.contains(&m) && !out.contains(&m) {
                    out.push(m);
                }
            }
        }
        out
    }

    /// Runtime captures resolve local helpers through their declaration's
    /// environment keys, not by expanding their bodies' source spellings.
    fn free_bindings(&self, cx: &Cx, t: &SurfaceTerm) -> Vec<(Option<CaptureKey>, usize)> {
        let mut out = Vec::new();
        for name in tauto::lin::free_vars(t) {
            if let Some(i) = self.find(cx, &name) {
                out.push((None, i));
            } else if let Some(caps) = self.local_caps.get(&name) {
                for cap in caps {
                    if let Some(i) = self.find_capture(cx, &cap.key) {
                        out.push((Some(cap.key.clone()), i));
                    }
                }
            }
        }
        out
    }

    /// The captures of a local function, from the names in scope where it is
    /// written.
    fn lift_captures(&mut self, cx: &mut Cx, f: &FnDecl) -> R<Vec<crate::Stmt>> {
        let free = tauto::lin::free_vars(&f.body);
        let mut inputs = Vec::new();
        let mut forwarded = HashSet::new();
        for name in free {
            if f.params.contains(&name) || name == f.name {
                continue;
            }
            if self.find(cx, &name).is_none() && self.nested_fns.contains(&name) {
                let Some(caps) = self.local_caps.get(&name) else {
                    return unsupported(
                        msg!(
                            "nir-the-local-function-used-before-it",
                            name = name.to_string()
                        ),
                        f.span,
                    );
                };
                for cap in caps {
                    if forwarded.insert(cap.key.clone()) {
                        inputs.push((cap.name.clone(), Some(cap.clone())));
                    }
                }
            } else {
                inputs.push((name, None));
            }
        }
        let mut mutated: HashSet<String> = HashSet::new();
        tauto::surface::walk::values(&f.body, &mut |node| match node {
            tauto::surface::walk::Node::Stmt(Stmt::Assign { name, .. }) => {
                mutated.insert(name.clone());
            }
            tauto::surface::walk::Node::Term(t)
                if matches!(&*t.kind, TermKind::Borrow { mutable: true, .. }) =>
            {
                let TermKind::Borrow { term, .. } = &*t.kind else {
                    unreachable!()
                };
                let mut root = &**term;
                while let TermKind::Field { base, .. } = &*root.kind {
                    root = base;
                }
                if let TermKind::Var(name) = &*root.kind {
                    mutated.insert(name.clone());
                }
            }
            _ => {}
        });
        let mut caps = Vec::new();
        let mut storage = Vec::new();
        for (name, inherited) in inputs {
            let found = match &inherited {
                Some(cap) => self.find_capture(cx, &cap.key),
                None => self.find(cx, &name),
            };
            let Some(i) = found else {
                if inherited.is_some() {
                    return unsupported(
                        msg!(
                            "nir-the-lexical-capture-of-local-function",
                            name = name.to_string(),
                            f = f.name.to_string()
                        ),
                        f.span,
                    );
                }
                continue;
            };
            let b = cx.bindings[i].clone();
            let mutable = inherited.as_ref().map_or_else(
                || mutated.contains(&name),
                |cap| matches!(cap.ty, TTy::Borrow(_, true)),
            );
            let key = CaptureKey {
                function: f.name.clone(),
                index: caps.len(),
            };
            let from = inherited.as_ref().map(|cap| cap.key.clone());
            self.note_capture(cx, i);
            if b.celled && matches!(b.local.repr, Repr::SharedVar(true) | Repr::SharedVar(false)) {
                cx.capture_bindings.push((key.clone(), i));
                caps.push(LiftedCap {
                    name,
                    key,
                    forwarded: from,
                    ty: b.ty.unborrowed().clone(),
                    source_owned: false,
                    owned: false,
                    cell: Some(b.local.repr),
                });
                continue;
            }
            if b.celled
                || !matches!(b.local.repr, Repr::Plain | Repr::Ref | Repr::RefMut)
                || matches!(b.mode, Mode::Cont | Mode::ContBudget | Mode::BorrowClosure)
                || matches!(b.ty.unborrowed(), TTy::Fn(..))
                || (mutable && !matches!(b.mode, Mode::Var | Mode::Borrow(true)))
            {
                return unsupported(
                    msg!(
                        "nir-the-local-function-that-uses-which",
                        f = f.name.to_string(),
                        name = name.to_string()
                    ),
                    f.span,
                );
            }
            let source_owned = inherited
                .as_ref()
                .map_or(b.mode == Mode::Owned, |cap| cap.source_owned);
            let ty = b.ty.unborrowed().clone();
            // A capture the body only lends (`&xs`) is lent to each call,
            // so the function may be called more than once.
            // A forwarded capture is owned as the function it comes from has it.
            let owned = source_owned
                && !self.kind_of(&ty).dup()
                && inherited
                    .as_ref()
                    .map_or_else(|| consumes(&f.body, &name), |cap| cap.owned);
            let binding = if source_owned {
                if owned && (b.mode != Mode::Owned || b.local.repr != Repr::Plain) {
                    return unsupported(
                        msg!(
                            "nir-the-owned-lexical-capture-of-local",
                            name = name.to_string(),
                            f = f.name.to_string()
                        ),
                        f.span,
                    );
                }
                // Capture now, even if the function is never called. This
                // slot belongs to the declaration's block, not its source
                // binding's block. Shared storage is a snapshot too.
                let local = self.fresh_local(&name, Repr::Plain);
                let nty = self.conv(&ty);
                storage.push(crate::Stmt::Let {
                    local: local.clone(),
                    ty: nty.clone(),
                    init: expr_of(
                        ExprKind::Read {
                            local: b.local.clone(),
                            how: self.use_of(&ty),
                        },
                        nty,
                        f.span,
                    ),
                    span: f.span,
                });
                let binding = cx.bindings.len();
                cx.hidden_bindings.insert(local.id);
                cx.bindings.push(Binding {
                    local,
                    ty: ty.clone(),
                    mode: Mode::Owned,
                    ..b
                });
                binding
            } else {
                i
            };
            cx.capture_bindings.push((key.clone(), binding));
            caps.push(LiftedCap {
                name,
                key,
                forwarded: from,
                ty: if owned {
                    ty
                } else {
                    TTy::Borrow(Box::new(ty), mutable)
                },
                source_owned,
                owned,
                cell: None,
            });
        }
        self.local_caps.insert(f.name.clone(), caps);
        Ok(storage)
    }

    /// What a call of a local function passes for what it captured.
    fn capture_args(&mut self, cx: &mut Cx, name: &str, span: Span) -> R<Vec<Expr>> {
        let Some(caps) = self.local_caps.get(name).cloned() else {
            if self.nested_fns.contains(name) {
                return unsupported(
                    msg!(
                        "nir-the-local-function-used-before-it",
                        name = name.to_string()
                    ),
                    span,
                );
            }
            return Ok(Vec::new());
        };
        let mut out = Vec::new();
        for cap in caps {
            let mutable = matches!(cap.ty, TTy::Borrow(_, true));
            let found = self
                .find_capture(cx, &cap.key)
                .map(|i| (i, cx.bindings[i].clone()));
            let Some((i, b)) = found else {
                return unsupported(
                    msg!(
                        "nir-the-local-function-called-where-is",
                        name = name.to_string(),
                        cap = cap.name.to_string()
                    ),
                    span,
                );
            };
            self.check_budget_value(cx, &b, span)?;
            if cx.under_budget
                && b.fn_row
                    .as_ref()
                    .is_some_and(|row| row.iter().any(|e| e == "Div" || e.starts_with('|')))
            {
                return unsupported(msg!("nir-a-local-function-capturing-a-potentially"), span);
            }
            if b.celled != cap.cell.is_some()
                || (mutable && !b.celled && !matches!(b.mode, Mode::Var | Mode::Borrow(true)))
            {
                return unsupported(
                    msg!(
                        "nir-the-local-function-called-where-is-2",
                        name = name.to_string(),
                        cap = cap.name.to_string()
                    ),
                    span,
                );
            }
            self.note_capture(cx, i);
            let ty = self.conv(b.ty.unborrowed());
            if cap.owned {
                if b.mode != Mode::Owned || b.local.repr != Repr::Plain {
                    return unsupported(
                        msg!(
                            "nir-the-owned-capture-of-local-function",
                            cap = cap.name.to_string(),
                            name = name.to_string()
                        ),
                        span,
                    );
                }
                out.push(expr_of(
                    ExprKind::Read {
                        local: b.local,
                        how: Use::Move,
                    },
                    ty,
                    span,
                ));
                continue;
            }
            if b.celled {
                let cell = match b.local.repr {
                    Repr::SharedVar(true) => Ty::SharedVar(true, Box::new(ty.clone())),
                    _ => Ty::SharedVar(false, Box::new(ty.clone())),
                };
                let p = Place {
                    local: b.local,
                    path: Vec::new(),
                    ty: cell.clone(),
                };
                out.push(expr_of(ExprKind::Ref(p), Ty::Ref(Box::new(cell)), span));
                continue;
            }
            let p = Place {
                local: b.local,
                path: Vec::new(),
                ty: ty.clone(),
            };
            out.push(if mutable {
                expr_of(ExprKind::RefMut(p), Ty::RefMut(Box::new(ty)), span)
            } else {
                expr_of(ExprKind::Ref(p), Ty::Ref(Box::new(ty)), span)
            });
        }
        Ok(out)
    }

    /// The row of a function-typed value written as `value`.
    pub(crate) fn value_row(&self, cx: &Cx, value: &SurfaceTerm) -> Option<Row> {
        match &*value.kind {
            TermKind::Lam { body, .. } => Some(self.term_row(body)),
            TermKind::BorrowLam { lam, .. } => self.value_row(cx, lam),
            TermKind::Var(n) => match self.find(cx, n) {
                Some(i) => cx.bindings[i].fn_row.clone(),
                None if self.fns.contains_key(n.as_str()) => Some(self.fn_row(n)),
                None => None,
            },
            TermKind::Field { base, name } => self
                .types
                .term(base)
                .and_then(|b| self.named_field_row(b, name)),
            _ => None,
        }
    }

    /// Whether a closure holds borrows or `var`s with affine content, that
    /// is, whether it is a closure that borrows.
    pub fn lam_borrows(&self, cx: &Cx, lam: &SurfaceTerm) -> bool {
        self.free_bindings(cx, lam).iter().any(|(_, i)| {
            let b = &cx.bindings[*i];
            if b.mode == Mode::BorrowClosure {
                return true;
            }
            let (inner, borrowed) = match &b.ty {
                TTy::Borrow(inner, _) => (&**inner, true),
                t => (t, false),
            };
            let affine = !self.kind_of(inner).dup();
            affine && (borrowed || b.mode == Mode::Var)
        })
    }

    /// Whether a `var` named `name` is captured by a closure that may
    /// outlive its scope: one not written where a borrowed function is
    /// expected.
    fn escaping_capture(&self, cx: &Cx, rest: &[&Stmt], name: &str) -> bool {
        let mentions = |t: &SurfaceTerm| self.free_names(t).iter().any(|n| n == name);
        let mut found = false;
        for s in rest {
            self.scan_stmt(cx, s, name, &mentions, &mut found);
        }
        found
    }

    fn scan_stmt(
        &self,
        cx: &Cx,
        s: &Stmt,
        name: &str,
        mentions: &dyn Fn(&SurfaceTerm) -> bool,
        found: &mut bool,
    ) {
        match s {
            Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
                self.scan(cx, value, name, mentions, false, found)
            }
            Stmt::Expr(e) | Stmt::Return(Some(e)) => self.scan(cx, e, name, mentions, false, found),
            Stmt::While { condition, body } => {
                self.scan(cx, condition, name, mentions, false, found);
                self.scan(cx, body, name, mentions, false, found);
            }
            // A local function is lifted: it is passed what it uses.
            Stmt::Fn(_) => {}
            _ => {}
        }
    }

    /// Looks for a closure literal that mentions the var and is not in a
    /// borrowed position (`borrowed`: it is an argument for a `&f`).
    fn scan(
        &self,
        cx: &Cx,
        t: &SurfaceTerm,
        name: &str,
        mentions: &dyn Fn(&SurfaceTerm) -> bool,
        borrowed: bool,
        found: &mut bool,
    ) {
        use tauto::surface::Handler;
        match &*t.kind {
            TermKind::Lam { body, .. } => {
                if !borrowed && mentions(t) && !self.lam_borrows(cx, t) {
                    *found = true;
                }
                self.scan(cx, body, name, mentions, false, found);
            }
            TermKind::BorrowLam { lam, .. } => self.scan(cx, lam, name, mentions, borrowed, found),
            // A local function that uses the var and is not called but passed
            // on, may outlive it.
            TermKind::Var(n) => {
                if !borrowed && self.nested_fns.contains(n) && mentions(t) {
                    *found = true;
                }
            }
            TermKind::App {
                function,
                arguments,
            } => {
                if !matches!(&*function.kind, TermKind::Var(_)) {
                    self.scan(cx, function, name, mentions, false, found);
                }
                let ps = match self.types.term(function) {
                    Some(TTy::Fn(ps, _, _)) => ps.clone(),
                    _ => Vec::new(),
                };
                for (i, a) in arguments.iter().enumerate() {
                    let b = matches!(ps.get(i), Some(TTy::Borrow(..)));
                    self.scan(cx, a, name, mentions, b, found);
                }
            }
            TermKind::Borrow { term, .. } | TermKind::Tagged { term, .. } => {
                self.scan(cx, term, name, mentions, borrowed, found)
            }
            TermKind::Record { fields, .. } => fields
                .iter()
                .for_each(|(_, v)| self.scan(cx, v, name, mentions, false, found)),
            TermKind::Tuple(members) => members
                .iter()
                .for_each(|v| self.scan(cx, v, name, mentions, false, found)),
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.scan(cx, condition, name, mentions, false, found);
                self.scan(cx, then, name, mentions, false, found);
                if let Some(o) = otherwise {
                    self.scan(cx, o, name, mentions, false, found);
                }
            }
            TermKind::Field { base, .. } => self.scan(cx, base, name, mentions, false, found),
            TermKind::Perform { args, .. } => args
                .iter()
                .for_each(|a| self.scan(cx, a, name, mentions, false, found)),
            TermKind::Budget { steps, body, .. } => {
                self.scan(cx, steps, name, mentions, false, found);
                self.scan(cx, body, name, mentions, false, found);
            }
            TermKind::Block(stmts) => {
                for s in stmts {
                    self.scan_stmt(cx, s, name, mentions, found);
                }
            }
            TermKind::Handle { body, handlers } => {
                self.scan(cx, body, name, mentions, false, found);
                let m_handle = handlers.iter().any(|h| {
                    matches!(h, Handler::Operation { effect, .. } if self.quant(effect) == Quant::Many)
                });
                if m_handle && mentions(body) {
                    self.m_hit.set(true);
                }
                // The arms of an operation that resumes run beside the
                // body, as futures that outlive the statement that starts
                // them: what they mention is shared.
                let suspends = handlers.iter().any(|h| {
                    matches!(h, Handler::Operation { effect, .. }
                        if !matches!(self.quant(effect), Quant::Direct | Quant::Zero))
                });
                for h in handlers {
                    match h {
                        Handler::Return { body, .. } => {
                            if suspends && mentions(body) {
                                *found = true;
                            }
                            self.scan(cx, body, name, mentions, false, found)
                        }
                        Handler::Operation { body, guard, .. } => {
                            if suspends
                                && (mentions(body) || guard.as_ref().is_some_and(|g| mentions(g)))
                            {
                                *found = true;
                            }
                            self.scan(cx, body, name, mentions, false, found);
                            if let Some(g) = guard {
                                self.scan(cx, g, name, mentions, false, found);
                            }
                        }
                    }
                }
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                self.scan(cx, scrutinee, name, mentions, false, found);
                for a in arms {
                    if let Some(g) = &a.guard {
                        self.scan(cx, g, name, mentions, false, found);
                    }
                    self.scan(cx, &a.body, name, mentions, false, found);
                }
            }
            _ => {}
        }
    }

    // ---- expressions ---------------------------------------------------

    /// A term, made to fit the type expected where it stands.
    pub fn expr_expect(&mut self, cx: &mut Cx, t: &SurfaceTerm, expected: &TTy) -> R<Expr> {
        // A field where its borrow is wanted: the result of a function
        // that returns one (`fn f(&mut s: S): &mut u64 { s.n }`) lends it.
        if let (TermKind::Field { .. }, TTy::Borrow(_, mutable)) = (&*t.kind, expected) {
            return self.borrow_expr(cx, t, *mutable, t);
        }
        let mut e = self.expr(cx, t)?;
        if let Some(TTy::Product(have)) = self.types.term(t).cloned() {
            e = self.fit_product(e, &have, expected);
        }
        let to = self.conv(expected);
        Ok(self.coerce(e, &to))
    }

    /// Makes `e` fit `to`: the union that holds it, the value a borrow
    /// stands for (`&A ≡ A`).
    pub fn coerce(&mut self, e: Expr, to: &Ty) -> Expr {
        if e.ty == *to || matches!(to, Ty::Infer) || matches!(e.ty, Ty::Infer | Ty::Never) {
            return e;
        }
        let span = e.span;
        // A `&mut` that was read as the value it points at, where the
        // borrow itself is wanted (`fn same(&mut x: i64): &mut i64 { x }`).
        if let (Ty::RefMut(inner), ExprKind::Read { local, how }) = (to, &e.kind)
            && e.ty == **inner
            && local.repr == Repr::RefMut
            && matches!(how, Use::Copy | Use::Clone)
        {
            return expr_of(
                ExprKind::Read {
                    local: local.clone(),
                    how: Use::Place,
                },
                to.clone(),
                span,
            );
        }
        if let (Ty::Fn(a), Ty::Fn(b)) = (&e.ty, to) {
            if a.kind != b.kind
                && a.kind.dup() != b.kind.dup()
                && a.params == b.params
                && a.ret == b.ret
                && a.tier == b.tier
            {
                let mut e = e;
                if let ExprKind::Closure(c) = &mut e.kind {
                    c.fn_ty.kind = b.kind;
                    e.ty = to.clone();
                    return e;
                }
                return expr_of(ExprKind::FnCast(Box::new(e)), to.clone(), span);
            }
        }
        match (&e.ty, to) {
            (Ty::Ref(x), t) if **x == *t || !matches!(t, Ty::Ref(_) | Ty::RefMut(_)) => {
                if let Some(how) = self.dup_use(x) {
                    let inner = (**x).clone();
                    let d = expr_of(
                        ExprKind::Deref {
                            value: Box::new(e),
                            how,
                        },
                        inner,
                        span,
                    );
                    return self.coerce(d, to);
                }
                e
            }
            (Ty::Union(from), Ty::Union(into)) => {
                let (from, into) = (*from, *into);
                expr_of(
                    ExprKind::Remap {
                        from,
                        to: Ty::Union(into),
                        value: Box::new(e),
                    },
                    Ty::Union(into),
                    span,
                )
            }
            (Ty::Union(from), t) => {
                // Every member fits `t`.
                let from = *from;
                expr_of(
                    ExprKind::Remap {
                        from,
                        to: t.clone(),
                        value: Box::new(e),
                    },
                    t.clone(),
                    span,
                )
            }
            (_, Ty::Union(into)) => {
                let members = self.unions[*into].members.clone();
                match members.iter().position(|m| *m == e.ty) {
                    Some(variant) => expr_of(
                        ExprKind::Inject {
                            union: *into,
                            variant,
                            value: Box::new(e),
                        },
                        Ty::Union(*into),
                        span,
                    ),
                    None => e,
                }
            }
            _ => e,
        }
    }

    pub fn expr(&mut self, cx: &mut Cx, t: &SurfaceTerm) -> R<Expr> {
        let span = t.span;
        Ok(match &*t.kind {
            TermKind::Nat(n) => {
                let ty = self.ety(t);
                match n.parse::<i128>() {
                    Ok(v) => expr_of(ExprKind::Int(v), ty, span),
                    Err(_) => {
                        return unsupported(
                            msg!("nir-the-literal-which-is-too-large", n = n.to_string()),
                            span,
                        );
                    }
                }
            }
            TermKind::Float(x) => match x.parse::<f64>() {
                Ok(v) if v.is_finite() => expr_of(ExprKind::Float(v), Ty::Float, span),
                _ => {
                    return unsupported(
                        msg!("nir-the-literal-which-is-too-large", n = x.to_string()),
                        span,
                    );
                }
            },
            TermKind::Text(s) => expr_of(ExprKind::Text(s.clone()), Ty::Text, span),
            TermKind::Bool(b) => expr_of(ExprKind::Bool(*b), Ty::Bool, span),
            TermKind::Var(name) => self.var_expr(cx, t, name)?,
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } => {
                self.closure(cx, t, None, false, None)?
            }
            TermKind::Borrow { mutable, term } => self.borrow_expr(cx, t, *mutable, term)?,
            TermKind::Record { name, fields, .. } => self.record(cx, t, name, fields)?,
            TermKind::App {
                function,
                arguments,
            } => self.app(cx, t, function, arguments)?,
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                let ty = self.ety(t);
                let want = self.types.term(t).cloned().unwrap_or(TTy::Unit);
                let cond = self.expr_expect(cx, condition, &TTy::Bool)?;
                let then = self.branch(cx, then, &want)?;
                let otherwise = match otherwise {
                    Some(o) => Some(Box::new(self.branch(cx, o, &want)?)),
                    None => None,
                };
                expr_of(
                    ExprKind::If {
                        cond: Box::new(cond),
                        then: Box::new(then),
                        otherwise,
                    },
                    ty,
                    span,
                )
            }
            TermKind::Block(stmts) => {
                let ty = self.ety(t);
                let want = self.types.term(t).cloned().unwrap_or(TTy::Unit);
                let refs: Vec<&Stmt> = stmts.iter().collect();
                let b = self.block_of(cx, &refs, false, &want)?;
                // A tail that reads a borrow of a copy type is the value.
                let ty = match (&ty, &b.tail) {
                    (Ty::Ref(_), Some(t)) if !matches!(t.ty, Ty::Ref(_)) => t.ty.clone(),
                    _ => ty,
                };
                expr_of(ExprKind::Block(b), ty, span)
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => self.match_with(cx, t, scrutinee, arms, None)?,
            TermKind::Perform { effect, args } => self.perform(cx, t, effect, args)?,
            TermKind::Handle { body, handlers } => self.handle_expr(cx, t, body, handlers)?,
            TermKind::Budget { limit, steps, body } => {
                let ty = self.ety(t);
                let steps_e = self.expr(cx, steps)?;
                let steps_e = self.deref_if_ref(steps_e);
                let outer = std::mem::replace(&mut cx.under_budget, true);
                let want = self.types.term(t).cloned().unwrap_or(TTy::Unit);
                let body_e = self.expr_expect(cx, body, &want);
                cx.under_budget = outer;
                let id = self.next_budget;
                self.next_budget += 1;
                expr_of(
                    ExprKind::Budget(Box::new(BudgetNode {
                        id,
                        memory: *limit == tauto::surface::BudgetLimit::Memory,
                        steps: steps_e,
                        body: body_e?,
                        m: cx.tier == Tier::M,
                        span,
                    })),
                    ty,
                    span,
                )
            }
            TermKind::Field { base, name } => self.field_expr(cx, t, base, name)?,
            TermKind::Product(members) | TermKind::Tuple(members) => {
                self.product_expr(cx, t, members)?
            }
            TermKind::Ascribe { term: base, .. } => self.ascribe_expr(cx, t, base)?,
            TermKind::Tagged { term, .. } => self.expr(cx, term)?,
            other => {
                return unsupported(msg!("nir-the-term", other = format!("{:?}", other)), span);
            }
        })
    }

    /// A branch of an `if` or a `match`, made to fit the whole's type.
    pub fn branch(&mut self, cx: &mut Cx, t: &SurfaceTerm, want: &TTy) -> R<Expr> {
        self.expr_expect(cx, t, want)
    }

    fn check_budget_value(&self, cx: &Cx, b: &Binding, span: Span) -> R<()> {
        if cx.under_budget
            && !b.budgeted
            && b.fn_row
                .as_ref()
                .is_some_and(|row| row.iter().any(|e| e == "Div" || e.starts_with('|')))
        {
            return unsupported(
                msg!(
                    "nir-the-potentially-divergent-function-value-created",
                    b = b.name.to_string()
                ),
                span,
            );
        }
        Ok(())
    }

    fn var_expr(&mut self, cx: &mut Cx, t: &SurfaceTerm, name: &str) -> R<Expr> {
        let span = t.span;
        if let Some(i) = self.find(cx, name) {
            self.note_capture(cx, i);
            let b = cx.bindings[i].clone();
            self.check_budget_value(cx, &b, span)?;
            let ty = b.ty.clone();
            if b.celled {
                let how = if self.kind_of(&ty) == Kind::Copy {
                    Use::Copy
                } else {
                    Use::Clone
                };
                let nty = self.conv(&ty);
                return Ok(expr_of(
                    ExprKind::Read {
                        local: b.local,
                        how,
                    },
                    nty,
                    span,
                ));
            }
            return Ok(match &ty {
                TTy::Borrow(inner, _) => {
                    let inner_n = self.conv(inner);
                    // As a value, a borrow is what it borrows when that can be
                    // copied; otherwise it is the borrow itself.
                    match self.dup_use(&inner_n) {
                        Some(how) => expr_of(
                            ExprKind::Read {
                                local: b.local,
                                how,
                            },
                            inner_n,
                            span,
                        ),
                        None => {
                            let nty = self.conv(&ty);
                            expr_of(
                                ExprKind::Read {
                                    local: b.local,
                                    how: Use::Place,
                                },
                                nty,
                                span,
                            )
                        }
                    }
                }
                _ => {
                    let how = self.use_of(&ty);
                    let nty = self.conv(&ty);
                    expr_of(
                        ExprKind::Read {
                            local: b.local,
                            how,
                        },
                        nty,
                        span,
                    )
                }
            });
        }
        if self.fns.contains_key(name)
            && matches!(self.fns[name].origin, Origin::Program | Origin::Prelude)
        {
            if self.local_caps.get(name).is_some_and(|c| !c.is_empty()) {
                return self.capturing_fn_value(cx, t, name, false);
            }
            if cx.under_budget && self.fn_row(name).contains("Div") {
                return unsupported(
                    msg!(
                        "nir-the-divergent-named-function-used-as",
                        name = name.to_string()
                    ),
                    span,
                );
            }
            let decl = self.fns[name].decl;
            if !self.row_vars(decl)?.is_empty() {
                return unsupported(
                    msg!(
                        "nir-the-row-polymorphic-function-used-as",
                        name = name.to_string()
                    ),
                    span,
                );
            }
            let rv = BTreeMap::new();
            let inst = self.instance(name, rv, false, false, false)?;
            // Function values carry the callee's bounds just as calls do.
            let targs = self.type_args(cx, name, t.id(), inst);
            let mut ty = self.ety(t);
            // The value calls the item in the tier of the item's own row:
            // a checked type carries no row, so it says S.
            if let Ty::Fn(f) = &mut ty {
                f.tier = f.tier.max(self.row_tier_in(&self.fn_row(name), cx));
            }
            return Ok(expr_of(ExprKind::FnValue { inst, targs }, ty, span));
        }
        if let Some(ctor) = self.ctor_ref_in(name, self.types.term(t)) {
            self.refuse_extern_type(name);
            if ctor.nullary || (ctor.fields.is_empty() && matches!(ctor.data, DataRef::Gen(_))) {
                let ty = self.ety(t);
                return Ok(expr_of(
                    ExprKind::Ctor {
                        ctor,
                        fields: Vec::new(),
                    },
                    ty,
                    span,
                ));
            }
            return unsupported(
                msg!(
                    "nir-the-constructor-used-as-a-function",
                    name = name.to_string()
                ),
                span,
            );
        }
        unsupported(msg!("nir-the-name", name = name.to_string()), span)
    }

    /// A local function that captures, used as a value: a closure that
    /// calls it with what it captured. `borrowed`: it stands where a `&f`
    /// is expected, so it may borrow what the function uses; otherwise it
    /// owns copies of them, or shares the cell of a `var`.
    fn capturing_fn_value(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        name: &str,
        borrowed: bool,
    ) -> R<Expr> {
        let span = t.span;
        let caps = self.local_caps[name].clone();
        if caps.iter().any(|cap| cap.owned) {
            return unsupported(
                msg!("nir-the-local-function-used-as-a", name = name.to_string()),
                span,
            );
        }
        if !borrowed {
            // The closure owns what it captured, and the function may be
            // used again: a capture has to be copied or cloned into it, or
            // be a cell.
            for cap in &caps {
                let Some(i) = self.find_capture(cx, &cap.key) else {
                    continue;
                };
                let b = &cx.bindings[i];
                let nty = self.conv(b.ty.unborrowed());
                if cap.cell.is_none()
                    && (matches!(b.mode, Mode::Var | Mode::Borrow(_))
                        || !self.kind_of(b.ty.unborrowed()).dup()
                        || self.dup_use(&nty).is_none())
                {
                    return unsupported(
                        msg!(
                            "nir-the-local-function-used-as-a-2",
                            name = name.to_string(),
                            cap = cap.name.to_string()
                        ),
                        span,
                    );
                }
            }
        }
        let Some(fty) = self.types.term(t).cloned() else {
            return unsupported(
                msg!("nir-the-function-without-a-type", name = name.to_string()),
                span,
            );
        };
        let TTy::Fn(ps, ret, kind) = &fty else {
            return unsupported(
                msg!("nir-the-function-without-a-type", name = name.to_string()),
                span,
            );
        };
        let (ret, kind) = ((**ret).clone(), *kind);
        if ps.iter().any(|p| match p {
            TTy::Borrow(inner, _) => matches!(**inner, TTy::Fn(..)),
            _ => false,
        }) {
            return unsupported(
                msg!(
                    "nir-the-local-function-that-borrows-a",
                    name = name.to_string()
                ),
                span,
            );
        }
        let row = self.fn_row(name);
        let diverges = row.contains("Div");
        if diverges && cx.under_budget {
            return unsupported(
                msg!(
                    "nir-the-local-function-that-may-diverge",
                    name = name.to_string()
                ),
                span,
            );
        }
        if !self.row_vars(self.fns[name].decl)?.is_empty() {
            return unsupported(
                msg!(
                    "nir-the-row-polymorphic-function-used-as",
                    name = name.to_string()
                ),
                span,
            );
        }
        let rv: BTreeMap<String, Tier> = BTreeMap::new();
        let rv_map: HashMap<String, Tier> = rv.iter().map(|(k, v)| (k.clone(), *v)).collect();
        let tier = self.row_tier(&row, &rv_map);
        // A state machine holds what it captured across suspensions, but the
        // function takes it by reference.
        if tier == Tier::M || cx.tier == Tier::M {
            return unsupported(
                msg!(
                    "nir-the-local-function-that-may-resume",
                    name = name.to_string()
                ),
                span,
            );
        }
        let inst = self.instance(name, rv, false, false, false)?;
        let capture_mark = cx.capture_bindings.len();
        let refs = if tier == Tier::O && borrowed {
            let used = caps
                .iter()
                .filter_map(|cap| {
                    self.find_capture(cx, &cap.key)
                        .map(|i| (Some(cap.key.clone()), i))
                })
                .collect();
            self.borrow_refs(cx, used, span)?
        } else {
            Vec::new()
        };
        let mark = cx.bindings.len();
        cx.frames.push(CFrame {
            base: mark,
            captures: Vec::new(),
        });
        let outer_ret = std::mem::replace(&mut cx.ret, ret.clone());
        let outer_tier = std::mem::replace(&mut cx.tier, tier);
        let outer_host = std::mem::replace(&mut cx.host_m, false);
        let built = (|| {
            let mut nparams = Vec::new();
            let mut args = self.capture_args(cx, name, span)?;
            // Resolve captures before the wrapper's synthetic argument names
            // enter scope: a source capture can itself be named `a0`.
            let targs = self.type_args(cx, name, t.id(), inst);
            for (i, pty) in ps.iter().enumerate() {
                let (local, nty) = self.bind_param(cx, &format!("a{i}"), pty, None);
                args.push(match pty {
                    TTy::Borrow(inner, mutable) => {
                        let ity = self.conv(inner);
                        let p = Place {
                            local: local.clone(),
                            path: Vec::new(),
                            ty: ity.clone(),
                        };
                        if *mutable {
                            expr_of(ExprKind::RefMut(p), Ty::RefMut(Box::new(ity)), span)
                        } else {
                            expr_of(ExprKind::Ref(p), Ty::Ref(Box::new(ity)), span)
                        }
                    }
                    _ => expr_of(
                        ExprKind::Read {
                            local: local.clone(),
                            how: self.use_of(pty),
                        },
                        nty.clone(),
                        span,
                    ),
                });
                nparams.push((local, nty));
            }
            let call = expr_of(
                ExprKind::Call(Box::new(CallNode {
                    callee: Callee::Inst(inst),
                    args,
                    tier,
                    targs,
                    tick: if diverges { Tick::Host } else { Tick::None },
                    recur: false,
                    span,
                })),
                self.conv(&ret),
                span,
            );
            Ok::<_, Unsupported>((nparams, call))
        })();
        cx.bindings.truncate(mark - refs.len());
        cx.capture_bindings.truncate(capture_mark);
        cx.ret = outer_ret;
        cx.tier = outer_tier;
        cx.host_m = outer_host;
        let frame = cx.frames.pop().expect("a frame");
        let (nparams, call) = built?;
        self.seal_closure(
            cx,
            ClosureParts {
                params: nparams,
                ret: &ret,
                body: call,
                kind,
                tier,
                borrowed,
                refs,
                captures: frame.captures,
            },
            span,
        )
    }

    pub(crate) fn borrow_expr(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        mutable: bool,
        term: &SurfaceTerm,
    ) -> R<Expr> {
        let span = t.span;
        if let Some(p) = self.place(cx, term)? {
            let ty = p.ty.clone();
            return Ok(if mutable {
                expr_of(ExprKind::RefMut(p), Ty::RefMut(Box::new(ty)), span)
            } else {
                expr_of(ExprKind::Ref(p), Ty::Ref(Box::new(ty)), span)
            });
        }
        let inner = self.expr(cx, term)?;
        let ty = inner.ty.clone();
        Ok(expr_of(
            ExprKind::TempRef(Box::new(inner)),
            if mutable {
                Ty::RefMut(Box::new(ty))
            } else {
                Ty::Ref(Box::new(ty))
            },
            span,
        ))
    }

    /// A name, or a field of one, as a place.
    pub fn place(&mut self, cx: &mut Cx, t: &SurfaceTerm) -> R<Option<Place>> {
        match &*t.kind {
            TermKind::Var(n) => {
                let Some(i) = self.find(cx, n) else {
                    return Ok(None);
                };
                self.note_capture(cx, i);
                let b = cx.bindings[i].clone();
                self.check_budget_value(cx, &b, t.span)?;
                if b.celled {
                    return Ok(None);
                }
                let mut ty = self.conv(b.ty.unborrowed());
                // A function whose type is written is held at the tier its
                // row gives, which a checked type does not say.
                if let Some(w) = cx.written.get(&b.local.id) {
                    set_written_tiers(&mut ty, w, &mut |row| self.row_tier_in(row, cx));
                } else if let Some(held) = cx.held.get(&b.local.id) {
                    // A closure is held at the tier its body gave it, which
                    // a checked type does not say either.
                    ty = held.clone();
                }
                Ok(Some(Place {
                    local: b.local,
                    path: Vec::new(),
                    ty,
                }))
            }
            TermKind::Field { base, name } => {
                let Some(mut p) = self.place(cx, base)? else {
                    return Ok(None);
                };
                let index = self.pair_index(base, name);
                let mut ty = match self.types.term(t) {
                    Some(ty) => {
                        let ty = ty.unborrowed().clone();
                        self.conv(&ty)
                    }
                    None => Ty::Infer,
                };
                if let Some(tier) = self
                    .types
                    .term(base)
                    .and_then(|b| self.named_field_tier(b, name))
                {
                    set_fn_tier(&mut ty, tier);
                }
                p.path.push(FieldRef {
                    name: name.clone(),
                    index,
                    indirect: self.field_indirect(base, name),
                });
                p.ty = ty;
                Ok(Some(p))
            }
            _ => Ok(None),
        }
    }

    fn pair_index(&self, base: &SurfaceTerm, field: &str) -> Option<usize> {
        match self.types.term(base).map(|t| t.unborrowed()) {
            Some(TTy::Named(n, _)) if n == "Pair" && !self.program_declares("Pair") => {
                match field {
                    "fst" => Some(0),
                    "snd" => Some(1),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn field_expr(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        base: &SurfaceTerm,
        name: &str,
    ) -> R<Expr> {
        let span = t.span;
        if let Some(TTy::Info(_)) = self.types.term(base).map(|t| t.unborrowed()) {
            return unsupported(msg!("nir-info-field", name = name.to_string()), span);
        }
        let result = self.types.term(t).cloned().unwrap_or(TTy::Var(0));
        let how = self.use_of(&result);
        let mut nty = self.conv(&result);
        if let Some(tier) = self
            .types
            .term(base)
            .and_then(|b| self.named_field_tier(b, name))
        {
            set_fn_tier(&mut nty, tier);
        }
        let index = self.pair_index(base, name);
        let indirect = self.field_indirect(base, name);
        let base_e = match self.place_read(cx, base)? {
            Some(e) => e,
            None => self.expr(cx, base)?,
        };
        Ok(expr_of(
            ExprKind::Field {
                base: Box::new(base_e),
                field: FieldRef {
                    name: name.to_string(),
                    index,
                    indirect,
                },
                how: if matches!(how, Use::Move) && matches!(result, TTy::Borrow(..)) {
                    Use::Place
                } else {
                    how
                },
                indirect,
            },
            nty,
            span,
        ))
    }

    /// A product taken to fewer members (`A × B <: A`), as `types.rs`
    /// fitted it: the members are told apart by their checked types.
    fn fit_product(&mut self, e: Expr, have: &[TTy], expected: &TTy) -> Expr {
        let span = e.span;
        let keys: Vec<String> = have.iter().map(|t| t.to_string()).collect();
        let at = |t: &TTy| keys.iter().position(|k| *k == t.to_string());
        match expected {
            TTy::Product(want) if want != have => {
                let Some(picks) = want
                    .iter()
                    .map(|w| at(w).map(|i| (0, Some(i))))
                    .collect::<Option<Vec<_>>>()
                else {
                    return e;
                };
                let ty = self.conv(expected);
                expr_of(
                    ExprKind::Product {
                        members: vec![e],
                        picks,
                    },
                    ty,
                    span,
                )
            }
            TTy::Product(_) | TTy::Var(_) | TTy::Borrow(..) | TTy::Union(_) => e,
            want => match at(want) {
                Some(index) => {
                    let ty = self.conv(want);
                    expr_of(
                        ExprKind::Member {
                            value: Box::new(e),
                            index,
                            how: Use::Move,
                        },
                        ty,
                        span,
                    )
                }
                None => e,
            },
        }
    }

    /// `a × b × …`: the members in the order written, put in the order of
    /// the product's type; a member that is a product gives its members.
    fn product_expr(&mut self, cx: &mut Cx, t: &SurfaceTerm, members: &[SurfaceTerm]) -> R<Expr> {
        let span = t.span;
        let whole = self.types.term(t).cloned().unwrap_or(TTy::Var(0));
        let TTy::Product(order) = whole.unborrowed().clone() else {
            return unsupported(msg!("nir-a-product-with-fewer-than-two"), span);
        };
        let keys: Vec<String> = order.iter().map(|t| t.to_string()).collect();
        let at = |t: &TTy| keys.iter().position(|k| *k == t.to_string());
        let mut picks: Vec<Option<(usize, Option<usize>)>> = vec![None; keys.len()];
        let mut exprs = Vec::new();
        for (i, m) in members.iter().enumerate() {
            let mt = self
                .types
                .term(m)
                .map(|t| t.unborrowed().clone())
                .unwrap_or(TTy::Var(0));
            let e = self.expr_expect(cx, m, &mt)?;
            match &mt {
                TTy::Product(inner) => {
                    for (j, x) in inner.iter().enumerate() {
                        if let Some(k) = at(x) {
                            picks[k] = Some((i, Some(j)));
                        }
                    }
                }
                TTy::Unit => {}
                x => {
                    if let Some(k) = at(x) {
                        picks[k] = Some((i, None));
                    }
                }
            }
            exprs.push(e);
        }
        let Some(picks) = picks.into_iter().collect::<Option<Vec<_>>>() else {
            return unsupported(msg!("nir-a-product-whose-members-do-not"), span);
        };
        let ty = self.conv(&whole);
        Ok(expr_of(
            ExprKind::Product {
                members: exprs,
                picks,
            },
            ty,
            span,
        ))
    }

    /// `(base: T)`. The member of type `T` of a product is copied or cloned
    /// out of a place, moved out of a temporary; fewer members (`A × C`) are
    /// taken as [`Self::fit_product`] takes them; anything else fits `T` as an
    /// argument does.
    fn ascribe_expr(&mut self, cx: &mut Cx, t: &SurfaceTerm, base: &SurfaceTerm) -> R<Expr> {
        let span = t.span;
        let result = self.types.term(t).cloned().unwrap_or(TTy::Var(0));
        let key = result.unborrowed().to_string();
        let index = match (
            self.types.term(base).map(|b| b.unborrowed()),
            result.unborrowed(),
        ) {
            (Some(TTy::Product(ms)), want)
                if !matches!(want, TTy::Product(_) | TTy::Union(_) | TTy::Var(_)) =>
            {
                ms.iter().position(|m| m.to_string() == key)
            }
            _ => return self.expr_expect(cx, base, &result),
        };
        let Some(index) = index else {
            return unsupported(
                msg!("nir-the-member-of-a-product", key = key.to_string()),
                span,
            );
        };
        let nty = self.conv(result.unborrowed());
        let (value, how) = match self.place_read(cx, base)? {
            Some(e) => (e, self.use_of(&result)),
            None => (self.expr(cx, base)?, Use::Move),
        };
        Ok(expr_of(
            ExprKind::Member {
                value: Box::new(value),
                index,
                how,
            },
            nty,
            span,
        ))
    }

    /// A place read keeps the checked type of its root and every projection.
    /// Intermediate fields are places, not owned reads of the containing value.
    fn place_read(&mut self, cx: &mut Cx, t: &SurfaceTerm) -> R<Option<Expr>> {
        let kind = match &*t.kind {
            TermKind::Var(_) => {
                let Some(p) = self.place(cx, t)? else {
                    return Ok(None);
                };
                return Ok(Some(expr_of(
                    ExprKind::Read {
                        local: p.local,
                        how: Use::Place,
                    },
                    p.ty,
                    t.span,
                )));
            }
            TermKind::Field { base, name } => {
                let Some(base_e) = self.place_read(cx, base)? else {
                    return Ok(None);
                };
                ExprKind::Field {
                    base: Box::new(base_e),
                    field: FieldRef {
                        name: name.clone(),
                        index: self.pair_index(base, name),
                        indirect: Indirect::None,
                    },
                    how: Use::Place,
                    indirect: Indirect::None,
                }
            }
            _ => return Ok(None),
        };
        let ty = match self.types.term(t) {
            Some(ty) => {
                let ty = ty.unborrowed().clone();
                self.conv(&ty)
            }
            None => Ty::Infer,
        };
        Ok(Some(expr_of(kind, ty, t.span)))
    }

    fn field_indirect(&self, base: &SurfaceTerm, field: &str) -> Indirect {
        let Some(TTy::Named(n, _)) = self.types.term(base).map(|t| t.unborrowed()) else {
            return Indirect::None;
        };
        let Some(ix) = self.data_index.get(n) else {
            return Indirect::None;
        };
        self.datas[*ix]
            .ctors
            .first()
            .and_then(|c| c.fields.iter().find(|f| f.name.as_deref() == Some(field)))
            .map(|f| f.indirect)
            .unwrap_or(Indirect::None)
    }

    fn record(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        name: &str,
        fields: &[(String, SurfaceTerm)],
    ) -> R<Expr> {
        let span = t.span;
        let Some(ctor) = self.ctor_ref_in(name, self.types.term(t)) else {
            return unsupported(msg!("nir-is-not-a-struct", name = name.to_string()), span);
        };
        self.refuse_extern_type(name);
        let ty_t = self.types.term(t).cloned().unwrap_or(TTy::Var(0));
        let ty = self.conv(&ty_t);
        let ftys = self.ctor_fields(name, &ty_t);
        let rows = self.ctor_field_rows(name, &ty_t);
        let mut out = Vec::new();
        for (f, v) in fields {
            let Some(ix) = ctor
                .fields
                .iter()
                .position(|n| n.as_deref() == Some(f.as_str()))
            else {
                return unsupported(
                    msg!(
                        "nir-has-no-field",
                        name = name.to_string(),
                        f = f.to_string()
                    ),
                    span,
                );
            };
            let want = ftys.get(ix).cloned().unwrap_or(TTy::Var(0));
            let e = self.field_arg(cx, v, &want, rows.get(ix).cloned().flatten())?;
            out.push((Some(f.clone()), e));
        }
        Ok(expr_of(ExprKind::Ctor { ctor, fields: out }, ty, span))
    }

    // ---- calls ---------------------------------------------------------

    fn app(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        function: &SurfaceTerm,
        arguments: &[SurfaceTerm],
    ) -> R<Expr> {
        let span = t.span;
        if let TermKind::Var(name) = &*function.kind {
            if self.find(cx, name).is_none() {
                if name == "Tuple" && arguments.is_empty() {
                    return Ok(expr_of(ExprKind::Unit, Ty::Unit, span));
                }
                if OPERATORS.contains(&name.as_str()) {
                    return self.operator(cx, t, name, arguments);
                }
                if let Some(ctor) = self.ctor_ref_in(name, self.types.term(t)) {
                    return self.construct(cx, t, ctor, name, arguments, None);
                }
                if let Some(src) = self.fns.get(name.as_str()) {
                    let origin = src.origin;
                    return match origin {
                        Origin::Program | Origin::Prelude => {
                            self.call_global(cx, t, name, function, arguments)
                        }
                        Origin::Builtin => self.call_builtin(cx, t, name, function, arguments),
                        Origin::Extern => self.call_builtin(cx, t, name, function, arguments),
                    };
                }
                if matches!(name.as_str(), "div" | "mod" | "clone") {
                    return self.call_builtin(cx, t, name, function, arguments);
                }
                return unsupported(msg!("nir-the-name", name = name.to_string()), span);
            }
            return self.call_local(cx, t, name, function, arguments);
        }
        if let TermKind::Field { base, name } = &*function.kind
            && matches!(name.as_str(), "more" | "unbounded")
            && let Some(TTy::Info(_)) = self.types.term(base).map(|t| t.unborrowed())
        {
            return self.info_call(cx, t, base, name, arguments);
        }
        // Computed values do not retain a callback's budget specialization.
        if cx.under_budget
            && self
                .term_row(t)
                .iter()
                .any(|e| e == "Div" || e.starts_with('|'))
        {
            return unsupported(
                msg!("nir-a-potentially-divergent-computed-function-call"),
                span,
            );
        }
        // A computed function value, called.
        self.detached_direct(cx, t, msg!("nir-direct-function-value"));
        let callee = self.expr(cx, function)?;
        let (ps, ret) = match self.types.term(function).map(|t| t.unborrowed().clone()) {
            Some(TTy::Fn(ps, r, _)) => (ps, *r),
            _ => return unsupported(msg!("nir-a-call-of-a-value-that"), span),
        };
        let args = self.call_args(cx, arguments, &ps, None, &HashMap::new())?;
        let ty = self.conv(&ret);
        let tier = match &callee.ty {
            Ty::Fn(f) => f.tier,
            _ => Tier::S,
        };
        Ok(expr_of(
            ExprKind::Call(Box::new(CallNode {
                callee: Callee::Value(Box::new(callee)),
                args,
                tier,
                targs: Vec::new(),
                tick: Tick::None,
                recur: false,
                span,
            })),
            ty,
            span,
        ))
    }

    /// `info.more(m)` and `info.unbounded()` in an `exceeded` arm: `k` with
    /// the answer.
    fn info_call(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        base: &SurfaceTerm,
        name: &str,
        arguments: &[SurfaceTerm],
    ) -> R<Expr> {
        let span = t.span;
        let Some(ki) = cx.bindings.iter().rposition(|b| b.mode == Mode::ContBudget) else {
            return unsupported(
                msg!("nir-info-outside-an-exceeded-arm", name = name.to_string()),
                span,
            );
        };
        let kb = cx.bindings[ki].clone();
        self.note_capture(cx, ki);
        let Some(TTy::Fn(kps, kret, _)) = Some(kb.ty.clone()) else {
            return unsupported(msg!("nir-an-exceeded-arm-without-k"), span);
        };
        let budget_ty = self.conv(kps.first().unwrap_or(&TTy::Unit));
        let info = self.expr(cx, base)?;
        let mut args = vec![info];
        for a in arguments {
            let e = self.expr(cx, a)?;
            args.push(self.deref_if_ref(e));
        }
        let answer = expr_of(
            ExprKind::Call(Box::new(CallNode {
                callee: Callee::Builtin(format!("info_{name}")),
                args,
                tier: Tier::S,
                targs: Vec::new(),
                tick: Tick::None,
                recur: false,
                span,
            })),
            Ty::BudgetAnswer(Box::new(budget_ty)),
            span,
        );
        let ty = self.conv(&kret);
        Ok(expr_of(
            ExprKind::Call(Box::new(CallNode {
                callee: Callee::Cont(kb.local),
                args: vec![answer],
                tier: Tier::O,
                targs: Vec::new(),
                tick: Tick::None,
                recur: false,
                span,
            })),
            ty,
            span,
        ))
    }

    fn operator(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        op: &str,
        arguments: &[SurfaceTerm],
    ) -> R<Expr> {
        let span = t.span;
        let ty = self.ety(t);
        if op == "&&" || op == "||" {
            let [a, b] = arguments else {
                return unsupported(
                    msg!(
                        "nir-with-operands",
                        op = op.to_string(),
                        arguments = arguments.len().to_string()
                    ),
                    span,
                );
            };
            let a = self.operand(cx, a)?;
            let b = self.operand(cx, b)?;
            let (a, b) = (Box::new(a), Box::new(b));
            return Ok(expr_of(
                if op == "&&" {
                    ExprKind::And(a, b)
                } else {
                    ExprKind::Or(a, b)
                },
                Ty::Bool,
                span,
            ));
        }
        let mut args = Vec::new();
        for a in arguments {
            args.push(self.operand(cx, a)?);
        }
        let width = self
            .types
            .widths
            .get(&t.id())
            .copied()
            .unwrap_or(Width::W64);
        let kind = match (op, args.len()) {
            ("+", 1) => return Ok(args.remove(0)),
            ("-", 1) => ExprKind::Arith {
                op: Arith::Neg,
                args,
                width,
            },
            ("+", 2) => ExprKind::Arith {
                op: Arith::Add,
                args,
                width,
            },
            ("-", 2) => ExprKind::Arith {
                op: Arith::Sub,
                args,
                width,
            },
            ("*", 2) => ExprKind::Arith {
                op: Arith::Mul,
                args,
                width,
            },
            ("/", 2) if matches!(args[0].ty, Ty::Float | Ty::Float32) => ExprKind::Arith {
                op: Arith::Div,
                args,
                width,
            },
            ("<", 2) => ExprKind::Cmp { op: Cmp::Lt, args },
            (">", 2) => ExprKind::Cmp { op: Cmp::Gt, args },
            ("<=", 2) => ExprKind::Cmp { op: Cmp::Le, args },
            (">=", 2) => ExprKind::Cmp { op: Cmp::Ge, args },
            ("==" | "!=", 2) => {
                let ty = args[0].ty.clone();
                self.need(cx, &ty, Bound::Eq);
                ExprKind::Eq {
                    negate: op == "!=",
                    args,
                }
            }
            _ => {
                return unsupported(
                    msg!(
                        "nir-the-operator-on-operands",
                        op = op.to_string(),
                        args = args.len().to_string()
                    ),
                    span,
                );
            }
        };
        Ok(expr_of(kind, ty, span))
    }

    /// An operand: a borrow of a duplicable value stands for the value.
    fn operand(&mut self, cx: &mut Cx, t: &SurfaceTerm) -> R<Expr> {
        let e = self.expr(cx, t)?;
        Ok(self.deref_if_ref(e))
    }

    pub fn deref_if_ref(&mut self, e: Expr) -> Expr {
        if let Ty::Ref(x) = &e.ty {
            let inner = (**x).clone();
            if let Some(how) = self.dup_use(&inner) {
                let span = e.span;
                return expr_of(
                    ExprKind::Deref {
                        value: Box::new(e),
                        how,
                    },
                    inner,
                    span,
                );
            }
        }
        e
    }

    fn construct(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        ctor: CtorRef,
        name: &str,
        arguments: &[SurfaceTerm],
        written: Option<&SurfaceTerm>,
    ) -> R<Expr> {
        let span = t.span;
        self.refuse_extern_type(name);
        let ty_t = self.types.term(t).cloned().unwrap_or(TTy::Var(0));
        let mut ty = self.conv(&ty_t);
        if let Some(w) = written {
            set_written_tiers_in_args(&mut ty, w, &mut |row| self.field_tier(row));
        }
        let ftys = self.ctor_fields(name, &ty_t);
        let rows = self.ctor_field_rows(name, &ty_t);
        let wfs = self.written_fields(name, &ty_t, written);
        let mut fields = Vec::new();
        for (i, a) in arguments.iter().enumerate() {
            let want = ftys.get(i).cloned().unwrap_or(TTy::Var(0));
            let wf = wfs.get(i).cloned().flatten();
            let row = rows.get(i).cloned().flatten().or_else(|| {
                wf.as_ref()
                    .and_then(pi_effects)
                    .map(|e| e.into_iter().collect())
            });
            let e = match (row, &wf) {
                (None, Some(wf)) => self.expr_written(cx, a, &want, wf)?,
                (row, _) => self.field_arg(cx, a, &want, row)?,
            };
            fields.push((None, e));
        }
        Ok(expr_of(ExprKind::Ctor { ctor, fields }, ty, span))
    }

    /// A value wanted at a type the program writes: a constructor
    /// application (a list literal) makes the functions it holds for the
    /// tiers the rows written in the type arguments give.
    pub(crate) fn expr_written(
        &mut self,
        cx: &mut Cx,
        a: &SurfaceTerm,
        want: &TTy,
        written: &SurfaceTerm,
    ) -> R<Expr> {
        if let TermKind::App {
            function,
            arguments,
        } = &*a.kind
            && let TermKind::Var(name) = &*function.kind
            && self.find(cx, name).is_none()
            && let Some(ctor) = self.ctor_ref_in(name, self.types.term(a))
        {
            return self.construct(cx, a, ctor, name, arguments, Some(written));
        }
        self.expr_expect(cx, a, want)
    }

    /// The value of a field. A function written with a row is made for the
    /// tier that row gives, whatever its own body performs; one that may
    /// suspend is taken only as a closure literal, which the field holds
    /// for any handlers it is called under.
    fn field_arg(&mut self, cx: &mut Cx, a: &SurfaceTerm, want: &TTy, row: Option<Row>) -> R<Expr> {
        let Some(row) = row else {
            return self.expr_expect(cx, a, want);
        };
        let tier = self.field_tier(&row);
        let mut to = self.conv(want);
        set_fn_tier(&mut to, tier);
        if matches!(&*a.kind, TermKind::Lam { .. }) {
            let e = self.closure(cx, a, Some(tier), false, None)?;
            return Ok(self.coerce(e, &to));
        }
        if tier == Tier::O {
            return unsupported(msg!("nir-a-field-whose-function-may-suspend"), a.span);
        }
        let e = self.expr(cx, a)?;
        Ok(self.coerce(e, &to))
    }

    /// The tiers a call gives the callee's row variables.
    fn call_rowvars(
        &self,
        cx: &Cx,
        decl: &FnDecl,
        call: &SurfaceTerm,
        arguments: &[SurfaceTerm],
    ) -> R<BTreeMap<String, Tier>> {
        let mut out = BTreeMap::new();
        let assumed = super::assumed_row_vars(decl);
        for v in self.row_vars(decl)? {
            let mut tier = Tier::S;
            // The row checker instantiates it with the empty row.
            if assumed.contains(&v) {
                out.insert(v, tier);
                continue;
            }
            for (pt, arg) in decl.param_types.iter().zip(arguments) {
                let Some(pt) = pt else { continue };
                let Some(effects) = pi_effects(pt) else {
                    continue;
                };
                if !effects
                    .iter()
                    .any(|e| e.strip_prefix('|') == Some(v.as_str()))
                {
                    continue;
                }
                let named: Vec<&String> = effects.iter().filter(|e| !e.starts_with('|')).collect();
                let row: Row = self
                    .known_arg_row(cx, arg)?
                    .ok_or_else(|| Unsupported {
                        what: msg!(
                            "nir-callback-row-needed",
                            var = v.to_string(),
                            decl = decl.name.as_str()
                        )
                        .to_string(),
                        span: Some(arg.span),
                    })?
                    .into_iter()
                    .filter(|e| !named.contains(&e))
                    .collect();
                tier = tier.max(self.row_tier_in(&row, cx));
            }
            if !decl.param_types.iter().flatten().any(|pt| {
                pi_effects(pt).is_some_and(|effects| {
                    effects
                        .iter()
                        .any(|e| e.strip_prefix('|') == Some(v.as_str()))
                })
            }) {
                tier = tier.max(self.call_row_tier(cx, decl, call, &v)?);
            }
            out.insert(v, tier);
        }
        Ok(out)
    }

    /// The tier of a row variable that no callback parameter carries, from
    /// the callee's row as this call instantiates it. The named effects of
    /// the callee's row are counted in its own tier already.
    fn call_row_tier(&self, cx: &Cx, decl: &FnDecl, call: &SurfaceTerm, v: &str) -> R<Tier> {
        let row = self.rows.calls.get(&call.id()).ok_or_else(|| Unsupported {
            what: msg!(
                "nir-instantiated-row-needed",
                var = v.to_string(),
                decl = decl.name.as_str()
            )
            .to_string(),
            span: Some(call.span),
        })?;
        let named: Vec<&String> = decl
            .effects
            .iter()
            .flatten()
            .filter(|e| !e.starts_with('|'))
            .collect();
        let row: Row = row.iter().filter(|e| !named.contains(e)).cloned().collect();
        let tier = self.row_tier_in(&row, cx);
        if tier > Tier::S && tier < Tier::M {
            // The records that carry `v` hold their functions at this tier,
            // in the next lowering if not in this one (`lower`).
            let datas = self.datas_carrying(decl, v);
            if !datas.is_empty() {
                let mut wanted = self.carried_wanted.borrow_mut();
                for d in &datas {
                    let at = wanted.entry(d.clone()).or_insert(tier);
                    *at = (*at).max(tier);
                }
                return Ok(tier);
            }
        }
        if tier > Tier::S {
            self.rust_unsupported
                .borrow_mut()
                .get_or_insert_with(|| Unsupported {
                    what: msg!(
                        "nir-row-variable-carried-suspending",
                        var = v.to_string(),
                        decl = decl.name.as_str()
                    )
                    .to_string(),
                    span: Some(call.span),
                });
        }
        Ok(tier)
    }

    /// The data types in `decl`'s parameter types that `v` is an argument
    /// of, and whose fields hold a function with a row variable.
    fn datas_carrying(&self, decl: &FnDecl, v: &str) -> Vec<String> {
        fn mentions(t: &SurfaceTerm, v: &str) -> bool {
            let mut found = false;
            visit(t, &mut |t| match &*t.kind {
                TermKind::Var(n) if n == v => found = true,
                TermKind::Pi {
                    effects: Some(effects),
                    ..
                } if effects.iter().any(|e| e.strip_prefix('|') == Some(v)) => found = true,
                _ => {}
            });
            found
        }
        fn visit(t: &SurfaceTerm, f: &mut dyn FnMut(&SurfaceTerm)) {
            f(t);
            match &*t.kind {
                TermKind::Pi { params, result, .. } => {
                    for (_, p) in params {
                        visit(p, f);
                    }
                    visit(result, f);
                }
                TermKind::Borrow { term, .. }
                | TermKind::Tagged { term, .. }
                | TermKind::FnKind { ty: term, .. } => visit(term, f),
                TermKind::App {
                    function,
                    arguments,
                } => {
                    visit(function, f);
                    for a in arguments {
                        visit(a, f);
                    }
                }
                TermKind::Union(ts) => {
                    for t in ts {
                        visit(t, f);
                    }
                }
                _ => {}
            }
        }
        // Each data type applied to `v`, with the row parameters `v` is given
        // as: a record of records, `App(R, e)` with `List(Answer(e))`, carries
        // `v` on to the data types its fields apply to those parameters.
        let mut seen: Vec<String> = Vec::new();
        let mut todo: Vec<(&SurfaceTerm, String)> = decl
            .param_types
            .iter()
            .flatten()
            .map(|pt| (pt, v.to_string()))
            .collect();
        while let Some((t, v)) = todo.pop() {
            visit(t, &mut |t| {
                if let TermKind::App {
                    function,
                    arguments,
                } = &*t.kind
                    && let TermKind::Var(name) = &*function.kind
                    && !seen.contains(name)
                    && let Some(d) = self.data_decl(name)
                {
                    let params: Vec<&String> = d
                        .generics
                        .iter()
                        .zip(&d.rows)
                        .zip(arguments)
                        .filter(|((_, row), a)| **row && mentions(a, &v))
                        .map(|((g, _), _)| g)
                        .collect();
                    if params.is_empty() {
                        return;
                    }
                    seen.push(name.clone());
                    for c in &d.constructors {
                        for (_, ft) in &c.fields {
                            for p in &params {
                                todo.push((ft, (*p).clone()));
                            }
                        }
                    }
                }
            });
        }
        seen.retain(|name| self.holds_row_function(name));
        seen
    }

    fn data_decl(&self, name: &str) -> Option<&'a DataDecl> {
        self.program.stmts.iter().find_map(|s| match s {
            Stmt::Struct(d) | Stmt::Enum(d) if d.name == name => Some(d),
            _ => None,
        })
    }

    /// Whether a field of the data type `name` holds a function whose row
    /// has a row variable.
    fn holds_row_function(&self, name: &str) -> bool {
        self.program.stmts.iter().any(|s| match s {
            Stmt::Struct(d) | Stmt::Enum(d) if d.name == name => d.constructors.iter().any(|c| {
                c.fields.iter().any(|(_, t)| {
                    pi_effects(t).is_some_and(|e| e.iter().any(|e| e.starts_with('|')))
                })
            }),
            _ => false,
        })
    }

    /// Only proved callback rows may bind a specialization. An expression
    /// whose latent row is unavailable is not evidence for an empty row.
    fn known_arg_row(&self, cx: &Cx, arg: &SurfaceTerm) -> R<Option<Row>> {
        Ok(match &*arg.kind {
            TermKind::Lam { body, .. } => Some(self.term_row(body)),
            TermKind::BorrowLam { lam, .. } => self.known_arg_row(cx, lam)?,
            TermKind::Borrow { term, .. } => self.known_arg_row(cx, term)?,
            TermKind::Var(name) => match self.find(cx, name) {
                Some(i) => cx.bindings[i].fn_row.clone(),
                None => match self.fns.get(name) {
                    Some(function) if self.row_vars(function.decl)?.is_empty() => {
                        Some(self.fn_row(name))
                    }
                    _ => None,
                },
            },
            _ => None,
        })
    }

    /// What calling the function value `arg` performs.
    fn arg_row(&self, cx: &Cx, arg: &SurfaceTerm) -> Row {
        match &*arg.kind {
            TermKind::Lam { body, .. } => self.term_row(body),
            TermKind::BorrowLam { lam, .. } => self.arg_row(cx, lam),
            TermKind::Borrow { term, .. } => self.arg_row(cx, term),
            TermKind::Var(n) => match self.find(cx, n) {
                Some(i) => cx.bindings[i].fn_row.clone().unwrap_or_default(),
                None if self.fns.contains_key(n.as_str()) => self.fn_row(n),
                None => Row::new(),
            },
            _ => Row::new(),
        }
    }

    fn call_global(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        name: &str,
        function: &SurfaceTerm,
        arguments: &[SurfaceTerm],
    ) -> R<Expr> {
        let span = t.span;
        let decl: &'a FnDecl = self.fns[name].decl;
        let rv = self.call_rowvars(cx, decl, t, arguments)?;
        // A function that runs a budget ticks, as one that diverges does.
        let diverges = self.fn_row(name).contains("Div") || self.runs_budget(name);
        // The callback row can carry divergence through a row variable.
        // Keep the budget specialization while forwarding such callbacks.
        let div_parameter = decl.param_types.iter().flatten().any(|ty| {
            pi_effects(ty).is_some_and(|effects| effects.iter().any(|effect| effect == "Div"))
        });
        let callback_o = div_parameter || rv.values().any(|tier| *tier >= Tier::O);
        let rv_map: HashMap<String, Tier> = rv.iter().map(|(k, v)| (k.clone(), *v)).collect();
        let mut tier = self.row_tier(&self.fn_row(name), &rv_map);
        if cx.under_budget && callback_o && !diverges && tier < Tier::O {
            return unsupported(
                msg!("nir-a-callback-budget-specialization-absent-from"),
                span,
            );
        }
        let under = cx.under_budget && (diverges || callback_o);
        // In code of the M tier a function that suspends is written in
        // continuation-passing style, too.
        // Under a budget, the steps are counted among the handlers in place.
        let m = cx.tier == Tier::M && (tier >= Tier::O || under);
        // A function that performs a `direct` operation, called where no
        // `direct` handler is held: its instance holds none either.
        let detached = cx.detached && self.has_direct(&self.term_row(t));
        let m = m && !detached;
        let inst = self.instance(name, rv.clone(), under, m, detached)?;
        if m || detached {
            tier = Tier::M;
        }
        if under {
            tier = tier.max(Tier::O);
        }
        let fty = self.types.term(function).cloned();
        let ps = match &fty {
            Some(TTy::Fn(ps, _, _)) => ps.clone(),
            _ => Vec::new(),
        };
        let mut args = self.capture_args(cx, name, span)?;
        let borrowed: Vec<_> = args
            .iter()
            .filter_map(|arg| match &arg.kind {
                ExprKind::Ref(p) | ExprKind::RefMut(p) if p.local.repr == Repr::Plain => {
                    Some(p.local.id)
                }
                _ => None,
            })
            .collect();
        let mut explicit = self.call_args(cx, arguments, &ps, Some(decl), &rv_map)?;
        if !borrowed.is_empty() {
            for arg in &mut explicit {
                keep_capture_clones(arg, &borrowed);
            }
        }
        args.extend(explicit);
        let ty = self.ety(t);
        let targs = self.type_args(cx, name, function.id(), inst);
        let tick = match (diverges, under) {
            (false, _) => Tick::None,
            (true, true) => Tick::Budget,
            (true, false) => Tick::Host,
        };
        Ok(expr_of(
            ExprKind::Call(Box::new(CallNode {
                callee: Callee::Inst(inst),
                args,
                tier,
                targs,
                tick,
                recur: false,
                span,
            })),
            ty,
            span,
        ))
    }

    /// The checked type arguments of this exact function occurrence, and
    /// the bounds it forces. Union shapes cannot reconstruct this mapping.
    fn type_args(&mut self, cx: &Cx, name: &str, at: TermId, callee: InstId) -> Vec<Ty> {
        let own_parameters = self.meta[callee].own_parameters;
        let own = match self.types.instantiations.get(&at) {
            Some(own) => own.clone(),
            None => {
                if own_parameters > 0 {
                    self.build_errors.push(format!(
                        "error: function `{name}` has no checked type arguments at this use"
                    ));
                }
                HashMap::new()
            }
        };
        // A capture's type is fixed by its binding, not instantiated from
        // the local function's scheme at each use.
        let mut captured: HashMap<ParamId, TTy> = HashMap::new();
        for cap in self.local_caps.get(name).into_iter().flatten() {
            if let Some(i) = self.find_capture(cx, &cap.key) {
                unify_shape(
                    cap.ty.unborrowed(),
                    cx.bindings[i].ty.unborrowed(),
                    &mut captured,
                );
            }
        }
        let parameters = self.meta[callee].parameters.clone();
        let generics = self.meta[callee].generics.clone();
        let mut out = Vec::new();
        let mut edge = Vec::new();
        let mut known = true;
        for (index, ((p, _), g)) in parameters.iter().zip(&generics).enumerate() {
            let map = if index < own_parameters {
                &own
            } else {
                &captured
            };
            match map.get(p.id()) {
                Some(t) => {
                    let n = self.conv(t);
                    if n.has_infer() {
                        known = false;
                    }
                    edge.push((g.clone(), n.clone()));
                    out.push(n);
                }
                None => {
                    self.build_errors.push(format!(
                        "error: type parameter `{}` of function `{name}` has no checked argument at this use",
                        p.name()
                    ));
                    known = false;
                    out.push(Ty::Infer);
                }
            }
        }
        self.meta[cx.inst].edges.push(Edge { callee, args: edge });
        if known { out } else { Vec::new() }
    }

    fn call_args(
        &mut self,
        cx: &mut Cx,
        arguments: &[SurfaceTerm],
        ps: &[TTy],
        decl: Option<&FnDecl>,
        callee_rv: &HashMap<String, Tier>,
    ) -> R<Vec<Expr>> {
        let mut out = Vec::new();
        for (i, a) in arguments.iter().enumerate() {
            let pty = ps.get(i).cloned().unwrap_or(TTy::Var(0));
            let declared = decl
                .and_then(|d| d.param_types.get(i))
                .and_then(|x| x.as_ref());
            let effects = declared.and_then(pi_effects);
            let budgeted_callback = cx.under_budget
                && effects
                    .as_ref()
                    .is_some_and(|es| es.iter().any(|e| e == "Div"));
            let tier = effects.map(|es| {
                let tier = self.row_tier(&es.into_iter().collect(), callee_rv);
                if budgeted_callback {
                    tier.max(Tier::O)
                } else {
                    tier
                }
            });
            if cx.under_budget
                && tier.is_some_and(|tier| tier >= Tier::O)
                && !matches!(&*a.kind, TermKind::Lam { .. } | TermKind::BorrowLam { .. })
                && self.row_tier_in(&self.arg_row(cx, a), cx) < tier.unwrap()
            {
                return unsupported(msg!("nir-a-synchronous-function-value-passed-as"), a.span);
            }
            let e = match (&pty, tier) {
                (TTy::Borrow(inner, m), _) => self.borrow_arg(cx, a, inner, *m, tier)?,
                // A closure literal for a parameter written with a row is
                // made for the tier that row gives, whatever its own body
                // performs: the callee calls it as a function of that tier.
                (TTy::Fn(..), Some(tier)) if matches!(&*a.kind, TermKind::Lam { .. }) => {
                    let e = self.closure(cx, a, Some(tier), false, None)?;
                    let mut to = self.conv(&pty);
                    set_fn_tier(&mut to, tier);
                    self.coerce(e, &to)
                }
                (_, None) if declared.is_some() => {
                    self.expr_written(cx, a, &pty, declared.unwrap())?
                }
                _ => {
                    let mut e = self.expr_expect(cx, a, &pty)?;
                    // A function item passed to a parameter written with a
                    // row is called in that row's tier, as a closure literal
                    // written there is.
                    if let (ExprKind::FnValue { .. }, Ty::Fn(f), Some(tier)) =
                        (&e.kind, &mut e.ty, tier)
                    {
                        f.tier = f.tier.max(tier);
                    }
                    e
                }
            };
            out.push(e);
        }
        Ok(out)
    }

    /// An argument for a borrowed parameter: `&x`, `&mut x`, a closure
    /// literal for `&f`, a name that is a borrow already.
    fn borrow_arg(
        &mut self,
        cx: &mut Cx,
        a: &SurfaceTerm,
        inner: &TTy,
        mutable: bool,
        tier: Option<Tier>,
    ) -> R<Expr> {
        let span = a.span;
        match &*a.kind {
            TermKind::Lam { .. } | TermKind::BorrowLam { .. } if matches!(inner, TTy::Fn(..)) => {
                let TTy::Fn(ps, _, _) = inner else {
                    unreachable!()
                };
                self.closure(cx, a, tier, true, Some(ps))
            }
            // `&(() => ..)` lends the closure literal as the literal alone
            // does: it is made where the borrow is, for the parameter's tier.
            TermKind::Borrow { term, .. }
                if matches!(
                    &*term.kind,
                    TermKind::Lam { .. } | TermKind::BorrowLam { .. }
                ) && matches!(inner, TTy::Fn(..)) =>
            {
                let TTy::Fn(ps, _, _) = inner else {
                    unreachable!()
                };
                self.closure(cx, term, tier, true, Some(ps))
            }
            TermKind::Borrow { mutable, term } => {
                let mut e = self.borrow_expr(cx, a, *mutable, term)?;
                // `&f` of a function item is called in the parameter's tier,
                // as `f` lent without the `&` is.
                if let (ExprKind::TempRef(inner), Some(tier)) = (&mut e.kind, tier) {
                    if let (ExprKind::FnValue { .. }, Ty::Fn(f)) = (&inner.kind, &mut inner.ty) {
                        f.tier = f.tier.max(tier);
                        let ty = inner.ty.clone();
                        e.ty = if *mutable {
                            Ty::RefMut(Box::new(ty))
                        } else {
                            Ty::Ref(Box::new(ty))
                        };
                    }
                }
                Ok(e)
            }
            TermKind::Var(n)
                if self.find(cx, n).is_none()
                    && self.local_caps.get(n).is_some_and(|c| !c.is_empty()) =>
            {
                self.capturing_fn_value(cx, a, n, true)
            }
            TermKind::Var(_) | TermKind::Field { .. } => match self.place(cx, a)? {
                Some(p) => {
                    let ty = p.ty.clone();
                    Ok(if mutable {
                        expr_of(ExprKind::RefMut(p), Ty::RefMut(Box::new(ty)), span)
                    } else {
                        expr_of(ExprKind::Ref(p), Ty::Ref(Box::new(ty)), span)
                    })
                }
                None => {
                    let mut e = self.expr(cx, a)?;
                    // A function item lent to a borrowed parameter is called
                    // in the parameter's tier, as a closure written there is.
                    if let (ExprKind::FnValue { .. }, Ty::Fn(f), Some(tier)) =
                        (&e.kind, &mut e.ty, tier)
                    {
                        f.tier = f.tier.max(tier);
                    }
                    let ty = e.ty.clone();
                    Ok(expr_of(
                        ExprKind::TempRef(Box::new(e)),
                        Ty::Ref(Box::new(ty)),
                        span,
                    ))
                }
            },
            _ => {
                let e = self.expr_expect(cx, a, inner)?;
                let ty = e.ty.clone();
                Ok(expr_of(
                    ExprKind::TempRef(Box::new(e)),
                    if mutable {
                        Ty::RefMut(Box::new(ty))
                    } else {
                        Ty::Ref(Box::new(ty))
                    },
                    span,
                ))
            }
        }
    }

    fn call_local(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        name: &str,
        function: &SurfaceTerm,
        arguments: &[SurfaceTerm],
    ) -> R<Expr> {
        let span = t.span;
        let i = self.find(cx, name).expect("a local");
        self.note_capture(cx, i);
        let b = cx.bindings[i].clone();
        self.check_budget_value(cx, &b, span)?;
        let (ps, ret) = match b.ty.unborrowed() {
            TTy::Fn(ps, r, _) => (ps.clone(), (**r).clone()),
            _ => match self.types.term(function).map(|t| t.unborrowed().clone()) {
                Some(TTy::Fn(ps, r, _)) => (ps, *r),
                _ => {
                    return unsupported(
                        msg!("nir-a-call-of-which-is-not", name = name.to_string()),
                        span,
                    );
                }
            },
        };
        let tier = match &b.fn_row {
            Some(r) => self.row_tier_in(r, cx),
            None => Tier::S,
        };
        let mut args = self.call_args(cx, arguments, &ps, None, &HashMap::new())?;
        let ty = self.conv(&ret);
        if b.mode == Mode::ContBudget && args.len() == 1 {
            let a = args.remove(0);
            let aty = Ty::BudgetAnswer(Box::new(a.ty.clone()));
            let aspan = a.span;
            args.push(expr_of(
                ExprKind::Call(Box::new(CallNode {
                    callee: Callee::Builtin("budget_value".into()),
                    args: vec![a],
                    tier: Tier::S,
                    targs: Vec::new(),
                    tick: Tick::None,
                    recur: false,
                    span: aspan,
                })),
                aty,
                aspan,
            ));
        }
        let callee = if matches!(b.mode, Mode::Cont | Mode::ContBudget) {
            Callee::Cont(b.local)
        } else {
            self.detached_direct(cx, t, msg!("nir-direct-function-value"));
            Callee::Local(b.local)
        };
        Ok(expr_of(
            ExprKind::Call(Box::new(CallNode {
                callee,
                args,
                tier,
                targs: Vec::new(),
                tick: Tick::None,
                recur: false,
                span,
            })),
            ty,
            span,
        ))
    }

    fn call_builtin(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        name: &str,
        function: &SurfaceTerm,
        arguments: &[SurfaceTerm],
    ) -> R<Expr> {
        let span = t.span;
        let fty = self.types.term(function).cloned();
        let ps = match &fty {
            Some(TTy::Fn(ps, _, _)) => ps.clone(),
            _ => Vec::new(),
        };
        let decl: Option<&'a FnDecl> = self.fns.get(name).map(|s| s.decl);
        let tier = match decl {
            Some(_) => self.row_tier(&self.fn_row(name), &cx.rowvars),
            None => Tier::S,
        };
        let is_extern = decl.is_some() && self.fns[name].origin == Origin::Extern;
        if is_extern
            && cx.under_budget
            && (decl.is_some_and(|d| {
                d.param_types
                    .iter()
                    .flatten()
                    .any(|t| pi_effects(t).is_some_and(|es| es.iter().any(|e| e == "Div")))
            }) || arguments
                .iter()
                .any(|a| self.row_tier_in(&self.arg_row(cx, a), cx) >= Tier::O))
        {
            return unsupported(msg!("nir-a-suspendable-callback-through-an-extern"), span);
        }
        let rv = HashMap::new();
        let args = self.call_args(cx, arguments, &ps, decl, &rv)?;
        let ty = self.ety(t);
        if name == "Syn::parse" && !is_extern {
            self.runtime_syntax(&args, &ty, span)?;
        }
        if name.starts_with("HashMap::") {
            if let Some(Ty::Ref(m) | Ty::RefMut(m)) = args.first().map(|a| a.ty.clone()) {
                if let Ty::HashMap(k, _) = &*m {
                    self.need(cx, k, Bound::Eq);
                    self.need(cx, k, Bound::Hash);
                }
            }
        }
        for e in self.fn_row(name) {
            if self.quant(&e) == Quant::Zero {
                self.op_index(&e);
            }
        }
        Ok(expr_of(
            ExprKind::Call(Box::new(CallNode {
                callee: if is_extern {
                    Callee::Extern(name.to_string())
                } else {
                    Callee::Builtin(name.to_string())
                },
                args,
                tier,
                targs: Vec::new(),
                tick: Tick::None,
                recur: false,
                span,
            })),
            ty,
            span,
        ))
    }

    // ---- closures ------------------------------------------------------

    /// The references a borrowing closure of the O tier holds to what it
    /// uses (its future may not borrow the closure): those names are
    /// borrowed parameters inside.
    fn borrow_refs(
        &mut self,
        cx: &mut Cx,
        used: Vec<(Option<CaptureKey>, usize)>,
        span: Span,
    ) -> R<Vec<CapturedRef>> {
        let mut refs: Vec<CapturedRef> = Vec::new();
        let mut bindings: Vec<(usize, Vec<CaptureKey>, bool)> = Vec::new();
        for (key, i) in used {
            let entry = if let Some(at) = bindings.iter().position(|(binding, _, _)| *binding == i)
            {
                &mut bindings[at]
            } else {
                bindings.push((i, Vec::new(), false));
                bindings.last_mut().unwrap()
            };
            if let Some(key) = key {
                if !entry.1.contains(&key) {
                    entry.1.push(key);
                }
            } else {
                entry.2 = true;
            }
        }
        for (i, keys, source_visible) in bindings {
            let b = cx.bindings[i].clone();
            let name = b.name.clone();
            let fn_kind = match b.ty.unborrowed() {
                TTy::Fn(_, _, kind) => Some(*kind),
                _ => None,
            };
            let fn_ref = matches!(b.local.repr, Repr::FnRef | Repr::BorrowClosure);
            if b.celled
                || !matches!(
                    b.local.repr,
                    Repr::Plain
                        | Repr::Ref
                        | Repr::RefMut
                        | Repr::FnRef
                        | Repr::BorrowClosure
                )
                || matches!(b.mode, Mode::Cont | Mode::ContBudget)
                || (fn_ref && fn_kind.is_none())
                // An owned function that suspends is a future of the
                // lifetime it was made for, which the future of this
                // closure (borrowing what it holds) is shorter than.
                || (fn_kind.is_some()
                    && !fn_ref
                    && !matches!(b.ty, TTy::Borrow(..))
                    && b.fn_row
                        .as_ref()
                        .is_some_and(|r| self.row_tier_in(r, cx) >= Tier::O))
            {
                return unsupported(
                    msg!(
                        "nir-a-borrowing-closure-that-uses-which",
                        name = name.to_string()
                    ),
                    span,
                );
            }
            self.note_capture(cx, i);
            // A function value is called through a `&mut` unless it can
            // be shared (`Rc`).
            let mutable = match (&b.ty, fn_kind) {
                (TTy::Borrow(_, m), None) => *m,
                (_, Some(kind)) => fn_ref || b.mode == Mode::Borrow(true) || !kind.dup(),
                (_, None) => b.mode == Mode::Var,
            };
            let ty = match &b.ty {
                TTy::Borrow(_, m) if *m == mutable => b.ty.clone(),
                other => TTy::Borrow(Box::new(other.unborrowed().clone()), mutable),
            };
            let repr = if fn_ref {
                Repr::FnRef
            } else if mutable {
                Repr::RefMut
            } else {
                Repr::Ref
            };
            let inner = self.fresh_local(&name, repr);
            refs.push(CapturedRef {
                inner,
                outer: b.local.clone(),
                mutable,
            });
            let binding = cx.bindings.len();
            if !source_visible {
                cx.hidden_bindings.insert(refs.last().unwrap().inner.id);
            }
            for key in keys {
                cx.capture_bindings.push((key, binding));
            }
            cx.bindings.push(Binding {
                name: name.clone(),
                local: refs.last().unwrap().inner.clone(),
                ty,
                mode: Mode::Borrow(mutable),
                fn_row: b.fn_row.clone(),
                budgeted: b.budgeted,
                celled: false,
            });
        }
        Ok(refs)
    }

    /// A closure literal. `tier` is the tier of the function type it is
    /// written for; `borrowed`: it stands where a `&f` is expected.
    pub fn closure(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        tier: Option<Tier>,
        borrowed: bool,
        expected_params: Option<&[TTy]>,
    ) -> R<Expr> {
        let span = t.span;
        let lam = match &*t.kind {
            TermKind::BorrowLam { lam, .. } => &**lam,
            _ => t,
        };
        let TermKind::Lam { params, body, .. } = &*lam.kind else {
            return unsupported(msg!("nir-a-borrowing-lambda-without-a-lambda"), span);
        };
        let fty = self
            .types
            .term(lam)
            .or_else(|| self.types.term(t))
            .cloned()
            .map(|t| t.unborrowed().clone());
        let Some(TTy::Fn(ps, ret, kind)) = fty else {
            return unsupported(msg!("nir-a-closure-without-a-type"), span);
        };
        // An affine closure whose body only lends what it captured is
        // called any number of times: it is held as a shared function,
        // which the language still neither copies nor drops freely.
        let kind = if kind == Kind::Affine
            && self.free_names(lam).iter().all(|n| match self.find(cx, n) {
                Some(i) => self.kind_of(cx.bindings[i].ty.unborrowed()).dup() || !consumes(body, n),
                None => true,
            }) {
            Kind::Shared
        } else {
            kind
        };
        let body_tier = self.row_tier_in(&self.term_row(body), cx);
        let mut tier = tier.map_or(body_tier, |expected| expected.max(body_tier));
        if cx.under_budget && self.term_row(body).contains("Div") {
            // A closure that may diverge under a budget yields to the budget
            // driver, so it is made suspendable whether it is lent or owned.
            tier = tier.max(Tier::O);
            if tier != Tier::O {
                return unsupported(msg!("nir-a-multi-shot-closure-that-may"), span);
            }
        }
        if tier == Tier::M && borrowed {
            return unsupported(msg!("nir-a-borrowing-closure-that-may-suspend"), span);
        }
        let mark = cx.bindings.len();
        let capture_mark = cx.capture_bindings.len();
        // A borrowing closure of the O tier holds references to what it uses
        // (its future may not borrow the closure): those names are borrowed
        // parameters inside.
        let refs = if tier == Tier::O && borrowed {
            let used = self.free_bindings(cx, lam);
            self.borrow_refs(cx, used, span)?
        } else {
            Vec::new()
        };
        let inner_mark = mark;
        cx.frames.push(CFrame {
            base: cx.bindings.len(),
            captures: Vec::new(),
        });
        let outer_ret = std::mem::replace(&mut cx.ret, (*ret).clone());
        let outer_tier = std::mem::replace(&mut cx.tier, tier);
        let outer_host = std::mem::replace(&mut cx.host_m, false);
        // A closure runs with the handlers of its caller.
        let outer_detached = std::mem::replace(&mut cx.detached, false);
        let mut nparams = Vec::new();
        let mut param_borrows = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let pty = ps
                .get(i)
                .cloned()
                .unwrap_or_else(|| self.local_ty(p, body.id(), None));
            let (local, nty) = self.bind_param(cx, p, &pty, None);
            // The checker accepts a shared borrowed parameter where a
            // duplicable value is supplied. Keep that borrow local to the
            // call while taking the value required by the callee's ABI.
            if let (TTy::Borrow(inner, false), Some(abi)) =
                (&pty, expected_params.and_then(|ps| ps.get(i)))
                && **inner == *abi
                && self.kind_of(abi).dup()
            {
                let arg = self.fresh_local("arg", Repr::Plain);
                let arg_ty = self.conv(abi);
                let place = Place {
                    local: arg.clone(),
                    path: Vec::new(),
                    ty: arg_ty.clone(),
                };
                param_borrows.push(crate::Stmt::Let {
                    local,
                    ty: nty.clone(),
                    init: expr_of(ExprKind::Ref(place), nty, span),
                    span,
                });
                nparams.push((arg, arg_ty));
            } else {
                nparams.push((local, nty));
            }
        }
        let body_e = self.expr_expect(cx, body, &ret);
        cx.bindings.truncate(inner_mark);
        cx.capture_bindings.truncate(capture_mark);
        cx.ret = outer_ret;
        cx.tier = outer_tier;
        cx.host_m = outer_host;
        cx.detached = outer_detached;
        let frame = cx.frames.pop().expect("a frame");
        let mut body_e = body_e?;
        if !param_borrows.is_empty() {
            let ty = body_e.ty.clone();
            body_e = expr_of(
                ExprKind::Block(Block {
                    stmts: param_borrows,
                    tail: Some(Box::new(body_e)),
                }),
                ty,
                span,
            );
        }
        self.seal_closure(
            cx,
            ClosureParts {
                params: nparams,
                ret: &ret,
                body: body_e,
                kind,
                tier,
                borrowed,
                refs,
                captures: frame.captures,
            },
            span,
        )
    }

    /// The closure node of a body lowered in its own frame: what it clones
    /// when it is made, and whether what it captured lets it be owned.
    fn seal_closure(&mut self, cx: &Cx, parts: ClosureParts<'_>, span: Span) -> R<Expr> {
        let ClosureParts {
            params: nparams,
            ret,
            body: body_e,
            kind,
            tier,
            borrowed,
            refs,
            captures,
        } = parts;
        let fn_ty = FnTy {
            params: nparams.iter().map(|(_, t)| t.clone()).collect(),
            ret: self.conv(ret),
            kind,
            tier,
        };
        let mut clones = Vec::new();
        let mut owned_refs = Vec::new();
        if !borrowed {
            for c in &captures {
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
                    Repr::Ref => {
                        let Some(b) = cx.bindings.iter().find(|b| b.local.id == c.id) else {
                            continue;
                        };
                        let nty = self.conv(b.ty.unborrowed());
                        if self.dup_use(&nty).is_some() {
                            owned_refs.push(c.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        if tier == Tier::O
            && !borrowed
            && captures.iter().any(|c| {
                !matches!(
                    c.repr,
                    Repr::Plain | Repr::SharedVar(true) | Repr::SharedVar(false)
                ) && !owned_refs.iter().any(|o: &Local| o.id == c.id)
            })
        {
            return unsupported(msg!("nir-a-closure-that-may-suspend-and"), span);
        }
        let ret_n = fn_ty.ret.clone();
        let ty = Ty::Fn(Box::new(fn_ty.clone()));
        let pure = !borrowed && captures.is_empty() && refs.is_empty();
        Ok(expr_of(
            ExprKind::Closure(Box::new(ClosureNode {
                params: nparams,
                ret: ret_n,
                body: body_e,
                fn_ty,
                borrowed,
                clones,
                pure,
                refs,
                owned_refs,
                span,
            })),
            ty,
            span,
        ))
    }
}

/// A closure body lowered in its frame, to be made into a closure node.
struct ClosureParts<'t> {
    params: Vec<(Local, Ty)>,
    ret: &'t TTy,
    body: Expr,
    kind: Kind,
    tier: Tier,
    borrowed: bool,
    refs: Vec<CapturedRef>,
    captures: Vec<Local>,
}

/// Matches a fixed capture's checked type against its lexical binding,
/// recording parameter identities rather than display names.
pub(crate) fn unify_shape(scheme: &TTy, at: &TTy, map: &mut HashMap<ParamId, TTy>) {
    match (scheme, at) {
        (TTy::Param(p, _), t) => {
            map.entry(p.id().clone()).or_insert_with(|| t.clone());
        }
        (TTy::Named(a, xs), TTy::Named(b, ys)) if a == b => {
            for (x, y) in xs.iter().zip(ys) {
                unify_shape(x, y, map);
            }
        }
        (TTy::Fn(ps, r, _), TTy::Fn(qs, s, _)) => {
            for (x, y) in ps.iter().zip(qs) {
                unify_shape(x, y, map);
            }
            unify_shape(r, s, map);
        }
        (TTy::Borrow(x, _), TTy::Borrow(y, _)) => unify_shape(x, y, map),
        (TTy::Borrow(x, _), y) => unify_shape(x, y, map),
        (TTy::Tagged(_, x), y) => unify_shape(x, y, map),
        (x, TTy::Tagged(_, y)) => unify_shape(x, y, map),
        (TTy::Info(x), TTy::Info(y)) => unify_shape(x, y, map),
        (TTy::Union(xs), TTy::Union(ys)) => {
            for (x, y) in xs.iter().zip(ys) {
                unify_shape(x, y, map);
            }
        }
        _ => {}
    }
}

/// Whether a type holds a borrow in a constructor (`Option(&A)`).
fn holds_ref(t: &Ty) -> bool {
    match t {
        Ty::Option(a) => matches!(**a, Ty::Ref(_) | Ty::RefMut(_)) || holds_ref(a),
        Ty::Result(a, b) | Ty::Pair(a, b) => {
            matches!(**a, Ty::Ref(_) | Ty::RefMut(_))
                || matches!(**b, Ty::Ref(_) | Ty::RefMut(_))
                || holds_ref(a)
                || holds_ref(b)
        }
        Ty::Product(ms) => ms
            .iter()
            .any(|(_, m)| matches!(m, Ty::Ref(_) | Ty::RefMut(_)) || holds_ref(m)),
        _ => false,
    }
}

/// Whether `body` may consume `name`: it names it other than to lend it
/// (`&name`, `&name.field`).
fn consumes(body: &SurfaceTerm, name: &str) -> bool {
    fn root_is(t: &SurfaceTerm, name: &str) -> bool {
        match &*t.kind {
            TermKind::Var(n) => n == name,
            TermKind::Field { base, .. } => root_is(base, name),
            _ => false,
        }
    }
    let (mut named, mut lent) = (0usize, 0usize);
    tauto::surface::walk::value_terms(body, &mut |t| match &*t.kind {
        TermKind::Var(n) if n == name => named += 1,
        TermKind::Borrow { term, .. } if root_is(term, name) => lent += 1,
        _ => {}
    });
    named > lent
}
