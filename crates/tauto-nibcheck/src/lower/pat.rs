use crate::types::Ty as TTy;
use tauto_surface::surface::{MatchArm as SurfaceArm, Pattern, SurfaceTerm, TermKind};

use super::ty::{set_fn_tier, set_written_tiers_in_args};
use super::*;

impl<'a> Lowerer<'a> {
    pub(crate) fn match_with(
        &mut self,
        cx: &mut Cx,
        t: &SurfaceTerm,
        scrutinee: &SurfaceTerm,
        arms: &[SurfaceArm],
        tail_k: Option<&super::handle::TailK>,
    ) -> R<Expr> {
        let span = t.span;
        let sty = self.types.term(scrutinee).cloned().unwrap_or(TTy::Var(0));
        if let TTy::Named(data, _) = sty.unborrowed() {
            let accessor = self.current_fn.clone();
            self.refuse_sealed_repr(data, accessor.as_ref());
        }
        let by_ref =
            matches!(sty, TTy::Borrow(..)) || matches!(&*scrutinee.kind, TermKind::Borrow { .. });
        let scrut = match &*scrutinee.kind {
            TermKind::Borrow { mutable, term, .. } => {
                self.borrow_expr(cx, scrutinee, *mutable, term)?
            }
            // A `&mut` scrutinee is matched through the same borrow, so a
            // write through a pattern variable reaches the matched place.
            _ if by_ref => match self.place(cx, scrutinee)? {
                Some(p) => {
                    let ty = p.ty.clone();
                    let (kind, ty) = if matches!(sty, TTy::Borrow(_, true)) {
                        (ExprKind::RefMut(p), Ty::RefMut(Box::new(ty)))
                    } else {
                        (ExprKind::Ref(p), Ty::Ref(Box::new(ty)))
                    };
                    Expr {
                        kind,
                        ty,
                        span: scrutinee.span,
                    }
                }
                None => self.expr(cx, scrutinee)?,
            },
            _ => self.expr(cx, scrutinee)?,
        };
        let inner = sty.unborrowed().clone();
        let (want, ty) = match tail_k {
            Some(tk) => (tk.ans.clone(), self.conv(&tk.ans)),
            None => (
                self.types.term(t).cloned().unwrap_or(TTy::Unit),
                self.ety(t),
            ),
        };
        let mut out = Vec::new();
        let mut catch_all = false;
        let mut covered: Vec<Name> = Vec::new();
        let written = self.written_type(cx, scrutinee);
        // The variants of the union the typed arms without a guard take.
        let mut variants: Vec<usize> = Vec::new();
        for arm in arms {
            if let Pattern::Typed { name, .. } = &arm.pattern {
                let (union, members) = self.typed_members(name, &inner, arm.body.id())?;
                let several = members.len() > 1;
                if several && arm.guard.is_some() {
                    return unsupported(msg!("nir-a-guard-on-a-typed-arm-of-several"), span);
                }
                if several && by_ref {
                    return unsupported(msg!("nir-a-typed-arm-of-several-members-on-a"), span);
                }
                for (variant, member) in members {
                    let mark = cx.bindings.len();
                    let (pat, bound) =
                        self.typed_pat(cx, name, union, variant, &member, arm.body.id(), by_ref);
                    let guard = match &arm.guard {
                        Some(g) => Some(self.expr_expect(cx, g, &TTy::Bool)?),
                        None => None,
                    };
                    let mut body = match tail_k {
                        Some(tk) => self.expr_tail(cx, &arm.body, tk)?,
                        None => self.branch(cx, &arm.body, &want)?,
                    };
                    cx.bindings.truncate(mark);
                    if let Some(bound) = bound {
                        let ty = body.ty.clone();
                        let bspan = body.span;
                        body = Expr {
                            kind: ExprKind::Block(Block {
                                stmts: vec![bound],
                                tail: Some(Box::new(body)),
                            }),
                            ty,
                            span: bspan,
                        };
                    }
                    if guard.is_none() {
                        variants.push(variant);
                    }
                    out.push(MatchArm { pat, guard, body });
                }
                continue;
            }
            let mark = cx.bindings.len();
            let outer_tests = std::mem::take(&mut cx.nat_tests);
            let pat = self.pattern_written(
                cx,
                &arm.pattern,
                &inner,
                arm.body.id(),
                by_ref,
                written.as_ref(),
            );
            let nat_tests = std::mem::replace(&mut cx.nat_tests, outer_tests);
            let pat = pat?;
            if arm.guard.is_some() && guard_blocked(&pat) {
                return unsupported(msg!("nir-a-guard-that-reads-what-a"), arm.body.span);
            }
            let (tests, lets) = self.nat_arm(cx, &nat_tests, span)?;
            if arm.guard.is_some() && !lets.is_empty() {
                return unsupported(msg!("nir-a-guard-that-reads-what-a"), arm.body.span);
            }
            let guard = match &arm.guard {
                Some(g) => Some(self.expr_expect(cx, g, &TTy::Bool)?),
                None => None,
            };
            let guard = tests.into_iter().chain(guard).reduce(|a, b| Expr {
                kind: ExprKind::And(Box::new(a), Box::new(b)),
                ty: Ty::Bool,
                span,
            });
            let body = match tail_k {
                Some(tk) => self.expr_tail(cx, &arm.body, tk)?,
                None => self.branch(cx, &arm.body, &want)?,
            };
            let body = if lets.is_empty() {
                body
            } else {
                let (ty, bspan) = (body.ty.clone(), body.span);
                Expr {
                    kind: ExprKind::Block(Block {
                        stmts: lets,
                        tail: Some(Box::new(body)),
                    }),
                    ty,
                    span: bspan,
                }
            };
            cx.bindings.truncate(mark);
            if guard.is_none() {
                match &pat {
                    Pat::Wild | Pat::Bind(..) => catch_all = true,
                    Pat::Ctor { ctor, fields }
                        if fields
                            .iter()
                            .all(|f| matches!(f, Pat::Wild | Pat::Bind(..))) =>
                    {
                        covered.push(ctor.name.clone());
                    }
                    _ => {}
                }
            }
            out.push(MatchArm { pat, guard, body });
        }
        let exhaustive = catch_all
            || self.covers_all(&inner, &covered)
            || match self.conv(&inner) {
                Ty::Union(u) => (0..self.unions[u].members.len()).all(|v| variants.contains(&v)),
                _ => false,
            };
        let mut bodies: Vec<&mut Expr> = out.iter_mut().map(|a| &mut a.body).collect();
        let ty = self.join_fn_branches(ty, &mut bodies);
        Ok(Expr {
            kind: ExprKind::Match(Box::new(MatchNode {
                scrut,
                by_ref,
                arms: out,
                exhaustive,
                span,
            })),
            ty,
            span,
        })
    }

    /// A function a branch gives may perform more than the type the branching
    /// is written with (a branch's closure that may overflow, beside one that
    /// may not): the branching gives a function of the highest tier of its
    /// branches, and each branch's function is lifted to it.
    pub(crate) fn join_fn_branches(&mut self, mut ty: Ty, bodies: &mut [&mut Expr]) -> Ty {
        let Ty::Fn(f) = &ty else {
            return ty;
        };
        let have = f.tier;
        let top = bodies
            .iter()
            .filter_map(|b| match &b.ty {
                Ty::Fn(g) => Some(g.tier),
                _ => None,
            })
            .fold(have, Tier::max);
        if top > have {
            set_fn_tier(&mut ty, top);
            for body in bodies.iter_mut() {
                let unit = Expr {
                    kind: ExprKind::Unit,
                    ty: Ty::Unit,
                    span: body.span,
                };
                let b = std::mem::replace(&mut **body, unit);
                **body = self.coerce(b, &ty);
            }
        }
        ty
    }

    /// The tests and the bindings of the `Succ(p)` patterns on a `nat` an arm's
    /// pattern holds: each value is at least 1 and `p` matches one less.
    fn nat_arm(
        &mut self,
        cx: &mut Cx,
        tests: &[(Local, Pattern, bool)],
        span: Span,
    ) -> R<(Vec<Expr>, Vec<tauto_nir::Stmt>)> {
        let nty = self.conv(&TTy::Int(Width::Nat));
        let mut conds = Vec::new();
        let mut lets = Vec::new();
        for (local, inner, borrowed) in tests {
            let read = if *borrowed {
                Expr {
                    kind: ExprKind::Deref {
                        value: Box::new(Expr {
                            kind: ExprKind::Read {
                                local: local.clone(),
                                how: Use::Clone,
                            },
                            ty: Ty::Ref(Box::new(nty.clone())),
                            span,
                        }),
                        how: Use::Clone,
                    },
                    ty: nty.clone(),
                    span,
                }
            } else {
                Expr {
                    kind: ExprKind::Read {
                        local: local.clone(),
                        how: Use::Clone,
                    },
                    ty: nty.clone(),
                    span,
                }
            };
            self.nat_test(
                cx,
                &Pattern::Ctor {
                    name: tauto_surface::bindings::library_name("Succ"),
                    args: vec![inner.clone()],
                },
                read,
                &nty,
                &mut conds,
                &mut lets,
                span,
            )?;
        }
        Ok((conds, lets))
    }

    #[allow(clippy::too_many_arguments)]
    fn nat_test(
        &mut self,
        cx: &mut Cx,
        p: &Pattern,
        value: Expr,
        nty: &Ty,
        conds: &mut Vec<Expr>,
        lets: &mut Vec<tauto_nir::Stmt>,
        span: Span,
    ) -> R<()> {
        let num = |k: i128| Expr {
            kind: ExprKind::Int(k),
            ty: nty.clone(),
            span,
        };
        let eq = |value: Expr, k: i128| Expr {
            kind: ExprKind::Eq {
                negate: false,
                args: vec![value, num(k)],
            },
            ty: Ty::Bool,
            span,
        };
        match p {
            Pattern::Wild => {}
            Pattern::Int(k) => conds.push(eq(value, i128::from(*k))),
            Pattern::Bind { name, .. }
                if tauto_surface::bindings::is_library_selected(name, "Zero") =>
            {
                conds.push(eq(value, 0))
            }
            Pattern::Bind { name, .. } => {
                let local = self.fresh_local(&name.to_string(), Repr::Plain);
                cx.bindings.push(Binding {
                    name: name.clone(),
                    local: local.clone(),
                    ty: TTy::Int(Width::Nat),
                    mode: Mode::Owned,
                    fn_row: None,
                    budgeted: cx.under_budget,
                    celled: false,
                });
                lets.push(tauto_nir::Stmt::Let {
                    local,
                    ty: nty.clone(),
                    init: value,
                    span,
                    stack: false,
                });
            }
            Pattern::Ctor { name, args } => match crate::types::nat_ctor(name, args) {
                Some(None) => conds.push(eq(value, 0)),
                Some(Some(inner)) => {
                    conds.push(Expr {
                        kind: ExprKind::Cmp {
                            op: Cmp::Ge,
                            args: vec![value.clone(), num(1)],
                        },
                        ty: Ty::Bool,
                        span,
                    });
                    let less = Expr {
                        kind: ExprKind::Arith {
                            op: Arith::Sub,
                            args: vec![value, num(1)],
                            num: Num::Int(Width::Nat),
                        },
                        ty: nty.clone(),
                        span,
                    };
                    self.nat_test(cx, inner, less, nty, conds, lets, span)?;
                }
                None => {
                    return unsupported(
                        msg!("nir-is-not-a-constructor", name = name.to_string()),
                        span,
                    );
                }
            },
            _ => {
                return unsupported(
                    msg!("nir-is-not-a-constructor", name = "Nat".to_string()),
                    span,
                );
            }
        }
        Ok(())
    }

    /// The union a typed arm `name: T` is on, and the variants of it that `T` takes, each with
    /// its member's type.
    fn typed_members(
        &mut self,
        name: &Name,
        scrutinee: &TTy,
        at: tauto_surface::surface::TermId,
    ) -> R<(usize, Vec<(usize, TTy)>)> {
        let Ty::Union(union) = self.conv(scrutinee) else {
            return unsupported(msg!("nir-a-typed-arm-on-a-union-of-one"), at.span());
        };
        let bound = self.local_ty(name, at, None);
        let picked = match bound.unborrowed() {
            TTy::Union(ms) => ms.clone(),
            t => vec![t.clone()],
        };
        let mut out = Vec::new();
        for m in picked {
            let nty = self.conv(&m);
            let Some(variant) = self.unions[union].members.iter().position(|x| *x == nty) else {
                return unsupported(msg!("nir-a-typed-arm-on-a-union-of-one"), at.span());
            };
            out.push((variant, m));
        }
        Ok((union, out))
    }

    /// The pattern of one variant a typed arm `name: T` takes, with `name` bound. When `T`
    /// has several members, the pattern binds the member's value and the statement given back
    /// binds `name` to it injected into `T`.
    #[allow(clippy::too_many_arguments)]
    fn typed_pat(
        &mut self,
        cx: &mut Cx,
        name: &Name,
        union: usize,
        variant: usize,
        member: &TTy,
        at: tauto_surface::surface::TermId,
        by_ref: bool,
    ) -> (Pat, Option<tauto_nir::Stmt>) {
        let bound = self.local_ty(name, at, None);
        let several = matches!(bound.unborrowed(), TTy::Union(_));
        let repr = match &bound {
            TTy::Borrow(inner, _) if matches!(**inner, TTy::Fn(..)) => Repr::FnRef,
            TTy::Borrow(_, false) | TTy::Orig(_) => Repr::Ref,
            TTy::Borrow(_, true) => Repr::RefMut,
            _ if by_ref => Repr::Ref,
            _ => Repr::Plain,
        };
        let local = self.fresh_local(name, repr);
        cx.bindings.push(Binding {
            name: name.clone(),
            local: local.clone(),
            ty: bound.clone(),
            mode: match &bound {
                TTy::Borrow(_, m) => Mode::Borrow(*m),
                _ => Mode::Owned,
            },
            fn_row: None,
            budgeted: cx.under_budget,
            celled: false,
        });
        let nty = self.conv(&bound);
        let wrap = |pat| Pat::Variant {
            union,
            variant,
            pat: Box::new(pat),
        };
        if !several {
            return (wrap(Pat::Bind(local, nty)), None);
        }
        let part = self.fresh_local(name, Repr::Plain);
        let mty = self.conv(member);
        let span = at.span();
        let read = Expr {
            kind: ExprKind::Read {
                local: part.clone(),
                how: self.use_of(member),
            },
            ty: mty.clone(),
            span,
        };
        let init = match &nty {
            Ty::Union(to) => {
                let to = *to;
                let k = self.unions[to]
                    .members
                    .iter()
                    .position(|x| *x == mty)
                    .unwrap_or(0);
                Expr {
                    kind: ExprKind::Inject {
                        union: to,
                        variant: k,
                        value: Box::new(read),
                    },
                    ty: nty.clone(),
                    span,
                }
            }
            _ => read,
        };
        let stmt = tauto_nir::Stmt::Let {
            local,
            ty: nty,
            init,
            span,
            stack: false,
        };
        (wrap(Pat::Bind(part, mty)), Some(stmt))
    }

    /// Whether the constructors listed are all of the type's.
    fn covers_all(&self, ty: &TTy, covered: &[Name]) -> bool {
        let TTy::Named(n, _) = ty else {
            return false;
        };
        let Some(d) = self.types.datas.decls.get(n) else {
            return false;
        };
        d.constructors.iter().all(|c| covered.contains(&c.name))
    }

    pub fn pattern(
        &mut self,
        cx: &mut Cx,
        p: &Pattern,
        ty: &TTy,
        at: tauto_surface::surface::TermId,
        by_ref: bool,
    ) -> R<Pat> {
        self.pattern_written(cx, p, ty, at, by_ref, None)
    }

    /// The type a scrutinee is written with, when the program writes it: the
    /// result of a call of a declared function, a local whose type is
    /// written. A checked type has no rows, so the rows of functions inside
    /// it are read from what is written.
    pub(crate) fn written_type(&self, cx: &Cx, scrutinee: &SurfaceTerm) -> Option<SurfaceTerm> {
        let scrutinee = match &*scrutinee.kind {
            TermKind::Borrow { term, .. } => term,
            _ => scrutinee,
        };
        if let TermKind::Var(name) = &*scrutinee.kind {
            let i = self.find(cx, name)?;
            return cx.written.get(&cx.bindings[i].local.id).cloned();
        }
        if let TermKind::Field { base, name } = &*scrutinee.kind {
            return self
                .types
                .term(base)
                .and_then(|b| self.named_field_term(b, name));
        }
        let TermKind::App { function, .. } = &*scrutinee.kind else {
            return None;
        };
        let TermKind::Var(name) = &*function.kind else {
            return None;
        };
        self.fns.get(name)?.decl.result.clone()
    }

    /// The types the fields of `ctor` take in a value written as `written`:
    /// a field whose type is a parameter of the data takes the argument
    /// written for that parameter, and a field of the data itself with its
    /// parameters in order (the tail of a list) takes `written`.
    pub(crate) fn written_fields(
        &self,
        ctor: &Name,
        ty: &TTy,
        written: Option<&SurfaceTerm>,
    ) -> Vec<Option<SurfaceTerm>> {
        let Some(written) = written else {
            return Vec::new();
        };
        let written = match &*written.kind {
            TermKind::Borrow { term, .. } => term,
            _ => written,
        };
        let TermKind::App { arguments, .. } = &*written.kind else {
            return Vec::new();
        };
        let Ok((data, i)) = self.types.datas.resolve_ctor(ctor, Some(ty)) else {
            return Vec::new();
        };
        let Some(d) = self.types.datas.decls.get(data) else {
            return Vec::new();
        };
        if d.generics.len() != arguments.len() {
            return Vec::new();
        }
        let Some(c) = d.constructors.get(*i) else {
            return Vec::new();
        };
        let params = d.parameters();
        let same = |args: &[TTy]| {
            args.len() == params.len()
                && args
                    .iter()
                    .zip(&params)
                    .all(|(a, p)| matches!(a, TTy::Param(q, _) if q == p))
        };
        c.fields
            .iter()
            .map(|(_, f)| match f {
                TTy::Param(p, _) => params
                    .iter()
                    .position(|x| x == p)
                    .map(|k| arguments[k].clone()),
                TTy::Named(n, args) if n == data && same(args) => Some(written.clone()),
                _ => None,
            })
            .collect()
    }

    pub(crate) fn pattern_written(
        &mut self,
        cx: &mut Cx,
        p: &Pattern,
        ty: &TTy,
        at: tauto_surface::surface::TermId,
        by_ref: bool,
        written: Option<&SurfaceTerm>,
    ) -> R<Pat> {
        // `@a p`: a label is not on the value, which `p` matches.
        if let Some((_, inner)) = p.label() {
            let under = match ty {
                TTy::Tagged(_, under) => (**under).clone(),
                TTy::Borrow(t, m) if let TTy::Tagged(_, under) = &**t => {
                    TTy::Borrow(under.clone(), *m)
                }
                other => other.clone(),
            };
            return self.pattern_written(cx, inner, &under, at, by_ref, written);
        }
        Ok(match p {
            Pattern::Wild => Pat::Wild,
            Pattern::Int(n) if matches!(self.conv(ty), Ty::Int(Width::Nat)) => Pat::Nat(*n),
            Pattern::Int(n) => Pat::Int(*n),
            Pattern::Bool(b) => Pat::Bool(*b),
            Pattern::Text(s) => Pat::Text(s.clone()),
            // `Zero` over a `nat` is the number 0, not a name for any value.
            Pattern::Bind { name: name, .. }
                if matches!(self.conv(ty), Ty::Int(Width::Nat))
                    && tauto_surface::bindings::is_library_selected(name, "Zero") =>
            {
                Pat::Nat(0)
            }
            Pattern::Bind { name: name, .. } => {
                if let Some(ctor) = self.ctor_ref_in(name, Some(ty))
                    && ctor.nullary
                {
                    return Ok(Pat::Ctor {
                        ctor,
                        fields: Vec::new(),
                    });
                }
                let bound = self.local_ty(name, at, Some(ty));
                let repr = match &bound {
                    TTy::Borrow(inner, _) if matches!(**inner, TTy::Fn(..)) => Repr::FnRef,
                    TTy::Borrow(_, false) | TTy::Orig(_) => Repr::Ref,
                    TTy::Borrow(_, true) => Repr::RefMut,
                    _ if by_ref => Repr::Ref,
                    _ => Repr::Plain,
                };
                let local = self.fresh_local(name, repr);
                let mut nty = self.conv(&bound);
                // A checked type has no rows: the tiers of the functions in
                // the bound value are read from the type written for it.
                if let Some(w) = written {
                    self.written_tiers(&mut nty, w, cx);
                    cx.written.insert(local.id, w.clone());
                }
                cx.bindings.push(Binding {
                    name: name.clone(),
                    local: local.clone(),
                    ty: bound.clone(),
                    mode: match &bound {
                        TTy::Borrow(_, m) => Mode::Borrow(*m),
                        _ => Mode::Owned,
                    },
                    // A function bound at a written type performs what the
                    // type's row names, as a parameter of that type does: an
                    // operation's argument `body: () -> Unit ! {fail(Text)}`
                    // given on to `catch(body)` specializes its row.
                    fn_row: written
                        .filter(|_| matches!(bound.unborrowed(), TTy::Fn(..)))
                        .map(|w| pi_effects(w).into_iter().flatten().collect::<Row>()),
                    budgeted: cx.under_budget,
                    celled: false,
                });
                Pat::Bind(local, nty)
            }
            // `Zero` on a `nat` is the number 0; `Succ(p)` binds the value, which
            // the arm's guard tests to be at least 1 and `p` to match one less.
            Pattern::Ctor { name, args }
                if matches!(self.conv(ty.unborrowed()), Ty::Int(Width::Nat))
                    && let Some(inner) = crate::types::nat_ctor(name, args) =>
            {
                match inner {
                    None => Pat::Nat(0),
                    Some(inner) => {
                        let borrowed = by_ref || matches!(ty, TTy::Borrow(..));
                        let local =
                            self.fresh_local("nat", if borrowed { Repr::Ref } else { Repr::Plain });
                        let nty = self.conv(ty.unborrowed());
                        let nty = if borrowed {
                            Ty::Ref(Box::new(nty))
                        } else {
                            nty
                        };
                        cx.nat_tests.push((local.clone(), inner.clone(), borrowed));
                        Pat::Bind(local, nty)
                    }
                }
            }
            // `#()` takes the one value of `Unit`.
            Pattern::Ctor { args, .. }
                if args.is_empty() && matches!(ty.unborrowed(), TTy::Unit) =>
            {
                Pat::Wild
            }
            Pattern::Ctor { name, args } => {
                let Some(ctor) = self.ctor_ref_in(name, Some(ty)) else {
                    return unsupported(
                        msg!("nir-is-not-a-constructor", name = name.to_string()),
                        at.span(),
                    );
                };
                let ftys = self.ctor_fields(name, ty);
                let rows = self.ctor_field_rows(name, ty);
                let wfs = self.written_fields(name, ty, written);
                let mut fields = Vec::new();
                for (i, a) in args.iter().enumerate() {
                    let fty = ftys.get(i).cloned().unwrap_or(TTy::Var(0));
                    fields.push(self.sub_pattern(
                        cx,
                        a,
                        &fty,
                        at,
                        by_ref,
                        rows.get(i).cloned().flatten(),
                        wfs.get(i).cloned().flatten(),
                    )?);
                }
                Pat::Ctor { ctor, fields }
            }
            Pattern::Record { name, fields } => {
                let Some(ctor) = self.ctor_ref_in(name, Some(ty)) else {
                    return unsupported(
                        msg!("nir-is-not-a-struct", name = name.to_string()),
                        at.span(),
                    );
                };
                let ftys = self.ctor_fields(name, ty);
                let rows = self.ctor_field_rows(name, ty);
                let wfs = self.written_fields(name, ty, written);
                let mut out = Vec::new();
                for (i, fname) in ctor.fields.iter().enumerate() {
                    let sub = fields
                        .iter()
                        .find(|(f, _)| Some(f) == fname.as_ref())
                        .map(|(_, p)| p.clone())
                        .unwrap_or(Pattern::Wild);
                    let fty = ftys.get(i).cloned().unwrap_or(TTy::Var(0));
                    out.push(self.sub_pattern(
                        cx,
                        &sub,
                        &fty,
                        at,
                        by_ref,
                        rows.get(i).cloned().flatten(),
                        wfs.get(i).cloned().flatten(),
                    )?);
                }
                Pat::Ctor { ctor, fields: out }
            }
            // Only a whole arm of a `match` is typed, and `match_with` takes it.
            Pattern::Typed { .. } => {
                return unsupported(
                    msg!("nir-the-pattern", what = "a typed arm inside a pattern"),
                    at.span(),
                );
            }
            Pattern::Other(what) => {
                return unsupported(msg!("nir-the-pattern", what = what.to_string()), at.span());
            }
        })
    }

    fn sub_pattern(
        &mut self,
        cx: &mut Cx,
        p: &Pattern,
        ty: &TTy,
        at: tauto_surface::surface::TermId,
        by_ref: bool,
        row: Option<Row>,
        written: Option<SurfaceTerm>,
    ) -> R<Pat> {
        let mut pat = self.pattern_written(cx, p, ty, at, by_ref, written.as_ref())?;
        if let (Some(w), Pat::Bind(local, _)) = (&written, &pat) {
            cx.written.insert(local.id, w.clone());
        }
        // A field whose type is a parameter of the data: the row is the one
        // written on the argument for it.
        let row = row.or_else(|| {
            written
                .as_ref()
                .and_then(pi_effects)
                .map(|e| e.into_iter().collect())
        });
        // A field of the data itself (the tail of a list): the functions in
        // its type arguments take the tiers their written rows give, as the
        // value matched does.
        if row.is_none()
            && let (Some(w), Pat::Bind(_, nty)) = (&written, &mut pat)
        {
            set_written_tiers_in_args(nty, w, &mut |row| self.field_tier(row));
        }
        if let (Some(row), Pat::Bind(local, nty)) = (row, &mut pat) {
            let tier = self.field_tier(&row);
            set_fn_tier(nty, tier);
            // A budget does not make the call suspend: the field's
            // function was made for this tier.
            let row: Row = if tier == Tier::O {
                row
            } else {
                row.into_iter()
                    .filter(|e| !tauto_surface::bindings::is_divergence(&e))
                    .collect()
            };
            if let Some(b) = cx
                .bindings
                .iter_mut()
                .rev()
                .find(|b| b.local.id == local.id)
            {
                b.fn_row = Some(row);
            }
        }
        Ok(pat)
    }
}

/// Whether a written guard cannot see the names of `pat`: those taken out
/// of a recursive field by value (`Box`), or from inside a pattern there.
fn guard_blocked(pat: &Pat) -> bool {
    fn binds(p: &Pat) -> bool {
        match p {
            Pat::Bind(..) => true,
            Pat::Ctor { fields, .. } => fields.iter().any(binds),
            _ => false,
        }
    }
    match pat {
        Pat::Ctor { ctor, fields } => fields.iter().enumerate().any(|(i, f)| {
            let boxed = matches!(
                ctor.indirect.get(i),
                Some(Indirect::Shared | Indirect::Unique)
            );
            match f {
                Pat::Bind(l, _) => {
                    matches!(ctor.indirect.get(i), Some(Indirect::Unique))
                        && !matches!(l.repr, Repr::Ref | Repr::RefMut)
                }
                Pat::Ctor { .. } if boxed => binds(f),
                f => guard_blocked(f),
            }
        }),
        _ => false,
    }
}
