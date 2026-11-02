use tauto::surface::{MatchArm as SurfaceArm, Pattern, SurfaceTerm, TermKind};
use tauto::types::Ty as TTy;

use super::ty::set_fn_tier;
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
        let by_ref =
            matches!(sty, TTy::Borrow(..)) || matches!(&*scrutinee.kind, TermKind::Borrow { .. });
        let scrut = match &*scrutinee.kind {
            TermKind::Borrow { mutable, term } => {
                self.borrow_expr(cx, scrutinee, *mutable, term)?
            }
            _ if by_ref => match self.place(cx, scrutinee)? {
                Some(p) => {
                    let ty = p.ty.clone();
                    Expr {
                        kind: ExprKind::Ref(p),
                        ty: Ty::Ref(Box::new(ty)),
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
        let mut covered: Vec<String> = Vec::new();
        let written = self.written_type(cx, scrutinee);
        for arm in arms {
            let mark = cx.bindings.len();
            let pat = self.pattern_written(
                cx,
                &arm.pattern,
                &inner,
                arm.body.id(),
                by_ref,
                written.as_ref(),
            )?;
            if arm.guard.is_some() && guard_blocked(&pat) {
                return unsupported(msg!("nir-a-guard-that-reads-what-a"), arm.body.span);
            }
            let guard = match &arm.guard {
                Some(g) => Some(self.expr_expect(cx, g, &TTy::Bool)?),
                None => None,
            };
            let body = match tail_k {
                Some(tk) => self.expr_tail(cx, &arm.body, tk)?,
                None => self.branch(cx, &arm.body, &want)?,
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
        let exhaustive = catch_all || self.covers_all(&inner, &covered);
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

    fn covers_all(&self, ty: &TTy, covered: &[String]) -> bool {
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
        at: tauto::surface::TermId,
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
        let TermKind::App { function, .. } = &*scrutinee.kind else {
            return None;
        };
        let TermKind::Var(name) = &*function.kind else {
            return None;
        };
        self.fns.get(name.as_str())?.decl.result.clone()
    }

    /// The types the fields of `ctor` take in a value written as `written`:
    /// a field whose type is a parameter of the data takes the argument
    /// written for that parameter, and a field of the data itself with its
    /// parameters in order (the tail of a list) takes `written`.
    pub(crate) fn written_fields(
        &self,
        ctor: &str,
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

    fn pattern_written(
        &mut self,
        cx: &mut Cx,
        p: &Pattern,
        ty: &TTy,
        at: tauto::surface::TermId,
        by_ref: bool,
        written: Option<&SurfaceTerm>,
    ) -> R<Pat> {
        // `#(p, #())` is `p` and `#(#(p, q), r)` is `#(p, q, r)`, as the value is.
        if let Some(flat) = tauto::surface::qualify::flatten_pair_pattern(p) {
            return self.pattern_written(cx, &flat, ty, at, by_ref, written);
        }
        if let Some(pat) = self.product_pattern(cx, p, ty, at, by_ref)? {
            return Ok(pat);
        }
        // `#(p, q)` is matched as the nested `Pair` its value is lowered to.
        if let Pattern::Tuple(_) = p {
            let pair = tauto::surface::qualify::tuple_pattern_as_pairs(p, "Pair");
            return self.pattern_written(cx, &pair, ty, at, by_ref, written);
        }
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
            Pattern::Int(n) if matches!(ty, TTy::Int(Width::Nat)) => Pat::Nat(*n),
            Pattern::Int(n) => Pat::Int(*n),
            Pattern::Bool(b) => Pat::Bool(*b),
            Pattern::Text(s) => Pat::Text(s.clone()),
            Pattern::Bind(name) => {
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
                    TTy::Borrow(_, false) => Repr::Ref,
                    TTy::Borrow(_, true) => Repr::RefMut,
                    _ if by_ref => Repr::Ref,
                    _ => Repr::Plain,
                };
                let local = self.fresh_local(name, repr);
                let nty = self.conv(&bound);
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
                Pat::Bind(local, nty)
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
            Pattern::Tuple(_) => unreachable!("`#(…)` is put as its `Pair` above"),
            Pattern::Other(what) => {
                return unsupported(msg!("nir-the-pattern", what = what.to_string()), at.span());
            }
        })
    }

    /// A pattern in a field. A name bound to a function the field's type
    /// (or the type argument it takes) writes a row for is called at the
    /// tier of that row.
    /// `#(p, q, …)` on a value of a product type, as the checker reads it:
    /// each member by its label, or else by position. `None`
    /// for another pattern or type, which is matched as it is written.
    fn product_pattern(
        &mut self,
        cx: &mut Cx,
        p: &Pattern,
        ty: &TTy,
        at: tauto::surface::TermId,
        by_ref: bool,
    ) -> R<Option<Pat>> {
        let TTy::Product(order) = ty.unborrowed().clone() else {
            return Ok(None);
        };
        let Pattern::Tuple(items) = p else {
            return Ok(None);
        };
        let pats: Vec<Pattern> = items.clone();
        if pats.len() != order.len() {
            return Ok(None);
        }
        let labels: Option<Vec<&str>> = pats.iter().map(|q| q.label().map(|(l, _)| l)).collect();
        let places: Option<Vec<usize>> = match labels {
            Some(labels) => labels
                .iter()
                .map(|l| {
                    order
                        .iter()
                        .position(|m| matches!(m, TTy::Tagged(ts, _) if ts.contains(*l)))
                })
                .collect(),
            None => Some((0..pats.len()).collect()),
        };
        let Some(places) = places else {
            return Ok(None);
        };
        let mut fields = vec![Pat::Wild; order.len()];
        for (q, i) in pats.iter().zip(places) {
            fields[i] = self.sub_pattern(cx, q, &order[i], at, by_ref, None, None)?;
        }
        let n = fields.len();
        let ctor = CtorRef {
            data: DataRef::Product,
            name: "Product".to_string(),
            index: 0,
            indirect: vec![Indirect::None; n],
            linear: false,
            fields: vec![None; n],
            nullary: false,
        };
        Ok(Some(Pat::Ctor { ctor, fields }))
    }

    fn sub_pattern(
        &mut self,
        cx: &mut Cx,
        p: &Pattern,
        ty: &TTy,
        at: tauto::surface::TermId,
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
        if let (Some(row), Pat::Bind(local, nty)) = (row, &mut pat) {
            let tier = self.field_tier(&row);
            set_fn_tier(nty, tier);
            // A budget does not make the call suspend: the field's
            // function was made for this tier.
            let row: Row = if tier == Tier::O {
                row
            } else {
                row.into_iter().filter(|e| e != "Div").collect()
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
