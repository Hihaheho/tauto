//! Instantiate reachable NIR functions before choosing a concrete Wasm ABI.
//! JavaScript bindings keep their original names and erased representation.
use std::collections::{BTreeMap, BTreeSet};
use tauto_nir::*;
type Subst = BTreeMap<String, Ty>;

pub fn package(
    input: &Package,
    native: &BTreeSet<Name>,
) -> Result<(Package, BTreeMap<Name, Name>), String> {
    if !input
        .externs
        .iter()
        .any(|x| native.contains(&x.name) && !x.generics.is_empty())
    {
        return Ok((input.clone(), BTreeMap::new()));
    }
    let mut state = Specializer {
        input,
        native,
        output: input.clone(),
        functions: BTreeMap::new(),
        externs: BTreeMap::new(),
        origins: BTreeMap::new(),
    };
    state.output.fns.clear();
    state
        .output
        .externs
        .retain(|x| x.generics.is_empty() || !native.contains(&x.name));
    state.output.top = input
        .top
        .map(|i| state.function(i, &Subst::new()))
        .transpose()?;
    state.output.exports.clear();
    for export in &input.exports {
        if input.fns[export.inst].generics.is_empty() {
            let mut export = export.clone();
            export.inst = state.function(export.inst, &Subst::new())?;
            state.output.exports.push(export);
        }
    }
    Ok((state.output, state.origins))
}

pub fn substitute(t: &Ty, s: &Subst) -> Ty {
    let sub = |a: &Ty| Box::new(substitute(a, s));
    match t {
        Ty::Param(n) => s.get(n).unwrap_or(t).clone(),
        Ty::Vec(a) => Ty::Vec(sub(a)),
        Ty::Array(a) => Ty::Array(sub(a)),
        Ty::Slice(a) => Ty::Slice(sub(a)),
        Ty::Option(a) => Ty::Option(sub(a)),
        Ty::Ref(a) => Ty::Ref(sub(a)),
        Ty::RefMut(a) => Ty::RefMut(sub(a)),
        Ty::SharedVar(true, a) => Ty::SharedVar(true, sub(a)),
        Ty::SharedVar(false, a) => Ty::SharedVar(false, sub(a)),
        Ty::Info(a) => Ty::Info(sub(a)),
        Ty::BudgetAnswer(a) => Ty::BudgetAnswer(sub(a)),
        Ty::Result(a, b) => Ty::Result(sub(a), sub(b)),
        Ty::Pair(a, b) => Ty::Pair(sub(a), sub(b)),
        Ty::HashMap(a, b) => Ty::HashMap(sub(a), sub(b)),
        Ty::Data(n, a) => Ty::Data(n.clone(), a.iter().map(|t| substitute(t, s)).collect()),
        Ty::Std(n, a) => Ty::Std(n.clone(), a.iter().map(|t| substitute(t, s)).collect()),
        Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
            params: f.params.iter().map(|t| substitute(t, s)).collect(),
            ret: substitute(&f.ret, s),
            ..**f
        })),
        _ => t.clone(),
    }
}
fn infer(pattern: &Ty, actual: &Ty, out: &mut Subst) -> Result<(), String> {
    if let Ty::Param(n) = pattern {
        if *actual != Ty::Infer
            && let Some(previous) = out.insert(n.clone(), actual.clone())
            && previous != *actual
        {
            return Err(crate::i18n::t!(
                "js-inconsistent-instantiation",
                name = n,
                a = format!("{previous:?}"),
                b = format!("{actual:?}")
            ));
        }
        return Ok(());
    }
    match (pattern, actual) {
        (Ty::Vec(a), Ty::Vec(b))
        | (Ty::Array(a), Ty::Array(b))
        | (Ty::Slice(a), Ty::Slice(b))
        | (Ty::Option(a), Ty::Option(b))
        | (Ty::Ref(a), Ty::Ref(b))
        | (Ty::RefMut(a), Ty::RefMut(b))
        | (Ty::SharedVar(true, a), Ty::SharedVar(true, b))
        | (Ty::SharedVar(false, a), Ty::SharedVar(false, b)) => infer(a, b, out)?,
        (Ty::Pair(a, b), Ty::Pair(c, d))
        | (Ty::Result(a, b), Ty::Result(c, d))
        | (Ty::HashMap(a, b), Ty::HashMap(c, d)) => {
            infer(a, c, out)?;
            infer(b, d, out)?;
        }
        (Ty::Data(n, a), Ty::Data(m, b)) if n == m => {
            for (a, b) in a.iter().zip(b) {
                infer(a, b, out)?;
            }
        }
        (Ty::Std(n, a), Ty::Std(m, b)) if n == m => {
            for (a, b) in a.iter().zip(b) {
                infer(a, b, out)?;
            }
        }
        (Ty::Fn(a), Ty::Fn(b)) => {
            for (a, b) in a.params.iter().zip(&b.params) {
                infer(a, b, out)?;
            }
            infer(&a.ret, &b.ret, out)?;
        }
        _ => {}
    }
    Ok(())
}
fn concrete(names: impl Iterator<Item = String>, s: &Subst) -> Result<Vec<Ty>, String> {
    names
        .map(|n| {
            let t = s
                .get(&n)
                .ok_or_else(|| crate::i18n::t!("js-no-concrete-instantiation", name = &n))?;
            let mut params = BTreeSet::new();
            t.params(&mut params);
            if !params.is_empty() || t.has_infer() {
                return Err(crate::i18n::t!(
                    "js-unresolved-type-argument",
                    name = &n,
                    ty = format!("{t:?}")
                ));
            }
            Ok(t.clone())
        })
        .collect()
}
struct Specializer<'a> {
    input: &'a Package,
    native: &'a BTreeSet<Name>,
    output: Package,
    functions: BTreeMap<(usize, Vec<Ty>), usize>,
    externs: BTreeMap<(Name, Vec<Ty>), Name>,
    origins: BTreeMap<Name, Name>,
}
impl Specializer<'_> {
    fn function(&mut self, id: usize, s: &Subst) -> Result<usize, String> {
        let mut f = self.input.fns[id].clone();
        let args = concrete(f.generics.iter().map(|(n, _)| n.clone()), s)?;
        if let Some(id) = self.functions.get(&(id, args.clone())) {
            return Ok(*id);
        }
        if self.output.fns.len() >= 4096 {
            return Err(crate::i18n::t!("js-specialization-limit", n = 4096u64));
        }
        let new = self.output.fns.len();
        self.functions.insert((id, args), new);
        f.id = new;
        f.generics.clear();
        for p in &mut f.params {
            p.ty = substitute(&p.ty, s);
        }
        f.ret = substitute(&f.ret, s);
        self.output.fns.push(f.clone()); // Reserve before visiting recursive calls.
        self.expr(&mut f.body, s)?;
        self.output.fns[new] = f;
        Ok(new)
    }
    fn block(&mut self, b: &mut Block, s: &Subst) -> Result<(), String> {
        for stmt in &mut b.stmts {
            match stmt {
                Stmt::Let { ty, init, .. } | Stmt::Var { ty, init, .. } => {
                    *ty = substitute(ty, s);
                    self.expr(init, s)?;
                }
                Stmt::Assign { target, value, .. } => {
                    target.ty = substitute(&target.ty, s);
                    self.expr(value, s)?;
                }
                Stmt::Expr(e) => self.expr(e, s)?,
                Stmt::While { cond, body, .. } => {
                    self.expr(cond, s)?;
                    self.block(body, s)?;
                }
                Stmt::Return { value: Some(e), .. } => self.expr(e, s)?,
                Stmt::Return { value: None, .. } => {}
            }
        }
        if let Some(e) = &mut b.tail {
            self.expr(e, s)?;
        }
        Ok(())
    }
    fn pat(p: &mut Pat, s: &Subst) {
        match p {
            Pat::Bind(_, t) => *t = substitute(t, s),
            Pat::Ctor { fields, .. } => {
                for p in fields {
                    Self::pat(p, s);
                }
            }
            _ => {}
        }
    }
    fn expr(&mut self, e: &mut Expr, s: &Subst) -> Result<(), String> {
        e.ty = substitute(&e.ty, s);
        // Every expression is visited exactly once, including suspended handler arms.
        match &mut e.kind {
            ExprKind::Block(b) => self.block(b, s)?,
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                self.expr(a, s)?;
                self.expr(b, s)?;
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.expr(cond, s)?;
                self.expr(then, s)?;
                if let Some(b) = otherwise {
                    self.expr(b, s)?;
                }
            }
            ExprKind::Match(m) => {
                self.expr(&mut m.scrut, s)?;
                for a in &mut m.arms {
                    Self::pat(&mut a.pat, s);
                    if let Some(g) = &mut a.guard {
                        self.expr(g, s)?;
                    }
                    self.expr(&mut a.body, s)?;
                }
            }
            ExprKind::Closure(c) => {
                for (_, t) in &mut c.params {
                    *t = substitute(t, s);
                }
                c.ret = substitute(&c.ret, s);
                c.fn_ty.params = c.fn_ty.params.iter().map(|t| substitute(t, s)).collect();
                c.fn_ty.ret = substitute(&c.fn_ty.ret, s);
                self.expr(&mut c.body, s)?;
            }
            ExprKind::Handle(h) => {
                h.body_ty = substitute(&h.body_ty, s);
                h.result = substitute(&h.result, s);
                h.host_ret = h.host_ret.as_ref().map(|t| substitute(t, s));
                self.expr(&mut h.body, s)?;
                if let Some(r) = &mut h.ret {
                    Self::pat(&mut r.pat, s);
                    self.expr(&mut r.body, s)?;
                }
                for a in h.direct.iter_mut().chain(&mut h.aborts).chain(&mut h.susp) {
                    for t in &mut a.params {
                        *t = substitute(t, s);
                    }
                    a.k_ans = substitute(&a.k_ans, s);
                    if let Some(instance) = &mut a.instance {
                        instance.type_args = instance
                            .type_args
                            .iter()
                            .map(|t| substitute(t, s))
                            .collect();
                        instance.params =
                            instance.params.iter().map(|t| substitute(t, s)).collect();
                        instance.answer = substitute(&instance.answer, s);
                    }
                    for p in &mut a.pats {
                        Self::pat(p, s);
                    }
                    if let Some(g) = &mut a.guard {
                        self.expr(g, s)?;
                    }
                    self.expr(&mut a.body, s)?;
                }
            }
            ExprKind::Budget(b) => {
                self.expr(&mut b.steps, s)?;
                self.expr(&mut b.body, s)?;
            }
            _ => {
                for operand in e.operands_mut() {
                    self.expr(operand, s)?;
                }
            }
        }
        match &mut e.kind {
            ExprKind::Ref(p) | ExprKind::RefMut(p) => p.ty = substitute(&p.ty, s),
            ExprKind::Remap { to, .. } => *to = substitute(to, s),
            ExprKind::Perform(p) => {
                p.result = substitute(&p.result, s);
                if let Some(instance) = &mut p.instance {
                    instance.type_args = instance
                        .type_args
                        .iter()
                        .map(|t| substitute(t, s))
                        .collect();
                    instance.params = instance.params.iter().map(|t| substitute(t, s)).collect();
                    instance.answer = substitute(&instance.answer, s);
                }
            }
            ExprKind::FnValue { inst, targs } => {
                let f = &self.input.fns[*inst];
                *targs = targs.iter().map(|t| substitute(t, s)).collect();
                if targs.len() != f.generics.len() {
                    return Err(crate::i18n::t!(
                        "js-incomplete-type-arguments",
                        name = f.source.to_string()
                    ));
                }
                let subst: Subst = f
                    .generics
                    .iter()
                    .zip(targs.iter())
                    .map(|((name, _), ty)| (name.clone(), ty.clone()))
                    .collect();
                *inst = self.function(*inst, &subst)?;
                targs.clear();
            }
            ExprKind::Call(c) => {
                c.targs = c.targs.iter().map(|t| substitute(t, s)).collect();
                match &mut c.callee {
                    Callee::Inst(id) => {
                        let f = &self.input.fns[*id];
                        let mut subst = Subst::new();
                        for (p, a) in f.params.iter().zip(&c.args) {
                            infer(&p.ty, &a.ty, &mut subst)?;
                        }
                        infer(&f.ret, &e.ty, &mut subst)?;
                        for ((n, _), t) in f.generics.iter().zip(&c.targs) {
                            if *t != Ty::Infer {
                                subst.insert(n.clone(), t.clone());
                            }
                        }
                        *id = self.function(*id, &subst)?;
                        c.targs.clear();
                    }
                    Callee::Extern(name) if self.native.contains(name) => {
                        let x = self
                            .input
                            .externs
                            .iter()
                            .find(|x| x.name == *name)
                            .expect("checked extern");
                        if !x.generics.is_empty() {
                            let mut subst = Subst::new();
                            for ((_, p, pass), a) in x.params.iter().zip(&c.args) {
                                let actual = match (pass, &a.ty) {
                                    (Pass::Ref, Ty::Ref(t)) | (Pass::RefMut, Ty::RefMut(t)) => {
                                        t.as_ref()
                                    }
                                    _ => &a.ty,
                                };
                                infer(p, actual, &mut subst)?;
                            }
                            infer(&x.ret, &e.ty, &mut subst)?;
                            let types = concrete(x.generics.iter().cloned(), &subst)?;
                            let key = (name.clone(), types);
                            let alias = if let Some(alias) = self.externs.get(&key) {
                                alias.clone()
                            } else {
                                let mut suffix = self.externs.len();
                                let alias = loop {
                                    let candidate = format!("__tauto_wasm_{suffix}");
                                    if !self
                                        .input
                                        .externs
                                        .iter()
                                        .any(|x| x.name.as_str() == candidate)
                                        && !self.origins.keys().any(|n| n.as_str() == candidate)
                                    {
                                        break Name::Global(tauto::identity::DeclRef::fresh(
                                            candidate,
                                        ));
                                    }
                                    suffix += 1;
                                };
                                let mut def = x.clone();
                                def.name = alias.clone();
                                def.generics.clear();
                                for (_, t, _) in &mut def.params {
                                    *t = substitute(t, &subst);
                                }
                                def.ret = substitute(&def.ret, &subst);
                                self.output.externs.push(def);
                                self.origins.insert(alias.clone(), name.clone());
                                self.externs.insert(key, alias.clone());
                                alias
                            };
                            *name = alias;
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        Ok(())
    }
}

/// Native Rust frames may be suspended once, but cannot be discarded or copied.
/// Handled operations inside the callback do not cross that native frame.
pub fn abandoning_callback(pkg: &Package, e: &Expr) -> bool {
    fn block(
        pkg: &Package,
        b: &Block,
        handled: &BTreeSet<usize>,
        seen: &mut BTreeSet<usize>,
    ) -> bool {
        b.stmts.iter().any(|s| match s {
            Stmt::Let { init, .. } | Stmt::Var { init, .. } => walk(pkg, init, handled, seen),
            Stmt::Assign { value, .. } | Stmt::Expr(value) => walk(pkg, value, handled, seen),
            Stmt::Return { value, .. } => {
                value.as_ref().is_some_and(|v| walk(pkg, v, handled, seen))
            }
            Stmt::While { cond, body, .. } => {
                walk(pkg, cond, handled, seen) || block(pkg, body, handled, seen)
            }
        }) || b.tail.as_ref().is_some_and(|e| walk(pkg, e, handled, seen))
    }
    fn walk(
        pkg: &Package,
        e: &Expr,
        handled: &BTreeSet<usize>,
        seen: &mut BTreeSet<usize>,
    ) -> bool {
        match &e.kind {
            ExprKind::Perform(p)
                if !handled.contains(&p.op)
                    && matches!(p.quant, Quant::Zero | Quant::AtMostOne | Quant::Many) =>
            {
                true
            }
            ExprKind::Handle(h) => {
                let mut inner = handled.clone();
                inner.extend(
                    h.direct
                        .iter()
                        .chain(&h.aborts)
                        .chain(&h.susp)
                        .map(|a| a.op),
                );
                walk(pkg, &h.body, &inner, &mut seen.clone())
                    || h.ret
                        .as_ref()
                        .is_some_and(|r| walk(pkg, &r.body, handled, seen))
                    || h.direct.iter().chain(&h.aborts).chain(&h.susp).any(|a| {
                        a.guard
                            .as_ref()
                            .is_some_and(|g| walk(pkg, g, handled, seen))
                            || walk(pkg, &a.body, handled, seen)
                    })
            }
            ExprKind::Read { .. } => {
                let ty = match &e.ty {
                    Ty::Ref(t) | Ty::RefMut(t) => t.as_ref(),
                    t => t,
                };
                matches!(ty,Ty::Fn(f) if f.tier!=Tier::S)
            }
            ExprKind::FnValue { inst, .. } => {
                seen.insert(*inst) && walk(pkg, &pkg.fns[*inst].body, handled, seen)
            }
            ExprKind::Call(c) => {
                let crosses = match &c.callee {
                    Callee::Inst(id) => {
                        seen.insert(*id) && walk(pkg, &pkg.fns[*id].body, handled, seen)
                    }
                    Callee::Value(v) => walk(pkg, v, handled, seen),
                    Callee::Local(_) => c.tier != Tier::S,
                    _ => false,
                };
                crosses || c.args.iter().any(|a| walk(pkg, a, handled, seen))
            }
            ExprKind::Closure(c) => walk(pkg, &c.body, handled, seen),
            ExprKind::Block(b) => block(pkg, b, handled, seen),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                walk(pkg, cond, handled, seen)
                    || walk(pkg, then, handled, seen)
                    || otherwise
                        .as_ref()
                        .is_some_and(|v| walk(pkg, v, handled, seen))
            }
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                walk(pkg, a, handled, seen) || walk(pkg, b, handled, seen)
            }
            ExprKind::Match(m) => {
                walk(pkg, &m.scrut, handled, seen)
                    || m.arms.iter().any(|a| {
                        a.guard
                            .as_ref()
                            .is_some_and(|g| walk(pkg, g, handled, seen))
                            || walk(pkg, &a.body, handled, seen)
                    })
            }
            ExprKind::Budget(b) => {
                walk(pkg, &b.steps, handled, seen) || walk(pkg, &b.body, handled, seen)
            }
            _ => e
                .clone()
                .operands_mut()
                .iter()
                .any(|e| walk(pkg, e, handled, seen)),
        }
    }
    walk(pkg, e, &BTreeSet::new(), &mut BTreeSet::new())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn generic_identity() -> Package {
        let local = Local {
            id: 0,
            name: "value".into(),
            repr: Repr::Plain,
        };
        Package {
            fns: vec![FnInst {
                id: 0,
                source: "identity".into(),
                rust_name: "identity__s".into(),
                tier: Tier::S,
                generics: vec![("B".into(), BTreeSet::new()), ("A".into(), BTreeSet::new())],
                params: vec![Param {
                    local: local.clone(),
                    ty: Ty::Param("A".into()),
                }],
                ret: Ty::Param("A".into()),
                body: Expr {
                    kind: ExprKind::Read {
                        local,
                        how: Use::Move,
                    },
                    ty: Ty::Param("A".into()),
                    span: Span::default(),
                },
                span: Span::default(),
            }],
            ..Package::default()
        }
    }

    fn value(targs: Vec<Ty>) -> Expr {
        Expr {
            kind: ExprKind::FnValue { inst: 0, targs },
            ty: Ty::Fn(Box::new(FnTy {
                params: vec![Ty::Param("B".into())],
                ret: Ty::Param("B".into()),
                kind: Kind::Shared,
                tier: Tier::S,
            })),
            span: Span::default(),
        }
    }

    fn state<'a>(input: &'a Package, native: &'a BTreeSet<Name>) -> Specializer<'a> {
        Specializer {
            input,
            native,
            output: Package::default(),
            functions: BTreeMap::new(),
            externs: BTreeMap::new(),
            origins: BTreeMap::new(),
        }
    }

    #[test]
    fn function_values_use_checked_declaration_order_in_the_callers_context() {
        let input = generic_identity();
        let native = BTreeSet::new();
        let mut state = state(&input, &native);
        let mut expression = value(vec![Ty::Param("A".into()), Ty::Param("B".into())]);
        let caller = Subst::from([("A".into(), Ty::Text), ("B".into(), Ty::Int(Width::W64))]);
        state.expr(&mut expression, &caller).unwrap();
        // B is absent from the signature, so signature-based inference cannot
        // recover this instantiation; the checked vector owns its order.
        assert!(
            state
                .functions
                .contains_key(&(0, vec![Ty::Text, Ty::Int(Width::W64)]))
        );
        let ExprKind::FnValue { inst, targs } = expression.kind else {
            panic!("function value")
        };
        assert!(targs.is_empty());
        assert!(state.output.fns[inst].generics.is_empty());
        assert_eq!(state.output.fns[inst].params[0].ty, Ty::Int(Width::W64));
        assert_eq!(state.output.fns[inst].ret, Ty::Int(Width::W64));
    }

    #[test]
    fn function_values_reject_missing_or_unresolved_checked_arguments() {
        let input = generic_identity();
        let native = BTreeSet::new();
        for (arguments, expected) in [
            (vec![], "incomplete checked type arguments"),
            (vec![Ty::Text], "incomplete checked type arguments"),
            (
                vec![Ty::Text, Ty::Infer],
                "unresolved JavaScript type argument",
            ),
        ] {
            let mut state = state(&input, &native);
            let mut expression = value(arguments);
            let error = state.expr(&mut expression, &Subst::new()).unwrap_err();
            assert!(error.contains(expected), "{error}");
            assert!(state.output.fns.is_empty());
        }
    }
}
