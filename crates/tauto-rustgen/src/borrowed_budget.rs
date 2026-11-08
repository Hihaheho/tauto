//! Private borrowed helpers in the guarded qualified synchronous budget path.
//!
//! A retained local's generated clone can be replaced by a borrow only when
//! its complete immutable value graph and the helper's reads are known. The
//! ordinary functions, including synchronous budget helpers, keep their ABI.

use std::collections::{BTreeMap, BTreeSet};

use tauto_nir::*;

use tauto_message::{Message, msg};

use crate::{Bindings, Gen, Sources};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BorrowReason {
    pub code: &'static str,
    pub message: String,
}

/// Selection of a private helper, independent of budget eligibility.
#[derive(Debug, Clone)]
pub struct BorrowDiagnostic {
    pub instance: InstId,
    pub function: String,
    pub span: Span,
    pub type_arguments: Vec<Ty>,
    pub borrowed_parameters: Vec<usize>,
    pub reason: Option<BorrowReason>,
}

pub fn borrowed_budget_diagnostics(
    pkg: &Package,
    sources: &Sources<'_>,
    bindings: &Bindings,
) -> Vec<BorrowDiagnostic> {
    crate::item::emit_with_borrow_diagnostics(pkg, sources, bindings).2
}

type Context = BTreeMap<String, Ty>;
pub(crate) type Key = (InstId, Vec<Ty>);

#[derive(Clone)]
pub(crate) struct Variant {
    pub function: FnInst,
    pub context: Context,
    pub parameters: BTreeSet<usize>,
}

#[derive(Default)]
pub(crate) struct Variants {
    pub functions: BTreeMap<Key, Variant>,
    pub active: Option<Context>,
    pub owned: BTreeMap<Key, Variant>,
    pub owned_active: Option<Context>,
    pub diagnostics: Vec<BorrowDiagnostic>,
}

fn reason(code: &'static str, message: Message) -> BorrowReason {
    BorrowReason {
        code,
        message: message.to_string(),
    }
}

fn scalar(t: &Ty) -> bool {
    matches!(
        t,
        Ty::Unit | Ty::Bool | Ty::Int(_) | Ty::Float | Ty::Float32
    ) && !matches!(t, Ty::Int(Width::Nat))
}

fn resolve(t: &Ty, context: &Context) -> Ty {
    match t {
        Ty::Param(name) => context.get(name).cloned().unwrap_or(Ty::Infer),
        Ty::Data(name, args) => Ty::Data(
            name.clone(),
            args.iter().map(|t| resolve(t, context)).collect(),
        ),
        _ => t.clone(),
    }
}

fn context(f: &FnInst, args: &[Ty]) -> Result<Context, BorrowReason> {
    if args.len() != f.generics.len() {
        return Err(reason(
            "generic-context",
            msg!("rustgen-borrow-generic-context"),
        ));
    }
    Ok(f.generics
        .iter()
        .zip(args)
        .map(|((name, _), ty)| (name.clone(), ty.clone()))
        .collect())
}

impl Gen<'_> {
    /// The type closure must have only generated, immutable clone operations.
    /// A host lifetime assertion does not make an opaque clone a read.
    pub(crate) fn borrow_type(&self, t: &Ty, seen: &mut BTreeSet<Ty>) -> bool {
        if scalar(t) || matches!(t, Ty::Text) {
            return true;
        }
        if let Ty::Option(inner) = t {
            return self.borrow_type(inner, seen);
        }
        let Ty::Data(name, args) = t else {
            return false;
        };
        if self.bindings.types.contains_key(name) {
            return false;
        }
        let Some(d) = self.data(name) else {
            return false;
        };
        if !d.clone || d.linear || d.view || d.generics.len() != args.len() {
            return false;
        }
        if seen.contains(t) {
            return true;
        }
        if seen.len() >= 128 {
            return false;
        }
        seen.insert(t.clone());
        let types = d
            .generics
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        args.iter().all(|t| self.borrow_type(t, seen))
            && d.ctors.iter().all(|c| {
                c.fields.iter().all(|f| {
                    f.indirect != Indirect::Unique
                        && self.borrow_type(&resolve(&f.ty, &types), seen)
                })
            })
    }

    fn borrow_copy(&self, t: &Ty) -> bool {
        scalar(t)
            || matches!(t, Ty::Data(name, args) if self.data(name).is_some_and(|d| d.copy) && args.iter().all(|t| self.borrow_copy(t)))
    }

    fn borrow_shape(&self, key: &Key) -> Result<(Context, BTreeSet<usize>), BorrowReason> {
        let f = &self.pkg.fns[key.0];
        let types = context(f, &key.1)?;
        if !matches!(f.tier, Tier::S | Tier::O) {
            return Err(reason(
                "helper-control",
                msg!("rustgen-borrow-helper-control"),
            ));
        }
        // The Rust declaration remains generic. Returning a type parameter is
        // not a scalar signature, even if one concrete call resolves it so.
        if !scalar(&f.ret) {
            return Err(reason(
                "escaping-result",
                msg!("rustgen-borrow-escaping-result"),
            ));
        }
        if key
            .1
            .iter()
            .any(|t| !self.borrow_type(t, &mut BTreeSet::new()))
        {
            return Err(reason(
                "generic-context",
                msg!("rustgen-borrow-generic-context-2"),
            ));
        }
        let mut parameters = BTreeSet::new();
        for (index, p) in f.params.iter().enumerate() {
            let ty = resolve(&p.ty, &types);
            if p.local.repr != Repr::Plain || !self.borrow_type(&ty, &mut BTreeSet::new()) {
                return Err(reason(
                    "parameter-ownership",
                    msg!("rustgen-borrow-parameter-ownership"),
                ));
            }
            if !self.borrow_copy(&ty) {
                parameters.insert(index);
            }
        }
        Ok((types, parameters))
    }

    fn borrow_graph(&self, root: Key) -> Result<BTreeMap<Key, Variant>, BorrowReason> {
        let mut pending = vec![root];
        let mut functions = BTreeMap::new();
        while let Some(key) = pending.pop() {
            if functions.contains_key(&key) {
                continue;
            }
            if functions.len() >= 256 {
                return Err(reason(
                    "analysis-limit",
                    msg!("rustgen-borrow-analysis-limit"),
                ));
            }
            let (types, parameters) = self.borrow_shape(&key)?;
            let original = &self.pkg.fns[key.0];
            let mut function = original.clone();
            let mut tracked = BTreeMap::new();
            for &index in &parameters {
                let p = &mut function.params[index];
                tracked.insert(p.local.id, p.local.id);
                p.local.repr = Repr::Ref;
                p.ty = Ty::Ref(Box::new(p.ty.clone()));
            }
            let mut proof = Reads {
                generator: self,
                types: &types,
                tracked,
                cursors: BTreeMap::new(),
                scalars: BTreeSet::new(),
                calls: Vec::new(),
            };
            proof.expr(&mut function.body)?;
            pending.extend(proof.calls);
            // Borrowing a concrete cloneable type must also typecheck in the
            // private generic declaration. No public bound is changed.
            for (_, bounds) in &mut function.generics {
                bounds.insert(Bound::Clone);
            }
            functions.insert(
                key,
                Variant {
                    function,
                    context: types,
                    parameters,
                },
            );
        }
        Ok(functions)
    }

    pub(crate) fn borrowed_budget_call(&mut self, c: &CallNode) -> Option<(String, Vec<Expr>)> {
        let Callee::Inst(inst) = c.callee else {
            return None;
        };
        let outer = self
            .borrowed_budget
            .active
            .clone()
            .or_else(|| self.borrowed_budget.owned_active.clone())
            .unwrap_or_default();
        let key = (
            inst,
            c.targs
                .iter()
                .map(|t| resolve(t, &outer))
                .collect::<Vec<_>>(),
        );
        let f = &self.pkg.fns[inst];
        // Scalar-only calls cannot remove an ownership operation.
        if !f
            .params
            .iter()
            .any(|p| matches!(p.ty, Ty::Data(..) | Ty::Param(_)))
        {
            return None;
        }
        let result = (|| {
            if std::env::var_os("TAUTO_KEEP_OWNED").is_some() {
                return Err(reason("keep-owned", msg!("rustgen-borrow-keep-owned")));
            }
            let (types, parameters) = self.borrow_shape(&key)?;
            if parameters.is_empty() {
                return Ok(None);
            }
            if c.args.len() != f.params.len() {
                return Err(reason(
                    "argument-shape",
                    msg!("rustgen-borrow-argument-shape"),
                ));
            }
            for (index, a) in c.args.iter().enumerate() {
                if parameters.contains(&index) {
                    let retained = retained_place(a).is_some();
                    let inherited = self.borrowed_budget.active.is_some()
                        && matches!(&a.kind,
                        ExprKind::Read { local, how: Use::Place } if local.repr == Repr::Ref);
                    if !retained && !inherited {
                        return Err(reason(
                            "owner-not-retained",
                            msg!("rustgen-borrow-owner-not-retained"),
                        ));
                    }
                } else if self.borrowed_budget.active.is_none()
                    && !self.trivial_borrow_argument(a, &types)
                {
                    return Err(reason(
                        "argument-snapshot",
                        msg!("rustgen-borrow-argument-snapshot"),
                    ));
                }
            }
            if !self.borrowed_budget.functions.contains_key(&key) {
                let graph = self.borrow_graph(key.clone())?;
                for (key, mut variant) in graph {
                    if variant.parameters.is_empty()
                        || self.borrowed_budget.functions.contains_key(&key)
                    {
                        continue;
                    }
                    let mut serial = self.borrowed_budget.functions.len();
                    let name = loop {
                        let name = format!("__tauto_budget_borrow_{}_{}", key.0, serial);
                        if !self.pkg.fns.iter().any(|f| {
                            f.rust_name == name || f.rust_name == format!("{name}_budget_sync")
                        }) && !self.pkg.datas.iter().any(|d| {
                            Self::data_name(self.pkg, &d.name).to_string()
                                == format!("{name}_budget_sync")
                        }) && !self
                            .borrowed_budget
                            .functions
                            .values()
                            .any(|v| v.function.rust_name == name)
                        {
                            break name;
                        }
                        serial += 1;
                    };
                    variant.function.rust_name = name;
                    self.borrowed_budget.functions.insert(key, variant);
                }
            }
            let variant = &self.borrowed_budget.functions[&key];
            let mut args = c.args.clone();
            for &index in &parameters {
                let a = &mut args[index];
                if let Some(place) = retained_place(a) {
                    a.kind = ExprKind::TempRef(Box::new(place));
                } else {
                    let ExprKind::Read { local, .. } = &a.kind else {
                        unreachable!()
                    };
                    a.kind = ExprKind::Ref(Place {
                        local: local.clone(),
                        path: Vec::new(),
                        ty: a.ty.clone(),
                    });
                }
                a.ty = Ty::Ref(Box::new(a.ty.clone()));
            }
            Ok(Some((
                format!("{}_budget_sync", variant.function.rust_name),
                args,
                parameters,
            )))
        })();
        match result {
            Ok(Some((name, args, parameters))) => {
                self.borrowed_budget.diagnostics.push(BorrowDiagnostic {
                    instance: inst,
                    function: f.source.to_string(),
                    span: c.span,
                    type_arguments: key.1,
                    borrowed_parameters: parameters.into_iter().collect(),
                    reason: None,
                });
                Some((name, args))
            }
            Ok(None) => None,
            Err(reason) => {
                self.borrowed_budget.diagnostics.push(BorrowDiagnostic {
                    instance: inst,
                    function: f.source.to_string(),
                    span: c.span,
                    type_arguments: key.1,
                    borrowed_parameters: Vec::new(),
                    reason: Some(reason),
                });
                None
            }
        }
    }

    pub(crate) fn owned_budget_call(&mut self, c: &CallNode) -> Option<String> {
        if self.borrowed_budget.active.is_some() || std::env::var_os("TAUTO_KEEP_OWNED").is_some() {
            return None;
        }
        let Callee::Inst(inst) = c.callee else {
            return None;
        };
        let f = &self.pkg.fns[inst];
        if f.tier != Tier::O {
            return None;
        }
        let outer = self
            .borrowed_budget
            .owned_active
            .clone()
            .unwrap_or_default();
        let key = (
            inst,
            c.targs
                .iter()
                .map(|t| resolve(t, &outer))
                .collect::<Vec<_>>(),
        );
        if !self.borrowed_budget.owned.contains_key(&key) {
            if self.borrowed_budget.owned.len() >= 4096 {
                return None;
            }
            let types = context(f, &key.1).ok()?;
            let mut function = f.clone();
            let mut serial = self.borrowed_budget.owned.len();
            loop {
                let name = format!("__tauto_budget_owned_{}_{}", inst, serial);
                if !self
                    .pkg
                    .fns
                    .iter()
                    .any(|f| f.rust_name == name || f.rust_name == format!("{name}_budget_sync"))
                    && !self
                        .borrowed_budget
                        .owned
                        .values()
                        .any(|v| v.function.rust_name == name)
                    && !self.pkg.datas.iter().any(|d| {
                        Self::data_name(self.pkg, &d.name).to_string()
                            == format!("{name}_budget_sync")
                    })
                {
                    function.rust_name = name;
                    break;
                }
                serial += 1;
            }
            self.borrowed_budget.owned.insert(
                key.clone(),
                Variant {
                    function,
                    context: types,
                    parameters: BTreeSet::new(),
                },
            );
        }
        Some(format!(
            "{}_budget_sync",
            self.borrowed_budget.owned[&key].function.rust_name
        ))
    }

    fn trivial_borrow_argument(&self, a: &Expr, types: &Context) -> bool {
        self.borrow_copy(&resolve(&a.ty, types))
            && match &a.kind {
                ExprKind::Unit | ExprKind::Int(_) | ExprKind::Bool(_) => true,
                ExprKind::Read { local, .. } => local.repr == Repr::Plain,
                _ => false,
            }
    }
}

fn retained_place(e: &Expr) -> Option<Expr> {
    fn place(e: &mut Expr) -> bool {
        match &mut e.kind {
            ExprKind::Read { local, how } if local.repr == Repr::Plain && *how != Use::Move => {
                *how = Use::Place;
                true
            }
            ExprKind::Field {
                base,
                how,
                indirect: Indirect::None,
                ..
            } if *how != Use::Move => {
                *how = Use::Place;
                place(base)
            }
            _ => false,
        }
    }
    if !matches!(
        e.kind,
        ExprKind::Read {
            how: Use::Clone,
            ..
        } | ExprKind::Field {
            how: Use::Clone,
            indirect: Indirect::None,
            ..
        }
    ) {
        return None;
    }
    let mut result = e.clone();
    place(&mut result).then_some(result)
}

/// This is an exhaustive visitor, not `Expr::walk`: omitted handler arms and
/// assignment targets must never turn an opaque use into a read proof.
struct Reads<'g, 'a, 't> {
    generator: &'g Gen<'a>,
    types: &'t Context,
    // Each reference is anchored to an original retained parameter, not to
    // the cursor slot or the arm-local binding from which it was obtained.
    tracked: BTreeMap<u32, u32>,
    cursors: BTreeMap<u32, u32>,
    scalars: BTreeSet<u32>,
    calls: Vec<Key>,
}

impl Reads<'_, '_, '_> {
    fn origin(&self, e: &Expr) -> Option<u32> {
        match &e.kind {
            ExprKind::Read { local, .. } if local.repr == Repr::Plain => {
                self.tracked.get(&local.id).copied()
            }
            _ => None,
        }
    }

    fn reference(&self, e: &mut Expr) {
        let ExprKind::Read { local, how } = &mut e.kind else {
            unreachable!()
        };
        local.repr = Repr::Ref;
        *how = Use::Place;
        e.ty = Ty::Ref(Box::new(e.ty.clone()));
    }

    fn copy(&self, e: &Expr) -> bool {
        self.generator.borrow_copy(&resolve(&e.ty, self.types))
    }

    fn expr(&mut self, e: &mut Expr) -> Result<(), BorrowReason> {
        let copy = self.copy(e);
        match &mut e.kind {
            ExprKind::Unit | ExprKind::Int(_) | ExprKind::Float(_) | ExprKind::Bool(_) => {}
            ExprKind::Read { local, how } => {
                if !copy {
                    return Err(reason("owned-use", msg!("rustgen-borrow-owned-use")));
                }
                if local.repr != Repr::Plain {
                    return Err(reason("mutable-read", msg!("rustgen-borrow-mutable-read")));
                }
                if self.tracked.contains_key(&local.id) {
                    local.repr = Repr::Ref;
                    *how = Use::Clone;
                }
            }
            ExprKind::Field {
                base,
                how,
                indirect,
                ..
            } => {
                if !copy || *indirect != Indirect::None {
                    return Err(reason("field-escape", msg!("rustgen-borrow-field-escape")));
                }
                self.field_base(base)?;
                // A reference must not turn a consumed generic field into a
                // move, so the field is cloned.
                *how = Use::Clone;
            }
            ExprKind::Call(c) => {
                let Callee::Inst(inst) = c.callee else {
                    return Err(reason("opaque-call", msg!("rustgen-borrow-opaque-call")));
                };
                let key = (
                    inst,
                    c.targs.iter().map(|t| resolve(t, self.types)).collect(),
                );
                let (_, parameters) = self.generator.borrow_shape(&key)?;
                if c.args.len() != self.generator.pkg.fns[inst].params.len() {
                    return Err(reason(
                        "argument-shape",
                        msg!("rustgen-borrow-argument-shape-2"),
                    ));
                }
                for (index, arg) in c.args.iter_mut().enumerate() {
                    if parameters.contains(&index) {
                        if self.origin(arg).is_none() {
                            return Err(reason("owned-child", msg!("rustgen-borrow-owned-child")));
                        }
                        let ExprKind::Read { local, how } = &mut arg.kind else {
                            unreachable!()
                        };
                        local.repr = Repr::Ref;
                        *how = Use::Place;
                    } else {
                        self.expr(arg)?;
                    }
                }
                self.calls.push(key);
            }
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => {
                for a in args {
                    self.expr(a)?;
                }
            }
            ExprKind::Not(a) => self.expr(a)?,
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                self.expr(a)?;
                self.expr(b)?;
            }
            ExprKind::Ctor { fields, .. } if copy => {
                for (_, f) in fields {
                    self.expr(f)?;
                }
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.expr(cond)?;
                self.expr(then)?;
                if let Some(o) = otherwise {
                    self.expr(o)?;
                }
            }
            ExprKind::Match(m) => {
                if m.by_ref || m.arms.iter().any(|a| a.guard.is_some()) {
                    return Err(reason("match-borrow", msg!("rustgen-borrow-match-borrow")));
                }
                let origin = self.origin(&m.scrut);
                if origin.is_some() {
                    let ExprKind::Read { local, .. } = &mut m.scrut.kind else {
                        unreachable!()
                    };
                    local.repr = Repr::Ref;
                    let place = Place {
                        local: local.clone(),
                        path: Vec::new(),
                        ty: m.scrut.ty.clone(),
                    };
                    m.scrut.kind = ExprKind::Ref(place);
                    m.scrut.ty = Ty::Ref(Box::new(m.scrut.ty.clone()));
                    m.by_ref = true;
                } else {
                    self.expr(&mut m.scrut)?;
                }
                for arm in &mut m.arms {
                    let saved = self.tracked.clone();
                    if let Some(root) = origin {
                        self.pattern(&mut arm.pat, root)?;
                    }
                    self.expr(&mut arm.body)?;
                    self.tracked = saved;
                }
            }
            ExprKind::Block(b) => self.block(b)?,
            ExprKind::Ctor { .. }
            | ExprKind::Text(_)
            | ExprKind::Declaration(_)
            | ExprKind::FnValue { .. }
            | ExprKind::Closure(_)
            | ExprKind::Perform(_)
            | ExprKind::Handle(_)
            | ExprKind::Inject { .. }
            | ExprKind::Remap { .. }
            | ExprKind::Ref(_)
            | ExprKind::RefMut(_)
            | ExprKind::TempRef(_)
            | ExprKind::Deref { .. }
            | ExprKind::Shown(_)
            | ExprKind::Budget(_)
            | ExprKind::Unreachable(_)
            | ExprKind::FnCast(_) => {
                return Err(reason("opaque-use", msg!("rustgen-borrow-opaque-use")));
            }
        }
        Ok(())
    }

    /// The invariant is fixed at each cursor declaration: every value ever
    /// stored in that slot is a root or substructure of the same retained
    /// parameter. Checking all assignments under that invariant proves both
    /// loop backedges and branch joins without speculative AST rewriting.
    fn block(&mut self, b: &mut Block) -> Result<(), BorrowReason> {
        let saved = (
            self.tracked.clone(),
            self.cursors.clone(),
            self.scalars.clone(),
        );
        for stmt in &mut b.stmts {
            match stmt {
                Stmt::Let {
                    local, ty, init, ..
                } if local.repr == Repr::Plain => {
                    if !self.copy(init)
                        && let Some(root) = self.origin(init)
                    {
                        self.reference(init);
                        self.tracked.insert(local.id, root);
                        local.repr = Repr::Ref;
                        *ty = Ty::Ref(Box::new(ty.clone()));
                    } else {
                        self.expr(init)?;
                    }
                }
                Stmt::Var {
                    local, ty, init, ..
                } if local.repr == Repr::Plain => {
                    if scalar(&resolve(ty, self.types)) {
                        self.expr(init)?;
                        self.scalars.insert(local.id);
                    } else if let Some(root) = self.origin(init) {
                        self.reference(init);
                        self.tracked.insert(local.id, root);
                        self.cursors.insert(local.id, root);
                        // The slot stores a reference, but remains Plain so
                        // assignment rebinds it rather than writing through it.
                        *ty = Ty::Ref(Box::new(ty.clone()));
                    } else {
                        return Err(reason(
                            "cursor-origin",
                            msg!("rustgen-borrow-cursor-origin"),
                        ));
                    }
                }
                Stmt::Assign { target, value, .. } => {
                    if target.local.repr != Repr::Plain || !target.path.is_empty() {
                        return Err(reason(
                            "helper-mutation",
                            msg!("rustgen-borrow-helper-mutation"),
                        ));
                    }
                    if let Some(root) = self.cursors.get(&target.local.id) {
                        if self.origin(value) != Some(*root) {
                            return Err(reason(
                                "cursor-origin",
                                msg!("rustgen-borrow-cursor-origin-2"),
                            ));
                        }
                        self.reference(value);
                    } else if self.scalars.contains(&target.local.id) {
                        self.expr(value)?;
                    } else {
                        return Err(reason(
                            "helper-mutation",
                            msg!("rustgen-borrow-helper-mutation-2"),
                        ));
                    }
                }
                Stmt::While { cond, body, .. } => {
                    self.expr(cond)?;
                    self.block(body)?;
                }
                Stmt::Expr(e) => self.expr(e)?,
                Stmt::Return { value, .. } => {
                    if let Some(e) = value {
                        self.expr(e)?;
                    }
                }
                Stmt::Let { .. } | Stmt::Var { .. } => {
                    return Err(reason(
                        "helper-mutation",
                        msg!("rustgen-borrow-helper-mutation-3"),
                    ));
                }
            }
            if self.tracked.len() + self.scalars.len() > 4096 {
                return Err(reason(
                    "analysis-limit",
                    msg!("rustgen-borrow-analysis-limit-2"),
                ));
            }
        }
        if let Some(e) = &mut b.tail {
            self.expr(e)?;
        }
        (self.tracked, self.cursors, self.scalars) = saved;
        Ok(())
    }

    fn field_base(&mut self, e: &mut Expr) -> Result<(), BorrowReason> {
        match &mut e.kind {
            ExprKind::Read { local, how } if local.repr == Repr::Plain => {
                if self.tracked.contains_key(&local.id) {
                    local.repr = Repr::Ref;
                }
                *how = Use::Place;
                Ok(())
            }
            ExprKind::Field {
                base,
                indirect: Indirect::None,
                ..
            } => self.field_base(base),
            _ => Err(reason("field-base", msg!("rustgen-borrow-field-base"))),
        }
    }

    fn pattern(&mut self, p: &mut Pat, root: u32) -> Result<(), BorrowReason> {
        match p {
            Pat::Bind(local, _) => {
                self.tracked.insert(local.id, root);
                local.repr = Repr::Ref;
            }
            Pat::Ctor { ctor, fields }
                if !ctor.linear && !ctor.indirect.contains(&Indirect::Unique) =>
            {
                for p in fields {
                    self.pattern(p, root)?;
                }
            }
            Pat::Wild | Pat::Int(_) | Pat::Nat(_) | Pat::Bool(_) => {}
            _ => {
                return Err(reason(
                    "pattern-ownership",
                    msg!("rustgen-borrow-pattern-ownership"),
                ));
            }
        }
        Ok(())
    }
}
