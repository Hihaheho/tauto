//! Which functions reuse their frame for their calls marked `recur`
//! (`tauto_nir::tail`): the runtime's restart is limited to concrete,
//! drop-free owned computations.
//! A helper may inspect a read-only borrow, but its complete call graph must
//! use only the structural operations and builtins admitted here. A tier is
//! not evidence that a function has no effects.
use std::collections::BTreeSet;
use tauto_nir::*;

pub(crate) fn candidates(pkg: &Package) -> BTreeSet<InstId> {
    let mut pure: BTreeSet<_> = pkg.fns.iter().map(|f| f.id).collect();
    loop {
        let next: BTreeSet<_> = pkg
            .fns
            .iter()
            .filter(|f| pure.contains(&f.id) && Checker::new(pkg, &pure, f, true).function(f))
            .map(|f| f.id)
            .collect();
        if next == pure {
            break;
        }
        pure = next;
    }
    pkg.fns
        .iter()
        .filter(|f| {
            pure.contains(&f.id)
                && f.generics.is_empty()
                && Checker::new(pkg, &pure, f, false).function(f)
        })
        .map(|f| f.id)
        .collect()
}

struct Checker<'a> {
    pkg: &'a Package,
    pure: &'a BTreeSet<InstId>,
    params: BTreeSet<String>,
    helper: bool,
}

impl<'a> Checker<'a> {
    fn new(pkg: &'a Package, pure: &'a BTreeSet<InstId>, f: &FnInst, helper: bool) -> Self {
        Self {
            pkg,
            pure,
            params: if helper {
                f.generics.iter().map(|(name, _)| name.clone()).collect()
            } else {
                BTreeSet::new()
            },
            helper,
        }
    }

    fn ty(&self, ty: &Ty) -> bool {
        safe_type(
            self.pkg,
            ty,
            &self.params,
            &mut BTreeSet::new(),
            self.helper,
            128,
        )
    }

    fn repr(&self, local: &Local) -> bool {
        local.storage() == Storage::Owned || self.helper && local.storage() == Storage::Borrow
    }

    fn function(&self, f: &FnInst) -> bool {
        f.params
            .iter()
            .all(|p| self.repr(&p.local) && self.ty(&p.ty))
            && self.ty(&f.ret)
            && self.expr(&f.body)
    }

    fn ctor(&self, ctor: &CtorRef) -> bool {
        !ctor.linear
            && match &ctor.data {
                DataRef::Option | DataRef::Result | DataRef::Pair => true,
                DataRef::Gen(name) => self.pkg.datas.iter().any(|d| {
                    d.name == *name
                        && !d.ctors.is_empty()
                        && !d.view
                        && !d.linear
                        && d.kind != Kind::Linear
                }),
            }
    }

    fn pat(&self, pat: &Pat) -> bool {
        match pat {
            Pat::Wild | Pat::Int(_) | Pat::Nat(_) | Pat::Bool(_) | Pat::Text(_) => true,
            Pat::Bind(local, ty) => self.repr(local) && self.ty(ty),
            Pat::Ctor { ctor, fields } => self.ctor(ctor) && fields.iter().all(|p| self.pat(p)),
        }
    }

    fn block(&self, block: &Block) -> bool {
        block.stmts.iter().all(|stmt| match stmt {
            Stmt::Let {
                local, ty, init, ..
            } => self.repr(local) && self.ty(ty) && self.expr(init),
            Stmt::Expr(expr) => self.expr(expr),
            Stmt::Return { value, .. } if self.helper => {
                value.as_ref().is_none_or(|e| self.expr(e))
            }
            Stmt::Var { .. } | Stmt::Assign { .. } | Stmt::While { .. } | Stmt::Return { .. } => {
                false
            }
        }) && block.tail.as_ref().is_none_or(|e| self.expr(e))
    }

    fn expr(&self, expr: &Expr) -> bool {
        if !self.ty(&expr.ty) {
            return false;
        }
        match &expr.kind {
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_)
            | ExprKind::Text(_)
            | ExprKind::Declaration(_) => true,
            ExprKind::Read { local, .. } => self.repr(local),
            ExprKind::Call(call) => {
                call.tick == Tick::None
                    && match &call.callee {
                        Callee::Inst(id) => self.pure.contains(id),
                        Callee::Builtin(name) => pure_builtin(name),
                        Callee::Extern(_)
                        | Callee::Local(_)
                        | Callee::Cont(_)
                        | Callee::Value(_) => false,
                    }
                    && call.targs.iter().all(|ty| self.ty(ty))
                    && call.args.iter().all(|arg| self.expr(arg))
            }
            ExprKind::Arith { args, .. }
            | ExprKind::Cmp { args, .. }
            | ExprKind::Eq { args, .. } => args.iter().all(|arg| self.expr(arg)),
            ExprKind::Not(value) | ExprKind::Unreachable(value) => self.expr(value),
            ExprKind::And(a, b) | ExprKind::Or(a, b) => self.expr(a) && self.expr(b),
            ExprKind::Ctor { ctor, fields } => {
                self.ctor(ctor) && fields.iter().all(|(_, value)| self.expr(value))
            }
            ExprKind::Field { base, .. } => self.expr(base),
            ExprKind::Match(m) => {
                (self.helper || !m.by_ref)
                    && self.expr(&m.scrut)
                    && m.arms.iter().all(|arm| {
                        self.pat(&arm.pat)
                            && arm.guard.as_ref().is_none_or(|g| self.expr(g))
                            && self.expr(&arm.body)
                    })
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.expr(cond)
                    && self.expr(then)
                    && otherwise.as_ref().is_none_or(|e| self.expr(e))
            }
            ExprKind::Block(block) => self.block(block),
            ExprKind::Ref(place) => self.helper && self.repr(&place.local) && self.ty(&place.ty),
            ExprKind::TempRef(value) | ExprKind::Deref { value, .. } => {
                self.helper && self.expr(value)
            }
            ExprKind::FnValue { .. }
            | ExprKind::Closure(_)
            | ExprKind::Perform(_)
            | ExprKind::Handle(_)
            | ExprKind::Inject { .. }
            | ExprKind::Remap { .. }
            | ExprKind::RefMut(_)
            | ExprKind::Shown(_)
            | ExprKind::Budget(_)
            | ExprKind::FnCast(_) => false,
        }
    }
}

fn safe_type(
    pkg: &Package,
    ty: &Ty,
    params: &BTreeSet<String>,
    active: &mut BTreeSet<Name>,
    borrowed: bool,
    fuel: usize,
) -> bool {
    if fuel == 0 {
        return false;
    }
    match ty {
        Ty::Int(_) | Ty::Bool | Ty::Text | Ty::Unit | Ty::Never | Ty::Float | Ty::Float32 => true,
        Ty::Param(name) => params.contains(name),
        Ty::Array(value) | Ty::Option(value) => {
            safe_type(pkg, value, params, active, borrowed, fuel - 1)
        }
        Ty::Pair(a, b) | Ty::Result(a, b) => {
            safe_type(pkg, a, params, active, borrowed, fuel - 1)
                && safe_type(pkg, b, params, active, borrowed, fuel - 1)
        }
        Ty::Ref(value) if borrowed => safe_type(pkg, value, params, active, borrowed, fuel - 1),
        Ty::Data(name, args) => {
            let Some(data) = pkg.datas.iter().find(|d| d.name == *name) else {
                return false;
            };
            if data.ctors.is_empty()
                || data.view
                || data.linear
                || data.kind == Kind::Linear
                || data.generics.len() != args.len()
                || !args
                    .iter()
                    .all(|arg| safe_type(pkg, arg, params, active, borrowed, fuel - 1))
            {
                return false;
            }
            // Check changed recursive arguments before accepting a cycle.
            // A type already visited in this walk is not checked again: if it
            // were unsafe, the walk would have ended there. Keeping it marked
            // makes the walk linear in the types instead of in the paths.
            if !active.insert(name.clone()) {
                return true;
            }
            let fields = data.generics.iter().cloned().collect();
            data.ctors
                .iter()
                .flat_map(|c| &c.fields)
                .all(|field| safe_type(pkg, &field.ty, &fields, active, borrowed, fuel - 1))
        }
        Ty::Buf
        | Ty::Vec(_)
        | Ty::Std(_, _)
        | Ty::HashMap(_, _)
        | Ty::Slice(_)
        | Ty::Union(_)
        | Ty::Fn(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::SharedVar(true, _)
        | Ty::SharedVar(false, _)
        | Ty::Info(_)
        | Ty::BudgetAnswer(_)
        | Ty::Shown
        | Ty::Infer => false,
    }
}

fn pure_builtin(name: &str) -> bool {
    crate::FLOAT_BUILTINS.contains(&name)
        || matches!(
            name,
            "concat"
                | "Text::of_i64"
                | "Text::of_u64"
                | "Text::of_nat"
                | "Text::len"
                | "Text::compare"
                | "Text::byte"
                | "Text::slice"
                | "Text::of_code_point"
                | "Text::of_utf8"
                | "words"
                | "div"
                | "mod"
                | "Array::get"
                | "Array::len"
                | "Array::of_list"
                | "Array::to_list"
                | "Bytes::of_list"
                | "Bytes::to_list"
                | "Bytes::len"
                | "secret"
                | "expose"
                | "Bytes::get"
                | "Bytes::slice"
                | "Bytes::concat"
                | "Bytes::eq"
                | "Bytes::of_text"
                | "Text::of_bytes"
                | "I64::of_i32"
                | "I32::of_i64"
                | "I64::of_u64"
                | "U64::of_i64"
                | "U64::of_u32"
                | "U32::of_u64"
                | "U64::of_u8"
                | "U8::of_u64"
                | "Nat::of_u64"
                | "U64::of_nat"
                | "U32::and"
                | "U32::or"
                | "U32::xor"
                | "U32::shl"
                | "U32::shr"
                | "U32::rotl"
                | "U32::rotr"
                | "U64::and"
                | "U64::or"
                | "U64::xor"
                | "U64::shl"
                | "U64::shr"
                | "U64::rotl"
                | "U64::rotr"
        )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span() -> Span {
        Span::new(0, 0)
    }
    fn local(id: u32) -> Local {
        Local {
            id,
            name: format!("x{id}"),
            repr: Repr::Plain,
        }
    }
    fn expr(kind: ExprKind, ty: Ty) -> Expr {
        Expr {
            kind,
            ty,
            span: span(),
        }
    }
    fn unit() -> Expr {
        expr(ExprKind::Unit, Ty::Unit)
    }
    fn call(callee: Callee, args: Vec<Expr>, ty: Ty) -> Expr {
        expr(
            ExprKind::Call(Box::new(CallNode {
                callee,
                args,
                tier: Tier::S,
                targs: vec![],
                tick: Tick::None,
                recur: false,
                span: span(),
            })),
            ty,
        )
    }
    fn function(id: InstId, body: Expr) -> FnInst {
        FnInst {
            id,
            source: format!("f{id}").into(),
            rust_name: format!("f{id}"),
            tier: Tier::S,
            generics: vec![],
            params: vec![],
            ret: body.ty.clone(),
            body,
            span: span(),
        }
    }
    fn package(fns: Vec<FnInst>) -> Package {
        Package {
            fns,
            ..Package::default()
        }
    }
    fn list(ty: Ty) -> Ty {
        Ty::Data("List".into(), vec![ty])
    }
    fn recursive_data() -> DataDef {
        DataDef {
            name: "List".into(),
            generics: vec!["A".into()],
            kind: Kind::Shared,
            is_struct: false,
            clone: true,
            copy: false,
            linear: false,
            view: false,
            host: false,
            ctors: vec![CtorDef {
                name: "Cons".into(),
                fields: vec![
                    FieldDef {
                        name: None,
                        ty: Ty::Param("A".into()),
                        indirect: Indirect::None,
                    },
                    FieldDef {
                        name: None,
                        ty: list(Ty::Param("A".into())),
                        indirect: Indirect::Shared,
                    },
                ],
            }],
        }
    }

    #[test]
    fn structural_purity_not_tier_controls_eligibility() {
        let mut f = function(0, call(Callee::Inst(0), vec![], Ty::Unit));
        f.tier = Tier::M;
        let mut pkg = package(vec![f]);
        assert_eq!(candidates(&pkg), BTreeSet::from([0]));
        pkg.fns[0].tier = Tier::S;
        pkg.fns[0].body = call(Callee::Extern("host".into()), vec![], Ty::Unit);
        assert!(candidates(&pkg).is_empty());
    }

    #[test]
    fn unsafe_callees_remove_their_transitive_callers_and_cycles() {
        let mut pkg = package(vec![
            function(0, call(Callee::Inst(1), vec![], Ty::Unit)),
            function(1, call(Callee::Inst(2), vec![], Ty::Unit)),
            function(
                2,
                expr(
                    ExprKind::Block(Block {
                        stmts: vec![Stmt::Expr(call(Callee::Inst(1), vec![], Ty::Unit))],
                        tail: Some(Box::new(call(
                            Callee::Builtin("Os::print".into()),
                            vec![],
                            Ty::Unit,
                        ))),
                    }),
                    Ty::Unit,
                ),
            ),
            function(3, unit()),
        ]);
        assert_eq!(candidates(&pkg), BTreeSet::from([3]));
        pkg.fns[2].body = call(Callee::Inst(1), vec![], Ty::Unit);
        assert_eq!(candidates(&pkg), BTreeSet::from([0, 1, 2, 3]));
    }

    #[test]
    fn unknown_calls_ticks_and_resource_builtins_are_not_pure() {
        for callee in [
            Callee::Inst(99),
            Callee::Local(local(1)),
            Callee::Cont(local(1)),
            Callee::Value(Box::new(unit())),
            Callee::Builtin("future_pure_operation".into()),
            Callee::Builtin("Ref::get".into()),
            Callee::Builtin("clone".into()),
            Callee::Builtin("Pending::take".into()),
        ] {
            assert!(
                candidates(&package(vec![function(0, call(callee, vec![], Ty::Unit))])).is_empty()
            );
        }
        for tick in [Tick::Host, Tick::Budget] {
            let mut body = call(
                Callee::Builtin("Text::len".into()),
                vec![],
                Ty::Int(Width::U64),
            );
            let ExprKind::Call(node) = &mut body.kind else {
                unreachable!()
            };
            node.tick = tick;
            let pkg = package(vec![
                function(0, call(Callee::Inst(1), vec![], body.ty.clone())),
                function(1, body),
            ]);
            assert!(candidates(&pkg).is_empty());
        }
    }

    #[test]
    fn concrete_data_check_recursive_arguments_and_every_field() {
        let mut pkg = package(vec![function(
            0,
            expr(
                ExprKind::Read {
                    local: local(0),
                    how: Use::Move,
                },
                list(Ty::Text),
            ),
        )]);
        pkg.datas.push(recursive_data());
        assert_eq!(candidates(&pkg), BTreeSet::from([0]));
        pkg.datas[0].ctors[0].fields[1].ty = list(Ty::Vec(Box::new(Ty::Text)));
        assert!(candidates(&pkg).is_empty());
        pkg.datas[0] = recursive_data();
        pkg.datas[0].ctors[0].fields[0].ty = Ty::Param("undeclared".into());
        assert!(candidates(&pkg).is_empty());
        for change in 0..4 {
            pkg.datas[0] = recursive_data();
            match change {
                0 => pkg.datas[0].view = true,
                1 => pkg.datas[0].linear = true,
                2 => pkg.datas[0].kind = Kind::Linear,
                _ => pkg.datas[0].ctors.clear(),
            }
            assert!(candidates(&pkg).is_empty());
        }
    }

    #[test]
    fn unknown_resource_and_borrowed_types_cannot_own_elided_frames() {
        for ty in [
            Ty::Param("A".into()),
            Ty::Infer,
            Ty::Data("Missing".into(), vec![]),
            Ty::Std(tauto_nir::StdType::Ref, vec![Ty::Text]),
            Ty::Buf,
            Ty::Vec(Box::new(Ty::Text)),
            Ty::Ref(Box::new(Ty::Text)),
            Ty::RefMut(Box::new(Ty::Text)),
            Ty::SharedVar(true, Box::new(Ty::Text)),
            Ty::Union(0),
        ] {
            let f = function(
                0,
                expr(
                    ExprKind::Read {
                        local: local(0),
                        how: Use::Move,
                    },
                    ty,
                ),
            );
            assert!(candidates(&package(vec![f])).is_empty());
        }
        let mut f = function(0, unit());
        f.generics.push(("Unused".into(), BTreeSet::new()));
        assert!(candidates(&package(vec![f])).is_empty());
    }

    #[test]
    fn generic_borrowing_helpers_do_not_make_the_owner_borrowed() {
        let a = list(Ty::Param("A".into()));
        let borrowed = expr(
            ExprKind::Ref(Place {
                local: local(1),
                path: vec![],
                ty: a.clone(),
            }),
            Ty::Ref(Box::new(a.clone())),
        );
        let mut helper = function(
            1,
            expr(
                ExprKind::Deref {
                    value: Box::new(borrowed),
                    how: Use::Clone,
                },
                a.clone(),
            ),
        );
        helper.generics.push(("A".into(), BTreeSet::new()));
        helper.params.push(Param {
            local: local(1),
            ty: a,
        });
        let value = expr(
            ExprKind::Read {
                local: local(0),
                how: Use::Move,
            },
            list(Ty::Text),
        );
        let mut caller = function(0, call(Callee::Inst(1), vec![value], list(Ty::Text)));
        caller.params.push(Param {
            local: local(0),
            ty: list(Ty::Text),
        });
        let mut pkg = package(vec![caller, helper]);
        pkg.datas.push(recursive_data());
        assert_eq!(candidates(&pkg), BTreeSet::from([0]));
        pkg.fns[1].body = call(
            Callee::Extern("hidden_host".into()),
            vec![],
            list(Ty::Param("A".into())),
        );
        assert!(candidates(&pkg).is_empty());
    }

    #[test]
    fn all_own_locals_statements_and_pattern_bindings_are_checked() {
        for repr in [
            Repr::Ref,
            Repr::RefMut,
            Repr::SharedVar(true),
            Repr::SharedVar(false),
            Repr::FnRef,
            Repr::BorrowClosure,
        ] {
            let mut bound = local(1);
            bound.repr = repr;
            let body = expr(
                ExprKind::Block(Block {
                    stmts: vec![Stmt::Let {
                        local: bound.clone(),
                        ty: Ty::Text,
                        init: expr(ExprKind::Text("x".into()), Ty::Text),
                        span: span(),
                    }],
                    tail: Some(Box::new(unit())),
                }),
                Ty::Unit,
            );
            assert!(candidates(&package(vec![function(0, body)])).is_empty());
            let body = expr(
                ExprKind::Match(Box::new(MatchNode {
                    scrut: unit(),
                    by_ref: false,
                    exhaustive: true,
                    span: span(),
                    arms: vec![MatchArm {
                        pat: Pat::Bind(bound, Ty::Unit),
                        guard: None,
                        body: unit(),
                    }],
                })),
                Ty::Unit,
            );
            assert!(candidates(&package(vec![function(0, body)])).is_empty());
        }
        for stmt in [
            Stmt::Var {
                local: local(1),
                ty: Ty::Unit,
                init: unit(),
                span: span(),
            },
            Stmt::Assign {
                target: Place {
                    local: local(1),
                    path: vec![],
                    ty: Ty::Unit,
                },
                value: unit(),
                span: span(),
            },
            Stmt::While {
                cond: expr(ExprKind::Bool(false), Ty::Bool),
                body: Block {
                    stmts: vec![],
                    tail: None,
                },
                tick: Tick::None,
                span: span(),
            },
            Stmt::Return {
                value: Some(unit()),
                span: span(),
            },
        ] {
            let body = expr(
                ExprKind::Block(Block {
                    stmts: vec![stmt],
                    tail: Some(Box::new(unit())),
                }),
                Ty::Unit,
            );
            assert!(candidates(&package(vec![function(0, body)])).is_empty());
        }
    }

    #[test]
    fn budgets_handlers_and_operations_are_rejected_even_in_plain_tiers() {
        let nodes = [
            ExprKind::Budget(Box::new(BudgetNode {
                id: 0,
                memory: false,
                steps: expr(ExprKind::Int(10), Ty::Int(Width::U64)),
                body: unit(),
                m: false,
                span: span(),
            })),
            ExprKind::Handle(Box::new(HandleNode {
                id: 0,
                body: unit(),
                body_ty: Ty::Unit,
                result: Ty::Unit,
                ret: None,
                direct: vec![],
                aborts: vec![],
                susp: vec![],
                captures: vec![],
                clones: vec![],
                body_tier: Tier::S,
                m: false,
                host_ret: None,
                kept: false,
                detached: false,
                span: span(),
            })),
            ExprKind::Perform(Box::new(PerformNode {
                instance: None,
                detached: false,
                op: 0,
                quant: Quant::Direct,
                args: vec![],
                result: Ty::Unit,
                span: span(),
            })),
        ];
        for kind in nodes {
            let pkg = package(vec![
                function(0, call(Callee::Inst(1), vec![], Ty::Unit)),
                function(1, expr(kind, Ty::Unit)),
            ]);
            assert!(candidates(&pkg).is_empty());
        }
        let fty = FnTy {
            params: vec![],
            ret: Ty::Unit,
            kind: Kind::Shared,
            tier: Tier::S,
        };
        let closure = expr(
            ExprKind::Closure(Box::new(ClosureNode {
                params: vec![],
                ret: Ty::Unit,
                body: unit(),
                fn_ty: fty.clone(),
                borrowed: false,
                clones: vec![],
                pure: true,
                refs: vec![],
                owned_refs: vec![],
                span: span(),
            })),
            Ty::Fn(Box::new(fty)),
        );
        let body = expr(
            ExprKind::Block(Block {
                stmts: vec![Stmt::Expr(closure)],
                tail: Some(Box::new(unit())),
            }),
            Ty::Unit,
        );
        assert!(candidates(&package(vec![function(0, body)])).is_empty());
    }

    #[test]
    fn generator_restarts_only_exact_self_calls_in_return_position() {
        let int = Ty::Int(Width::U64);
        let arithmetic = function(
            0,
            expr(
                ExprKind::Arith {
                    op: Arith::Add,
                    args: vec![
                        call(Callee::Inst(0), vec![], int.clone()),
                        expr(ExprKind::Int(1), int.clone()),
                    ],
                    width: Width::U64,
                },
                int,
            ),
        );
        let statement = function(
            1,
            expr(
                ExprKind::Block(Block {
                    stmts: vec![Stmt::Let {
                        local: local(1),
                        ty: Ty::Unit,
                        init: call(Callee::Inst(1), vec![], Ty::Unit),
                        span: span(),
                    }],
                    tail: Some(Box::new(unit())),
                }),
                Ty::Unit,
            ),
        );
        let condition = function(
            2,
            expr(
                ExprKind::If {
                    cond: Box::new(call(Callee::Inst(2), vec![], Ty::Bool)),
                    then: Box::new(expr(ExprKind::Bool(true), Ty::Bool)),
                    otherwise: Some(Box::new(expr(ExprKind::Bool(false), Ty::Bool))),
                },
                Ty::Bool,
            ),
        );
        let scrutinee = function(
            3,
            expr(
                ExprKind::Match(Box::new(MatchNode {
                    scrut: call(Callee::Inst(3), vec![], Ty::Bool),
                    by_ref: false,
                    exhaustive: true,
                    span: span(),
                    arms: vec![MatchArm {
                        pat: Pat::Wild,
                        guard: None,
                        body: expr(ExprKind::Bool(true), Ty::Bool),
                    }],
                })),
                Ty::Bool,
            ),
        );
        let tail = function(
            4,
            expr(
                ExprKind::If {
                    cond: Box::new(expr(ExprKind::Bool(true), Ty::Bool)),
                    then: Box::new(call(Callee::Inst(4), vec![], Ty::Unit)),
                    otherwise: Some(Box::new(unit())),
                },
                Ty::Unit,
            ),
        );
        let mut pkg = package(vec![arithmetic, statement, condition, scrutinee, tail]);
        tauto_nir::mark_tail_calls(&mut pkg);
        assert_eq!(candidates(&pkg), BTreeSet::from([0, 1, 2, 3, 4]));
        let generated = crate::generate(&pkg).unwrap();
        for id in 0..4 {
            assert!(!generated.contains(&format!("tailSelfCall(pure(f{id}),")));
            assert!(generated.contains(&format!("callFunction(pure(f{id}),")));
        }
        assert!(generated.contains("tailSelfCall(pure(f4),"));
    }
}
