//! Checked, directly determined instances of parameterized operations.

use super::*;

/// What the bounded, directly executed body establishes about an arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperationAdmission {
    Legacy,
    BuiltinShow,
    Unique,
    Incomplete,
    ExplicitReturn,
    Missing,
    Indeterminate,
    Distinct,
    Unresolved,
}

impl OperationAdmission {
    pub fn limitation(self) -> Option<&'static str> {
        match self {
            Self::Legacy | Self::BuiltinShow | Self::Unique => None,
            Self::Incomplete => {
                Some("the handled body has an opaque or storage-sensitive operation context")
            }
            Self::ExplicitReturn => {
                Some("an explicit return arm is outside checked operation-instance admission")
            }
            Self::Missing => {
                Some("the handled body supplies no directly determined operation instance")
            }
            Self::Indeterminate => {
                Some("the handled operation instances are not determined before checking the arm")
            }
            Self::Distinct => {
                Some("the handled body has distinct parameterized operation instances")
            }
            Self::Unresolved => {
                Some("a checked operation instance still has unresolved type arguments")
            }
        }
    }
}

/// The complete formal signature, instantiated together by the checker.
#[derive(Debug, Clone)]
pub struct CheckedOperationInstance {
    owner: Option<EffectOwner>,
    pub type_args: Vec<Ty>,
    pub params: Vec<Ty>,
    pub answer: Ty,
    pub admission: OperationAdmission,
}

impl CheckedOperationInstance {
    pub fn is_generic(&self) -> bool {
        !self.type_args.is_empty()
    }
    pub fn is_builtin_show(&self) -> bool {
        self.admission == OperationAdmission::BuiltinShow
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArmPass {
    Widen,
    Complete,
}

#[derive(Debug, Clone)]
pub(super) struct ArmObservation {
    occurrence: TermId,
    pass: ArmPass,
    instance: CheckedOperationInstance,
}

#[derive(Debug, Default)]
pub struct OperationFacts {
    program: Option<Program>,
    occurrences: Vec<TermId>,
    performs: HashMap<TermId, CheckedOperationInstance>,
    arms: HashMap<TermId, CheckedOperationInstance>,
    perform_observations: Vec<(TermId, CheckedOperationInstance)>,
    arm_observations: Vec<ArmObservation>,
}

impl OperationFacts {
    pub fn perform(&self, at: TermId) -> Option<&CheckedOperationInstance> {
        self.performs.get(&at)
    }
    pub fn arm(&self, at: TermId) -> Option<&CheckedOperationInstance> {
        self.arms.get(&at)
    }
}

impl TypeReport {
    /// Complete signature facts sealed to these checked occurrences. Public
    /// type-table edits cannot supply operation-instance evidence.
    pub fn operation_instances_for(&self, program: &Program) -> Option<&OperationFacts> {
        let facts = self.operation_facts.as_ref()?;
        if !self.errors.is_empty()
            || facts.program.as_ref() != Some(program)
            || facts.occurrences != value_occurrences(program)
        {
            return None;
        }
        Some(facts)
    }

    pub(super) fn seal_operation_instances(&mut self, program: &Program) {
        if !self.errors.is_empty() {
            return;
        }
        let occurrences = value_occurrences(program);
        let unique: HashSet<_> = occurrences.iter().copied().collect();
        if unique.len() != occurrences.len() {
            self.operation_facts = None;
            return;
        }
        if let Some(facts) = &mut self.operation_facts {
            facts.program = Some(program.clone());
            facts.occurrences = occurrences;
        }
    }
}

#[derive(Default)]
pub(super) struct BodyOperations {
    complete: bool,
    explicit_return: bool,
    requests: Vec<(usize, CheckedOperationInstance)>,
}

impl Checker {
    pub(super) fn instantiate_operation(&mut self, sig: &EffectSig) -> CheckedOperationInstance {
        let type_args = sig.generics.iter().map(|_| self.fresh()).collect();
        self.instantiate_operation_with(sig, type_args)
    }

    /// An operation's signature at the given type arguments, one per generic.
    pub(super) fn instantiate_operation_with(
        &mut self,
        sig: &EffectSig,
        type_args: Vec<Ty>,
    ) -> CheckedOperationInstance {
        let map: HashMap<_, _> = sig
            .generics
            .iter()
            .zip(&type_args)
            .map(|(p, ty)| (p.id.clone(), ty.clone()))
            .collect();
        let owner = sig.generics.first().and_then(|p| match p.id() {
            ParamId::Effect { owner, .. } => Some(owner.clone()),
            _ => None,
        });
        let admission = if owner.is_some() && owner == self.builtin_show_owner {
            OperationAdmission::BuiltinShow
        } else {
            OperationAdmission::Legacy
        };
        CheckedOperationInstance {
            owner,
            type_args,
            params: sig.params.iter().map(|p| substitute(p, &map)).collect(),
            answer: substitute(&sig.result, &map),
            admission,
        }
    }

    fn owned_known(&self, ty: &Ty) -> bool {
        self.owned_known_in(ty, &mut HashSet::new())
    }

    fn owned_known_in(&self, ty: &Ty, visiting: &mut HashSet<String>) -> bool {
        let ty = self.resolve(ty);
        if self.has_vars(&ty) || self.is_view(&ty) {
            return false;
        }
        match &ty {
            Ty::Int(_)
            | Ty::Bool
            | Ty::Text
            | Ty::Unit
            | Ty::Never
            | Ty::Decimal
            | Ty::Float
            | Ty::Float32
            | Ty::Param(..) => true,
            // Function signatures do not describe borrowed captures or shared cells.
            // Product ownership is outside this bounded admission.
            Ty::Borrow(..)
            | Ty::Fn(..)
            | Ty::Product(_)
            | Ty::Var(_)
            | Ty::App(..)
            | Ty::Poly(..) => false,
            Ty::Union(args) => args.iter().all(|p| self.owned_known_in(p, visiting)),
            Ty::Tagged(_, inner) | Ty::Info(inner) => self.owned_known_in(inner, visiting),
            Ty::Named(name, args) => {
                let Some(data) = self.datas.decls.get(name) else {
                    return false;
                };
                if data.view
                    || data.builtin
                    || data.recursive
                    || data.generics.len() != args.len()
                    || data.constructors.is_empty()
                    || !visiting.insert(name.clone())
                {
                    return false;
                }
                let owned = args.iter().all(|p| self.owned_known_in(p, visiting))
                    && (0..data.constructors.len()).all(|ctor| {
                        self.datas
                            .fields(name, ctor, args)
                            .iter()
                            .all(|(_, field)| self.owned_known_in(field, visiting))
                    });
                visiting.remove(name);
                owned
            }
        }
    }

    fn observed_owned(&self, term: &SurfaceTerm) -> bool {
        self.terms
            .iter()
            .rev()
            .find(|(at, _)| *at == term.id())
            .is_some_and(|(_, ty)| self.owned_known(ty))
    }

    /// Only the eager, view-free spine contributes requests. In particular,
    /// checking a latent declaration is not evidence that it executes here.
    fn direct_requests(&self, term: &SurfaceTerm, tail: bool, out: &mut Vec<TermId>) -> bool {
        match &*term.kind {
            TermKind::Nat(_) | TermKind::Text(_) | TermKind::Bool(_) => true,
            TermKind::Var(_) => self.observed_owned(term),
            TermKind::Lam { .. } => self.observed_owned(term),
            TermKind::Perform { args, .. } => {
                let complete = (tail || self.observed_owned(term))
                    && args.iter().all(|arg| self.direct_requests(arg, false, out));
                out.push(term.id());
                complete
            }
            TermKind::Block(stmts) => stmts.iter().enumerate().all(|(index, stmt)| {
                let last = tail && index + 1 == stmts.len();
                match stmt {
                    Stmt::Expr(value) => self.direct_requests(value, last, out),
                    Stmt::Let {
                        value,
                        borrow: false,
                        borrow_mut: false,
                        ..
                    } => {
                        self.locals
                            .iter()
                            .rev()
                            .find(|((_, at), _)| *at == value.id())
                            .is_some_and(|(_, ty)| self.owned_known(ty))
                            && self.direct_requests(value, false, out)
                    }
                    Stmt::Fn(_) | Stmt::Effect(_) | Stmt::Struct(_) | Stmt::Enum(_) => true,
                    _ => false,
                }
            }),
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                self.direct_requests(condition, false, out)
                    && self.direct_requests(then, tail, out)
                    && otherwise
                        .as_ref()
                        .is_none_or(|other| self.direct_requests(other, tail, out))
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                self.direct_requests(scrutinee, false, out)
                    && arms.iter().all(|arm| {
                        arm.guard
                            .as_ref()
                            .is_none_or(|g| self.direct_requests(g, false, out))
                            && self.direct_requests(&arm.body, tail, out)
                    })
            }
            TermKind::Record { fields, .. } => {
                self.observed_owned(term)
                    && fields
                        .iter()
                        .all(|(_, value)| self.direct_requests(value, false, out))
            }
            TermKind::Field { base, .. } => {
                self.observed_owned(term) && self.direct_requests(base, false, out)
            }
            TermKind::Tagged { term, .. } => self.direct_requests(term, tail, out),
            // Calls, nested handlers, mutable storage, borrows and budgets
            // need information this direct-body admission does not provide.
            _ => false,
        }
    }

    pub(super) fn body_operations(
        &self,
        body: &SurfaceTerm,
        handlers: &[Handler],
        start: usize,
    ) -> BodyOperations {
        let mut ids = Vec::new();
        let mut complete = self.direct_requests(body, true, &mut ids);
        let unique: HashSet<_> = ids.iter().copied().collect();
        complete &= unique.len() == ids.len();
        let mut requests = Vec::new();
        for id in ids {
            let found: Vec<_> = self
                .operation_performs
                .iter()
                .enumerate()
                .skip(start)
                .filter(|(_, (at, _))| *at == id)
                .collect();
            if found.len() != 1 {
                complete = false;
                continue;
            }
            requests.push((found[0].0, found[0].1.1.clone()));
        }
        BodyOperations {
            complete,
            explicit_return: handlers.iter().any(|h| matches!(h, Handler::Return { .. })),
            requests,
        }
    }

    pub(super) fn connect_operation_arm(
        &mut self,
        instance: &mut CheckedOperationInstance,
        body: &BodyOperations,
        at: TermId,
        complete_pass: bool,
        span: Span,
    ) {
        if instance.is_generic() && !instance.is_builtin_show() {
            let candidates: Vec<_> = body
                .requests
                .iter()
                .filter(|(_, request)| request.owner == instance.owner)
                .collect();
            let admission = if body.explicit_return {
                OperationAdmission::ExplicitReturn
            } else if !body.complete {
                OperationAdmission::Incomplete
            } else if candidates.is_empty() {
                OperationAdmission::Missing
            } else if candidates.len() == 1 {
                OperationAdmission::Unique
            } else {
                let args: Vec<Vec<_>> = candidates
                    .iter()
                    .map(|(_, request)| request.type_args.iter().map(|t| self.resolve(t)).collect())
                    .collect();
                if args.iter().flatten().any(|t| self.has_vars(t)) {
                    OperationAdmission::Indeterminate
                } else if args.iter().all(|actual| actual == &args[0]) {
                    // Compared below against one common, fully resolved vector.
                    OperationAdmission::Unique
                } else {
                    OperationAdmission::Distinct
                }
            };
            instance.admission = admission;
            if admission == OperationAdmission::Unique {
                let request = &candidates[0].1;
                let linked = self.attempt(|checker| {
                    if instance.type_args.len() != request.type_args.len()
                        || instance.params.len() != request.params.len()
                    {
                        return Err(());
                    }
                    for (arm, actual) in instance.type_args.iter().zip(&request.type_args) {
                        checker.unify(arm, actual)?;
                    }
                    for (arm, actual) in instance.params.iter().zip(&request.params) {
                        checker.unify(arm, actual)?;
                    }
                    checker.unify(&instance.answer, &request.answer)
                });
                if linked.is_err() {
                    self.error("the handler's parameterized operation instance does not match its handled request", span);
                } else {
                    for (event, _) in candidates {
                        self.operation_performs[*event].1.admission = OperationAdmission::Unique;
                    }
                }
            }
        }
        self.operation_arms.push(ArmObservation {
            occurrence: at,
            pass: if complete_pass {
                ArmPass::Complete
            } else {
                ArmPass::Widen
            },
            instance: instance.clone(),
        });
    }

    fn resolved_operation(
        &self,
        mut instance: CheckedOperationInstance,
    ) -> CheckedOperationInstance {
        instance.type_args = instance.type_args.iter().map(|t| self.resolve(t)).collect();
        instance.params = instance.params.iter().map(|t| self.resolve(t)).collect();
        instance.answer = self.resolve(&instance.answer);
        if instance.admission == OperationAdmission::Unique
            && instance
                .type_args
                .iter()
                .chain(&instance.params)
                .chain(std::iter::once(&instance.answer))
                .any(|t| self.has_vars(t))
        {
            instance.admission = OperationAdmission::Unresolved;
        }
        instance
    }

    pub(super) fn finish_operation_facts(&mut self) -> OperationFacts {
        let perform_observations: Vec<_> = std::mem::take(&mut self.operation_performs)
            .into_iter()
            .map(|(at, instance)| (at, self.resolved_operation(instance)))
            .collect();
        let performs = perform_observations.iter().cloned().collect();
        let arm_observations: Vec<_> = std::mem::take(&mut self.operation_arms)
            .into_iter()
            .map(|observation| ArmObservation {
                instance: self.resolved_operation(observation.instance),
                ..observation
            })
            .collect();
        let mut arms = HashMap::new();
        for observation in &arm_observations {
            if observation.pass == ArmPass::Complete {
                arms.insert(observation.occurrence, observation.instance.clone());
            }
        }
        OperationFacts {
            program: None,
            occurrences: Vec::new(),
            performs,
            arms,
            perform_observations,
            arm_observations,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn checked(case: &str) -> (Program, TypeReport) {
        let source = crate::types::operation_instances::case_inputs::source_static("types/operation-instances.eure", case);
        let program = crate::surface::parse_program_as_written(source).unwrap();
        let report = check_program(&program);
        (program, report)
    }

    fn fixture(name: &str) -> (Program, TypeReport) {
        let source = crate::types::operation_instances::case_inputs::fixture_static("types/operation-instances.eure", name);
        let program = crate::surface::parse_program_as_written(source).unwrap();
        let report = check_program(&program);
        (program, report)
    }

    #[test]
    fn complete_signatures_preserve_independent_parameters_and_result_only_answers() {
        for (case, args, params, answer) in [
            (
                "operation-instance-independent-parameters-and-wildcard",
                vec![Ty::Text, Ty::Int(Width::W64)],
                vec![Ty::Text, Ty::Int(Width::W64)],
                Ty::Int(Width::W64),
            ),
            (
                "operation-instance-result-only-singleton",
                vec![Ty::Int(Width::W64)],
                vec![],
                Ty::Int(Width::W64),
            ),
        ] {
            let (program, report) = checked(case);
            assert!(report.errors.is_empty(), "{case}: {:?}", report.errors);
            let facts = report.operation_instances_for(&program).unwrap();
            let arms: Vec<_> = facts
                .arms
                .values()
                .filter(|instance| instance.admission == OperationAdmission::Unique)
                .collect();
            assert_eq!(arms.len(), 1, "{case}");
            assert_eq!(arms[0].type_args, args, "{case}");
            assert_eq!(arms[0].params, params, "{case}");
            assert_eq!(arms[0].answer, answer, "{case}");
            assert_eq!(facts.arm_observations.len(), 2, "{case}");
            assert_eq!(facts.arm_observations[0].pass, ArmPass::Widen);
            assert_eq!(facts.arm_observations[1].pass, ArmPass::Complete);
            assert!(
                facts
                    .perform_observations
                    .iter()
                    .any(|(_, instance)| instance.admission == OperationAdmission::Unique)
            );
        }
    }

    #[test]
    fn conflicting_reports_cannot_supply_sealed_operation_facts() {
        for case in [
            "operation-instance-narrowed-arm-mismatch",
            "operation-instance-independent-parameters-cannot-collapse",
        ] {
            let (program, report) = checked(case);
            assert!(report.operation_instances_for(&program).is_none());
        }
    }

    #[test]
    fn linear_pattern_admission_retains_complete_formal_payloads() {
        for case in [
            "operation-instance-linear-wildcard-is-rejected",
            "operation-instance-nested-linear-wildcard-is-rejected",
        ] {
            let (program, report) = checked(case);
            let facts = report.operation_instances_for(&program).unwrap();
            let arms: Vec<_> = facts
                .arms
                .values()
                .filter(|instance| instance.admission == OperationAdmission::Unique)
                .collect();
            assert_eq!(arms.len(), 1, "{case}");
            assert_eq!(arms[0].type_args.len(), 2, "{case}");
            assert_eq!(arms[0].params.len(), 2, "{case}");
            assert!(
                matches!(&arms[0].type_args[0], Ty::Named(name, args)
                if name == "Token" && args.is_empty()),
                "{case}: {:?}",
                arms[0]
            );
            assert_eq!(arms[0].type_args[1], Ty::Int(Width::W64), "{case}");
            assert_eq!(arms[0].answer, arms[0].type_args[1], "{case}");
        }
    }

    #[test]
    fn opaque_and_indeterminate_contexts_do_not_gain_shared_type_errors() {
        for (case, admission) in [
            (
                "operation-instance-distinct-requests-remain-a-rust-boundary",
                OperationAdmission::Distinct,
            ),
            (
                "operation-instance-indeterminate-integers-keep-frontend-behavior",
                OperationAdmission::Indeterminate,
            ),
            (
                "operation-instance-opaque-callback-keeps-javascript-behavior",
                OperationAdmission::Incomplete,
            ),
            (
                "operation-instance-linear-return-wildcard-builds-with-its-instance",
                OperationAdmission::ExplicitReturn,
            ),
            (
                "operation-instance-nested-linear-return-builds-with-its-instance",
                OperationAdmission::ExplicitReturn,
            ),
        ] {
            let (program, report) = checked(case);
            assert!(report.errors.is_empty(), "{case}: {:?}", report.errors);
            let facts = report.operation_instances_for(&program).unwrap();
            assert!(
                facts
                    .arms
                    .values()
                    .any(|instance| instance.admission == admission),
                "{case}: {facts:?}"
            );
        }
        for (name, expected) in [
            (
                "operation-instance-equal-payloads-have-distinct-answer-arguments",
                OperationAdmission::Distinct,
            ),
            (
                "operation-instance-result-only-requests-remain-distinct",
                OperationAdmission::Distinct,
            ),
            (
                "operation-instance-phantom-argument-is-not-invented",
                OperationAdmission::Unresolved,
            ),
        ] {
            let (program, report) = fixture(name);
            let facts = report.operation_instances_for(&program).unwrap();
            let arm = facts.arms.values().next().unwrap();
            assert_eq!(facts.arms.len(), 1, "{name}");
            assert_eq!(arm.admission, expected, "{name}");
            let requests: Vec<_> = facts.performs.values().collect();
            if expected == OperationAdmission::Distinct {
                assert_eq!(requests.len(), 2, "{name}");
                assert_eq!(requests[0].params, requests[1].params, "{name}");
                assert_ne!(requests[0].type_args, requests[1].type_args, "{name}");
                assert_ne!(requests[0].answer, requests[1].answer, "{name}");
            } else {
                assert_eq!(requests.len(), 1, "{name}");
                assert!(matches!(arm.type_args.as_slice(), [Ty::Var(_)]), "{name}");
                assert_eq!(arm.params, vec![Ty::Int(Width::W64)], "{name}");
                assert_eq!(arm.answer, Ty::Int(Width::W64), "{name}");
            }
        }
    }

    #[test]
    fn latent_nested_and_mutable_bodies_have_distinct_admission_boundaries() {
        for (name, admission) in [
            (
                "operation-instance-latent-body-is-not-a-request",
                OperationAdmission::Unique,
            ),
            (
                "operation-instance-nested-handler-is-not-a-direct-summary",
                OperationAdmission::Incomplete,
            ),
            (
                "operation-instance-mutable-storage-is-not-replayed",
                OperationAdmission::Incomplete,
            ),
            (
                "operation-instance-captured-cell-is-not-owned-evidence",
                OperationAdmission::Incomplete,
            ),
            (
                "operation-instance-return-storage-is-not-replayed",
                OperationAdmission::ExplicitReturn,
            ),
        ] {
            let (program, report) = fixture(name);
            assert!(report.errors.is_empty(), "{name}: {:?}", report.errors);
            let facts = report.operation_instances_for(&program).unwrap();
            let identity: Vec<_> = facts
                .arms
                .values()
                .filter(|instance| {
                    instance
                        .owner
                        .as_ref()
                        .is_some_and(|owner| owner.name == "identity")
                })
                .collect();
            assert_eq!(identity.len(), 1, "{name}: {facts:?}");
            assert_eq!(identity[0].admission, admission, "{name}");
        }
    }

    #[test]
    fn builtin_show_exemption_belongs_to_its_checked_owner() {
        let (program, report) = checked("operation-instance-builtin-show-keeps-erased-payloads");
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        let facts = report.operation_instances_for(&program).unwrap();
        assert!(
            facts
                .arms
                .values()
                .all(CheckedOperationInstance::is_builtin_show)
        );
        let (program, report) = fixture("operation-instance-user-show-is-not-builtin");
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        let facts = report.operation_instances_for(&program).unwrap();
        assert!(
            facts
                .arms
                .values()
                .all(|instance| !instance.is_builtin_show())
        );
        assert!(
            facts
                .performs
                .values()
                .all(|instance| !instance.is_builtin_show())
        );
    }

    #[test]
    fn sealed_signature_facts_do_not_come_from_mutable_public_type_tables() {
        let (program, mut report) =
            checked("operation-instance-independent-parameters-and-wildcard");
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        report.locals.clear();
        report.terms.clear();
        report.effects.clear();
        let facts = report.operation_instances_for(&program).unwrap();
        assert!(
            facts
                .arms
                .values()
                .any(|instance| instance.type_args == vec![Ty::Text, Ty::Int(Width::W64)])
        );
        let mut changed = program.clone();
        changed.stmts.reverse();
        assert!(report.operation_instances_for(&changed).is_none());
        let mut reused = program.clone();
        reused.stmts.push(reused.stmts[1].clone());
        let repeated = check_program(&reused);
        assert!(repeated.operation_instances_for(&reused).is_none());
    }

    #[test]
    fn owned_admission_is_exhaustive_over_structural_and_nominal_types() {
        for (name, admission) in [
            (
                "operation-instance-product-is-not-owned-evidence",
                OperationAdmission::Incomplete,
            ),
            (
                "operation-instance-nominal-fields-are-owned-evidence",
                OperationAdmission::Incomplete,
            ),
            (
                "operation-instance-rigid-outer-parameter-is-owned",
                OperationAdmission::Unique,
            ),
        ] {
            let (program, report) = fixture(name);
            let facts = report.operation_instances_for(&program).unwrap();
            let arms: Vec<_> = facts
                .arms
                .values()
                .filter(|instance| {
                    instance
                        .owner
                        .as_ref()
                        .is_some_and(|owner| owner.name == "identity")
                })
                .collect();
            assert_eq!(arms.len(), 1, "{name}: {facts:?}");
            assert_eq!(arms[0].admission, admission, "{name}: {facts:?}");
        }
    }

    #[test]
    fn host_wrapper_has_distinct_occurrences_and_preserves_full_signatures() {
        let (program, _) = checked("operation-instance-host-wrapper-keeps-signatures");
        let wrapped = crate::host::wrap(&program).unwrap();
        let original_occurrences = value_occurrences(&program);
        let wrapped_occurrences = value_occurrences(&wrapped);
        let unique: HashSet<_> = wrapped_occurrences.iter().copied().collect();
        assert_eq!(unique.len(), wrapped_occurrences.len());
        assert!(original_occurrences.iter().all(|at| unique.contains(at)));
        let report = check_program(&wrapped);
        let facts = report.operation_instances_for(&wrapped).unwrap();
        for owner in ["identity", "keep"] {
            let arms: Vec<_> = facts
                .arms
                .values()
                .filter(|instance| instance.owner.as_ref().is_some_and(|at| at.name == owner))
                .collect();
            assert_eq!(arms.len(), 1, "{owner}: {facts:?}");
            assert_eq!(arms[0].admission, OperationAdmission::Unique, "{owner}");
            let requests: Vec<_> = facts
                .performs
                .values()
                .filter(|instance| instance.owner.as_ref().is_some_and(|at| at.name == owner))
                .collect();
            assert_eq!(requests.len(), 1, "{owner}: {facts:?}");
            assert_eq!(requests[0].params, arms[0].params, "{owner}");
            assert_eq!(requests[0].type_args, arms[0].type_args, "{owner}");
            assert_eq!(requests[0].answer, arms[0].answer, "{owner}");
        }
    }
}

#[cfg(test)]
/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn fixture_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
        ("types/operation-instances.eure", "operation-instance-equal-payloads-have-distinct-answer-arguments") => r#"effect convert<A, B>(value: A): B
handle {
  let number: i64 := perform convert(true)
  let text: Text := perform convert(true)
  true
} with { ∀ A, B. convert<A, B>(_), k => true }"#,
        ("types/operation-instances.eure", "operation-instance-mutable-storage-is-not-replayed") => r#"effect identity<A>(value: A): A
let result := handle {
  var value := perform identity(7)
  value
} with { ∀ A. identity<A>(value), k => k(value) }"#,
        ("types/operation-instances.eure", "operation-instance-latent-body-is-not-a-request") => r#"effect identity<A>(value: A): A
let result := handle {
  fn unused(): Text { perform identity("latent") }
  perform identity(7)
} with { ∀ A. identity<A>(value), k => k(value) }"#,
        ("types/operation-instances.eure", "operation-instance-phantom-argument-is-not-invented") => r#"effect phantom<A>(value: i64): i64
let result := handle { perform phantom(7) } with { phantom(value), k => k(value) }"#,
        ("types/operation-instances.eure", "operation-instance-rigid-outer-parameter-is-owned") => r#"effect identity<A>(value: A): A
fn relay<T>(input: T): T {
  handle { perform identity(input) } with { identity<T>(value), k => k(value) }
}"#,
        ("types/operation-instances.eure", "operation-instance-product-is-not-owned-evidence") => r#"effect identity<A>(value: A): A
let callback := () => "kept"
let product := callback × true
let result := handle { perform identity(product) } with { ∀ A. identity<A>(value), k => k(value) }"#,
        ("types/operation-instances.eure", "operation-instance-nominal-fields-are-owned-evidence") => r#"struct Holder { callback: () -> Text }
struct Wrapped { holder: Holder }
effect identity<A>(value: A): A
let wrapped := Wrapped { holder: Holder { callback: () => "kept" } }
let result := handle { perform identity(wrapped) } with { ∀ A. identity<A>(value), k => k(value) }"#,
        ("types/operation-instances.eure", "operation-instance-return-storage-is-not-replayed") => r#"linear struct Token {}
effect identity<A>(): A
let result := handle { perform identity() } with {
  return value => { var saved := value; 7 }
  identity<Token>(), k => k(Token {})
}"#,
        ("types/operation-instances.eure", "operation-instance-result-only-requests-remain-distinct") => r#"effect supply<A>(): A
handle {
  let number: i64 := perform supply()
  let text: Text := perform supply()
  true
} with { ∀ A. supply<A>(), k => true }"#,
        ("types/operation-instances.eure", "operation-instance-nested-handler-is-not-a-direct-summary") => r#"effect identity<A>(value: A): A
effect ask(): i64
let result := handle {
  handle { perform ask() } with { ask(), k => k(perform identity(7)) }
} with { ∀ A. identity<A>(value), k => k(value) }"#,
        ("types/operation-instances.eure", "operation-instance-user-show-is-not-builtin") => r#"effect show<A>(value: A): A
let result := handle { perform show(7) } with { ∀ A. show<A>(value), k => k(value) }"#,
        ("types/operation-instances.eure", "operation-instance-captured-cell-is-not-owned-evidence") => r#"effect identity<A>(value: A): A
var text: Text := "kept"
let callback := () => text
let result := handle { perform identity(callback) } with { ∀ A. identity<A>(value), k => k(value) }"#,
        _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn fixture(file: &str, name: &str) -> String {
        fixture_static(file, name).to_string()
    }
    pub fn source_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
        ("types/operation-instances.eure", "operation-instance-linear-wildcard-is-rejected") => r#"linear struct Token {}
effect second<A, B>(first: A, second: B): B
let result := handle { perform second(Token {}, 7) } with {
  second<Token, i64>(_, value), k => k(value)
}"#,
        ("types/operation-instances.eure", "operation-instance-nested-linear-wildcard-is-rejected") => r#"linear struct Token {}
struct Wrapped(A: Type) { value: A }
effect second<A, B>(first: Wrapped(A), second: B): B
let token: Token := Token {}
let wrapped: Wrapped(Token) := Wrapped { value: token }
let result := handle { perform second(wrapped, 7) } with {
  second<Token, i64>(Wrapped { value: _ }, value), k => k(value)
}"#,
        ("types/operation-instances.eure", "operation-instance-nested-linear-return-builds-with-its-instance") => r#"linear struct Token {}
struct Wrapped(A: Type) { value: A }
effect supply<A>(): A
let result := handle { let w: Wrapped(Token) := perform supply(); w } with {
  return Wrapped { value: _ } => 7
  supply<Wrapped(Token)>(), k => k(Wrapped { value: Token {} })
}"#,
        ("types/operation-instances.eure", "operation-instance-independent-parameters-and-wildcard") => r#"effect second<A, B>(first: A, second: B): B
let result := handle { perform second("kept", 7) } with {
  second<Text, i64>(_, value), k => k(value)
}
perform show("answer", result)"#,
        ("types/operation-instances.eure", "operation-instance-result-only-singleton") => r#"effect supply<A>(): A
let result: i64 := handle { perform supply() } with { supply<i64>(), k => k(7) }
perform show("answer", result)"#,
        ("types/operation-instances.eure", "operation-instance-indeterminate-integers-keep-frontend-behavior") => r#"effect identity<A>(value: A): A
let result := handle {
  if true { perform identity(7) } else { perform identity(8) }
} with { ∀ A. identity<A>(value), k => k(value) }
perform show("answer", result)"#,
        ("types/operation-instances.eure", "operation-instance-host-wrapper-keeps-signatures") => r#"effect identity<A>(value: A): A
effect keep<B>(fixed: i64 | Text, value: B): B
let number: i64 := 7
let result := handle { perform identity(number) } with { ∀ A. identity<A>(value), k => k(value) }
let kept := handle { perform keep(number, true) } with { ∀ B. keep<B>(_, value), k => k(value) }
perform stdout("host\n")
perform show("answer", result)
perform show("kept", kept)"#,
        ("types/operation-instances.eure", "operation-instance-independent-parameters-cannot-collapse") => r#"effect second<A, B>(first: A, second: B): B
let result := handle { perform second("kept", 7) } with {
  second<Text, i64>(first, second), k => k(first)
}"#,
        ("types/operation-instances.eure", "operation-instance-distinct-requests-remain-a-rust-boundary") => r#"effect identity<A>(value: A): A
handle {
  let number: i64 := perform identity(7)
  let text: Text := perform identity("kept")
  perform show("number", number)
  perform show("text", text)
} with { ∀ A. identity<A>(value), k => k(value) }"#,
        ("types/operation-instances.eure", "operation-instance-builtin-show-keeps-erased-payloads") => r#"let result := handle {
  perform show("number", 7)
  perform show("text", "kept")
  9
} with { ∀ A. show<A>(_, _), k => k(#()) }
perform show("answer", result)"#,
        ("types/operation-instances.eure", "operation-instance-opaque-callback-keeps-javascript-behavior") => r#"effect identity<A>(value: A): A
let action := () => perform identity(7)
let result := handle { action() } with { ∀ A. identity<A>(value), k => k(value) }
perform show("answer", result)"#,
        ("types/operation-instances.eure", "operation-instance-linear-return-wildcard-builds-with-its-instance") => r#"linear struct Token {}
effect supply<A>(): A
let result := handle { let t: Token := perform supply(); t } with {
  return _ => 7
  supply<Token>(), k => k(Token {})
}"#,
        ("types/operation-instances.eure", "operation-instance-narrowed-arm-mismatch") => r#"effect identity<A>(value: A): A
let result := handle { perform identity("kept") } with {
  identity<Text>(value), k => k(value + 1)
}"#,
        _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn source(file: &str, name: &str) -> String {
        source_static(file, name).to_string()
    }
}
