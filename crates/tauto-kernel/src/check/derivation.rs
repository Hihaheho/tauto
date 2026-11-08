//! Judgments recorded during core checking. These observations do not authorize declarations.
use crate::surface::{Name, SurfaceTerm};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InferenceRule {
    Assumption,
    Constant,
    UnverifiedReference,
    Literal,
    Sort,
    Formation,
    Introduction,
    Application,
    Conversion,
    Reduction,
    Hole,
}

#[derive(Clone, Debug)]
pub struct Derivation {
    pub context: Vec<(Name, SurfaceTerm)>,
    pub term: SurfaceTerm,
    pub ty: SurfaceTerm,
    pub rule: InferenceRule,
    /// New local assumptions, discharged by an introduction.
    pub introduced: Vec<(Name, SurfaceTerm)>,
    pub premises: Vec<Derivation>,
}

impl Derivation {
    pub fn is_complete(&self) -> bool {
        !matches!(
            self.rule,
            InferenceRule::Hole | InferenceRule::UnverifiedReference
        ) && self.premises.iter().all(Self::is_complete)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::core::{Ask, Core};
    use crate::surface::TermKind;
    fn var(n: &str) -> SurfaceTerm {
        SurfaceTerm::var(n, Default::default())
    }
    #[test]
    fn writing_equality_preserves_the_source_occurrence() {
        let left = var("a");
        let right = var("b");
        let term = SurfaceTerm::app(
            &tauto_surface::bindings::library_name("Eq"),
            vec![var("Nat"), left.clone(), right.clone()],
            Default::default(),
        );
        let written = crate::check::Kernel::eqs_written(&term);
        assert_eq!(written.id(), term.id());
        let crate::surface::TermKind::App { arguments, .. } = &*written.kind else {
            panic!("equality is an application");
        };
        assert_eq!(arguments[0].id(), left.id());
        assert_eq!(arguments[1].id(), right.id());
    }
    fn pi(n: &str, a: SurfaceTerm, b: SurfaceTerm) -> SurfaceTerm {
        SurfaceTerm::new(
            TermKind::Pi {
                params: vec![(Some(n.into()), a)],
                result: Box::new(b),
                effects: None,
            },
            Default::default(),
        )
    }
    fn lam(n: &str, body: SurfaceTerm) -> SurfaceTerm {
        SurfaceTerm::new(
            TermKind::Lam {
                params: vec![n.into()],
                body: Box::new(body),
                types: Vec::new(),
            },
            Default::default(),
        )
    }
    fn apply(f: SurfaceTerm, a: SurfaceTerm) -> SurfaceTerm {
        SurfaceTerm::new(
            TermKind::App {
                function: Box::new(f),
                arguments: vec![a],
            },
            Default::default(),
        )
    }
    #[test]
    fn recording_preserves_core_answers_and_restores_state() {
        let ctx = vec![
            ("P".into(), var("Prop")),
            ("Q".into(), var("Prop")),
            ("a".into(), var("P")),
            ("f".into(), pi("x", var("P"), var("Q"))),
        ];
        let terms = vec![
            var("a"),
            var("f"),
            apply(var("f"), var("a")),
            lam("a", var("a")),
            apply(lam("x", var("x")), var("a")),
            var("unknown"),
            SurfaceTerm::new(TermKind::Hole("h".into()), Default::default()),
        ];
        let types = vec![
            var("P"),
            var("Q"),
            pi("x", var("P"), var("P")),
            apply(lam("x", var("P")), var("a")),
        ];
        let declared = |_: &Name| None;
        for term in &terms {
            for ty in &types {
                let mut normal = Core::new();
                let mut traced = normal.clone();
                let want = normal
                    .type_in(&ctx, term, Ask::Check(ty), &declared, &[])
                    .is_ok();
                let got = traced.derivation_in(&ctx, term, ty, &declared, &[]);
                assert_eq!(want, got.is_ok());
                if let Ok(typed) = got {
                    let tree = typed
                        .derivation
                        .expect("a successful recorded question has a derivation");
                    recheck(&tree);
                }
                let again = traced.type_in(&ctx, term, Ask::Check(ty), &declared, &[]);
                assert_eq!(want, again.is_ok());
                if let Ok(typed) = again {
                    assert!(typed.derivation.is_none());
                }
            }
        }
    }
    fn recheck(d: &Derivation) {
        let declared = |_: &Name| None;
        assert!(
            Core::new()
                .type_in(&d.context, &d.term, Ask::Check(&d.ty), &declared, &[])
                .is_ok()
        );
        for p in &d.premises {
            recheck(p);
        }
    }

    #[test]
    fn dependent_application_instantiates_the_result_and_conversion_is_explicit() {
        let ctx = vec![
            ("P".into(), var("Prop")),
            ("a".into(), var("P")),
            ("B".into(), pi("x", var("P"), var("Prop"))),
            ("k".into(), pi("x", var("P"), apply(var("B"), var("x")))),
        ];
        let declared = |_: &Name| None;
        let result = apply(var("B"), var("a"));
        let mut core = Core::new();
        let tree = core
            .derivation_in(&ctx, &apply(var("k"), var("a")), &result, &declared, &[])
            .unwrap_or_else(|_| panic!("dependent application must check"))
            .derivation
            .unwrap();
        assert_eq!(tree.rule, InferenceRule::Application);
        assert_eq!(crate::surface::print::print_term(&tree.ty), "B(a)");
        recheck(&tree);
        let converted = apply(lam("x", var("P")), var("a"));
        let tree = core
            .derivation_in(&ctx, &var("a"), &converted, &declared, &[])
            .unwrap_or_else(|_| panic!("conversion must check"))
            .derivation
            .unwrap();
        assert_eq!(tree.rule, InferenceRule::Conversion);
        assert_eq!(tree.premises[0].rule, InferenceRule::Assumption);
        recheck(&tree);
    }

    #[test]
    fn introduction_and_application_have_scoped_typed_premises() {
        let ctx = vec![
            ("P".into(), var("Prop")),
            ("Q".into(), var("Prop")),
            ("a".into(), var("P")),
            ("f".into(), pi("x", var("P"), var("Q"))),
        ];
        let declared = |_: &Name| None;
        let mut c = Core::new();
        let term = lam("a", apply(var("f"), var("a")));
        let tree = c
            .derivation_in(&ctx, &term, &pi("x", var("P"), var("Q")), &declared, &[])
            .unwrap_or_else(|_| panic!("the derivation must check"))
            .derivation
            .unwrap();
        assert_eq!(tree.rule, InferenceRule::Introduction);
        assert_eq!(tree.context.len(), 4);
        assert_eq!(tree.introduced[0].0.as_str(), "a'1");
        let body = &tree.premises[0];
        assert_eq!(body.rule, InferenceRule::Application);
        assert_eq!(body.context.len(), 5);
        assert_eq!(body.premises.len(), 2);
        assert_eq!(body.premises[0].rule, InferenceRule::Assumption);
        assert_eq!(body.premises[1].rule, InferenceRule::Assumption);
        assert!(matches!(&*body.premises[1].term.kind,TermKind::Var(n) if n.as_str()=="a'1"));
        assert!(matches!(&*body.ty.kind,TermKind::Var(n) if n.as_str()=="Q"));
    }
    #[test]
    fn presentation_queries_distinguish_proofs_from_types_and_unknowns() {
        let kernel = crate::check::Kernel::new();
        let mut inspect = kernel.proof_inspector();
        let context = vec![("P".into(), var("Prop")), ("h".into(), var("P"))];
        let mut d = Derivation {
            context: context.clone(),
            term: var("h"),
            ty: var("P"),
            rule: InferenceRule::Assumption,
            introduced: Vec::new(),
            premises: Vec::new(),
        };
        assert_eq!(inspect.is_proof(&d), Some(true));
        d.term = var("P");
        d.ty = var("Prop");
        assert_eq!(inspect.is_proof(&d), Some(false));
        d.ty = var("missing");
        assert_eq!(inspect.is_proof(&d), None);
        let reduced = inspect
            .reduce(&context, &apply(lam("x", var("P")), var("h")))
            .expect("beta reduction");
        assert!(matches!(&*reduced.normal.kind,TermKind::Var(n) if n.as_str()=="P"));
        assert!(reduced.unfolded.is_empty());
    }

    #[test]
    fn presentation_reports_actual_unfolded_definitions_without_changing_the_environment() {
        let mut kernel = crate::check::Kernel::new();
        kernel
            .core
            .add_decl(&"Alias".into(), &var("Type"), Some(&var("Prop")), true)
            .unwrap();
        let mut inspect = kernel.proof_inspector();
        let reduced = inspect
            .reduce(&[], &var("Alias"))
            .expect("a transparent definition");
        assert!(matches!(&*reduced.normal.kind,TermKind::Var(n) if n.as_str()=="Prop"));
        assert_eq!(
            reduced
                .unfolded
                .iter()
                .map(Name::as_str)
                .collect::<Vec<_>>(),
            vec!["Alias"]
        );
        let before = kernel
            .core
            .type_in(&Vec::new(), &var("Alias"), Ask::Infer, &|_| None, &[])
            .unwrap_or_else(|_| panic!("the original environment is intact"));
        assert!(matches!(&*before.ty.unwrap().kind,TermKind::Var(n) if n.as_str()=="Type"));
    }
}

/// Bounded queries for presenting an already recorded derivation. Its copy of
/// the environment and reduction budget never accepts or changes a declaration.
pub struct ProofInspector {
    core: super::core::Core,
    declared: std::collections::HashMap<Name, SurfaceTerm>,
}

pub struct ProofReduction {
    pub normal: SurfaceTerm,
    pub unfolded: Vec<Name>,
}

impl super::Kernel {
    pub fn proof_inspector(&self) -> ProofInspector {
        ProofInspector {
            core: self.core.clone(),
            declared: self
                .globals
                .iter()
                .map(|(n, g)| (n.clone(), g.ty.clone()))
                .collect(),
        }
    }
}

impl ProofInspector {
    pub fn is_proof(&mut self, judgment: &Derivation) -> Option<bool> {
        let declared = &self.declared;
        self.core.start_budget(Some(4096), None);
        let result = self.core.type_in(
            &judgment.context,
            &judgment.ty,
            super::core::Ask::Sort,
            &|n| declared.get(n).cloned(),
            &[],
        );
        let spent = self.core.end_budget();
        if spent.out {
            return None;
        }
        result.ok()?.sort.map(|s| s == super::Sort::Prop)
    }

    pub fn reduce(
        &mut self,
        context: &[(Name, SurfaceTerm)],
        term: &SurfaceTerm,
    ) -> Option<ProofReduction> {
        self.core.proof_reduction_in(context, term)
    }

    /// `true` is definitional equality; `false` on a recorded conversion
    /// distinguishes cumulativity. Exhaustion leaves the explanation unknown.
    pub fn definitionally_equal(
        &mut self,
        context: &[(Name, SurfaceTerm)],
        a: &SurfaceTerm,
        b: &SurfaceTerm,
    ) -> Option<bool> {
        self.core.start_budget(Some(4096), None);
        let declared = &self.declared;
        let same = self
            .core
            .proof_conversion_in(&context.to_vec(), a, b, &|n| declared.get(n).cloned());
        let spent = self.core.end_budget();
        (!spent.out).then_some(same)
    }
}
