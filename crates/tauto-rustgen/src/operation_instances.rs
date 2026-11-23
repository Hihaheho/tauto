//! Rust's boundary for checked parameterized operation representations.

use std::collections::BTreeSet;

use proc_macro2::TokenStream;
use quote::quote;
use tauto_nir::*;

fn unresolved(instance: &OperationInstance) -> bool {
    instance
        .type_args
        .iter()
        .chain(&instance.params)
        .chain(std::iter::once(&instance.answer))
        .any(Ty::has_arm_generic)
}

fn arm_limitation(arm: &OpArm, operation: &OpDef) -> Option<String> {
    let Some(instance) = &arm.instance else {
        return (!operation.generics.is_empty()
            && arm
                .params
                .iter()
                .chain(std::iter::once(&arm.k_ans))
                .any(Ty::has_arm_generic))
        .then(|| "no sealed full operation instance is available".into());
    };
    if instance.type_args.is_empty() {
        return None;
    }
    match instance.admission {
        OperationAdmission::Unique => {
            if unresolved(instance) {
                return Some("the admitted operation signature is unresolved".into());
            }
            if arm.params != instance.params || (arm.k.is_some() && arm.k_ans != instance.answer) {
                return Some(
                    "the handler representation differs from its checked formal signature".into(),
                );
            }
            None
        }
        OperationAdmission::Legacy => None,
        OperationAdmission::Incomplete | OperationAdmission::Missing if !unresolved(instance) => {
            None
        }
        // An arm for every instance leaves its payload's type open, and
        // NIR writes it once for each payload type the program performs the
        // operation with (`tauto_nir::arms`).
        OperationAdmission::Incomplete | OperationAdmission::Missing
            if arm.instantiated || arm.params.iter().any(Ty::has_arm_generic) =>
        {
            None
        }
        other => Some(
            other
                .limitation()
                .unwrap_or("the operation instance is unsupported")
                .into(),
        ),
    }
}

pub(crate) fn diagnostics(package: &Package) -> TokenStream {
    let mut messages = BTreeSet::new();
    for function in &package.fns {
        function.body.walk(&mut |expression| match &expression.kind {
            ExprKind::Handle(handle) => {
                for arm in handle.direct.iter().chain(&handle.aborts).chain(&handle.susp) {
                    if let Some(reason) = arm_limitation(arm, &package.ops[arm.op]) {
                        messages.insert(format!("Rust operation instance {} at byte {}: {reason}", package.ops[arm.op].name, arm.span.start));
                    }
                }
            }
            ExprKind::Perform(perform) => {
                if let Some(instance) = &perform.instance {
                    if instance.admission == OperationAdmission::Unique {
                        let payload_matches = perform.args.len() == instance.params.len()
                            && perform.args.iter().zip(&instance.params)
                                .all(|(actual, formal)| actual.ty == *formal || actual.ty == Ty::Never);
                        if !payload_matches || perform.result != instance.answer || unresolved(instance) {
                            messages.insert(format!("Rust operation instance {} at byte {}: the request representation differs from its checked formal signature", package.ops[perform.op].name, perform.span.start));
                        }
                    }
                }
            }
            _ => {}
        });
    }
    messages
        .into_iter()
        .map(|message| quote!(compile_error!(#message);))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compile_both(source: &str) -> (Package, Package) {
        let loaded =
            tauto::program::load_texts(vec![("operation-instance.nib".into(), source.into())])
                .unwrap();
        let rust = tauto_nibcheck::lower::compile_loaded_with_observer(
            &loaded,
            false,
            tauto_nir::Target::Rust,
            |_| {},
        )
        .unwrap();
        let mut javascript = tauto_nibcheck::lower::compile_loaded_with_observer(
            &loaded,
            false,
            tauto_nir::Target::JavaScript,
            |_| {},
        )
        .unwrap();
        // Each lowering allocates its own synthetic entry declaration.
        if let (Some(a), Some(b)) = (rust.top, javascript.top) {
            let source = rust.fns.iter().find(|f| f.id == a).unwrap().source.clone();
            javascript
                .fns
                .iter_mut()
                .find(|f| f.id == b)
                .unwrap()
                .source = source;
        }
        (rust, javascript)
    }

    #[test]
    fn unresolved_instance_diagnostics_are_only_a_rust_boundary() {
        for case in [
            "operation-instance-distinct-requests-remain-a-rust-boundary",
            "operation-instance-indeterminate-integers-keep-frontend-behavior",
        ] {
            let source = tauto_case_inputs::source("types/operation-instances.eure", case);
            let (rust, javascript) = compile_both(&source);
            let emitted = diagnostics(&rust).to_string();
            assert!(emitted.contains("compile_error"), "{case}: {emitted}");
            assert_eq!(
                format!("{rust:?}"),
                format!("{javascript:?}"),
                "{case}: target-specific rejection leaked into shared lowering"
            );
        }
        for name in [
            "operation-instance-equal-payloads-have-distinct-answer-arguments",
            "operation-instance-result-only-requests-remain-distinct",
            "operation-instance-phantom-argument-is-not-invented",
        ] {
            let source = tauto_case_inputs::source("types/operation-instances.eure", name);
            let (rust, javascript) = compile_both(&source);
            assert!(
                diagnostics(&rust).to_string().contains("compile_error"),
                "{name}"
            );
            assert_eq!(format!("{rust:?}"), format!("{javascript:?}"), "{name}");
        }
    }

    #[test]
    fn formal_payload_coercion_matches_the_handler_downcast_shape() {
        let source = r#"effect keep<A>(fixed: i64 | Text, value: A): A
let number: i64 := 7
let result := handle { perform keep(number, true) } with { ∀ A. keep<A>(_, value), k => k(value) }
show(&result)"#;
        let package = tauto::nir::compile(source).unwrap();
        assert!(diagnostics(&package).is_empty());
        let mut requests = 0;
        let mut arms = 0;
        for function in &package.fns {
            function
                .body
                .walk(&mut |expression| match &expression.kind {
                    ExprKind::Perform(perform)
                        if package.ops[perform.op].name.as_str() == "keep" =>
                    {
                        let instance = perform.instance.as_ref().unwrap();
                        assert_eq!(instance.admission, OperationAdmission::Unique);
                        assert_eq!(perform.args[0].ty, instance.params[0]);
                        assert!(matches!(perform.args[0].ty, Ty::Union(_)));
                        requests += 1;
                    }
                    ExprKind::Handle(handle) => {
                        // A tail-form arm is lowered as `direct`.
                        for arm in handle.susp.iter().chain(&handle.direct) {
                            if package.ops[arm.op].name.as_str() == "keep" {
                                let instance = arm.instance.as_ref().unwrap();
                                assert_eq!(arm.params, instance.params);
                                assert!(matches!(arm.pats[0], Pat::Wild));
                                arms += 1;
                            }
                        }
                    }
                    _ => {}
                });
        }
        assert_eq!((requests, arms), (1, 1));
    }
}
