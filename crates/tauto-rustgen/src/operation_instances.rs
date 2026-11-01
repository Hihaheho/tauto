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
        .any(Ty::has_infer)
}

fn arm_limitation(arm: &OpArm, operation: &OpDef) -> Option<String> {
    let Some(instance) = &arm.instance else {
        return (!operation.generics.is_empty()
            && arm
                .params
                .iter()
                .chain(std::iter::once(&arm.k_ans))
                .any(Ty::has_infer))
        .then(|| "no sealed full operation instance is available".into());
    };
    if operation.name == "show" {
        return (instance.admission != OperationAdmission::BuiltinShow).then(|| {
            "a user operation named show does not have the builtin erased operation identity".into()
        });
    }
    if instance.type_args.is_empty() {
        return None;
    }
    match instance.admission {
        OperationAdmission::BuiltinShow => None,
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
                    if package.ops[perform.op].name == "show"
                        && instance.admission != OperationAdmission::BuiltinShow {
                        messages.insert(format!("Rust operation instance show at byte {}: a user declaration does not have the builtin erased operation identity", perform.span.start));
                    } else if instance.admission == OperationAdmission::Unique {
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

    #[test]
    fn unresolved_instance_diagnostics_are_only_a_rust_boundary() {
        for case in [
            "operation-instance-distinct-requests-remain-a-rust-boundary",
            "operation-instance-indeterminate-integers-keep-frontend-behavior",
            "operation-instance-opaque-callback-keeps-javascript-behavior",
        ] {
            let source = crate::operation_instances::case_inputs::source_static(
                "types/operation-instances.eure",
                case,
            );
            let javascript = tauto_nir::compile_javascript(source)
                .unwrap_or_else(|error| panic!("{case}: {error}"));
            let rust = tauto_nir::compile(source).unwrap_or_else(|error| panic!("{case}: {error}"));
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
            let source = crate::operation_instances::case_inputs::fixture_static(
                "types/operation-instances.eure",
                name,
            );
            let javascript = tauto_nir::compile_javascript(source).unwrap();
            let rust = tauto_nir::compile(source).unwrap();
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
perform show("answer", result)"#;
        let package = tauto_nir::compile(source).unwrap();
        assert!(diagnostics(&package).is_empty());
        let mut requests = 0;
        let mut arms = 0;
        for function in &package.fns {
            function
                .body
                .walk(&mut |expression| match &expression.kind {
                    ExprKind::Perform(perform) if package.ops[perform.op].name == "keep" => {
                        let instance = perform.instance.as_ref().unwrap();
                        assert_eq!(instance.admission, OperationAdmission::Unique);
                        assert_eq!(perform.args[0].ty, instance.params[0]);
                        assert!(matches!(perform.args[0].ty, Ty::Union(_)));
                        requests += 1;
                    }
                    ExprKind::Handle(handle) => {
                        for arm in &handle.susp {
                            if package.ops[arm.op].name == "keep" {
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

    #[test]
    fn reserved_show_identity_is_not_inferred_from_its_spelling() {
        let source = r#"effect show<A>(value: A): A
let result := handle { perform show(7) } with { ∀ A. show<A>(value), k => k(value) }"#;
        let package = tauto_nir::compile(source).unwrap();
        assert!(diagnostics(&package).to_string().contains("compile_error"));
    }
}

#[cfg(test)]
/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn source_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
            (
                "types/operation-instances.eure",
                "operation-instance-distinct-requests-remain-a-rust-boundary",
            ) => {
                r#"effect identity<A>(value: A): A
handle {
  let number: i64 := perform identity(7)
  let text: Text := perform identity("kept")
  perform show("number", number)
  perform show("text", text)
} with { ∀ A. identity<A>(value), k => k(value) }"#
            }
            (
                "types/operation-instances.eure",
                "operation-instance-opaque-callback-keeps-javascript-behavior",
            ) => {
                r#"effect identity<A>(value: A): A
let action := () => perform identity(7)
let result := handle { action() } with { ∀ A. identity<A>(value), k => k(value) }
perform show("answer", result)"#
            }
            (
                "types/operation-instances.eure",
                "operation-instance-indeterminate-integers-keep-frontend-behavior",
            ) => {
                r#"effect identity<A>(value: A): A
let result := handle {
  if true { perform identity(7) } else { perform identity(8) }
} with { ∀ A. identity<A>(value), k => k(value) }
perform show("answer", result)"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn source(file: &str, name: &str) -> String {
        source_static(file, name).to_string()
    }
    pub fn fixture_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
            (
                "types/operation-instances.eure",
                "operation-instance-phantom-argument-is-not-invented",
            ) => {
                r#"effect phantom<A>(value: i64): i64
let result := handle { perform phantom(7) } with { phantom(value), k => k(value) }"#
            }
            (
                "types/operation-instances.eure",
                "operation-instance-result-only-requests-remain-distinct",
            ) => {
                r#"effect supply<A>(): A
handle {
  let number: i64 := perform supply()
  let text: Text := perform supply()
  true
} with { ∀ A. supply<A>(), k => true }"#
            }
            (
                "types/operation-instances.eure",
                "operation-instance-equal-payloads-have-distinct-answer-arguments",
            ) => {
                r#"effect convert<A, B>(value: A): B
handle {
  let number: i64 := perform convert(true)
  let text: Text := perform convert(true)
  true
} with { ∀ A, B. convert<A, B>(_), k => true }"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn fixture(file: &str, name: &str) -> String {
        fixture_static(file, name).to_string()
    }
}
