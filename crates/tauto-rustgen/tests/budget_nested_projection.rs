//! Projection spelling preserves the concrete lifetime proof.

use std::path::Path;

use tauto_nir::{Expr, ExprKind, Package, Ty};
use tauto_rustgen::{Bindings, BudgetDiagnostic, Sources, budget_diagnostics, emit_lib};

const MANIFEST: &str = r#"rust {
  exports = ["run"]
  nonresuming { entries { run_trusted = "run" } }
}"#;

fn package(source: &str) -> Package {
    let mut package = tauto_nir::compile_with(source, true).unwrap();
    package
        .exports
        .retain(|export| export.name.as_str() == "run");
    assert_eq!(package.exports.len(), 1);
    package
}

fn inspect(package: &Package, source: &str) -> (Vec<BudgetDiagnostic>, String) {
    let manifest = tauto::manifest::parse(MANIFEST, Path::new("Tauto.eure")).unwrap();
    let bindings = Bindings::resolve(package, Some(&manifest), None).unwrap();
    let sources = Sources {
        file: "nested-projection.taut",
        text: source,
    };
    let reports = budget_diagnostics(package, &sources, &bindings);
    let (rust, _) = emit_lib(package, &sources, &bindings);
    (reports, rust)
}

fn report<'a>(reports: &'a [BudgetDiagnostic], variant: &str) -> &'a BudgetDiagnostic {
    reports
        .iter()
        .find(|report| report.function == "run" && report.variant == variant)
        .unwrap_or_else(|| panic!("missing {variant}: {reports:?}"))
}

fn qualified_only(source: &str) {
    let (reports, rust) = inspect(&package(source), source);
    let ordinary = report(&reports, "ordinary");
    assert!(!ordinary.eligible(), "{ordinary:?}");
    assert!(ordinary.assumptions.is_empty(), "{ordinary:?}");
    assert!(
        ordinary
            .reasons
            .iter()
            .any(|reason| reason.code == "unproven-lifetime"),
        "{ordinary:?}"
    );
    let qualified = report(&reports, "run_trusted");
    assert!(qualified.eligible(), "{qualified:?}");
    assert_eq!(qualified.assumptions.len(), 1, "{qualified:?}");
    assert_eq!(qualified.assumptions[0].kind, "embedding");
    assert!(rust.contains("run_nonresuming"), "{rust}");
}

fn concrete_source(body: &str) -> String {
    format!(
        r#"struct Inner {{ values: List(u64) }}
struct Outer {{ inner: Inner }}
fn count(xs: List(u64)): u64 ! {{Div}} {{
  match xs {{
    Nil => 0
    Cons(item, tail) => 1 + count(tail)
  }}
}}
fn inspect(value: Outer): u64 ! {{Div}} {{ {} }}
fn run(value: Outer): u64 {{
  handle {{ budget(steps: 100) {{ inspect(value) }} }} with {{ exceeded(info), k => 0 }}
}}"#,
        body
    )
}

#[test]
fn nested_and_split_fields_have_the_same_qualified_eligibility() {
    tauto_messages::install();
    for body in [
        r#"count(value.inner.values)"#,
        r#"let inner := value.inner
count(inner.values)"#,
    ] {
        qualified_only(&concrete_source(body));
    }
}

#[test]
fn deeper_field_chains_keep_every_intermediate_type() {
    tauto_messages::install();
    for body in [
        r#"count(value.outer.inner.values)"#,
        r#"let outer := value.outer
let inner := outer.inner
count(inner.values)"#,
    ] {
        let source = format!(
            r#"struct Inner {{ values: List(u64) }}
struct Outer {{ inner: Inner }}
struct Wrapper {{ outer: Outer }}
fn count(xs: List(u64)): u64 ! {{Div}} {{
  match xs {{
    Nil => 0
    Cons(item, tail) => 1 + count(tail)
  }}
}}
fn inspect(value: Wrapper): u64 ! {{Div}} {{ {} }}
fn run(value: Wrapper): u64 {{
  handle {{ budget(steps: 100) {{ inspect(value) }} }} with {{ exceeded(info), k => 0 }}
}}"#,
            body
        );
        qualified_only(&source);
    }
}

#[test]
fn generic_field_types_are_proved_under_the_concrete_call_context() {
    tauto_messages::install();
    for body in [
        r#"count(value.outer.inner.values)"#,
        r#"let outer := value.outer
let inner := outer.inner
count(inner.values)"#,
    ] {
        let source = format!(
            r#"shared struct Inner(A: Shared) {{ values: List(A) }}
shared struct Outer(B: Shared) {{ inner: Inner(B) }}
shared struct Wrapper(C: Shared) {{ outer: Outer(C) }}
fn count<T: Shared>(xs: List(T)): u64 ! {{Div}} {{
  match xs {{
    Nil => 0
    Cons(item, tail) => 1 + count(tail)
  }}
}}
fn inspect<U: Shared>(value: Wrapper(U)): u64 ! {{Div}} {{ {} }}
fn run(value: Wrapper(u64)): u64 {{
  handle {{ budget(steps: 100) {{ inspect(value) }} }} with {{ exceeded(info), k => 0 }}
}}"#,
            body
        );
        qualified_only(&source);
    }
}

fn projection_argument(expr: &mut Expr) -> &mut Expr {
    match &mut expr.kind {
        ExprKind::Block(block) => projection_argument(block.tail.as_deref_mut().unwrap()),
        ExprKind::Call(call) => {
            assert_eq!(call.args.len(), 1);
            &mut call.args[0]
        }
        other => panic!("unexpected inspect body: {other:?}"),
    }
}

#[test]
fn genuinely_unknown_intermediate_types_still_fail_closed() {
    tauto_messages::install();
    let source = concrete_source(r#"count(value.inner.values)"#);
    qualified_only(&source);
    for unknown in [Ty::Infer, Ty::Param("Unknown".into())] {
        let mut package = package(&source);
        let inner = package
            .datas
            .iter()
            .find(|data| data.name.as_str() == "Inner")
            .unwrap()
            .name
            .clone();
        let mut changed = 0;
        for function in &mut package.fns {
            if function.source.as_str() != "inspect" {
                continue;
            }
            let ExprKind::Field { base, field, .. } =
                &mut projection_argument(&mut function.body).kind
            else {
                panic!("expected the values projection");
            };
            assert_eq!(field.name, "values");
            assert!(
                matches!(&base.kind, ExprKind::Field { field, .. } if field.name.as_str() == "inner")
            );
            assert_eq!(base.ty, Ty::Data(inner.clone(), Vec::new()));
            base.ty = unknown.clone();
            changed += 1;
        }
        assert!(changed > 0);
        let (reports, rust) = inspect(&package, &source);
        let qualified = report(&reports, "run_trusted");
        assert!(!qualified.eligible(), "{unknown:?}: {qualified:?}");
        assert!(
            qualified
                .reasons
                .iter()
                .any(|reason| reason.code == "unproven-lifetime"),
            "{unknown:?}: {qualified:?}"
        );
        assert!(!rust.contains("run_nonresuming"), "{rust}");
    }
}

#[test]
fn a_safe_projected_field_does_not_hide_an_unproven_sibling() {
    tauto_messages::install();
    let source = concrete_source(r#"count(value.inner.values)"#).replace(
        r#"struct Outer { inner: Inner }"#,
        r#"shared struct Outer { inner: Inner, read: (u64) -> u64 }"#,
    );
    let package = package(&source);
    let outer = package
        .datas
        .iter()
        .find(|data| data.name.as_str() == "Outer")
        .unwrap()
        .name
        .clone();
    let mut reads = 0;
    for function in &package.fns {
        if function.source.as_str() == "inspect" {
            function.body.walk(&mut |expr| {
                if matches!(&expr.kind, ExprKind::Read { local, .. } if local.name.as_str() == "value") {
                    assert_eq!(expr.ty, Ty::Data(outer.clone(), Vec::new()));
                    reads += 1;
                }
            });
        }
    }
    assert!(reads > 0);
    let (reports, rust) = inspect(&package, &source);
    let qualified = report(&reports, "run_trusted");
    assert!(!qualified.eligible(), "{qualified:?}");
    assert!(
        qualified.reasons.iter().any(|reason| {
            reason.code == "unproven-lifetime" && reason.message.to_string().contains("Outer")
        }),
        "{qualified:?}"
    );
    assert!(!rust.contains("run_nonresuming"), "{rust}");
}
