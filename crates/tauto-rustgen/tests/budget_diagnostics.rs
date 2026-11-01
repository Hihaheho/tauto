//! Static eligibility reports use the same checks as emitted budget branches.

use tauto_rustgen::{Bindings, Sources, budget_diagnostics, emit_module};

fn inspect(source: &str) -> (Vec<tauto_rustgen::BudgetDiagnostic>, String) {
    let pkg = tauto_nir::compile_with(source, true).unwrap();
    let sources = Sources {
        file: "main.taut",
        text: source,
    };
    let bindings = Bindings::default();
    (
        budget_diagnostics(&pkg, &sources, &bindings),
        emit_module(&pkg, &sources, &bindings),
    )
}

#[test]
fn eligible_report_agrees_with_generated_guard() {
    tauto_messages::install();
    let (reports, rust) = inspect(
        r#"let r := handle { budget(steps: 0) { 42 } } with { exceeded(info), k => -1 }
perform show("r", r)"#,
    );
    assert_eq!(reports.len(), 1);
    assert!(reports[0].eligible());
    assert!(rust.contains("can_run_nonresuming"));
}

#[test]
fn unknown_callbacks_and_externs_have_specific_reasons() {
    tauto_messages::install();
    for (source, expected) in [
        (
            r#"pub fn run(&read: (u64) -> u64): u64 { handle { budget(steps: 5) { read(0) } } with { exceeded(info), k => 0 } }"#,
            "unknown-call",
        ),
        (
            r#"extern { fn read(value: u64): u64 }
let r := handle { budget(steps: 5) { read(0) } } with { exceeded(info), k => 0 }"#,
            "extern-contract",
        ),
    ] {
        let (reports, rust) = inspect(source);
        assert!(
            reports
                .iter()
                .flat_map(|r| &r.reasons)
                .any(|r| r.code == expected),
            "{reports:?}"
        );
        assert!(!rust.contains("run_nonresuming"));
    }
}

#[test]
fn discarded_continuation_is_not_a_host_lifetime_proof() {
    tauto_messages::install();
    let source = r#"extern { fn refs(value: Text): i64 }
fn hold(value: Text, n: i64): Text ! {Div} { var i := 0
while i < n { i := i + 1 }
value }
let text := concat("held", "value")
let r := handle { budget(steps: 2) { hold(text, 5) } } with { exceeded(info), k => Text::of_i64(refs(text)) }"#;
    let (reports, rust) = inspect(source);
    assert!(
        reports
            .iter()
            .flat_map(|r| &r.reasons)
            .any(|r| r.code == "observable-handler"),
        "{reports:?}"
    );
    assert!(
        reports
            .iter()
            .flat_map(|r| &r.reasons)
            .any(|r| r.code == "extern-contract" && r.function.starts_with("handler of ")),
        "{reports:?}"
    );
    assert!(!rust.contains("run_nonresuming"));
}

#[test]
fn concurrent_shared_value_observers_keep_the_future_path() {
    tauto_messages::install();
    let source = r#"let r := handle { budget(steps: 0) { 42 } } with { exceeded(info), k => -1 }"#;
    let mut pkg = tauto_nir::compile(source).unwrap();
    pkg.sync = true;
    let reports = budget_diagnostics(
        &pkg,
        &Sources {
            file: "main.taut",
            text: source,
        },
        &Bindings::default(),
    );
    assert!(
        reports
            .iter()
            .flat_map(|r| &r.reasons)
            .any(|r| r.code == "concurrent-observer")
    );
}

#[test]
fn escaping_abort_and_panicking_handler_have_explicit_reasons() {
    tauto_messages::install();
    for (source, code) in [
        (
            r#"effect stop(value: i64): Never resume 0
fn run(): i64 ! {stop} { handle { budget(steps: 5) { perform stop(2) } } with { exceeded(info), k => 0 } }"#,
            "abort-not-locally-total",
        ),
        (
            r#"pub fn run(n: i64): i64 { handle { budget(steps: 0) { 42 } } with { exceeded(info), k => n + 1 } }"#,
            "handler-may-panic",
        ),
    ] {
        let (reports, rust) = inspect(source);
        assert!(
            reports
                .iter()
                .flat_map(|r| &r.reasons)
                .any(|r| r.code == code),
            "{reports:?}"
        );
        assert!(!rust.contains("run_nonresuming"));
    }
}

#[test]
fn a_known_callback_does_not_bless_a_later_unknown_call_context() {
    tauto_messages::install();
    let source = r#"fn value(index: u64): u64 { index + 1 }
fn sum(&read: (u64) -> u64, size: u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size { total := total + read(index)
    index := index + 1 }
  total
}
fn run(&unknown: (u64) -> u64): u64 {
  handle { budget(steps: 100) { sum(&value, 4) + sum(unknown, 4) } } with { exceeded(info), k => 0 }
}
"#;
    let (reports, rust) = inspect(source);
    assert!(
        reports
            .iter()
            .flat_map(|r| &r.reasons)
            .any(|r| r.code == "unknown-callback"),
        "{reports:?}"
    );
    assert!(!rust.contains("run_nonresuming"));
}

#[test]
fn generated_union_needs_an_embedding_augmentation_contract() {
    tauto_messages::install();
    let source = r#"let result := handle { budget(steps: 0) { if true { 42 } else { "body" } } } with { exceeded(info), k => "end" }"#;
    let (reports, rust) = inspect(source);
    assert!(!reports[0].eligible(), "{:?}", reports);
    assert!(!rust.contains("run_nonresuming"));
}
