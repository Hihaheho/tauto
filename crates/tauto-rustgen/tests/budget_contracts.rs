//! Host assertions are explicit, scoped, and distinct from compiler eligibility.
//! These checks inspect resolution, diagnostics, and source, not native execution.

use std::path::Path;

use tauto_nir::Package;
use tauto_rustgen::{Bindings, BudgetDiagnostic, Sources, budget_diagnostics, emit_lib};

const MANIFEST_FILE: &str = "contracts/Tauto.eure";
const QUALIFIED: &str = "run_with_nonresuming_contract";
const ENTRY: &str = r#"rust {
  nonresuming {
    entries { run_with_nonresuming_contract = "run" }
  }
}"#;
fn callback_source() -> &'static str {
    r#"fn sum(&read: (u64) -> u64, size: u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size {
    total := total + read(index)
    index := index + 1
  }
  total
}
fn run(&read: (u64) -> u64, size: u64): Result(u64, Text) {
  handle { budget(steps: 1000) { Ok(sum(&(index) => read(index), size)) } } with {
    exceeded(info), k => Err("exhausted")
  }
}
"#
}
fn extern_source() -> &'static str {
    r#"extern { fn native_read(value: u64): u64 }
fn run(size: u64): u64 {
  handle { budget(steps: 1000) { native_read(size) } } with {
    exceeded(info), k => 0
  }
}
"#
}

fn package(source: &str) -> Package {
    tauto_nir::compile_with(source, true).unwrap()
}

fn manifest(text: &str) -> tauto::manifest::Manifest {
    tauto::manifest::parse(text, Path::new(MANIFEST_FILE)).unwrap()
}

fn resolve(pkg: &Package, text: &str) -> Result<Bindings, String> {
    Bindings::resolve(pkg, Some(&manifest(text)), None)
}

fn inspect(source: &str, text: &str) -> (Vec<BudgetDiagnostic>, String) {
    let pkg = package(source);
    let bindings = resolve(&pkg, text).unwrap();
    let sources = Sources {
        file: "main.taut",
        text: source,
    };
    let reports = budget_diagnostics(&pkg, &sources, &bindings);
    let (rust, _) = emit_lib(&pkg, &sources, &bindings);
    (reports, rust)
}

fn report<'a>(reports: &'a [BudgetDiagnostic], variant: &str) -> &'a BudgetDiagnostic {
    let mut matching = reports
        .iter()
        .filter(|report| report.function == "run" && report.variant == variant);
    let report = matching
        .next()
        .unwrap_or_else(|| panic!("missing {variant} diagnostic: {reports:?}"));
    assert!(
        matching.next().is_none(),
        "duplicate {variant}: {reports:?}"
    );
    report
}

fn has_reason(report: &BudgetDiagnostic, code: &str) -> bool {
    report.reasons.iter().any(|reason| reason.code == code)
}

fn assert_error(error: String, expected: &str) {
    assert!(error.contains(MANIFEST_FILE), "{error}");
    assert!(error.contains(expected), "{error}");
}

#[test]
fn entry_assertions_are_absent_by_default() {
    tauto_messages::install();
    let pkg = package(callback_source());
    for bindings in [
        Bindings::default(),
        Bindings::resolve(&pkg, None, None).unwrap(),
        resolve(&pkg, "rust {}").unwrap(),
    ] {
        assert!(bindings.nonresuming_entries.is_empty());
        assert!(bindings.nonresuming_externs.is_empty());
        let sources = Sources {
            file: "main.taut",
            text: callback_source(),
        };
        let reports = budget_diagnostics(&pkg, &sources, &bindings);
        assert!(reports.iter().all(|report| report.variant == "ordinary"));
        let ordinary = report(&reports, "ordinary");
        assert!(!ordinary.eligible(), "{ordinary:?}");
        assert!(ordinary.assumptions.is_empty(), "{ordinary:?}");
        let (rust, _) = emit_lib(&pkg, &sources, &bindings);
        assert!(!rust.contains("TrustedBudgetHost"), "{rust}");
        assert!(!rust.contains("run_nonresuming"), "{rust}");
    }
}

#[test]
fn facade_names_are_validated_before_emission() {
    tauto_messages::install();
    let pkg = package(r#"pub fn run(): u64 { 7 }"#);
    for name in ["", "_", "9run", "bad-name", "bad.name"] {
        // Mutating a parsed entry isolates binding validation from key syntax.
        let mut input = manifest(ENTRY);
        let entry = input.rust.nonresuming_entries.remove(QUALIFIED).unwrap();
        input.rust.nonresuming_entries.insert(name.into(), entry);
        assert_error(
            Bindings::resolve(&pkg, Some(&input), None).unwrap_err(),
            "invalid Rust nonresuming facade name",
        );
    }
}

#[test]
fn facade_names_cannot_collide_after_rust_name_normalization() {
    tauto_messages::install();
    let pkg = package(r#"pub fn run(): u64 { 7 }"#);
    assert_error(
        resolve(&pkg, r#"rust { nonresuming { entries { run = "run" } } }"#).unwrap_err(),
        "collides with an exported name",
    );
    // A keyword is written raw (`r#type`), so it no longer meets `type_`.
    let text = r#"rust { nonresuming { entries { type = "run" type_ = "run" } } }"#;
    if let Err(e) = resolve(&pkg, text) {
        assert!(!e.contains("collides"), "{e}");
    }
}

#[test]
fn entries_name_selected_exports_not_arbitrary_functions() {
    tauto_messages::install();
    let mut pkg = package(r#"pub fn run(): u64 { 7 }"#);
    assert_error(
        resolve(
            &pkg,
            r#"rust { nonresuming { entries { trusted = "missing" } } }"#,
        )
        .unwrap_err(),
        "unknown or unselected export missing",
    );
    assert!(pkg.exports.iter().any(|export| export.name == "run"));
    pkg.exports.retain(|export| export.name != "run");
    assert_error(
        resolve(&pkg, ENTRY).unwrap_err(),
        "unknown or unselected export run",
    );
}

#[test]
fn binding_contracts_reject_unknown_externs_and_versions() {
    tauto_messages::install();
    let pkg = package(extern_source());
    assert_error(
        resolve(
            &pkg,
            r#"rust {
  extern { native_read = "bridge::read" }
  nonresuming { extern { missing = "closed-host-v1" } }
}"#,
        )
        .unwrap_err(),
        "nonresuming contract names unknown extern missing",
    );
    assert_error(
        resolve(
            &pkg,
            r#"rust {
  extern { native_read = "bridge::read" }
  nonresuming { extern { native_read = "closed-host-v2" } }
}"#,
        )
        .unwrap_err(),
        "unknown nonresuming host contract",
    );
}

#[test]
fn qualified_callbacks_have_assumptions_without_blessing_the_ordinary_entry() {
    tauto_messages::install();
    let (reports, rust) = inspect(callback_source(), ENTRY);
    let ordinary = report(&reports, "ordinary");
    assert!(!ordinary.eligible(), "{ordinary:?}");
    assert!(
        has_reason(ordinary, "unknown-call") || has_reason(ordinary, "unknown-callback"),
        "{ordinary:?}"
    );
    assert!(ordinary.assumptions.is_empty(), "{ordinary:?}");
    let qualified = report(&reports, QUALIFIED);
    assert!(qualified.eligible(), "{qualified:?}");
    for (kind, name) in [("embedding", QUALIFIED), ("callback", "run.read")] {
        assert!(
            qualified.assumptions.iter().any(|assumption| {
                assumption.kind == kind
                    && assumption.name == name
                    && assumption.contract == "closed-host-v1"
                    && assumption.at.starts_with(MANIFEST_FILE)
            }),
            "{qualified:?}"
        );
    }
    assert_eq!(ordinary.budget_id, qualified.budget_id);
    assert_eq!(ordinary.span, qualified.span);
    assert!(rust.contains("run_nonresuming"), "{rust}");
    // Source availability is not evidence that a runtime guard chose this path.
    let compact = rust.split_whitespace().collect::<String>();
    for (name, trusted) in [("run", false), (QUALIFIED, true)] {
        let signature = compact
            .split(&format!("pubfn{name}("))
            .nth(1)
            .unwrap_or_else(|| panic!("missing facade {name}: {rust}"))
            .split('{')
            .next()
            .unwrap();
        assert_eq!(
            signature.contains("TrustedBudgetHost"),
            trusted,
            "{signature}"
        );
        assert!(signature.contains("&dynFn(u64)->u64"), "{signature}");
    }
}

#[test]
fn externs_need_both_binding_metadata_and_a_qualified_entry() {
    tauto_messages::install();
    for (entry, binding) in [(false, false), (false, true), (true, false), (true, true)] {
        let text = format!(
            "rust {{ extern {{ native_read = \"bridge::read\" }} nonresuming {{ {} {} }} }}",
            if entry {
                "entries { run_with_nonresuming_contract = \"run\" }"
            } else {
                ""
            },
            if binding {
                "extern { native_read = \"closed-host-v1\" }"
            } else {
                ""
            },
        );
        let (reports, rust) = inspect(extern_source(), &text);
        let ordinary = report(&reports, "ordinary");
        assert!(has_reason(ordinary, "extern-contract"), "{ordinary:?}");
        assert!(ordinary.assumptions.is_empty(), "{ordinary:?}");
        if entry {
            let qualified = report(&reports, QUALIFIED);
            assert_eq!(qualified.eligible(), binding, "{qualified:?}");
            assert!(
                qualified.assumptions.iter().any(|a| a.kind == "embedding"),
                "{qualified:?}"
            );
            assert_eq!(
                qualified.assumptions.iter().any(|a| {
                    a.kind == "extern"
                        && a.name == "native_read"
                        && a.contract == "closed-host-v1"
                        && a.at.starts_with(MANIFEST_FILE)
                }),
                binding,
                "{qualified:?}"
            );
            if !binding {
                assert!(has_reason(qualified, "extern-contract"), "{qualified:?}");
            }
        } else {
            assert!(reports.iter().all(|r| r.variant == "ordinary"));
        }
        assert_eq!(rust.contains("run_nonresuming"), entry && binding, "{rust}");
    }
}

#[test]
fn trusted_text_externs_keep_directional_signature_checks() {
    tauto_messages::install();
    let text = r#"rust {
  extern { native_read = "bridge::read" }
  nonresuming {
    extern { native_read = "closed-host-v1" }
    entries { run_with_nonresuming_contract = "run" }
  }
}"#;
    for source in [
        r#"extern { fn native_read(value: Text): u64 }
fn run(): u64 {
  handle { budget(steps: 5) { native_read("value") } } with { exceeded(info), k => 0 }
}"#,
        r#"extern { fn native_read(value: u64): Text }
fn run(): Text {
  handle { budget(steps: 5) { native_read(0) } } with { exceeded(info), k => "exhausted" }
}"#,
        r#"extern { fn native_read(&value: Text): Text }
fn run(): Text {
  handle { budget(steps: 5) {
    let input := concat("a", "b")
    native_read(&input)
  } } with { exceeded(info), k => "exhausted" }
}"#,
        r#"extern { fn native_read(&value: Text): Option(Text) }
fn run(): Option(Text) {
  handle { budget(steps: 5) {
    let input := concat("a", "b")
    native_read(&input)
  } } with { exceeded(info), k => None }
}"#,
    ] {
        let (reports, rust) = inspect(source, text);
        let ordinary = report(&reports, "ordinary");
        assert!(!ordinary.eligible(), "{ordinary:?}");
        assert!(has_reason(ordinary, "extern-contract"), "{ordinary:?}");
        let qualified = report(&reports, QUALIFIED);
        assert!(qualified.eligible(), "{qualified:?}");
        assert!(qualified.assumptions.iter().any(|a| a.kind == "extern"));
        assert!(rust.contains("run_nonresuming"), "{rust}");
    }
}

#[test]
fn unsupported_trusted_extern_signatures_name_the_boundary_and_type() {
    tauto_messages::install();
    let text = r#"rust {
  extern { native_read = "bridge::read" }
  nonresuming {
    extern { native_read = "closed-host-v1" }
    entries { run_with_nonresuming_contract = "run" }
  }
}"#;
    for (source, location, ty) in [
        (
            r#"extern { fn native_read(value: Option(Text)): u64 }
fn run(): u64 {
  handle { budget(steps: 5) { native_read(Some("value")) } } with { exceeded(info), k => 0 }
}"#,
            "argument 1",
            "Option",
        ),
        (
            r#"extern { fn native_read(&value: Option(Text)): u64 }
fn run(): u64 {
  handle { budget(steps: 5) {
    let input := Some("value")
    native_read(&input)
  } } with { exceeded(info), k => 0 }
}"#,
            "argument 1",
            "Option",
        ),
        (
            r#"extern { fn native_read(&mut value: Text): u64 }
fn run(): u64 {
  handle { budget(steps: 5) {
    var input := "value"
    native_read(&mut input)
  } } with { exceeded(info), k => 0 }
}"#,
            "argument 1",
            "mut",
        ),
        (
            r#"extern { fn native_read(value: u64): Vec(Text) }
fn run(): u64 {
  handle { budget(steps: 5) { Vec::len(&native_read(0)) } } with { exceeded(info), k => 0 }
}"#,
            "result",
            "Vec",
        ),
        (
            r#"extern { fn native_read(&value: Text): &Text }
fn run(): u64 {
  handle { budget(steps: 5) {
    let input := "value"
    Text::len(native_read(&input))
  } } with { exceeded(info), k => 0 }
}"#,
            "result",
            "Text",
        ),
    ] {
        let (reports, rust) = inspect(source, text);
        let qualified = report(&reports, QUALIFIED);
        let reason = qualified
            .reasons
            .iter()
            .find(|r| r.code == "extern-signature")
            .unwrap_or_else(|| panic!("{qualified:?}"));
        for expected in ["native_read", location, ty] {
            assert!(reason.message.to_string().contains(expected), "{reason:?}");
        }
        assert!(!qualified.eligible());
        assert!(!rust.contains("run_nonresuming"), "{rust}");
    }
}

#[test]
fn generated_noncopy_data_requires_whole_embedding_assertion_without_callbacks() {
    tauto_messages::install();
    let source = r#"struct Held { value: Text }
fn run(): Held {
  handle { budget(steps: 5) { Held { value: "body" } } } with {
    exceeded(info), k => Held { value: "exhausted" }
  }
}
"#;
    let pkg = package(source);
    assert!(
        !pkg.datas
            .iter()
            .find(|data| data.name == "Held")
            .unwrap()
            .copy
    );
    let (reports, rust) = inspect(source, ENTRY);
    let ordinary = report(&reports, "ordinary");
    assert!(has_reason(ordinary, "unproven-lifetime"), "{ordinary:?}");
    assert!(ordinary.assumptions.is_empty(), "{ordinary:?}");
    let qualified = report(&reports, QUALIFIED);
    assert!(qualified.eligible(), "{qualified:?}");
    assert_eq!(qualified.assumptions.len(), 1, "{qualified:?}");
    assert_eq!(qualified.assumptions[0].kind, "embedding");
    assert_eq!(qualified.assumptions[0].name, QUALIFIED);
    assert!(rust.contains("TrustedBudgetHost"), "{rust}");
    assert!(rust.contains("run_nonresuming"), "{rust}");
}

#[test]
fn qualified_names_cannot_collide_with_exported_data_or_reserved_name_mappings() {
    tauto_messages::install();
    let pkg = package(
        r#"struct TrustedBudgetHost { value: u64 }
fn run(value: TrustedBudgetHost): u64 { value.value }"#,
    );
    assert_error(
        resolve(
            &pkg,
            r#"rust { nonresuming { entries { TrustedBudgetHost = "run" } } }"#,
        )
        .unwrap_err(),
        "collides with an exported data name",
    );
    let pkg = package(r#"pub fn run(): u64 { 7 }"#);
    // `self` is `self_` and `self_` is `self__`: the two stay apart.
    if let Err(e) = resolve(
        &pkg,
        r#"rust { nonresuming { entries { self = "run" self_ = "run" } } }"#,
    ) {
        assert!(!e.contains("collides"), "{e}");
    }
}

#[test]
fn invalid_direct_bindings_do_not_report_suppressed_qualified_variants() {
    tauto_messages::install();
    let source = r#"pub fn run(): u64 { handle { budget(steps: 0) { 7 } } with { exceeded(info), k => 0 } }"#;
    let mut pkg = package(source);
    pkg.exports
        .iter_mut()
        .find(|e| e.name == "run")
        .unwrap()
        .row
        .push("Div".into());
    let mut bindings = Bindings::default();
    bindings.nonresuming_entries.insert(
        "qualified".into(),
        tauto_rustgen::EntryContract {
            function: "run".into(),
            at: "manual binding".into(),
        },
    );
    let sources = Sources {
        file: "main.taut",
        text: source,
    };
    assert!(
        budget_diagnostics(&pkg, &sources, &bindings)
            .iter()
            .all(|r| r.variant == "ordinary")
    );
    let (rust, _) = emit_lib(&pkg, &sources, &bindings);
    assert!(!rust.contains("TrustedBudgetHost"));
    assert!(!rust.contains("pub fn qualified"));
}
