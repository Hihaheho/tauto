//! Facade selection does not change package validation or helper lowering.
use std::path::PathBuf;
fn generate(
    name: &str,
    exports: &str,
    source: &str,
) -> Result<(String, String, Vec<String>), String> {
    let dir = std::env::temp_dir().join(format!("tauto-exports-{}-{name}", std::process::id()));
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Tauto.eure"),
        format!("package {{ name = \"exports\"\n version = \"0.1.0\" }}\nrust {{ {exports} }}\n"),
    )
    .unwrap();
    std::fs::write(dir.join("src/main.taut"), source).unwrap();
    let result = tauto_build::generate(&PathBuf::from(&dir).join("Tauto.eure"), None);
    std::fs::remove_dir_all(dir).unwrap();
    result
}
fn source_source() -> &'static str {
    r#"
fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
fn safe(steps: i64): Bool {
  handle { budget(steps: steps) { visit(2); true } } with { exceeded(info), k => false }
}
fn unused(n: i64): i64 { n + 1 }
"#
}
#[test]
fn selection_omission_and_empty_have_distinct_contracts() {
    tauto_messages::install();
    let (_, legacy, warnings) = generate("legacy", "", source_source()).unwrap();
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("visit") && w.contains("Div"))
    );
    assert!(legacy.contains("pub fn unused"));
    let (_, selected, warnings) =
        generate("selected", "exports = [\"safe\"]", source_source()).unwrap();
    assert!(warnings.is_empty());
    let facade = selected.split("pub mod api").nth(1).unwrap();
    assert!(facade.contains("pub fn safe"));
    assert!(!facade.contains("pub fn unused"));
    let (_, empty, warnings) = generate("empty", "exports = []", source_source()).unwrap();
    assert!(warnings.is_empty());
    let facade = empty.split("pub mod api").nth(1).unwrap();
    for name in ["safe", "visit", "unused"] {
        assert!(!facade.contains(&format!("pub fn {name}")));
    }
}
#[test]
fn explicit_invalid_exports_are_errors() {
    tauto_messages::install();
    for (name, setting, expected) in [
        ("unknown", "exports = [\"typo\"]", "unknown or generic"),
        ("duplicate", "exports = [\"safe\", \"safe\"]", "duplicate"),
        ("effect", "exports = [\"visit\"]", "Div"),
    ] {
        let err = generate(name, setting, source_source()).unwrap_err();
        assert!(err.contains(expected), "{err}");
    }
    let err = generate(
        "closure",
        "exports = [\"run\"]",
        r#"fn run(f: () -> i64): i64 { f() }"#,
    )
    .unwrap_err();
    assert!(err.contains("not exposed to Rust"), "{err}");
    let err = generate(
        "generic",
        "exports = [\"identity\"]",
        r#"fn identity<A>(x: A): A { x }"#,
    )
    .unwrap_err();
    assert!(err.contains("unknown or generic"), "{err}");
}
#[test]
fn unselected_helpers_are_still_checked() {
    tauto_messages::install();
    let err = generate(
        "bad-helper",
        "exports = [\"safe\"]",
        r#"fn safe(): i64 { 1 }
fn broken(): i64 { true }"#,
    )
    .unwrap_err();
    assert!(err.contains("type") || err.contains("expected"), "{err}");
}

#[test]
fn propositions_are_checked_despite_runtime_constructor_names() {
    tauto_messages::install();
    let source = r#"
enum Token { True, False }
inductive Box: Type { Mk(value: Nat): Box }
fn Valid(b: Option(Box), n: Nat): Prop {
  match b: Prop { None => False, Some(v) => n = Zero }
}
theorem box_zero(): Valid(Some(Box::Mk(Zero)), Zero) { Refl }
"#;
    generate("logical-constructor", "exports = []", source).unwrap();
    let invalid = source.replace(r#"Zero) { Refl }"#, r#"Succ(Zero)) { Refl }"#);
    let err = generate("logical-constructor-invalid", "exports = []", &invalid).unwrap_err();
    assert!(
        err.contains("box_zero") && !err.contains("`Valid` is not defined"),
        "{err}"
    );
    let invalid_body = source.replace("None => False", "None => missing_predicate");
    let err = generate(
        "logical-constructor-invalid-body",
        "exports = []",
        &invalid_body,
    )
    .unwrap_err();
    assert!(
        err.contains("Valid") && err.contains("missing_predicate"),
        "{err}"
    );
}

#[test]
fn borrowed_callback_facade_is_explicit_and_effect_free() {
    tauto_messages::install();
    let source = r#"fn apply(&f: (u64) -> u64, value: u64): u64 { f(value) }"#;
    for (name, setting) in [
        ("borrowed-selected", "exports = [\"apply\"]"),
        ("borrowed-legacy", ""),
    ] {
        let (_, generated, warnings) = generate(name, setting, source).unwrap();
        assert!(warnings.is_empty(), "{warnings:?}");
        let facade = generated.split("pub mod api").nth(1).unwrap();
        assert!(facade.contains("&dyn Fn(u64) -> u64"), "{facade}");
        assert!(!facade.contains("'static"), "{facade}");
    }
    for (name, source) in [
        (
            "borrowed-mut",
            r#"fn apply(&mut f: (u64) -> u64, value: u64): u64 { f(value) }"#,
        ),
        (
            "borrowed-effect",
            r#"fn apply(&f: (u64) -> u64 ! {∀ A. show(A)}, value: u64): u64 { handle { f(value) } with { ∀ A. show<A>(name, text), k => k(#()) } }"#,
        ),
        (
            "borrowed-nested-fn",
            r#"fn apply(&f: (() -> u64) -> u64): u64 { 0 }"#,
        ),
        (
            "borrowed-return-fn",
            r#"fn apply(&f: () -> (() -> u64)): u64 { 0 }"#,
        ),
        (
            "borrowed-hidden-fn",
            r#"struct Holder { callback: () -> u64 }
fn apply(&f: (Holder) -> u64): u64 { 0 }"#,
        ),
    ] {
        let error = generate(name, "exports = [\"apply\"]", source).unwrap_err();
        assert!(error.contains("not exposed to Rust"), "{name}: {error}");
    }
}

#[test]
fn borrowed_callbacks_cannot_supply_borrowed_or_function_results() {
    tauto_messages::install();
    for (name, source) in [
        (
            "borrowed-result",
            r#"fn apply(&f: (&Text) -> &Text, value: u64): u64 { value }"#,
        ),
        (
            "borrowed-hidden-result",
            r#"struct Holder { callback: () -> u64 }
fn apply(&f: () -> Holder, value: u64): u64 { value }"#,
        ),
    ] {
        let error = generate(name, "exports = [\"apply\"]", source).unwrap_err();
        assert!(error.contains("not exposed to Rust"), "{name}: {error}");
    }
    let source = r#"fn apply(&f: (u64) -> u64): ((u64) -> u64) { (value) => f(value) }"#;
    let error = generate("borrowed-escape", "exports = [\"apply\"]", source).unwrap_err();
    assert!(
        error.contains("borrow") || error.contains("not exposed to Rust"),
        "{error}"
    );
}

#[test]
fn a_budget_cannot_export_a_callback_result() {
    tauto_messages::install();
    let source = r#"
fn leak(&read: (u64) -> u64): ((u64) -> u64) {
  handle { budget(steps: 1000) { (i) => read(i) } } with { exceeded(info), k => (j) => 0 }
}
"#;
    let error = generate("budget-return", "exports = [\"leak\"]", source).unwrap_err();
    assert!(
        error.contains("cannot follow the effects of a function value required by its type"),
        "{error}"
    );
}

#[test]
fn nonresuming_entries_reject_missing_unselected_and_unsupported_targets() {
    tauto_messages::install();
    for (name, config, source, expected) in [
        (
            "contract-missing",
            "nonresuming { entries { trusted = \"missing\" } }",
            source_source(),
            "unknown or unselected export missing",
        ),
        (
            "contract-unselected",
            "exports = [\"safe\"] nonresuming { entries { trusted = \"unused\" } }",
            source_source(),
            "unknown or unselected export unused",
        ),
        (
            "contract-empty-selection",
            "exports = [] nonresuming { entries { trusted = \"safe\" } }",
            source_source(),
            "unknown or unselected export safe",
        ),
        (
            "contract-effect",
            "nonresuming { entries { trusted = \"visit\" } }",
            source_source(),
            "performs Div",
        ),
        (
            "contract-owned-callback",
            "nonresuming { entries { trusted = \"run\" } }",
            r#"fn run(read: (u64) -> u64): u64 { read(0) }"#,
            "not exposed to Rust",
        ),
        (
            "contract-generic",
            "nonresuming { entries { trusted = \"identity\" } }",
            r#"fn identity<A>(value: A): A { value }"#,
            "unknown or unselected export identity",
        ),
    ] {
        let error = generate(name, config, source).unwrap_err();
        assert!(error.contains(expected), "{name}: {error}");
    }
}

#[test]
fn nonresuming_entries_are_additive_to_the_selected_callback_facade() {
    tauto_messages::install();
    let source = r#"fn run(&read: (u64) -> u64, value: u64): u64 {
      handle { budget(steps: 10) { read(value) } } with { exceeded(info), k => 0 }
    }"#;
    let (_, generated, warnings) = generate(
        "contract-selected",
        "exports = [\"run\"] nonresuming { entries { run_trusted = \"run\" } }",
        source,
    )
    .unwrap();
    assert!(warnings.is_empty(), "{warnings:?}");
    let facade = generated.split("pub mod api").nth(1).unwrap();
    assert!(facade.contains("pub fn run("), "{facade}");
    assert!(facade.contains("pub fn run_trusted("), "{facade}");
    assert!(facade.contains("TrustedBudgetHost"), "{facade}");
    assert!(facade.contains("&dyn Fn(u64) -> u64"), "{facade}");
}
#[test]
fn uniffi_exports_wrap_the_facade() {
    tauto_messages::install();
    let source = r#"import std::prelude::Affine

fn greet(name: Text, times: i64): Text { if times > 0 { name } else { "nobody" } }
fn first(names: Vec(Text)): Option(Text) { None }
fn twice(n: i64): i64 { n + n }
fn keep(u: Unit): i64 { 1 }
"#;
    let (_, text, warnings) = generate("uniffi", "uniffi = true", source).unwrap();
    let api = text.split("pub mod uniffi_api").nth(1).unwrap();
    assert!(api.contains("#[uniffi::export]"), "{api}");
    assert!(
        api.contains("pub fn greet(name: String, times: i64) -> String"),
        "{api}"
    );
    assert!(
        api.contains("pub fn first(names: Vec<String>) -> Option<String>"),
        "{api}"
    );
    assert!(api.contains("pub fn twice(n: i64) -> i64"), "{api}");
    assert!(!api.contains("pub fn keep"), "{api}");
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("keep") && w.contains("UniFFI")),
        "{warnings:?}"
    );
    let (_, plain, _) = generate("no-uniffi", "", source).unwrap();
    assert!(!plain.contains("uniffi::export"));
    let err = generate(
        "uniffi-keep",
        "uniffi = true\n exports = [\"keep\"]",
        source,
    )
    .unwrap_err();
    assert!(err.contains("not exposed to UniFFI"), "{err}");
}
