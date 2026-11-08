//! The case runner rejects assertions it cannot check.
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use tauto_test_suite::{Outcome, run_all, run_path};
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let dir = std::env::temp_dir().join(format!(
            "tauto-runner-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&dir).unwrap();
        Self(dir)
    }
    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, text).unwrap();
        path
    }
    fn outcome(&self, text: &str) -> Outcome {
        let path = self.write("case.eure", text);
        let mut report = run_path(&path, &self.0, None).unwrap();
        assert!(report.error.is_none(), "{:?}", report.error);
        assert_eq!(report.results.len(), 1);
        report.results.remove(0).1
    }
    fn passes(&self, text: &str) {
        match self.outcome(text) {
            Outcome::Passed => {}
            Outcome::Failed(e) => panic!("{e}"),
            _ => panic!("case did not pass"),
        }
    }
    fn fails(&self, text: &str, expected: &str) {
        match self.outcome(text) {
            Outcome::Failed(e) => assert!(e.contains(expected), "{e}"),
            _ => panic!("expected failure: {expected}"),
        }
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
#[test]
fn validation_is_shared_and_cannot_be_hidden_by_unimplemented() {
    let f = Fixture::new();
    for text in [
        "source = \"\"\nchekcs = \"ok\"",
        "source = \"\"\nchecks {}",
        "source = \"\"\nunimplemented = true\nchecks.typo = 1",
        "source = \"\"\nshows = [1]",
        "source = \"\"\nchecks_all = \"typo\"",
        "source = \"\"\nbudget = 1",
        "a = []\nb = []\nequal = true\nshows = []",
        "source = \"\"\nbuild = \"typo\"",
        "source = \"\"\nparses = true\nrust = \"typo\"",
        "source = \"\"\ndiagnostics = [{ message => \"\", typo => true }]",
    ] {
        assert!(matches!(f.outcome(text), Outcome::Failed(_)), "{text}");
        let reports = run_all(&f.0, None).unwrap();
        assert!(reports[0].failed(), "{text}");
    }
}
#[test]
fn path_sources_keep_their_import_and_include_base() {
    let f = Fixture::new();
    f.write("lib/dep.taut", r#"pub def identity(n: Nat): Nat := n"#);
    f.write(
        "lib/main.taut",
        r#"import "dep.taut"
theorem good(): identity(3) = 3 { Refl }"#,
    );
    f.passes("source = path`lib/main.taut`\nchecks_all = \"ok\"\nchecks.good = \"ok\"");
    f.write(
        "cases/nested.eure",
        "source = path`../lib/main.taut`\nchecks_all = \"ok\"",
    );
    let report = run_path(&f.0.join("cases/nested.eure"), &f.0, None).unwrap();
    assert!(!report.failed(), "{:?}", report.error);
    f.write("lib/message.txt", "hello");
    f.write(
        "lib/include.taut",
        r#"perform show("text", include_text!("message.txt"))"#,
    );
    f.passes(
        r#"source = path`lib/include.taut`
shows = ["text = \"hello\""]"#,
    );
    f.fails(
        "source = path`absent.taut`\nchecks_all = \"ok\"",
        "absent.taut",
    );
}
#[test]
fn all_declarations_and_qualified_names_are_checked() {
    let f = Fixture::new();
    let source = r#"source = ```tauto
theorem good(): Nat { 0 }
theorem bad(): Eq(Nat, 0, 1) { Refl }
```
"#;
    f.fails(&format!("{source}checks_all = \"ok\""), "bad");
    f.passes(&format!(
        "{source}checks_all = \"ok\"\nchecks.bad = \"error: \""
    ));
    f.fails("source = \"\"\nchecks_all = \"ok\"", "no declarations");
    f.passes(
        r#"files."dep.taut" = `theorem good(): Nat { 0 }`
files."main.nib" = `import "dep.taut"`
checks."dep.taut::good" = "ok""#,
    );
}
#[test]
fn load_errors_and_multifile_type_errors_are_expectations() {
    let f = Fixture::new();
    f.passes(
        r#"files."main.nib" = `import "absent.taut"`
load_error = "absent.taut""#,
    );
    f.passes(
        r#"files."main.nib" = `import "dep.taut"`
files."dep.taut" = `import "main.nib"`
load_error = "cycle""#,
    );
    f.passes(
        r#"files."main.nib" = `let x: i64 := true`
types = "error: ""#,
    );
    f.fails(
        "files.\"main.nib\" = \"\"\nload_error = \"missing\"",
        "success",
    );
}
#[test]
fn diagnostics_check_counts_messages_and_byte_positions() {
    let f = Fixture::new();
    let source = r#"source = `theorem bad(): Eq(Nat, 0, 1) { Refl }`
"#;
    f.passes(&format!(
        "{source}diagnostics = [{{ name => \"bad\", message => \"\", span => \"theorem bad(): Eq(Nat, 0, 1) {{ «Refl» }}\" }}]"
    ));
    f.fails(&format!("{source}diagnostics = []"), "diagnostic count");
    f.fails(
        &format!("{source}diagnostics = [{{ message => \"\", span => \"«absent»\" }}]"),
        "is not in the source",
    );
    f.passes(
        r#"source = `let x: i64 := true`
diagnostics = [{ stage => "types", message => "", span => "let x: i64 := «true»" }]"#,
    );
}
#[test]
fn runtime_assertions_cover_streams_exit_and_budget() {
    let f = Fixture::new();
    f.passes(
        r#"source = `perform show("answer", 42)`
shows = ["answer = 42"]
stdout = ""
stderr = ""
exit = 0
budget = 10000"#,
    );
    f.fails(
        r#"source = `perform show("answer", 42)`
stdout = "wrong""#,
        "stdout",
    );
    f.passes(
        r#"source = `while true { }`
budget = 0
run_error = "step limit""#,
    );
}
#[test]
fn stale_unimplemented_marks_make_the_report_fail() {
    let f = Fixture::new();
    let path = f.write(
        "case.eure",
        "source = \"\"\nparses = true\nunimplemented = true",
    );
    let report = run_path(&path, &f.0, None).unwrap();
    assert!(report.failed());
    assert!(matches!(report.results[0].1, Outcome::UnexpectedPass));
}

#[test]
fn holes_preserve_the_goal_and_ordered_context() {
    let f = Fixture::new();
    let source = r#"source = `theorem unfinished(n: Nat): n = n { ?proof }`
"#;
    f.passes(&format!("{source}holes = [{{ declaration => \"unfinished\", name => \"proof\", goal => \"n = n\", context => [\"n: Nat\"] }}]"));
    f.fails(&format!("{source}holes = []"), "hole count");
}
#[test]
fn external_sources_are_resolved_for_the_rust_backend() {
    let f = Fixture::new();
    f.write("lib/helper.taut", r#"pub fn twice(n: i64): i64 { n + n }"#);
    f.write(
        "lib/main.taut",
        r#"import "helper.taut"
perform show("answer", twice(21))"#,
    );
    f.write(
        "case.eure",
        "source = path`lib/main.taut`\nshows = [\"answer = 42\"]",
    );
    let cases = tauto_test_suite::rust_cases(&f.0).unwrap();
    let source = cases[0].compilation_source().unwrap();
    assert!(!source.contains("import "));
    tauto_nir::compile(&source).unwrap();
}
#[test]
fn utf8_diagnostics_use_byte_offsets_and_character_columns() {
    let f = Fixture::new();
    f.passes(
        r#"source = `let あ: i64 := true`
diagnostics = [{ stage => "types", message => "", span => "let あ: i64 := «true»" }]"#,
    );
}
#[test]
fn runtime_streams_and_nonzero_exit_are_checked() {
    let f = Fixture::new();
    f.passes(
        r#"source = ```tauto
import std::prelude::Os
print("hello"); eprint("warning"); perform exit(7)
```
stdout = "hello"
stderr = "warning"
exit = 7"#,
    );
}

#[test]
fn direct_case_invocation_finds_repository_grammar_fixtures() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let path = repo.join("cases/macro/syntax.eure");
    let report = run_path(
        &path,
        path.parent().unwrap(),
        Some(tauto_test_suite::Filter::Contains(
            "a-syntax-macro-makes-the-theorem-statement",
        )),
    )
    .unwrap();
    assert_eq!(report.results.len(), 1);
    assert!(!report.failed());
}
#[test]
fn missing_path_expectations_are_not_backend_inputs() {
    let f = Fixture::new();
    let case = "source = path`absent.taut`\nload_error = \"absent.taut\"";
    f.passes(case);
    assert!(tauto_test_suite::rust_cases(&f.0).unwrap().is_empty());
}

#[test]
fn imports_keep_source_positions_and_work_for_the_backend() {
    let f = Fixture::new();
    f.write("lib/helper.taut", r#"pub fn twice(n: i64): i64 { n + n }"#);
    f.passes(
        r#"source = `perform show("answer", twice(21))`
imports = [path`lib/helper.taut`]
shows = ["answer = 42"]"#,
    );
    let cases = tauto_test_suite::rust_cases(&f.0).unwrap();
    tauto_nir::compile(&cases[0].compilation_source().unwrap()).unwrap();
    f.write("lib/proof.taut", r#"theorem identity(n: Nat): Nat { n }"#);
    f.passes(
        r#"source = `theorem bad(): Eq(Nat, 0, 1) { Refl }`
imports = [path`lib/proof.taut`]
diagnostics = [{ name => "bad", message => "", span => "theorem bad(): Eq(Nat, 0, 1) { «Refl» }" }]"#,
    );
}

#[test]
fn repeated_declarations_need_an_explicit_occurrence() {
    let f = Fixture::new();
    let source = r#"source = ```tauto
theorem t(): Nat { 0 }
theorem t(): Nat { 0 }
```
"#;
    f.fails(&format!("{source}checks.t = \"ok\""), "found 2");
    f.passes(&format!("{source}checks_all = \"ok\"\nchecks.\"t#2\" = \"error: already defined\"\ndeclarations = [\"t\", \"t\"]"));
    f.fails(
        &format!("{source}checks.\"t#0\" = \"ok\""),
        "invalid declaration occurrence",
    );
}

#[test]
fn tote_sources_use_the_manifest_and_runtime_assertions() {
    let f = Fixture::new();
    f.write(
        "demo/Tauto.eure",
        "package { name = \"demo\"\nversion = \"0.1.0\" }",
    );
    f.write(
        "demo/src/main.taut",
        "import std::prelude::Os\nprint(\"hello\")",
    );
    f.passes("tote = path`demo`\nstdout = \"hello\"");
}

#[test]
fn insertion_fixes_are_checked_at_the_written_call() {
    let f = Fixture::new();
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap();
    let text = std::fs::read_to_string(repo.join("cases/check/macros.eure"))
        .unwrap()
        .replace(
            "path`../fixtures/",
            &format!("path`{}/cases/fixtures/", repo.display()),
        )
        .replace(
            "path`../../crates/",
            &format!("path`{}/crates/", repo.display()),
        );
    let filter = Some(tauto_test_suite::Filter::Contains(
        "a-call-that-makes-a-declaration-without-a-list-is-an-error-0",
    ));
    let path = f.write("case.eure", &text);
    let report = run_path(&path, &f.0, filter).unwrap();
    assert!(report.error.is_none(), "{:?}", report.error);
    assert_eq!(report.results.len(), 1);
    match &report.results[0].1 {
        Outcome::Passed => {}
        Outcome::Failed(error) => panic!("{error}"),
        _ => panic!("case did not pass"),
    }
    let correct = r#"fixed_source = ```tauto
import "mk.nib"
mk!(`produced unused`) => fn produced
fn user(): i64 { produced() }
```"#;
    let wrong = r#"fixed_source = ```tauto
 => fn producedimport "mk.nib"
mk!(`produced unused`)
fn user(): i64 { produced() }
```"#;
    assert!(text.contains(correct));
    f.write("case.eure", &text.replace(correct, wrong));
    let report = run_path(&path, &f.0, filter).unwrap();
    assert!(report.error.is_none(), "{:?}", report.error);
    match &report.results[0].1 {
        Outcome::Failed(error) => assert!(error.contains("diagnostic fixed source"), "{error}"),
        _ => panic!("an insertion at the wrong position passed"),
    }
}

impl Fixture {
    fn backend_case(&self, text: &str) -> tauto_test_suite::RustCase {
        self.write("case.eure", text);
        let mut cases = tauto_test_suite::rust_cases(&self.0).expect("valid backend case");
        assert_eq!(cases.len(), 1);
        cases.remove(0)
    }
}

#[test]
fn backend_selection_is_explicit_and_validated() {
    let f = Fixture::new();
    let case = f.backend_case("source = \"\"\nshows = []\nbackends = [\"javascript\"]");
    assert!(!case.selects_backend("rust"));
    assert!(case.selects_backend("javascript"));
    assert!(!case.explicit_backend("rust"));
    assert!(case.explicit_backend("javascript"));
    for backends in ["[]", "[\"other\"]", "[\"rust\", \"rust\"]"] {
        assert!(matches!(
            f.outcome(&format!(
                "source = \"\"\nparses = true\nbackends = {backends}"
            )),
            Outcome::Failed(_)
        ));
    }
    f.fails(
        "source = \"\"\nparses = true\nbackends = [\"rust\"]\ncompile_errors.javascript = \"front: rejected\"",
        "excluded",
    );
    f.fails(
        "source = \"\"\nparses = true\nbackends = [\"rust\"]\nbackend_known_failure.javascript = \"runtime: unavailable\"",
        "excluded",
    );
    assert!(matches!(
        f.outcome("source = \"\"\ncompile_errors.rust = \"front: rejected\""),
        Outcome::BackendOnly
    ));
}

#[test]
fn compilation_failures_require_both_the_declared_stage_and_message() {
    tauto_messages::install();
    let f = Fixture::new();
    let case = f.backend_case(
        r#"source = `let value: i64 := true`
compile_errors.rust = "front: type error""#,
    );
    assert!(case.selects_backend("rust"));
    assert!(!case.selects_backend("javascript"));
    assert_eq!(
        case.check_compile_error("rust", "front", "type error: mismatch"),
        Ok(true)
    );
    assert!(
        case.check_compile_error("rust", "unsupported", "type error: mismatch")
            .is_err()
    );
    assert!(
        case.check_compile_error("rust", "front", "unrelated failure")
            .is_err()
    );
    assert_eq!(
        case.check_compile_error("javascript", "front", "type error"),
        Ok(false)
    );
    assert!(
        case.check_compiled("rust")
            .unwrap_err()
            .contains("compilation succeeded")
    );
    assert!(case.check_compiled("javascript").is_ok());
    match case.compile("rust") {
        Err(tauto_nir::CompileError::Front(message)) => {
            assert_eq!(
                case.check_compile_error("rust", "front", &message),
                Ok(true)
            );
        }
        other => panic!("expected the frontend type failure, got {other:?}"),
    }
    for value in ["message only", "runtime: wrong stage", "front: "] {
        f.fails(
            &format!("source = \"\"\nparses = true\ncompile_errors.rust = {value:?}"),
            "compile_errors",
        );
    }
}

#[test]
fn known_backend_failures_do_not_hide_wrong_errors_or_stale_success() {
    let f = Fixture::new();
    let compile = f.backend_case("source = \"\"\nparses = true\nbackend_known_failure.rust = \"unsupported: missing feature\"");
    assert_eq!(
        compile.check_limitation("rust", "unsupported", "missing feature: details"),
        Ok(true)
    );
    assert!(
        compile
            .check_limitation("rust", "front", "missing feature")
            .is_err()
    );
    assert!(
        compile
            .check_limitation("rust", "unsupported", "different feature")
            .is_err()
    );
    assert_eq!(
        compile.check_limitation("javascript", "unsupported", "missing feature"),
        Ok(false)
    );
    assert!(
        compile.check_compiled("rust").is_err(),
        "a stale compile limitation passed"
    );

    let runtime = f.backend_case("source = \"\"\nshows = []\nbackend_known_failure.rust = \"runtime: unavailable operation\"");
    assert!(runtime.check_compiled("rust").is_ok());
    assert_eq!(
        runtime.check_limitation("rust", "runtime", "unavailable operation: details"),
        Ok(true)
    );
    assert!(
        runtime
            .check_limitation("rust", "build", "unavailable operation")
            .is_err()
    );
    assert!(
        runtime.check_output("rust", &[], "", "", Some(0)).is_err(),
        "a stale runtime limitation passed"
    );
    for value in ["message only", "unknown: message", "runtime: "] {
        f.fails(
            &format!("source = \"\"\nparses = true\nbackend_known_failure.rust = {value:?}"),
            "backend_known_failure",
        );
    }
    f.fails(
        "source = \"\"\nparses = true\ncompile_errors.rust = \"front: rejected\"\nbackend_known_failure.rust = \"front: rejected\"",
        "both",
    );
}

#[test]
fn shared_fixtures_are_validated_but_never_count_as_passed_cases() {
    let f = Fixture::new();
    let path = f.write(
        "case.eure",
        "@ fixtures.host\nsource = \"not a complete program\"\nreason = \"Host API fragment\"",
    );
    let report = run_path(&path, &f.0, None).unwrap();
    assert!(report.error.is_none());
    assert!(report.results.is_empty());
    assert!(tauto_test_suite::rust_cases(&f.0).unwrap().is_empty());
    assert!(tauto_test_suite::capabilities(&f.0).unwrap().is_empty());
    for body in [
        "source = \"\"\nreason = \" \"",
        "source = \"\"",
        "reason = \"missing source\"",
        "source = \"\"\nreason = \"host\"\nunknown = true",
    ] {
        f.write("case.eure", &format!("@ fixtures.host\n{body}"));
        assert!(
            run_path(&path, &f.0, None).unwrap().error.is_some(),
            "{body}"
        );
        assert!(tauto_test_suite::rust_cases(&f.0).is_err(), "{body}");
        assert!(tauto_test_suite::capabilities(&f.0).is_err(), "{body}");
    }
    f.fails(
        "@ cases.one\nsource = \"\"\nparses = true\nfixtures.hidden { source = \"\"\nreason = \"nested\" }",
        "cannot be nested",
    );
}

#[test]
fn inferred_expectations_check_names_values_rows_and_kinds() {
    let f = Fixture::new();
    let source = r#"source = ```tauto
effect ask(): i64
fn query(): i64 ! {ask} { perform ask() }
affine struct Resource {}
let number: i32 := 1
```
"#;
    f.passes(&format!("{source}inferred_types.number = \"i32\"\ninferred_rows.query = [\"ask\"]\ninferred_kinds.Resource = \"affine\""));
    f.fails(
        &format!("{source}inferred_types.number = \"i64\""),
        "inferred_types.number",
    );
    f.fails(
        &format!("{source}inferred_types.missing = \"i32\""),
        "expected one binding",
    );
    f.fails(
        &format!("{source}inferred_rows.query = []"),
        "inferred_rows.query",
    );
    f.fails(
        &format!("{source}inferred_rows.missing = []"),
        "expected one function",
    );
    f.fails(
        &format!("{source}inferred_kinds.Resource = \"copy\""),
        "inferred_kinds.Resource",
    );
    f.fails(
        &format!("{source}inferred_kinds.Missing = \"shared\""),
        "inferred_kinds.Missing",
    );
    f.fails(
        r#"source = "let value := 1\nlet value := 2"
inferred_types.value = "i64""#,
        "expected one binding",
    );
    for field in ["inferred_types", "inferred_rows", "inferred_kinds"] {
        f.fails(&format!("source = \"\"\n{field} {{}}"), "cannot be empty");
    }
    f.fails(
        &format!("{source}inferred_kinds.Resource = \"unknown\""),
        "copy/shared/affine/linear",
    );
}

#[test]
fn javascript_row_expectations_use_the_javascript_checker() {
    let f = Fixture::new();
    let source = r#"source = ```tauto
effect ask(): Text
extern { fn host(&read: () -> Text): Text }
fn caller(): Text ! {ask} { host(&(() => perform ask())) }
```
"#;
    f.passes(&format!(
        "{source}rows = \"error: cannot perform ask\"\nrows_javascript = \"ok\""
    ));
    f.fails(
        &format!("{source}rows_javascript = \"error: cannot perform ask\""),
        "rows_javascript",
    );
    let restricted = source.replace("&read: () -> Text)", "&read: () -> Text ! {})");
    f.passes(&format!(
        "{restricted}rows_javascript = \"error: its type permits\""
    ));
}

#[test]
fn formatting_and_lint_expectations_are_exact_and_validate_failures() {
    let f = Fixture::new();
    f.passes(
        r#"source = "let value := 1\n"
format = "let value := 1\n""#,
    );
    f.fails(
        r#"source = "let value := 1\n"
format = "let value := 2\n""#,
        "format",
    );
    f.passes(
        r#"source = "let value := 'open"
format_error = "an unclosed string""#,
    );
    f.fails(
        r#"source = "let value := 1"
format_error = "an unclosed string""#,
        "format_error",
    );
    f.fails(
        r#"source = "let value := 'open"
format_error = "different error""#,
        "format_error",
    );
    f.fails(
        "source = \"\"\nformat = \"\"\nformat_error = \"error\"",
        "mutually exclusive",
    );
    f.fails("source = \"\"\nformat_error = \" \"", "nonempty");
    f.passes(
        r#"source = `fn identity(n: Nat): Nat { n }`
lint = []"#,
    );
    let hole = r#"source = `theorem identity(n: Nat): n = n { ?hole }`
"#;
    f.passes(&format!("{hole}lint = [\"a hole\"]"));
    f.fails(&format!("{hole}lint = []"), "lint count");
    f.fails(&format!("{hole}lint = [\"different finding\"]"), "lint");
}

#[test]
fn backend_output_contracts_keep_streams_and_exit_distinct() {
    let f = Fixture::new();
    let case = f.backend_case("source = \"\"\nshows = [\"common = 1\"]\nrust_shows = [\"rust = 2\"]\njavascript_shows = [\"javascript = 3\"]\nstdout = \"output\"\nstderr = \"warning\"\nexit = 7");
    let rust = vec!["rust = 2".to_string()];
    let javascript = vec!["javascript = 3".to_string()];
    assert!(
        case.check_output("rust", &rust, "output", "warning", Some(7))
            .is_ok()
    );
    assert!(
        case.check_output("javascript", &javascript, "output", "warning", Some(7))
            .is_ok()
    );
    assert!(
        case.check_output("javascript", &rust, "output", "warning", Some(7))
            .is_err()
    );
    for (out, err, exit, wanted) in [
        ("wrong", "warning", Some(7), "stdout"),
        ("output", "wrong", Some(7), "stderr"),
        ("output", "warning", Some(0), "exit"),
        ("output", "warning", None, "exit"),
    ] {
        assert!(
            case.check_output("rust", &rust, out, err, exit)
                .unwrap_err()
                .contains(wanted)
        );
    }
    assert!(
        case.check_output("rust", &[], "rust = 2\noutput", "warning", Some(7))
            .unwrap_err()
            .contains("shows")
    );
    let error = f.backend_case("source = \"\"\nrun_error = \"common failure\"\nrust_error = \"rust failure\"\njavascript_error = \"javascript failure\"");
    assert!(
        error
            .check_output("rust", &[], "", "rust failure", Some(1))
            .is_ok()
    );
    assert!(
        error
            .check_output("javascript", &[], "", "javascript failure", Some(1))
            .is_ok()
    );
    assert!(
        error
            .check_output("javascript", &[], "", "rust failure", Some(1))
            .is_err()
    );
    assert!(
        error
            .check_output("rust", &[], "rust failure", "", Some(1))
            .is_err()
    );
    assert!(
        error
            .check_output("rust", &[], "", "rust failure", Some(0))
            .is_err()
    );

    let partial = f.backend_case("source = \"\"\nrust_error = \"rust failure\"\nrust_shows = [\"partial = 1\"]\nstdout = \"before failure\"\nstderr = \"rust failure: detail\"\nexit = 7");
    let observations = vec!["partial = 1".to_string()];
    assert!(
        partial
            .check_output(
                "rust",
                &observations,
                "before failure",
                "rust failure: detail",
                Some(7)
            )
            .is_ok()
    );
    for (shows, stdout, stderr, exit, message) in [
        (
            &observations[..],
            "wrong",
            "rust failure: detail",
            Some(7),
            "stdout",
        ),
        (
            &observations[..],
            "before failure",
            "rust failure: different",
            Some(7),
            "stderr",
        ),
        (
            &observations[..],
            "before failure",
            "rust failure: detail",
            Some(1),
            "exit",
        ),
        (
            &[][..],
            "before failure",
            "rust failure: detail",
            Some(7),
            "shows before error",
        ),
    ] {
        assert!(
            partial
                .check_output("rust", shows, stdout, stderr, exit)
                .unwrap_err()
                .contains(message)
        );
    }
    // An explicit JavaScript success contract overrides inherited failures,
    // but it does not change what the Rust route must observe.
    for failure_field in ["rust_error", "run_error"] {
        let divergent = f.backend_case(&format!(
            "source = \"\"\n{failure_field} = \"inherited failure\"\njavascript_shows = [\"javascript = 3\"]"
        ));
        assert!(
            divergent
                .check_output("rust", &[], "", "inherited failure", Some(1))
                .is_ok()
        );
        assert!(
            divergent
                .check_output("javascript", &javascript, "", "", Some(0))
                .is_ok()
        );
        assert!(
            divergent
                .check_output("javascript", &[], "", "", Some(0))
                .is_err()
        );
        assert!(
            divergent
                .check_output("javascript", &javascript, "", "inherited failure", Some(1))
                .is_err()
        );
    }
    let inherited = f.backend_case(
        "source = \"\"\nrun_error = \"common failure\"\nrust_error = \"rust failure\"",
    );
    assert!(
        inherited
            .check_output("javascript", &[], "", "rust failure", Some(1))
            .is_ok()
    );
    assert!(
        inherited
            .check_output("javascript", &[], "", "common failure", Some(1))
            .is_err()
    );
    assert!(
        inherited
            .check_output("javascript", &[], "", "", Some(0))
            .is_err()
    );

    // A JavaScript error remains authoritative even when partial output is
    // explicit; neither the Rust error nor the success override can mask it.
    let javascript_partial = f.backend_case("source = \"\"\nrust_error = \"rust failure\"\nrust_shows = [\"partial = 1\"]\njavascript_error = \"javascript failure\"\njavascript_shows = [\"javascript = 3\"]");
    assert!(
        javascript_partial
            .check_output("javascript", &javascript, "", "javascript failure", Some(1))
            .is_ok()
    );
    assert!(
        javascript_partial
            .check_output("javascript", &javascript, "", "rust failure", Some(1))
            .is_err()
    );
    assert!(
        javascript_partial
            .check_output(
                "javascript",
                &observations,
                "",
                "javascript failure",
                Some(1)
            )
            .is_err()
    );
    assert!(
        javascript_partial
            .check_output("javascript", &[], "", "javascript failure", Some(1))
            .is_err()
    );
    assert!(
        javascript_partial
            .check_output("javascript", &javascript, "", "", Some(0))
            .is_err()
    );
}

#[test]
fn evaluator_budget_and_drop_assertions_are_native_coverage_gaps() {
    let f = Fixture::new();
    let case = f.backend_case("source = \"\"\nshows = []\nbudget = 1000\ndrops = []");
    assert!(case.check_output("rust", &[], "", "", Some(0)).is_ok());
    let gaps = case.assertion_gaps();
    assert_eq!(gaps.len(), 2);
    assert!(gaps.iter().any(|g| g.starts_with("drops:")));
    assert!(gaps.iter().any(|g| g.starts_with("budget:")));
    let ordinary = f.backend_case("source = \"\"\nshows = []");
    assert!(ordinary.assertion_gaps().is_empty());
}

#[test]
fn multifile_backend_inputs_preserve_imports_and_source_maps() {
    let f = Fixture::new();
    let case = f.backend_case(
        r#"files."main.nib" = ```tauto
import "lib.nib"
perform show("answer", twice(21))
```
files."lib.nib" = `pub fn twice(n: i64): i64 { n + n }`
shows = ["answer = 42"]
rust_shows = ["answer = 42"]
build = "ok""#,
    );
    assert!(!case.compilation_source().unwrap().contains("import "));
    assert_eq!(case.build.as_deref(), Some("ok"));
    assert_eq!(
        case.rust_shows.as_deref(),
        Some(["answer = 42".to_string()].as_slice())
    );
    for backend in ["rust", "javascript"] {
        let package = case.compile(backend).unwrap();
        let sources = package.sources.expect("file boundaries retained");
        assert!(sources.files.iter().any(|s| s.path.ends_with("main.nib")));
        assert!(sources.files.iter().any(|s| s.path.ends_with("lib.nib")));
    }
}

#[test]
fn extracted_file_and_tote_compilation_keep_kernel_checked_evidence() {
    let f = Fixture::new();
    let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../std/Base.taut")
        .canonicalize()
        .unwrap();
    let proof = r#"mutual {
  fn twice(n: Nat): Nat {
    ⊢ Nat from match n {
      Zero => Zero
      Succ(k) => Succ(Succ(twice_again(k)))
    }
  }
  fn twice_again(n: Nat): Nat {
    ⊢ Nat from match n {
      Zero => Zero
      Succ(k) => Succ(Succ(twice(k)))
    }
  }
}
pub fn mapped(xs: List(Nat)): List(Nat) { List::map(twice, xs) }
"#;
    let case = f.backend_case(&format!(
        "extract = true\nimports = [path`{}`]\nfiles.\"main.tauto\" = {:?}\nentry = \"main.tauto\"\nshows = [\"value = Cons(4, Nil)\"]",
        base.display(),
        format!(
r#"{}perform show("value", mapped(Cons(2, Nil)))
"#,
proof
)
    ));
    let flattened = case.compilation_source().unwrap();
    for backend in ["rust", "javascript"] {
        case.compile(backend).unwrap();
        let without_evidence = if backend == "rust" {
            tauto_nir::compile(&flattened)
        } else {
            tauto_nir::compile_javascript(&flattened)
        };
        assert!(
            without_evidence.is_err(),
            "flattened {backend} source forged totality"
        );
    }

    // The real tote is outside the directory enumerated for case documents.
    let real_tote = Fixture::new();
    real_tote.write(
        "Tauto.eure",
        "package { name = \"runner\"\nversion = \"0.1.0\" }",
    );
    real_tote.write(
        "src/proof.tauto",
        &format!(
            r#"import {}
{}"#,
            format!("{base:?}"),
            proof
        ),
    );
    real_tote.write(
        "src/main.tauto",
        r#"import "proof.tauto"
perform show("value", mapped(Cons(2, Nil)))"#,
    );
    let tote = f.backend_case(&format!(
        "tote = path`{}`\nshows = [\"value = Cons(4, Nil)\"]",
        real_tote.0.display()
    ));
    assert_eq!(tote.tote.as_deref(), Some(real_tote.0.as_path()));
    for backend in ["rust", "javascript"] {
        tote.compile(backend).unwrap();
    }
}

#[test]
fn runtime_arguments_preserve_order_unicode_and_empty_values() {
    let f = Fixture::new();
    let document = r#"source = ```tauto
import std::prelude::Os
perform show("args", perform argv())
```
args = ["first", "日本語", ""]
shows = ["args = Cons(\"first\", Cons(\"日本語\", Cons(\"\", Nil)))"]"#;
    f.passes(document);
    let case = f.backend_case(document);
    assert_eq!(case.args, ["first", "日本語", ""]);
    f.fails(
        "source = \"\"\nparses = true\nargs = [\"unexpected\"]",
        "args requires a runtime assertion",
    );
    assert!(matches!(
        f.outcome("source = \"\"\nshows = []\nargs = [1]"),
        Outcome::Failed(_)
    ));
}

#[test]
fn virtual_totes_obey_manifests_and_suppress_dependency_entries() {
    let f = Fixture::new();
    let document = r#"files_tote = "app"
files."app/Tauto.eure" = ```eure
package { name = "app" }
dependencies { support { path = "../support" } }
```
files."app/src/main.taut" = ```tauto
import support::library
perform show("value", answer())
```
files."app/unlisted.taut" = `perform show("outside declared sources", 0)`
files."support/Tauto.eure" = `package { name = "support" }`
files."support/src/library.tauto" = `pub fn answer(): i64 { 42 }`
files."support/src/main.taut" = `perform show("dependency taut entry", 0)`
files."support/src/main.tauto" = `perform show("dependency tauto entry", 0)`
shows = ["value = 42"]"#;
    f.passes(document);
    let case = f.backend_case(document);
    let source = case.compilation_source().unwrap();
    assert!(!source.contains("outside declared sources"));
    assert!(!source.contains("dependency taut entry"));
    assert!(!source.contains("dependency tauto entry"));
    for backend in ["rust", "javascript"] {
        let package = case.compile(backend).unwrap();
        let sources = package.sources.expect("tote source boundaries retained");
        assert!(
            sources
                .files
                .iter()
                .any(|file| file.path.ends_with("app/src/main.taut"))
        );
        assert!(
            sources
                .files
                .iter()
                .any(|file| file.path.ends_with("support/src/library.tauto"))
        );
        assert!(
            sources
                .files
                .iter()
                .all(|file| !file.path.ends_with("support/src/main.taut")
                    && !file.path.ends_with("support/src/main.tauto")
                    && !file.path.ends_with("app/unlisted.taut"))
        );
    }
    let configured = document.replace(
        "package { name = \"app\" }",
        "package { name = \"app\" }\nrust { executor = \"threads\" }",
    );
    f.passes(&configured);
    let configured_case = f.backend_case(&configured);
    for backend in ["rust", "javascript"] {
        match configured_case.compile(backend) {
            Err(tauto_nir::CompileError::Front(message)) => assert!(message.contains(
                "files_tote backend host configuration needs a retained host fixture or external tote; it is not replaced by defaults"
            )),
            other => panic!("{backend} discarded a virtual tote's host configuration: {other:?}"),
        }
    }
    for excluded in [
        "entry = \"app/src/main.taut\"",
        "imports = [path`other.taut`]",
        "parses = true",
    ] {
        f.fails(&format!("{document}\n{excluded}"), "files_tote");
    }
    f.fails(
        "source = \"\"\nshows = []\nfiles_tote = \"app\"",
        "files_tote",
    );
    for invalid in ["../app", "/app", "app/../app", ""] {
        assert!(
            matches!(
                f.outcome(
                    &document.replace("files_tote = \"app\"", &format!("files_tote = {invalid:?}"))
                ),
                Outcome::Failed(_)
            ),
            "invalid tote path {invalid:?}"
        );
    }
    f.fails(
        &document.replace(
            "files.\"app/Tauto.eure\"",
            "files.\"app/not-the-manifest.eure\"",
        ),
        "Tauto.eure",
    );
}
#[test]
fn every_expectation_is_read_by_a_scenario_the_case_runs() {
    let f = Fixture::new();
    for (text, unread) in [
        (
            "source = \"\"\nshows = []\nbackends = [\"rust\"]\njavascript_shows = []",
            "javascript_shows",
        ),
        (
            "source = \"\"\nshows = []\nbackends = [\"javascript\"]\nbuild = \"ok\"",
            "build",
        ),
        (
            "source = \"\"\ntypes = \"ok\"\nrust = \"skip: eval-only\"",
            "rust",
        ),
    ] {
        f.fails(text, unread);
    }
}
#[test]
fn declared_scenarios_must_be_the_ones_that_run() {
    let f = Fixture::new();
    f.passes("source = \"\"\ntypes = \"ok\"\nscenarios = [\"eval\"]");
    f.fails(
        "source = \"\"\ntypes = \"ok\"\nscenarios = [\"eval\", \"rust\"]",
        "this case runs [\"eval\"]",
    );
    f.fails(
        "source = \"\"\nshows = []\nscenarios = [\"eval\"]",
        "this case runs [\"eval\", \"rust\", \"javascript\", \"vm\"]",
    );
    f.fails(
        "source = \"\"\ntypes = \"ok\"\nscenarios = [\"evl\"]",
        "unknown scenario",
    );
}
