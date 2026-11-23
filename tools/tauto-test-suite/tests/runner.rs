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
        "source = \"\"\neval.bug = \"x\"\nchecks.typo = 1",
        "source = \"\"\nstdout = 1",
        "source = \"\"\nchecks_all = \"typo\"",
        "source = \"\"\nbudget = 1",
        "a = []\nb = []\nequal = true\nstdout = \"\"",
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
        r#"show(&(include_text!("message.txt")))"#,
    );
    f.passes(
        r#"source = path`lib/include.taut`
stdout = "\"hello\"\n""#,
    );
    f.fails(
        "source = path`absent.taut`\nchecks_all = \"ok\"",
        "absent.taut",
    );
}
#[test]
fn files_real_links_the_repository_file_in_place() {
    let f = Fixture::new();
    f.write(
        "lib/Tauto.eure",
        "package { name = \"std\"\nversion = \"0.1.0\"\nprelude = false }",
    );
    // Named like a prelude stub in `stdlib::FILES`, with real text, so only
    // path membership under the tote `std` makes it standard.
    f.write(
        "lib/builtin/classes.taut",
        r#"import std::builtin::ord { Ord }
import std::prelude::std { Ordering }

instance Ord(i64) {
  fn compare(a: &i64, b: &i64): Ordering {
    if a < b { Less } else if a == b { Equal } else { Greater }
  }
}
"#,
    );
    // The scratch entry imports a `real` link: the check reads the library file
    // by its repository path, so standard-library path membership applies.
    // `Marker` has two type parameters so dictionary ownership runs.
    f.write(
        "cases/real.eure",
        r#"files."Tauto.eure" = ```eure
package { name = "std"
version = "0.1.0"
prelude = false }
```
files."builtin/classes.taut" = real`../lib/builtin/classes.taut`
files."probe.taut" = ````tauto
import "builtin/classes.taut"

class Marker(A: Type, B: Type) {
  fn mark(a: &A, b: &B): Unit
}

instance Marker(Bool, Bool) {
  fn mark(a: &Bool, b: &Bool): Unit { () }
}
````
entry = "probe.taut"
checks."Ord::inst@i64" = "skipped"
"#,
    );
    let report = run_path(&f.0.join("cases/real.eure"), &f.0, None).unwrap();
    assert!(!report.failed(), "{:?}", report.error);
    f.fails(
        "source = real`lib/main.taut`\nchecks_all = \"ok\"",
        "real`…` is only for files values",
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
        r#"source = `show(&42)`
stdout = "42\n"
stderr = ""
exit = 0
budget = 10000"#,
    );
    f.fails(
        r#"source = `show(&42)`
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
        "source = \"\"\nparses = true\neval.unimplemented = \"x\"",
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
show(&twice(21))"#,
    );
    f.write(
        "case.eure",
        "source = path`lib/main.taut`\nstdout = \"42\\n\"",
    );
    let cases = tauto_test_suite::rust_cases(&f.0).unwrap();
    let source = cases[0].compilation_source().unwrap();
    assert!(!source.contains("import "));
    tauto::nir::compile(&source).unwrap();
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
import std::builtin::os
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
        r#"source = `show(&twice(21))`
imports = [path`lib/helper.taut`]
stdout = "42\n""#,
    );
    let cases = tauto_test_suite::rust_cases(&f.0).unwrap();
    tauto::nir::compile(&cases[0].compilation_source().unwrap()).unwrap();
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
        "import std::builtin::os\nprint(\"hello\")",
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
fn every_backend_runs_unless_it_opts_out_with_a_reason() {
    let f = Fixture::new();
    let case = f.backend_case("source = \"\"\nstdout = \"\"");
    for backend in ["rust", "javascript", "vm", "llvm", "niri"] {
        assert!(case.selects_backend(backend));
        assert!(!case.explicit_backend(backend));
    }
    let opted = f.backend_case("source = \"\"\nstdout = \"\"\nvm.unimplemented = \"unsupported: missing\"");
    assert!(opted.selects_backend("vm"));
    assert!(opted.explicit_backend("vm"));
    f.fails(
        "source = \"\"\nstdout = \"\"\nvm.unimplemented = \"runtime: a\"\nvm.bug = \"runtime: b\"",
        "exactly one",
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
        Err(tauto_nibcheck::lower::CompileError::Front(message)) => {
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
    let compile = f.backend_case(
        "source = \"\"\nparses = true\nrust.unimplemented = \"unsupported: missing feature\"",
    );
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

    let runtime = f.backend_case("source = \"\"\nstdout = \"\"\nrust.unimplemented = \"runtime: unavailable operation\"");
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
        runtime.check_output("rust", "", "", Some(0)).is_err(),
        "a stale runtime limitation passed"
    );
    for value in ["message only", "unknown: message", "runtime: "] {
        f.fails(
            &format!("source = \"\"\nparses = true\nrust.unimplemented = {value:?}"),
            "opt-out",
        );
    }
    f.fails(
        "source = \"\"\nparses = true\ncompile_errors.rust = \"front: rejected\"\nrust.unimplemented = \"front: rejected\"",
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
struct(affine) Resource {}
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
extern { fn host(read: &(() -> Text)): Text }
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
    let restricted = source.replace("read: &(() -> Text)", "read: &(() -> Text ! {})");
    assert_ne!(
        restricted, source,
        "the host's parameter is spelled as the test expects"
    );
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
    let case = f.backend_case("source = \"\"\nstdout = \"output\"\nstderr = \"warning\"\nexit = 7");
    for backend in ["rust", "javascript", "vm", "llvm", "niri"] {
        assert_eq!(case.check_output(backend, "output", "warning", Some(7)), Ok(None));
    }
    for (out, err, exit, wanted) in [
        ("wrong", "warning", Some(7), "stdout"),
        ("output", "wrong", Some(7), "stderr"),
        ("output", "warning", Some(0), "exit"),
        ("output", "warning", None, "exit"),
    ] {
        assert!(
            case.check_output("rust", out, err, exit)
                .unwrap_err()
                .contains(wanted)
        );
    }
    let error = f.backend_case("source = \"\"\nrun_error = \"common failure\"");
    assert_eq!(error.check_output("javascript", "", "common failure", Some(1)), Ok(None));
    assert!(error.check_output("rust", "common failure", "", Some(1)).is_err());
    assert!(error.check_output("rust", "", "common failure", Some(0)).is_err());

    // A backend whose output differs opts out with the part of the mismatch.
    let differs = f.backend_case("source = \"\"\nstdout = \"1\\n\"\njavascript.bug = \"output: stdout: expected\"");
    assert!(matches!(differs.check_output("javascript", "2\n", "", Some(0)), Ok(Some(_))));
    assert!(
        differs
            .check_output("javascript", "1\n", "", Some(0))
            .unwrap_err()
            .contains("remove it")
    );
    assert_eq!(differs.check_output("rust", "1\n", "", Some(0)), Ok(None));
}

#[test]
fn a_budget_is_no_native_coverage_gap() {
    let f = Fixture::new();
    // The machine counts budget steps as the backends do, so a budget is no gap.
    let case = f.backend_case("source = \"\"\nstdout = \"\"\nbudget = 1000");
    assert!(case.check_output("rust", "", "", Some(0)).is_ok());
    assert!(case.assertion_gaps().is_empty());
    let ordinary = f.backend_case("source = \"\"\nstdout = \"\"");
    assert!(ordinary.assertion_gaps().is_empty());
}

#[test]
fn multifile_backend_inputs_preserve_imports_and_source_maps() {
    let f = Fixture::new();
    let case = f.backend_case(
        r#"files."main.nib" = ```tauto
import "lib.nib"
show(&twice(21))
```
files."lib.nib" = `pub fn twice(n: i64): i64 { n + n }`
stdout = "42\n"
build = "ok""#,
    );
    assert!(!case.compilation_source().unwrap().contains("import "));
    assert_eq!(case.build.as_deref(), Some("ok"));
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
        .join("../../std/base.taut")
        .canonicalize()
        .unwrap();
    // Each call passes a rebuilt `Succ(j)`, not a part of the parameter: the
    // kernel accepts the recursion, but the rows of the flattened source,
    // which see only a call on a part of a parameter as ending
    // (`rows/structural.rs`), do not. Without the kernel's evidence the
    // flattened source performs `div`.
    let proof = r#"mutual {
  fn twice(n: Nat): Nat {
    ⊢ Nat from match n {
      Zero => Zero
      Succ(k) => ⊢ Nat from match k {
        Zero => Succ(Succ(Zero))
        Succ(j) => Succ(Succ(twice_again(Succ(j))))
      }
    }
  }
  fn twice_again(n: Nat): Nat {
    ⊢ Nat from match n {
      Zero => Zero
      Succ(k) => ⊢ Nat from match k {
        Zero => Succ(Succ(Zero))
        Succ(j) => Succ(Succ(twice(Succ(j))))
      }
    }
  }
}
pub fn mapped(xs: List(Nat)): List(Nat) { List::map(twice, xs) }
"#;
    let case = f.backend_case(&format!(
        "extract = true\nimports = [path`{}`]\nfiles.\"main.tauto\" = {:?}\nentry = \"main.tauto\"\nstdout = \"[4]\\n\"",
        base.display(),
        format!(
r#"{}show(&mapped(Cons(2, Nil)))
"#,
proof
)
    ));
    let flattened = case.compilation_source().unwrap();
    for backend in ["rust", "javascript"] {
        case.compile(backend).unwrap();
        let without_evidence = if backend == "rust" {
            tauto::nir::compile(&flattened)
        } else {
            tauto::nir::compile_javascript(&flattened)
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
show(&mapped(Cons(2, Nil)))"#,
    );
    let tote = f.backend_case(&format!(
        "tote = path`{}`\nstdout = \"[4]\\n\"",
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
import std::builtin::os
show(&(perform argv()))
```
args = ["first", "日本語", ""]
stdout = "[\"first\", \"日本語\", \"\"]\n""#;
    f.passes(document);
    let case = f.backend_case(document);
    assert_eq!(case.args, ["first", "日本語", ""]);
    f.fails(
        "source = \"\"\nparses = true\nargs = [\"unexpected\"]",
        "args requires a runtime assertion",
    );
    assert!(matches!(
        f.outcome("source = \"\"\nstdout = \"\"\nargs = [1]"),
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
show(&answer())
```
files."app/unlisted.taut" = `show(&0)`
files."support/Tauto.eure" = `package { name = "support" }`
files."support/src/library.tauto" = `pub fn answer(): i64 { 42 }`
files."support/src/main.taut" = `show(&0)`
files."support/src/main.tauto" = `show(&0)`
stdout = "42\n""#;
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
            Err(tauto_nibcheck::lower::CompileError::Front(message)) => assert!(message.contains(
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
        "source = \"\"\nstdout = \"\"\nfiles_tote = \"app\"",
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
fn declared_scenarios_must_be_the_ones_that_run() {
    let f = Fixture::new();
    f.passes("source = \"\"\ntypes = \"ok\"\nscenarios = [\"eval\"]");
    f.fails(
        "source = \"\"\ntypes = \"ok\"\nscenarios = [\"eval\", \"rust\"]",
        "this case runs [\"eval\"]",
    );
    f.fails(
        "source = \"\"\nstdout = \"\"\nscenarios = [\"eval\"]",
        "this case runs [\"eval\", \"rust\", \"javascript\", \"vm\", \"llvm\", \"niri\"]",
    );
    f.fails(
        "source = \"\"\ntypes = \"ok\"\nscenarios = [\"evl\"]",
        "unknown scenario",
    );
}

#[test]
fn nir_expectations_compare_the_printed_text() {
    let f = Fixture::new();
    let text = "fn count@0(n#1: u64): u64 S = if eq(copy n#1, 0u64) then 0u64 else count@0(sub<u64>(copy n#1, 1u64)): u64";
    let marked = text.replace(")): u64", ")) recur: u64");
    let case = |source: &str, rest: &str| format!("nir.source = ```nir\n{source}\n```\n{rest}");
    f.passes(&case(
        text,
        &format!("nir.passes = [\"tail\"]\nnir.package = ```nir\n{marked}\n```"),
    ));
    // The pass that marks the call was not run.
    f.fails(
        &case(text, &format!("nir.package = ```nir\n{marked}\n```")),
        "nir.package",
    );
    f.fails(
        &case(
            text,
            &format!("nir.passes = [\"tail\"]\nnir.fns.other = ```nir\n{marked}\n```"),
        ),
        "selects 0 functions",
    );
    f.fails(
        &case(text, "nir.passes = [\"tail\"]\nnir.error = \"x\""),
        "every pass succeeded",
    );
    f.fails(
        &case(text, "nir.passes = [\"tails\"]\nnir.error = \"x\""),
        "unknown pass",
    );
    f.fails(
        &case(text, "nir.passes = [\"tail\"]"),
        "nir needs fns, datas, evidence, package or error",
    );
    // A program's NIR is checked beside what the program shows.
    let program =
        "source = \"fn one(): u64 { 1 }\\nshow(&one())\"\nstdout = \"1\\n\"\n";
    let one = "fn one@1(): u64 S = 1u64";
    f.passes(&format!("{program}nir.fns.one = ```nir\n{one}\n```"));
    f.fails(
        &format!(
            "{program}nir.fns.one = ```nir\n{}\n```",
            one.replace("1u64", "2u64")
        ),
        "nir.fns.one",
    );
    f.fails(
        &case(
            text,
            &format!("stdout = \"1\\n\"\nnir.package = ```nir\n{text}\n```"),
        ),
        "nir.source is not combined with expectations of a program",
    );
}
