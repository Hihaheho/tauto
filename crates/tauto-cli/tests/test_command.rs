use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
};
struct Fixture(PathBuf);
impl Fixture {
    fn new(name: &str) -> Self {
        let path =
            std::env::temp_dir().join(format!("tauto-test-command-{name}-{}", std::process::id()));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, path: &str, text: &str) {
        let p = self.0.join(path);
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        fs::write(p, text).unwrap();
    }
    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .arg("test")
            .arg(&self.0)
            .args(args)
            .output()
            .unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn package_sources_are_not_tests_and_order_is_stable() {
    let d = Fixture::new("package");
    d.write(
        "Tauto.eure",
        "package { name = \"calc\"\nversion = \"0.1.0\"\nsources = [\"src\"] }",
    );
    d.write("src/main.taut", r#"this is not a test entry"#);
    d.write("tests/z.taut", r#"perform show("answer", 6 * 7)"#);
    d.write(
        "tests/a.taut",
        r#"theorem identity(n: Nat): n = n { Refl(Nat, n) }"#,
    );
    let out = d.run(&["--json"]);
    assert!(
        out.status.success(),
        "{} {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    // A test file's theorems count as proved tests, before the file's run.
    assert_eq!(json["passed"], 3);
    assert_eq!(json["tests"][0]["name"], "tests/a.taut::identity");
    assert_eq!(json["tests"][0]["status"], "proved");
    assert_eq!(json["tests"][1]["name"], "tests/a.taut");
    assert_eq!(json["tests"][2]["name"], "tests/z.taut");
    assert_eq!(out.stdout, d.run(&["--json"]).stdout);
}

#[test]
fn incomplete_and_runtime_failure_are_failures() {
    let d = Fixture::new("fail");
    d.write(
        "hole.taut",
        r#"theorem unfinished(n: Nat): n = n { ?proof }"#,
    );
    d.write(
        "bad.taut",
        r#"let x: i64 := true
perform show("x", x)"#,
    );
    let out = d.run(&["--json"]);
    assert_eq!(out.status.code(), Some(1));
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(json["failed"], 2);
}

#[test]
fn cases_reuse_expected_type_errors_and_runtime_assertions() {
    let d = Fixture::new("cases");
    d.write(
        "calc.eure",
        r#"@ cases.value
source = "perform show(\"answer\", 6 * 7)"
shows = ["answer = 42"]
@ cases.reject
source = "let x: i64 := true"
types = "error: "
"#,
    );
    let out = d.run(&["--json"]);
    assert!(
        out.status.success(),
        "{} {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(json["passed"], 2);
    let one = d.run(&["--filter", "reject", "--json"]);
    let json: serde_json::Value = serde_json::from_slice(&one.stdout).unwrap();
    assert_eq!(json["passed"], 1);
    assert_eq!(d.run(&["--filter", "absent"]).status.code(), Some(1));
}

#[test]
fn empty_unsupported_and_bad_options_do_not_pass() {
    let d = Fixture::new("empty");
    assert_eq!(d.run(&[]).status.code(), Some(1));
    assert_eq!(d.run(&["--filter"]).status.code(), Some(2));
    assert_eq!(d.run(&["--unknown"]).status.code(), Some(2));
    d.write(
        "later.eure",
        r#"source = "perform show(\"x\", 1)"
compiles = true
"#,
    );
    assert_eq!(d.run(&[]).status.code(), Some(1));
}

#[test]
fn case_files_cannot_escape_scratch_directory() {
    let d = Fixture::new("traversal");
    d.write(
        "escape.eure",
        r#"files { "../outside.taut" = "perform show(\"x\", 1)" }
shows = []
"#,
    );
    let out = d.run(&[]);
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stdout).contains("relative path"));
}

#[cfg(unix)]
#[test]
fn discovery_rejects_symlink_cycles() {
    let d = Fixture::new("symlink");
    std::os::unix::fs::symlink(&d.0, d.0.join("cycle")).unwrap();
    assert_eq!(d.run(&[]).status.code(), Some(2));
}

#[test]
fn nonzero_exit_and_vacuous_case_fail() {
    let d = Fixture::new("exit");
    d.write("exit.taut", r#"perform exit(7)"#);
    d.write(
        "empty.eure",
        r#"source = "let x := 1"
"#,
    );
    let out = d.run(&["--json"]);
    assert_eq!(out.status.code(), Some(1));
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(json["failed"], 2);
}

#[test]
fn fixture_cannot_overwrite_shared_tables() {
    let d = Fixture::new("tables");
    d.write("macro/.tauto-syntax/sentinel.tables", "original");
    d.write(
        "escape.eure",
        "files { \".tauto-syntax/sentinel.tables\" = \"overwrite\" }\nshows = []\n",
    );
    let out = d.run(&[]);
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stdout).contains("shared syntax tables"));
    assert_eq!(
        fs::read_to_string(d.0.join("macro/.tauto-syntax/sentinel.tables")).unwrap(),
        "original"
    );
}

#[test]
fn empty_checks_and_nonzero_show_cases_do_not_pass() {
    let d = Fixture::new("assertions");
    d.write(
        "empty.eure",
        r#"source = "theorem bad(): Zero = Zero { ?todo }"
checks {}
"#,
    );
    d.write(
        "exit.eure",
        r#"source = "perform exit(7)"
shows = []
"#,
    );
    let out = d.run(&["--json"]);
    assert_eq!(out.status.code(), Some(1));
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(json["failed"], 2);
    assert!(String::from_utf8_lossy(&out.stdout).contains("program exited with 7"));
}

#[test]
fn ambiguous_or_ignored_case_inputs_are_rejected() {
    let d = Fixture::new("ambiguous");
    d.write(
        "both.eure",
        r#"source = "let x := 1"
files { "main.nib" = "let x := 2" }
shows = []
"#,
    );
    d.write(
        "unused.eure",
        r#"source = "let x := 1"
entry = "ignored.taut"
shows = []
"#,
    );
    let out = d.run(&["--json"]);
    assert_eq!(out.status.code(), Some(1));
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(json["failed"], 2);
}

#[test]
fn test_bodies_can_print() {
    let d = Fixture::new("print");
    d.write(
        "print.taut",
        "perform test(\"prints\", () => print(\"hi\\n\"))\nperform test(\"fails\", () => { print(\"hi\\n\"); expect(false, \"no\") })\n",
    );
    for backend in [
        &[][..],
        &["--backend", "rust"],
        &["--backend", "javascript"],
    ] {
        let mut args = vec!["--json"];
        args.extend_from_slice(backend);
        let out = d.run(&args);
        let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        let tests = json["tests"].as_array().unwrap();
        assert_eq!(tests.len(), 2, "{backend:?}: {json}");
        assert_eq!(
            tests[0]["name"], "print.taut::prints",
            "{backend:?}: {json}"
        );
        assert_eq!(tests[0]["status"], "passed", "{backend:?}: {json}");
        assert_eq!(tests[1]["status"], "failed", "{backend:?}: {json}");
        assert!(
            !json.to_string().contains("nothing handles stdout"),
            "{backend:?}: {json}"
        );
    }
}

#[test]
fn a_failing_test_reports_its_message_alike_on_every_backend() {
    let d = Fixture::new("fail-message");
    d.write(
        "fail.taut",
        "perform test(\"a\", () => expect(false, \"no\"))\n",
    );
    for backend in [
        &[][..],
        &["--backend", "rust"],
        &["--backend", "javascript"],
    ] {
        let mut args = vec!["--json"];
        args.extend_from_slice(backend);
        let out = d.run(&args);
        let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        let tests = json["tests"].as_array().unwrap();
        assert_eq!(tests.len(), 1, "{backend:?}: {json}");
        assert_eq!(tests[0]["status"], "failed", "{backend:?}: {json}");
        assert!(
            !json.to_string().contains("nothing handles"),
            "{backend:?}: {json}"
        );
        assert!(json.to_string().contains("\"no\""), "{backend:?}: {json}");
    }
}
