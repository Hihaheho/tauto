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
            // A run may write only under the folder it starts in, so the
            // tests that write a file start in the fixture.
            .current_dir(&self.0)
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

fn parse(out: &Output) -> serde_json::Value {
    serde_json::from_slice(&out.stdout).unwrap_or_else(|e| {
        panic!(
            "{e}: {} {}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        )
    })
}

#[test]
fn tests_are_found_in_any_source_file_in_stable_order() {
    let d = Fixture::new("package");
    d.write(
        "Tauto.eure",
        "package { name = \"calc\"\nversion = \"0.1.0\" additional-sources = [\"proof\"] }",
    );
    d.write("src/main.taut", "let answer: i64 := 6 * 7\n");
    d.write(
        "src/z.taut",
        "perform test(\"answer\", () => expect(6 * 7 == 42, \"no\"))\n",
    );
    d.write(
        "src/deep/a.taut",
        "theorem identity(n: Nat): n = n { Refl(<A: Nat, a: n>) }\nperform test(\"one\", () => expect(true, \"no\"))\nperform test(\"two\", () => expect(true, \"no\"))\n",
    );
    d.write(
        "proof/p.taut",
        "perform test(\"extra\", () => expect(true, \"no\"))\n",
    );
    // Outside the sources, a file is not searched.
    d.write(
        "examples/e.taut",
        "perform test(\"example\", () => expect(false, \"no\"))\n",
    );
    let out = d.run(&["--json"]);
    assert!(out.status.success(), "{}", parse(&out));
    let json = parse(&out);
    let names: Vec<_> = json["tests"]
        .as_array()
        .unwrap()
        .iter()
        .map(|t| t["name"].as_str().unwrap())
        .collect();
    assert_eq!(
        names,
        [
            "proof/p.taut::extra",
            "src/deep/a.taut::one",
            "src/deep/a.taut::two",
            "src/z.taut::answer"
        ]
    );
    assert_eq!(json["passed"], 4);
    assert_eq!(out.stdout, d.run(&["--json"]).stdout);
    let one = d.run(&["--filter", "answer", "--json"]);
    assert_eq!(parse(&one)["passed"], 1);
}

#[test]
fn a_file_with_no_test_is_not_run() {
    let d = Fixture::new("no-test");
    d.write("bad.taut", "let x: i64 := true\n");
    assert_eq!(d.run(&[]).status.code(), Some(1));
    let out = d.run(&["--json"]);
    assert_eq!(parse(&out)["empty"], true);
}

#[test]
fn incomplete_and_runtime_failure_are_failures() {
    let d = Fixture::new("fail");
    d.write(
        "hole.taut",
        "theorem unfinished(n: Nat): n = n { ?proof }\nperform test(\"t\", () => expect(true, \"no\"))\n",
    );
    d.write(
        "bad.taut",
        "let x: i64 := true\nperform test(\"t\", () => expect(true, \"no\"))\n",
    );
    let out = d.run(&["--json"]);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(parse(&out)["failed"], 2);
}

#[test]
fn empty_and_bad_options_do_not_pass() {
    let d = Fixture::new("empty");
    assert_eq!(d.run(&[]).status.code(), Some(1));
    assert_eq!(d.run(&["--filter"]).status.code(), Some(2));
    assert_eq!(d.run(&["--unknown"]).status.code(), Some(2));
    // Eure case files are not tests.
    d.write(
        "calc.eure",
        "source = \"show(&(6 * 7))\"\nstdout = \"42\\n\"\n",
    );
    assert_eq!(d.run(&[]).status.code(), Some(1));
}

#[cfg(unix)]
#[test]
fn discovery_rejects_symlink_cycles() {
    let d = Fixture::new("symlink");
    std::os::unix::fs::symlink(&d.0, d.0.join("cycle")).unwrap();
    assert_eq!(d.run(&[]).status.code(), Some(2));
}

#[test]
fn a_top_level_beside_an_entry_only_names_entries() {
    let d = Fixture::new("exit");
    d.write(
        "exit.taut",
        "import std::builtin::os\n\nperform test(\"t\", () => expect(true, \"no\"))\nperform exit(7)\n",
    );
    let out = d.run(&["--json"]);
    assert_eq!(out.status.code(), Some(1));
    let json = parse(&out);
    assert_eq!(json["tests"][0]["status"], "error", "{json}");
    assert_eq!(json["tests"][0]["name"], "exit.taut", "{json}");
    assert!(
        json.to_string()
            .contains("the top level performs exit beside an entry"),
        "{json}"
    );
}

#[test]
fn a_test_that_is_not_selected_is_not_called() {
    let d = Fixture::new("select");
    d.write(
        "t.taut",
        "import std::builtin::os\n\nperform main(() => print(\"main ran\\n\"))\nperform test(\"quiet\", () => expect(true, \"no\"))\nperform test(\"loud\", () => { print(\"loud ran\\n\"); expect(false, \"no\") })\n",
    );
    let out = d.run(&["--filter", "quiet", "--json"]);
    let json = parse(&out);
    assert!(out.status.success(), "{json}");
    assert_eq!(json["tests"].as_array().unwrap().len(), 1, "{json}");
    assert_eq!(json["tests"][0]["name"], "t.taut::quiet", "{json}");
    // Neither the other test nor `main` ran, and a body's output is no result.
    let all = d.run(&["--json"]);
    let json = parse(&all);
    assert_eq!(json["passed"], 1, "{json}");
    assert_eq!(json["failed"], 1, "{json}");
    let listed = d.run(&["--list"]);
    assert_eq!(
        String::from_utf8_lossy(&listed.stdout),
        "t.taut::quiet\nt.taut::loud\n"
    );
    // `tauto run` calls the `main` and no test.
    let run = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .env("TAUTO_LANG", "en")
        .arg("run")
        .arg(d.0.join("t.taut"))
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "main ran\n");
}

#[test]
fn a_run_that_stops_says_which_test_it_was_in() {
    let d = Fixture::new("stopped");
    d.write(
        "t.taut",
        "fn spin(): i64 ! {div} {\n  while true { }\n  0\n}\nperform test(\"a\", () => expect(true, \"no\"))\nperform test(\"b\", () => expect(spin() == 1, \"no\"))\nperform test(\"c\", () => expect(true, \"no\"))\n",
    );
    let out = d.run(&["--json", "--steps", "100000"]);
    let json = parse(&out);
    assert_eq!(out.status.code(), Some(1), "{json}");
    let status: Vec<_> = json["tests"]
        .as_array()
        .unwrap()
        .iter()
        .map(|t| t["status"].as_str().unwrap())
        .collect();
    assert_eq!(status, ["passed", "stopped", "not_run"], "{json}");
}

#[test]
fn a_test_that_failed_is_called_again_when_retries_are_given() {
    let d = Fixture::new("retry");
    // The first call of `flaky` leaves a file behind and fails; the next finds it.
    let mark = d.0.join("mark").to_string_lossy().replace('\\', "/");
    d.write(
        "src/t.taut",
        &format!(
            "import std::builtin::os\n\nperform test(\"flaky\", () => match read_file(\"{mark}\") {{\n  Ok(text) => #()\n  Err(why) => {{\n    raise(write_file(\"{mark}\", \"x\"))\n    expect(false, \"first call\")\n  }}\n}})\nperform test(\"broken\", () => expect(false, \"always\"))\n"
        ),
    );
    for backend in [
        &[][..],
        &["--backend", "rust"],
        &["--backend", "javascript"],
    ] {
        let _ = fs::remove_file(d.0.join("mark"));
        let mut args = vec!["--json", "--yes"];
        args.extend_from_slice(backend);
        let json = parse(&d.run(&args));
        assert_eq!(json["tests"][0]["status"], "failed", "{backend:?}: {json}");
        let _ = fs::remove_file(d.0.join("mark"));
        args.extend_from_slice(&["--retries", "1"]);
        let out = d.run(&args);
        let json = parse(&out);
        assert_eq!(out.status.code(), Some(1), "{backend:?}: {json}");
        assert_eq!(
            json["tests"][0]["status"], "passed_after_retry",
            "{backend:?}: {json}"
        );
        assert_eq!(json["tests"][0]["detail"], "1", "{backend:?}: {json}");
        assert_eq!(json["tests"][1]["status"], "failed", "{backend:?}: {json}");
        assert_eq!(json["tests"][1]["detail"], "always", "{backend:?}: {json}");
        assert_eq!(json["retried"], 1, "{backend:?}: {json}");
    }
    // A tote says it in its manifest.
    let _ = fs::remove_file(d.0.join("mark"));
    d.write(
        "Tauto.eure",
        "package { name = \"retry\"\nversion = \"0.1.0\" }\ntest { retries = 1 }\n",
    );
    let json = parse(&d.run(&["--json", "--yes"]));
    assert_eq!(json["retried"], 1, "{json}");
}

#[test]
fn a_test_asks_what_check_says_of_a_file() {
    let d = Fixture::new("check-effect");
    d.write("reject/bad.taut", "fn f(): i64 { true }\n");
    d.write("reject/good.taut", "fn f(): i64 { 1 }\n");
    d.write(
        "t.taut",
        "perform test(\"rejects\", () => match perform check(\"reject/bad.taut\") {\n  Nil => perform fail(\"it checked\")\n  Cons(d, rest) => {\n    expect(d.severity == \"error\", d.severity)\n    expect(d.line == 1, \"line\")\n    expect(d.col == 15, \"col\")\n    expect(d.message == \"the result of `f`: Bool does not fit i64\", d.message)\n  }\n})\nperform test(\"accepts\", () => match perform check(\"reject/good.taut\") {\n  Nil => #()\n  Cons(d, rest) => perform fail(d.message)\n})\n",
    );
    for backend in [
        &[][..],
        &["--backend", "rust"],
        &["--backend", "javascript"],
    ] {
        let mut args = vec!["--json"];
        args.extend_from_slice(backend);
        let out = d.run(&args);
        let json = parse(&out);
        assert!(out.status.success(), "{backend:?}: {json}");
        assert_eq!(json["passed"], 2, "{backend:?}: {json}");
    }
}

#[test]
fn finding_the_tests_always_has_a_step_limit() {
    let d = Fixture::new("finding");
    d.write(
        "t.taut",
        "fn spin(): i64 ! {div} {\n  while true { }\n  0\n}\nlet n := spin()\nperform test(\"a\", () => expect(true, \"no\"))\n",
    );
    let out = d.run(&["--json", "--steps", "100000"]);
    let json = parse(&out);
    assert_eq!(out.status.code(), Some(1), "{json}");
    assert_eq!(json["tests"][0]["status"], "error", "{json}");
    assert!(
        json.to_string().contains("while finding the tests")
            && json.to_string().contains("the step limit ran out"),
        "{json}"
    );
}

#[test]
fn entries_that_make_no_plan_are_errors_before_a_body_is_called() {
    let d = Fixture::new("plan");
    d.write(
        "twice.taut",
        "perform test(\"a\", () => expect(true, \"no\"))\nperform test(\"a\", () => expect(true, \"no\"))\n",
    );
    let out = d.run(&["--json"]);
    let json = parse(&out);
    assert_eq!(json["tests"][0]["status"], "error", "{json}");
    assert!(
        json.to_string().contains("two tests are named `a`"),
        "{json}"
    );
    d.write(
        "mains.taut",
        "import std::builtin::os\n\nperform main(() => print(\"one\\n\"))\nperform main(() => print(\"two\\n\"))\n",
    );
    let run = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .env("TAUTO_LANG", "en")
        .arg("run")
        .arg(d.0.join("mains.taut"))
        .output()
        .unwrap();
    assert!(!run.status.success());
    assert_eq!(String::from_utf8_lossy(&run.stdout), "");
    assert!(
        String::from_utf8_lossy(&run.stderr).contains("performs `main` 2 times"),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
}

#[test]
fn a_file_argument_runs_that_file() {
    let d = Fixture::new("file");
    d.write(
        "one.taut",
        "perform test(\"t\", () => expect(true, \"no\"))\n",
    );
    d.write(
        "two.taut",
        "perform test(\"u\", () => expect(false, \"no\"))\n",
    );
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .env("TAUTO_LANG", "en")
        .arg("test")
        .arg(d.0.join("one.taut"))
        .arg("--json")
        .output()
        .unwrap();
    assert!(out.status.success());
    let json = parse(&out);
    assert_eq!(json["tests"][0]["name"], "one.taut::t");
    assert_eq!(json["passed"], 1);
}

#[test]
fn test_bodies_can_print() {
    let d = Fixture::new("print");
    d.write(
        "print.taut",
        "import std::builtin::os\n\nperform test(\"prints\", () => print(\"hi\\n\"))\nperform test(\"fails\", () => { print(\"hi\\n\"); expect(false, \"no\") })\n",
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
