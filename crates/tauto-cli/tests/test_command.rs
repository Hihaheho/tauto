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
        "theorem identity(n: Nat): n = n { Refl(Nat, n) }\nperform test(\"one\", () => expect(true, \"no\"))\nperform test(\"two\", () => expect(true, \"no\"))\n",
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
        "source = \"perform show(\\\"answer\\\", 6 * 7)\"\nshows = [\"answer = 42\"]\n",
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
fn nonzero_exit_fails() {
    let d = Fixture::new("exit");
    d.write(
        "exit.taut",
        "import std::prelude::Os\n\nperform test(\"t\", () => expect(true, \"no\"))\nperform exit(7)\n",
    );
    let out = d.run(&["--json"]);
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(parse(&out)["failed"], 1);
    assert!(String::from_utf8_lossy(&out.stdout).contains("program exited with 7"));
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
        "import std::prelude::Os\n\nperform test(\"prints\", () => print(\"hi\\n\"))\nperform test(\"fails\", () => { print(\"hi\\n\"); expect(false, \"no\") })\n",
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
