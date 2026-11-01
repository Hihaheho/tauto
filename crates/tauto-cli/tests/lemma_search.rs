use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new(name: &str, text: &str) -> Self {
        let dir =
            std::env::temp_dir().join(format!("tauto-lemma-command-{name}-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("main.taut"), text).unwrap();
        Self(dir)
    }
    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .arg("suggest")
            .arg(self.0.join("main.taut"))
            .args(["--hole", "h"])
            .args(args)
            .output()
            .unwrap()
    }
    fn json(&self, args: &[&str]) -> serde_json::Value {
        let result = self.run(args);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        serde_json::from_slice(&result.stdout).unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn explicit_scope_and_validation_are_deterministic_and_read_only() {
    let source = r#"theorem t<A: Prop>(a: A, b: A): A { ?h }"#;
    let f = Fixture::new("scoped", source);
    let args = ["--using", "b", "--limit", "1", "--verify", "--json"];
    let out = f.run(&args);
    assert!(out.status.success());
    assert_eq!(out.stdout, f.run(&args).stdout);
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(json.as_array().unwrap().len(), 1);
    assert_eq!(json[0]["term"], "b");
    assert_eq!(json[0]["validation"]["status"], "checked");
    assert_eq!(json[0]["validation"]["axioms"], serde_json::json!([]));
    assert_eq!(fs::read_to_string(f.0.join("main.taut")).unwrap(), source);
    let unchecked = f.json(&["--using", "b", "--json"]);
    assert_eq!(unchecked[0]["validation"]["status"], "unchecked");
    assert!(unchecked[0]["validation"].get("axioms").is_none());
}

#[test]
fn partial_candidates_are_never_reported_as_checked() {
    let f = Fixture::new(
        "partial",
        r#"theorem t<A: Prop, B: Prop>(a: A, b: B): And(A, B) { ?h }"#,
    );
    let json = f.json(&["--using", "AndIntro", "--verify", "--json"]);
    assert_eq!(json[0]["validation"]["status"], "incomplete");
    assert!(
        !json[0]["validation"]["remaining_holes"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    let out = f.run(&["--using", "AndIntro", "--verify"]);
    assert!(String::from_utf8_lossy(&out.stdout).contains("[incomplete]"));
}

#[test]
fn unknown_scope_and_mutating_flags_fail_without_writing() {
    let source = r#"theorem t<A: Prop>(a: A): A { ?h }"#;
    let f = Fixture::new("bad-options", source);
    assert!(!f.run(&["--using", "missing"]).status.success());
    assert_eq!(f.run(&["--using"]).status.code(), Some(2));
    assert_eq!(f.run(&["--using", "--json"]).status.code(), Some(2));
    assert_eq!(f.run(&["--write"]).status.code(), Some(2));
    assert_eq!(fs::read_to_string(f.0.join("main.taut")).unwrap(), source);
}

#[test]
fn wrong_type_has_no_results_and_zero_limit_has_no_checks() {
    let f = Fixture::new("empty", r#"theorem t<A: Prop>(a: A, n: Nat): A { ?h }"#);
    assert_eq!(
        f.json(&["--using", "n", "--verify", "--json"]),
        serde_json::json!([])
    );
    assert_eq!(
        f.json(&["--limit", "0", "--verify", "--json"]),
        serde_json::json!([])
    );
}

#[test]
fn axiom_dependencies_are_shown_in_human_and_json_output() {
    let f = Fixture::new(
        "axioms",
        r#"axiom assumed(): Zero = Zero
theorem alias(): Zero = Zero { assumed() }
theorem t(): Zero = Zero { ?h }"#,
    );
    let json = f.json(&["--using", "alias", "--verify", "--json"]);
    assert_eq!(json[0]["validation"]["status"], "checked");
    assert_eq!(
        json[0]["validation"]["axioms"],
        serde_json::json!(["assumed"])
    );
    let out = f.run(&["--using", "alias", "--verify"]);
    assert!(String::from_utf8_lossy(&out.stdout).contains("axioms: assumed"));
}
