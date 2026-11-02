//! The tools of the differential tests work.

use std::collections::HashSet;
use std::fs;

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_at};

fn temp(name: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().canonicalize().unwrap().join(format!(
        "selfhost-harness-smoke-{name}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(d.join("src")).unwrap();
    d
}

#[test]
fn a_tote_runs_and_prints() {
    let d = temp("run");
    fs::write(
        d.join("Tauto.eure"),
        "package {\n  name = \"smoke\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    let dir = d.join("smoke");
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::rename(d.join("Tauto.eure"), dir.join("Tauto.eure")).unwrap();
    fs::write(
        dir.join("src/main.taut"),
        r#"match perform argv() {
  Nil => print("none")
  Cons(first, rest) => print(first)
}"#,
    )
    .unwrap();
    let none = run_tote_at(&dir, &[], 100_000);
    assert_eq!(none.error, None);
    assert_eq!(none.stdout, "none");
    let one = run_tote_at(&dir, &["x".to_string()], 100_000);
    assert_eq!(one.stdout, "x");
}

#[test]
fn a_failing_tote_says_why() {
    let d = temp("fail");
    let dir = d.join("bad");
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::write(
        dir.join("Tauto.eure"),
        "package {\n  name = \"bad\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    fs::write(
        dir.join("src/main.taut"),
        r#"
let x: i64 := true
"#,
    )
    .unwrap();
    let out = run_tote_at(&dir, &[], 100_000);
    let error = out.error.unwrap();
    assert!(error.contains("main.taut:2:"), "{error}");
}

#[test]
fn the_corpus_has_each_kind_of_input_once() {
    let corpus = corpus();
    assert!(!corpus.is_empty());
    let names: HashSet<&str> = corpus.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names.len(), corpus.len(), "names repeat");
    let has = |prefix: &str| corpus.iter().any(|(n, _)| n.starts_with(prefix));
    assert!(has("std/"));
    assert!(has("meta/"));
    assert!(has("std/prelude/Std.taut"));
    assert!(has("cases/eval/basics.eure#"));
    assert!(has("cases/check/proofs.eure#"));
    // The files of the language come before the cases.
    let first_case = corpus
        .iter()
        .position(|(n, _)| n.contains(".eure#"))
        .unwrap();
    let last_file = corpus
        .iter()
        .rposition(|(n, _)| !n.contains(".eure#"))
        .unwrap();
    assert!(last_file < first_case);
}

#[test]
fn the_corpus_is_written_to_files() {
    let inputs = vec![
        ("a".to_string(), "x".to_string()),
        ("b".to_string(), "y".to_string()),
    ];
    let m = materialize("smoke", &inputs);
    assert_eq!(m.paths.len(), 2);
    assert_eq!(fs::read_to_string(&m.paths[1]).unwrap(), "y");
}

#[test]
#[should_panic(expected = "the dumps differ at line 2")]
fn different_dumps_are_reported_at_the_first_difference() {
    assert_same_dump("x", "a\nb\nc\n", "a\nB\nc\n");
}

#[test]
fn equal_dumps_pass() {
    assert_same_dump("x", "a\nb\n", "a\nb\n");
}
