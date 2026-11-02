//! `totes/scan`, `totes/llk` and `totes/syntax` against `tauto_parol`
//! (`docs/design/self-host.md`).

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};

const STEPS: u64 = 200_000_000_000;

/// What `tauto_parol` gives, in the form the tote prints: the dump of the
/// tree, or `error` (the position of an error is not compared).
fn expected(source: &str) -> String {
    std::panic::catch_unwind(|| {
        let parsed = tauto_parol::parse(source);
        parsed.is_ok().then(|| parsed.cst.dump())
    })
    .ok()
    .flatten()
    .unwrap_or_else(|| "error\n".to_string())
}

fn compare(label: &str, inputs: Vec<(String, String)>) {
    let m = materialize(label, &inputs);
    let out = run_tote_native("syntax", &m.paths, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let mut rust = String::new();
    for (path, (_, source)) in m.paths.iter().zip(&inputs) {
        rust.push_str(&format!("== {path}\n{}", expected(source)));
    }
    assert_same_dump("syntax", &rust, &out.stdout);
}

/// One part of the corpus, so that the parts run side by side.
fn part(label: &str, n: usize, of: usize) {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .enumerate()
        .filter(|(i, _)| i % of == n)
        .map(|(_, x)| x)
        .collect();
    compare(label, inputs);
}

#[test]
fn the_tables_are_not_stale() {
    let problems = selfhost_harness::stale(&selfhost_harness::syntax_table_files());
    assert!(
        problems.is_empty(),
        "{problems:?}: run `bash scripts/generate-syntax-tables.sh`"
    );
}

#[test]
fn syntax_matches_the_corpus_0() {
    part("syntax-0", 0, 4);
}

#[test]
fn syntax_matches_the_corpus_1() {
    part("syntax-1", 1, 4);
}

#[test]
fn syntax_matches_the_corpus_2() {
    part("syntax-2", 2, 4);
}

#[test]
fn syntax_matches_the_corpus_3() {
    part("syntax-3", 3, 4);
}

/// The scanner alone against the terminals of the tree.
#[test]
fn scan_matches_the_terminals() {
    let inputs: Vec<(String, String)> = corpus()
        .into_iter()
        .filter(|(_, s)| tauto_parol::parse(s).is_ok())
        .step_by(3)
        .collect();
    let m = materialize("scan", &inputs);
    let mut args = vec!["--tokens".to_string()];
    args.extend(m.paths.iter().cloned());
    let out = run_tote_native("syntax", &args, STEPS);
    assert_eq!(out.error, None);
    let mut rust = String::new();
    for (path, (_, source)) in m.paths.iter().zip(&inputs) {
        rust.push_str(&format!("== {path}\n"));
        for (kind, span) in tauto_parol::parse(source).cst.terminals() {
            rust.push_str(&format!("{kind} {} {}\n", span.start, span.end));
        }
    }
    assert_same_dump("scan", &rust, &out.stdout);
}
