//! `totes/fmt` against `tauto::fmt::format` (`docs/design/self-host.md`).

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};

/// Converts formatter output to the tote's format. Returned errors and panics
/// on malformed input both produce the tote's error result.
fn expected(source: &str) -> String {
    std::panic::catch_unwind(|| tauto::fmt::format(source))
        .ok()
        .and_then(Result::ok)
        .unwrap_or_else(|| "error\n".to_string())
}

fn compare(label: &str, inputs: Vec<(String, String)>) {
    let m = materialize(label, &inputs);
    let out = run_tote_native("fmt", &m.paths, 20_000_000_000);
    assert_eq!(out.error, None);
    let mut rust = String::new();
    for (path, (_, source)) in m.paths.iter().zip(&inputs) {
        rust.push_str(&format!("== {path}\n{}", expected(source)));
    }
    assert_same_dump("fmt", &rust, &out.stdout);
}

#[test]
fn fmt_matches_the_corpus() {
    compare("fmt-corpus", corpus());
}
