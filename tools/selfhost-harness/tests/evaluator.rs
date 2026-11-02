//! The evaluator and the Rust backend run the totes alike.
//!
//! The differential tests use the Rust backend. These tests compare its output
//! with the evaluator's output on a small part of the corpus. Execution timings
//! for both backends are measured in `tools/selfhost-harness/benches/compiler.rs`.

use selfhost_harness::{corpus, materialize, run_tote, run_tote_native};

const STEPS: u64 = 200_000_000_000;

/// The smallest inputs of the corpus, a dozen of them.
fn small() -> Vec<(String, String)> {
    let mut inputs = corpus();
    inputs.retain(|(_, source)| source.len() < 400);
    inputs.truncate(12);
    assert!(!inputs.is_empty());
    inputs
}

fn same(label: &str, tote: &str, flag: Option<&str>, with_prelude: bool) {
    let mut all = Vec::new();
    if with_prelude {
        all.push(("prelude".to_string(), tauto::nibstd::PRELUDE.to_string()));
    }
    all.extend(small());
    let m = materialize(label, &all);
    let mut args: Vec<String> = flag.into_iter().map(String::from).collect();
    args.extend(m.paths.iter().cloned());
    let evaluated = run_tote(tote, &args, STEPS);
    let native = run_tote_native(tote, &args, STEPS);
    assert_eq!(evaluated.error, None);
    assert_eq!(native.error, None);
    assert_eq!(evaluated.stderr, native.stderr);
    assert_eq!(evaluated.exit.unwrap_or(0), native.exit.unwrap_or(0));
    assert_eq!(evaluated.stdout, native.stdout, "{tote} {flag:?}");
}

#[test]
fn nibcheck_rows() {
    same("eval-rows", "nibcheck", Some("--rows"), true);
}

#[test]
fn nibcheck_types() {
    same("eval-types", "nibcheck", Some("--types"), true);
}

#[test]
fn nibcheck_lin() {
    same("eval-lin", "nibcheck", Some("--lin"), true);
}

#[test]
fn fmt() {
    same("eval-fmt", "fmt", None, false);
}
