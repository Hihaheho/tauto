//! `totes/nibcheck`'s rows against `tauto::rows` (`docs/design/self-host.md`).

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};
use tauto::rows::{check_program_rows, dump_rows};
use tauto::surface::parse_program_as_written;

const STEPS: u64 = 200_000_000_000;

/// What the Rust analysis gives, in the form the tote prints: the dump of the
/// report, or `error` when the source does not parse.
fn expected(source: &str) -> String {
    std::panic::catch_unwind(|| {
        parse_program_as_written(source)
            .ok()
            .map(|p| dump_rows(&check_program_rows(&p)))
    })
    .ok()
    .flatten()
    .unwrap_or_else(|| "error\n".to_string())
}

fn compare(label: &str, inputs: Vec<(String, String)>) {
    let mut all = vec![("prelude".to_string(), tauto::nibstd::PRELUDE.to_string())];
    all.extend(inputs.iter().cloned());
    let m = materialize(label, &all);
    let mut args = vec!["--rows".to_string()];
    args.extend(m.paths.iter().cloned());
    let out = run_tote_native("nibcheck", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let mut rust = String::new();
    for (path, (_, source)) in m.paths.iter().skip(1).zip(&inputs) {
        rust.push_str(&format!("== {path}\n{}", expected(source)));
    }
    assert_same_dump("rows", &rust, &out.stdout);
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
fn rows_match_the_corpus_0() {
    part("rows-0", 0, 4);
}

#[test]
fn rows_match_the_corpus_1() {
    part("rows-1", 1, 4);
}

#[test]
fn rows_match_the_corpus_2() {
    part("rows-2", 2, 4);
}

#[test]
fn rows_match_the_corpus_3() {
    part("rows-3", 3, 4);
}
