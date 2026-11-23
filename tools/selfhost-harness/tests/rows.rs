//! `totes/nibcheck`'s rows against `tauto::rows` (`docs/design/self-host.md`).

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};
use tauto::rows::{check_program_rows, dump_rows};
use tauto_parse::parse_program_as_written;

const STEPS: u64 = 200_000_000_000;

/// What the Rust analysis gives, in the form the tote prints: the dump of the
/// report, or `error` when the source does not parse.
///
/// A list literal is nested `Cons` calls, one level for each element, and the
/// Rust analysis goes down it recursively: the long literal of
/// `cases/extract-long-list-literal.eure` is deeper than a test thread's
/// stack. The analysis runs on the stack `tauto` and the case runner give it.
fn expected(source: &str) -> String {
    tauto_test_suite::with_deep_stack(|| expected_here(source))
}

fn expected_here(source: &str) -> String {
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

/// A function value given for a callback parameter performs only what the
/// parameter's row names: the errors are at the value, in the order of the
/// functions around them.
#[test]
fn rows_value_performs_matches() {
    let source = "effect ask(): i64\n\
        fn apply(f: (i64) -> i64): i64 { f(1) }\n\
        fn a(): i64 ! {} { perform ask() }\n\
        fn b(): i64 ! {ask} { apply((x) => perform ask()) }\n\
        fn c(): i64 ! {} { perform ask() }\n";
    compare(
        "rows-value-performs",
        vec![("value-performs.taut".to_string(), source.to_string())],
    );
}

/// Replaceable `extern` validation runs through `--rows` (shared `types_check_with`).
#[test]
fn rows_match_replaceable_extern_validate_cases() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| {
            name.starts_with("cases/selfhost-rows.eure#rows-replaceable-mix-required")
                || name.starts_with("cases/selfhost-rows.eure#rows-replaceable-open")
        })
        .collect();
    assert_eq!(inputs.len(), 2);
    compare("rows-replaceable-extern-validate", inputs);
}
