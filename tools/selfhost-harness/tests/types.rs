//! `totes/nibcheck`'s types against `tauto::types` (`docs/design/self-host.md`).

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};
use tauto::surface::parse_program_as_written;
use tauto::types::{check_program, dump_types};

const STEPS: u64 = 200_000_000_000;

/// What the Rust analysis gives, in the form the tote prints: the dump of the
/// report, or `error` when the source does not parse.
fn expected(source: &str) -> String {
    std::panic::catch_unwind(|| {
        parse_program_as_written(source)
            .ok()
            .map(|p| dump_types(&check_program(&p)))
    })
    .ok()
    .flatten()
    .unwrap_or_else(|| "error\n".to_string())
}

fn compare(label: &str, inputs: Vec<(String, String)>) {
    let mut all = vec![("prelude".to_string(), tauto::nibstd::PRELUDE.to_string())];
    all.extend(inputs.iter().cloned());
    let m = materialize(label, &all);
    let mut args = vec!["--types".to_string()];
    args.extend(m.paths.iter().cloned());
    let out = run_tote_native("nibcheck", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let mut rust = String::new();
    for (path, (_, source)) in m.paths.iter().skip(1).zip(&inputs) {
        rust.push_str(&format!("== {path}\n{}", expected(source)));
    }
    assert_same_dump(
        "types",
        &canonical_variables(&rust),
        &canonical_variables(&out.stdout),
    );
}

// Allocation order is not part of a type: preserve sharing while comparing
// unresolved variables up to a consistent renaming within each program dump.
fn canonical_variables(dump: &str) -> String {
    let mut names = std::collections::HashMap::new();
    let mut out = String::new();
    for line in dump.split_inclusive('\n') {
        if line.starts_with("== ") {
            names.clear();
        }
        let mut rest = line;
        while let Some(at) = rest.find("Var(") {
            out.push_str(&rest[..at + 4]);
            rest = &rest[at + 4..];
            let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
            if digits > 0 && rest.as_bytes().get(digits) == Some(&b')') {
                let next = names.len();
                let id = *names.entry(rest[..digits].to_owned()).or_insert(next);
                out.push_str(&id.to_string());
                rest = &rest[digits..];
            }
        }
        out.push_str(rest);
    }
    out
}

#[test]
fn variable_comparison_preserves_sharing_and_resets_between_programs() {
    let a = "== a\nterm Fn([Var(9)],Var(9),copy)\n== b\nterm Var(2)\n";
    let b = "== a\nterm Fn([Var(1)],Var(1),copy)\n== b\nterm Var(8)\n";
    assert_eq!(canonical_variables(a), canonical_variables(b));
    assert_ne!(
        canonical_variables("term Fn([Var(1)],Var(1),copy)"),
        canonical_variables("term Fn([Var(1)],Var(2),copy)")
    );
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
fn types_match_the_corpus_0() {
    part("types-0", 0, 4);
}

#[test]
fn types_match_the_corpus_1() {
    part("types-1", 1, 4);
}

#[test]
fn types_match_the_corpus_2() {
    part("types-2", 2, 4);
}

#[test]
fn types_match_the_corpus_3() {
    part("types-3", 3, 4);
}

#[test]
fn types_match_contextual_constructor_owners() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| name.starts_with("cases/selfhost-constructor-owner.eure#"))
        .collect();
    assert_eq!(inputs.len(), 14);
    compare("types-constructor-owners", inputs);
}
