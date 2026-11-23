//! The text of the block form (`blocks { … }`) says everything a function in
//! blocks holds: for every function of every case that compiles, its blocks
//! printed, read back and printed again give the same text, and the blocks
//! read back differ from the first only in spans and name identities.
//! Checked as the compiler gives the package and again in A-normal form with
//! its drops written, for both targets.
//!
//! `cargo test -p tauto-test-suite --test nir_blocks_text -- <filter>` runs
//! only the cases whose name contains the filter.

use std::path::Path;

/// `Ok` when the function reads back from its text as it was.
fn round_trip(pkg: &tauto_nir::Package, f: &tauto_nir::FnInst) -> Result<(), String> {
    let bf = tauto_nir::blocks::lower_body(&f.body, f.tier);
    let text = tauto_nir::blocks::print(pkg, f, &bf)?;
    let (head, back) = tauto_nir::text::parse_blocks(pkg, &text).map_err(|e| {
        let at = (e.span.start as usize).min(text.len());
        let from = text[..at].rfind('\n').map(|i| i + 1).unwrap_or(0);
        let to = text[at..].find('\n').map(|i| at + i).unwrap_or(text.len());
        format!("read: {e}\n{}", &text[from..to])
    })?;
    let again = tauto_nir::blocks::print(pkg, &head, &back)?;
    if again != text {
        let line = text
            .lines()
            .zip(again.lines())
            .find(|(a, b)| a != b)
            .map(|(a, b)| format!("{a}\n{b}"))
            .unwrap_or_else(|| "the lengths differ".into());
        return Err(format!("the text read back prints differently:\n{line}"));
    }
    tauto_nir::blocks::same(&bf, &back)
}

fn main() -> std::process::ExitCode {
    use tauto_test_suite::{Harness, harness_tests};

    const TEST: &str = "round_trip";
    let filter = match harness_tests(|| vec![TEST.into()]) {
        Harness::Listed => return std::process::ExitCode::SUCCESS,
        Harness::Run { positional, exact } => {
            let name = positional.into_iter().next();
            if exact {
                return if name.as_deref() == Some(TEST) {
                    run(None)
                } else {
                    std::process::ExitCode::SUCCESS
                };
            }
            name
        }
    };
    run(filter.as_deref())
}

fn run(filter: Option<&str>) -> std::process::ExitCode {
    tauto_messages::install();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases");
    let all: Vec<_> = tauto_test_suite::rust_cases(&root)
        .expect("the case files are read")
        .into_iter()
        .filter(|c| filter.is_none_or(|f| c.name.contains(f)))
        .collect();
    // The same source compiles to the same packages: the first case written
    // with it stands for the others.
    let mut seen = std::collections::HashSet::new();
    let cases: Vec<_> = all
        .iter()
        .filter(|c| c.compiled_source().is_none_or(|s| seen.insert(s)))
        .collect();
    const TARGETS: [&str; 2] = ["rust", "javascript"];
    let results = tauto_test_suite::parallel_map(
        &cases,
        |_| (),
        |_, _, case| {
            let mut checked = 0;
            let mut failures = Vec::new();
            let compiled = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                case.compile_backends(&TARGETS)
            }))
            .map(|packages| packages.into_iter().map(Ok).collect::<Vec<_>>())
            // A panic in one target leaves the other to be compiled alone.
            .unwrap_or_else(|_| {
                TARGETS
                    .iter()
                    .map(|target| {
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            case.compile(target)
                        }))
                    })
                    .collect()
            });
            for (target, compiled) in TARGETS.iter().zip(compiled) {
                let Ok(Ok(mut pkg)) = compiled else { continue };
                for form in ["anf", "anf+drops"] {
                    if form == "anf+drops" {
                        tauto_nir::anf::normalize(&mut pkg);
                        tauto_nir::ownership::insert(&mut pkg);
                    } else {
                        tauto_nir::anf::normalize(&mut pkg);
                    }
                    checked += 1;
                    for f in &pkg.fns {
                        if let Err(e) = round_trip(&pkg, f) {
                            failures.push(format!(
                                "{} ({target}, {form}) {}@{}: {e}",
                                case.name, f.source, f.id
                            ));
                        }
                    }
                }
            }
            (checked, failures)
        },
    );
    let checked: usize = results.iter().map(|r| r.0).sum();
    let failures: Vec<&String> = results.iter().flat_map(|r| &r.1).collect();
    for f in failures.iter().take(40) {
        println!("FAIL {f}\n");
    }
    println!(
        "{checked} packages of {} cases ({} inputs), {} functions failed",
        all.len(),
        cases.len(),
        failures.len()
    );
    if failures.is_empty() && checked > 0 {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::FAILURE
    }
}
