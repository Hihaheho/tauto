//! The text of NIR says everything a package holds: for every case that
//! compiles, the package printed, read back and printed again gives the
//! same text, and the package read back differs from the first only in
//! where its nodes came from. Checked as the compiler gives the package
//! and again in A-normal form with its drops written, for both targets.
//!
//! `cargo test -p tauto-test-suite --test nir_text -- <filter>` runs only
//! the cases whose name contains the filter.
//!
//! Compiling the cases is nearly all the time this takes, so each input is
//! compiled once: cases written as the same source share their packages,
//! and a case is read and its types checked once for both targets
//! (`RustCase::compile_backends`).

use std::path::Path;

fn round_trip(pkg: &tauto_nir::Package) -> Result<(), String> {
    let text = tauto_nir::text::print(pkg)?;
    let back = tauto_nir::text::parse(&text).map_err(|e| {
        let at = e.span.start as usize;
        let from = text[..at].rfind('\n').map(|i| i + 1).unwrap_or(0);
        let to = text[at..].find('\n').map(|i| at + i).unwrap_or(text.len());
        format!("read: {e}\n{}", &text[from..to])
    })?;
    let again = tauto_nir::text::print(&back)?;
    if again != text {
        let line = text
            .lines()
            .zip(again.lines())
            .find(|(a, b)| a != b)
            .map(|(a, b)| format!("{a}\n{b}"))
            .unwrap_or_default();
        return Err(format!("the text read back prints differently:\n{line}"));
    }
    tauto_nir::text::same(pkg, &back)
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
                for form in ["compiled", "with drops"] {
                    if form == "with drops" {
                        tauto_nir::anf::normalize(&mut pkg);
                        tauto_nir::ownership::insert(&mut pkg);
                    }
                    checked += 1;
                    if let Err(e) = round_trip(&pkg) {
                        failures.push(format!("{} ({target}, {form}): {e}", case.name));
                    }
                }
            }
            (checked, failures)
        },
    );
    let checked: usize = results.iter().map(|r| r.0).sum();
    let failures: Vec<&String> = results.iter().flat_map(|r| &r.1).collect();
    for f in &failures {
        println!("FAIL {f}\n");
    }
    println!(
        "{checked} packages of {} cases ({} inputs), {} failed",
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
