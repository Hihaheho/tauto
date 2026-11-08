//! Runs every case file under the repository's `cases/`, one line per file,
//! after Eure's test-suite. Each file is one test (`category/file`), so
//! `cargo nextest` runs the files side by side; `cargo test -p
//! tauto-test-suite --test cases -- <filter>` runs only the cases whose
//! `category/file/case` contains the filter.

use std::path::Path;
use std::process::ExitCode;

use tauto_test_suite::{FileReport, Filter, Harness, Outcome, run_all_with};

fn main() -> ExitCode {
    tauto_test_suite::with_deep_stack(run)
}

fn run() -> ExitCode {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = crate_dir.join("../../cases");
    // One test for each case file, so that the runner can run them side by side.
    let (positional, exact) = match tauto_test_suite::harness_tests(|| {
        tauto_test_suite::case_file_names(&root).unwrap_or_default()
    }) {
        Harness::Listed => return ExitCode::SUCCESS,
        Harness::Run { positional, exact } => (positional, exact),
    };
    let filter = positional.first().map(|f| {
        if exact {
            Filter::File(f)
        } else {
            Filter::Contains(f)
        }
    });
    let (mut passed, mut total, mut todo, mut failed) = (0, 0, 0, 0);
    let reports = match run_all_with(&root, filter, |file: &FileReport| {
        let ok = file
            .results
            .iter()
            .filter(|(_, o)| matches!(o, Outcome::Passed))
            .count();
        let file_todo = file
            .results
            .iter()
            .filter(|(_, o)| matches!(o, Outcome::Todo | Outcome::BackendOnly))
            .count();
        passed += ok;
        todo += file_todo;
        total += file.results.len();
        println!(
            "{} {ok}/{} {}",
            file.name,
            file.results.len(),
            if file.failed() {
                "FAIL"
            } else if ok == 0 {
                "DEFERRED"
            } else if file_todo > 0 {
                "PARTIAL"
            } else {
                "PASS"
            }
        );
        if let Some(e) = &file.error {
            failed += 1;
            println!("  file: {e}");
        }
        for (case, outcome) in &file.results {
            match outcome {
                Outcome::Failed(why) => {
                    failed += 1;
                    println!("  {case}: {why}");
                }
                Outcome::UnexpectedPass => {
                    failed += 1;
                    println!("  {case}: passes now; take `unimplemented` off");
                }
                Outcome::Passed | Outcome::Todo | Outcome::BackendOnly => {}
            }
        }
    }) {
        Ok(found) => found,
        Err(e) => {
            eprintln!("cannot read cases under {}: {e}", root.display());
            return ExitCode::FAILURE;
        }
    };
    println!(
        "\n{passed}/{} cases passed, {todo} todo, {failed} failed, {} files",
        total - todo,
        reports.len()
    );
    // One file may hold only cases that do not run yet; the whole suite may not.
    let none_passed = passed == 0 && !matches!(filter, Some(Filter::File(_)));
    if failed > 0 || total == 0 || none_passed {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
