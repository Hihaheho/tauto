//! Runs every case file under the repository's `cases/`, one line per file,
//! after Eure's test-suite. `cargo test -p tauto-test-suite --test cases --
//! <filter>` runs only the cases whose `category/file/case` contains the
//! filter.
//!
//! Each case's status is compared with `cases/coverage/eval.tsv`, as the
//! backend runners do with theirs; see `tauto_test_suite::coverage`.

use std::path::Path;
use std::process::ExitCode;

use tauto_test_suite::{FileReport, Outcome, coverage, run_all_with};

fn main() -> ExitCode {
    tauto_test_suite::with_deep_stack(run)
}

fn run() -> ExitCode {
    // cargo passes its own flags (`--nocapture`, `--quiet`, …) through.
    let filter = std::env::args().skip(1).find(|a| !a.starts_with('-'));
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = crate_dir.join("../../cases");
    let (mut passed, mut total, mut todo, mut failed) = (0, 0, 0, 0);
    let mut got = std::collections::BTreeMap::new();
    let reports = match run_all_with(&root, filter.as_deref(), |file: &FileReport| {
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
            got.insert(file.name.clone(), coverage::status("fail", e));
        }
        for (case, outcome) in &file.results {
            let status = match outcome {
                Outcome::Passed => "pass".to_string(),
                Outcome::Todo => "todo: unimplemented".into(),
                Outcome::Failed(why) => coverage::status("fail", why),
                Outcome::UnexpectedPass => "fail: passes now; take `unimplemented` off".into(),
                // Not an evaluator case; the backend records hold it.
                Outcome::BackendOnly => String::new(),
            };
            if !status.is_empty() {
                got.insert(format!("{}/{case}", file.name), status);
            }
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
    let recorded = coverage::report(&root, "eval", filter.as_deref(), &got);
    if !recorded || failed > 0 || total == 0 || passed == 0 {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
