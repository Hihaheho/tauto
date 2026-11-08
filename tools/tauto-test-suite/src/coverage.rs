//! What each backend does with every case it runs.
//!
//! A backend runner reports one status per selected case: `pass`, or a
//! status that says why the case is not a pass. `partial` checked the output
//! but leaves an assertion no backend observes, `declined` is a declared
//! `rust = "skip: …"`, and `todo` is a failure the case itself declares
//! (`backend_known_failure`, or `unimplemented`). Anything else is `fail`,
//! and one `fail` fails the run. A declared failure that no longer happens
//! is a `fail` too, so the declarations in the cases are the whole list of
//! what a backend does not do yet.

use std::collections::BTreeMap;
use std::path::Path;

pub fn status(kind: &str, text: &str) -> String {
    let line = text.lines().find(|l| !l.trim().is_empty()).unwrap_or("");
    let line = without_scratch_dirs(&line.replace('\t', " "));
    let line: String = line.trim().chars().take(160).collect();
    if line.is_empty() {
        kind.to_string()
    } else {
        format!("{kind}: {line}")
    }
}

/// A case's scratch directory is named by the process and a counter, so a
/// status that names a file in it says `<case>` for the directory instead.
/// The Rust backend's work directory sits under a machine's temporary or
/// target directory, so a status that names it says `<work>`.
fn without_scratch_dirs(line: &str) -> String {
    without_work_dirs(&without_case_dirs(line))
}

fn without_work_dirs(line: &str) -> String {
    const WORK: &str = "tauto-rust-backend/work-";
    let mut out = String::new();
    let mut rest = line;
    while let Some(at) = rest.find(WORK) {
        let start = rest[..at]
            .rfind(|c: char| c.is_whitespace() || c == '(' || c == '`' || c == '\'')
            .map_or(0, |i| i + 1);
        out.push_str(&rest[..start]);
        let tail = &rest[at + WORK.len()..];
        let end = tail
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(tail.len());
        out.push_str("<work>");
        rest = &tail[end..];
    }
    out.push_str(rest);
    out
}

fn without_case_dirs(line: &str) -> String {
    let dir = std::env::temp_dir().join("tauto-cases-");
    let dir = dir.to_string_lossy();
    let mut out = String::new();
    let mut rest = line;
    while let Some(at) = rest.find(dir.as_ref()) {
        out.push_str(&rest[..at]);
        let tail = &rest[at + dir.len()..];
        let end = tail
            .find(|c: char| !(c.is_ascii_digit() || c == '-'))
            .unwrap_or(tail.len());
        out.push_str("<case>");
        rest = &tail[end..];
    }
    out.push_str(rest);
    out
}

/// Print a summary and every failure; true when no case failed.
pub fn report(backend: &str, got: &BTreeMap<String, String>) -> bool {
    let mut counts = BTreeMap::<&str, usize>::new();
    for status in got.values() {
        *counts.entry(kind(status)).or_default() += 1;
    }
    println!("\n{backend}: {counts:?}");
    let failed: Vec<_> = got.iter().filter(|(_, s)| kind(s) == "fail").collect();
    if failed.is_empty() {
        return true;
    }
    println!("\n{} failed on {backend}:", failed.len());
    for (case, status) in failed {
        println!("  {case}: {status}");
    }
    false
}

fn kind(status: &str) -> &str {
    status.split(':').next().unwrap()
}

/// Run every case `backend` selects through a runner, print the statuses that
/// are not `pass`, and report the failures. True when no case failed and at
/// least one case checked successfully.
///
/// Cases run on `test_threads()` workers. `make_runner` builds one runner for
/// each worker (given its number), so a runner keeps its own scratch
/// directories and build lanes; the statuses are printed and compared in the
/// order of the case names.
pub fn run_backend<R: FnMut(usize, &crate::RustCase) -> String>(
    cases_dir: &Path,
    backend: crate::Scenario,
    filter: Option<crate::Filter>,
    make_runner: impl Fn(usize) -> R + Sync,
) -> Result<bool, String> {
    // The expected messages of the cases are the English ones, whichever
    // cases the filter leaves to run first.
    tauto_messages::install();
    let mut cases = crate::rust_cases(cases_dir)?;
    cases.retain(|case| {
        filter.is_none_or(|f| f.admits(&case.name)) && case.selects_backend(backend.name())
    });
    let statuses = crate::parallel_map(&cases, make_runner, |run, i, case| {
        let mut s = run(i, case);
        // An `unimplemented` case is a declared failure, never a hard one.
        if case.unimplemented {
            if let Some(why) = s.strip_prefix("fail") {
                s = format!("todo: unimplemented{why}");
            }
        }
        s
    });
    let mut got = BTreeMap::new();
    for (case, s) in cases.iter().zip(statuses) {
        got.insert(case.name.clone(), s);
    }
    for (name, s) in &got {
        if s != "pass" {
            println!("{} {name}: {s}", backend.name());
        }
    }
    if !got.values().any(|s| s == "pass") {
        println!("{}: no case checked successfully", backend.name());
        return Ok(false);
    }
    Ok(report(backend.name(), &got))
}

#[cfg(test)]
mod tests {
    use super::without_work_dirs;

    #[test]
    fn a_work_directory_is_named_without_its_machine_path() {
        assert_eq!(
            without_work_dirs("the source is in /tmp/tauto-rust-backend/work-0):"),
            "the source is in <work>):"
        );
        assert_eq!(
            without_work_dirs("(/a/b/tauto-rust-backend/work-12/src/main.rs)"),
            "(<work>/src/main.rs)"
        );
    }
}
