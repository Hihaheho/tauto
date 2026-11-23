//! Source tests: the `test` entries of a tote's source files.
//!
//! Each file that performs `test` is run as `tauto run` runs it, in a process
//! of its own, told to call its tests and not its `main` (`tauto_rt::entry`).
//! The process writes what it found and how each test ended to a report file,
//! so a test's own output cannot be read as a result and a run that stops
//! leaves what it reported.
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use serde::Serialize;
use tauto_rt::entry::{Outcome, Report};

use crate::i18n;

#[derive(Serialize)]
struct ResultLine {
    name: String,
    /// `passed`, `passed_after_retry` (the body returned after failing
    /// before; the detail says how many times), `failed` (the body performed
    /// `fail`, every time it was called), `stopped` (the run
    /// ended while the body ran), `not_run` (the run ended before it), or
    /// `error` (the file did not check, or its entries make no plan).
    status: &'static str,
    detail: String,
}

/// What `tauto run` reads of the arguments of `tauto test`: they are passed on.
fn run_flag(arg: &str) -> Option<bool> {
    match arg {
        "--steps" => Some(true),
        "--check-ownership" | "--yes" => Some(false),
        _ => None,
    }
}

pub fn command(args: &[String]) -> ExitCode {
    let (mut path, mut filter, mut json, mut list, mut backend) = (None, None, false, false, None);
    let mut retries: Option<usize> = None;
    let mut flags: Vec<String> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        if let Some(takes_value) = run_flag(arg) {
            flags.push(arg.clone());
            if takes_value {
                let Some(value) = rest.next() else {
                    return usage();
                };
                flags.push(value.clone());
            }
            continue;
        }
        if arg.starts_with('-') && !seen.insert(arg) {
            return usage();
        }
        match arg.as_str() {
            "--json" => json = true,
            "--list" => list = true,
            "--filter" => {
                let Some(value) = rest.next() else {
                    return usage();
                };
                filter = Some(value.as_str());
            }
            "--retries" => {
                let Some(value) = rest.next().and_then(|v| v.parse().ok()) else {
                    eprintln!("{}", i18n::t!("test-retries-number"));
                    return usage();
                };
                retries = Some(value);
            }
            "--backend" => {
                let Some(value) = rest
                    .next()
                    .filter(|v| matches!(v.as_str(), "vm" | "rust" | "javascript"))
                else {
                    return usage();
                };
                backend = Some(value.as_str());
            }
            "--help" | "-h" if args.len() == 1 => {
                println!("{}", usage_text());
                return ExitCode::SUCCESS;
            }
            a if a.starts_with('-') => return usage(),
            p if path.is_none() => path = Some(PathBuf::from(p)),
            _ => return usage(),
        }
    }
    let mut path = path.unwrap_or_else(|| PathBuf::from("."));
    if path.file_name().is_some_and(|name| name == "Tauto.eure") {
        path = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."))
            .to_path_buf();
    }
    let mut files = Vec::new();
    // How many times a test that failed is called again: what `--retries`
    // says, or else the tote's `test { retries = N }`, or else never.
    let retries = match retries {
        Some(n) => n,
        None if path.is_dir() && path.join("Tauto.eure").is_file() => {
            match tauto::manifest::read(&path) {
                Ok(manifest) => manifest.test_retries.unwrap_or(0),
                Err(error) => {
                    eprintln!("{error}");
                    return ExitCode::from(2);
                }
            }
        }
        None => 0,
    };
    let discovered = if path.is_dir() && path.join("Tauto.eure").is_file() {
        // A tote's tests are in its sources: the files `tauto check --tote` reads.
        tauto::program::package_source_files(&path).map(|sources| files = sources)
    } else {
        discover(&path, &mut files)
    };
    if let Err(error) = discovered {
        eprintln!("{error}");
        return ExitCode::from(2);
    }
    files.sort();
    let root = if path.is_dir() {
        path.as_path()
    } else {
        path.parent().unwrap_or(Path::new("."))
    };
    let mut results = Vec::new();
    for file in files {
        let name = file
            .strip_prefix(root)
            .unwrap_or(&file)
            .to_string_lossy()
            .replace('\\', "/");
        let error = |detail: String| ResultLine {
            name: name.clone(),
            status: "error",
            detail,
        };
        // A file whose text performs no `test` holds no test and is not run.
        match performs_test(&file) {
            Ok(true) => {}
            Ok(false) => continue,
            Err(detail) => {
                if filter.is_none_or(|f| name.contains(f)) {
                    results.push(error(detail));
                }
                continue;
            }
        }
        // When every test of the file is selected (no filter, or the filter
        // is in the file's name) and they are to be called, one run finds
        // and calls them: the file is read, checked and compiled once.
        // Otherwise a first run finds the tests without calling one, and a
        // second calls the ones the filter selects. Finding them always has
        // a step limit, whatever the tests may do: a top level that does not
        // end is reported, not waited for.
        let all = filter.is_none_or(|f| name.contains(f));
        let mut bounded: Vec<String> = flags.clone();
        if !bounded.iter().any(|f| f == "--steps") {
            bounded.extend(["--steps".into(), tauto_rt::DEFAULT_STEP_LIMIT.to_string()]);
        }
        let once = all && !list;
        let first = if once {
            run(&file, backend, &flags, "test", None, retries, root)
        } else {
            run(&file, backend, &bounded, "list", None, 0, root)
        };
        let found = match first {
            Ok(report) => report,
            Err(detail) => {
                if all {
                    results.push(error(i18n::t!("test-finding", detail = detail)));
                }
                continue;
            }
        };
        if let Some(why) = found.error {
            results.push(error(why));
            continue;
        }
        let report = if once {
            if found.tests.is_empty() {
                continue;
            }
            found
        } else {
            let selected: Vec<String> = found
                .found
                .into_iter()
                .filter(|test| filter.is_none_or(|f| format!("{name}::{test}").contains(f)))
                .collect();
            if selected.is_empty() {
                continue;
            }
            if list {
                Report {
                    tests: selected
                        .iter()
                        .map(|n| (n.clone(), Outcome::NotRun))
                        .collect(),
                    ..Report::default()
                }
            } else {
                match run(
                    &file,
                    backend,
                    &flags,
                    "test",
                    Some(&selected),
                    retries,
                    root,
                ) {
                    Ok(report) => report,
                    Err(detail) => {
                        results.push(error(detail));
                        continue;
                    }
                }
            }
        };
        if let Some(why) = report.error {
            results.push(error(why));
            continue;
        }
        let stopped = report.stopped.unwrap_or_default();
        for (test, outcome) in report.tests {
            let (status, detail) = match outcome {
                Outcome::Passed => ("passed", String::new()),
                Outcome::Retried(times) => ("passed_after_retry", times.to_string()),
                Outcome::Failed(why) => ("failed", why),
                Outcome::Stopped => ("stopped", stopped.clone()),
                Outcome::NotRun if list => ("listed", String::new()),
                Outcome::NotRun => ("not_run", String::new()),
            };
            results.push(ResultLine {
                name: format!("{name}::{test}"),
                status,
                detail,
            });
        }
    }
    let count = |status: &str| results.iter().filter(|r| r.status == status).count();
    let retried = count("passed_after_retry");
    let passed = count("passed") + retried;
    let failed = results.len() - passed - count("listed");
    if json {
        println!(
            "{}",
            serde_json::json!({"tests": results, "passed": passed, "retried": retried, "failed": failed, "empty": results.is_empty()})
        );
    } else {
        for r in &results {
            if list {
                println!("{}", r.name);
                continue;
            }
            println!(
                "{} {}{}",
                r.status,
                r.name,
                if r.detail.is_empty() {
                    String::new()
                } else {
                    format!(": {}", r.detail)
                }
            );
        }
        if !list {
            println!(
                "{}",
                i18n::t!("test-summary", passed = passed, failed = failed)
            );
            if retried > 0 {
                println!("{}", i18n::t!("test-summary-retried", count = retried));
            }
        }
    }
    if results.is_empty() {
        eprintln!("{}", i18n::t!("test-none-selected"));
    }
    if failed == 0 && !results.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn discover(path: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let metadata =
        std::fs::symlink_metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if metadata.file_type().is_symlink() {
        return Err(i18n::t!(
            "test-discovery-symlink",
            path = path.display().to_string()
        ));
    }
    if metadata.is_dir() {
        for entry in std::fs::read_dir(path).map_err(|e| e.to_string())? {
            discover(&entry.map_err(|e| e.to_string())?.path(), out)?;
        }
    } else if metadata.is_file()
        && path.file_name().is_none_or(|n| n != "Tauto.eure")
        && path
            .extension()
            .is_some_and(|e| e == "taut" || e == "tauto")
    {
        out.push(path.to_path_buf());
    }
    Ok(())
}

/// Whether the file's statements perform the `test` effect anywhere they run.
fn performs_test(path: &Path) -> Result<bool, String> {
    use tauto::surface::walk::{Node, values_stmt};
    let loaded = tauto::program::load(path)?;
    if let Some((error, _)) = loaded.program.errors.first() {
        return Err(error.to_string());
    }
    let own = std::fs::canonicalize(path).map_err(|e| e.to_string())?;
    let mut found = false;
    for (file, stmts) in loaded.files.iter().zip(&loaded.per_file) {
        if std::fs::canonicalize(&file.path).ok().as_ref() != Some(&own) {
            continue;
        }
        for stmt in stmts {
            values_stmt(stmt, &mut |node| {
                if let Node::Term(term) = node
                    && let tauto::surface::TermKind::Perform { effect, .. } = &*term.kind
                    && tauto::bindings::is_library(effect, "test")
                {
                    found = true;
                }
            });
        }
    }
    Ok(found)
}

/// Runs `path` as `tauto run` does, for its tests (`what`: `list` names them,
/// `test` calls the ones `names` selects), and reads the report it wrote. An
/// error is why the file did not get to its entries: it does not check, or it
/// performs none where its top level runs.
fn run(
    path: &Path,
    backend: Option<&str>,
    flags: &[String],
    what: &str,
    names: Option<&[String]>,
    retries: usize,
    root: &Path,
) -> Result<Report, String> {
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let file = std::env::temp_dir().join(format!(
        "tauto-test-{}-{}.report",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    let _ = std::fs::remove_file(&file);
    let mut command = std::process::Command::new(&exe);
    command.arg("run");
    if let Some(backend) = backend {
        command.args(["--backend", backend]);
    }
    command.args(flags).arg(path);
    command
        .env("TAUTO_ENTRY", what)
        .env("TAUTO_TEST_REPORT", &file)
        .env_remove("TAUTO_TEST_NAMES")
        .env("TAUTO_TEST_RETRIES", retries.to_string())
        // What answers a test's `check`: this command, reading paths from
        // the directory the tests were found in.
        .env("TAUTO_EXE", &exe)
        .env(
            "TAUTO_TEST_ROOT",
            std::fs::canonicalize(root).unwrap_or_else(|_| root.to_path_buf()),
        )
        .stdin(std::process::Stdio::null());
    if let Some(names) = names {
        let names: Vec<&str> = names.iter().map(String::as_str).collect();
        let line = tauto_rt::entry::line(&names);
        command.env("TAUTO_TEST_NAMES", line.trim_end_matches('\n'));
    }
    let out = command.output().map_err(|e| e.to_string())?;
    let text = std::fs::read_to_string(&file).unwrap_or_default();
    let _ = std::fs::remove_file(&file);
    let mut report = tauto_rt::entry::read(&text);
    let stderr = String::from_utf8_lossy(&out.stderr).trim().to_string();
    if !report.planned {
        // The run ended before its entries made a plan: the file does not
        // check, or its top level performs none.
        return if out.status.success() {
            Ok(report)
        } else {
            Err(stderr)
        };
    }
    if !out.status.success() && report.error.is_none() {
        report.stopped = Some(stderr);
    }
    Ok(report)
}

const USAGE: &str = "tauto test [PATH] [--filter TEXT] [--list] [--retries N] [--json] [--backend vm|rust|javascript] [--steps N] [--yes]";

fn usage_text() -> String {
    i18n::t!("test-usage", usage = USAGE)
}

fn usage() -> ExitCode {
    eprintln!("{}", usage_text());
    ExitCode::from(2)
}
