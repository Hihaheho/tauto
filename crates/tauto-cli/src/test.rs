//! Source tests: the `perform test` statements in a tote's source files.
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use serde::Serialize;

use crate::i18n;

#[derive(Serialize)]
struct ResultLine {
    name: String,
    status: &'static str,
    detail: String,
}

pub fn command(args: &[String]) -> ExitCode {
    let (mut path, mut filter, mut json, mut backend) = (None, None, false, None);
    let mut seen = std::collections::HashSet::new();
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        if arg.starts_with('-') && !seen.insert(arg) {
            return usage();
        }
        match arg.as_str() {
            "--json" => json = true,
            "--filter" => {
                let Some(value) = rest.next() else {
                    return usage();
                };
                filter = Some(value.as_str());
            }
            "--backend" => {
                let Some(value) = rest.next().filter(|v| *v == "rust" || *v == "javascript") else {
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
        // A file whose program performs no `test` holds no test and is not run.
        match performs_test(&file) {
            Ok(true) => {}
            Ok(false) => continue,
            Err(detail) => {
                results.push(ResultLine {
                    name,
                    status: "failed",
                    detail,
                });
                continue;
            }
        }
        // The file is an entry: its top-level `perform test` statements are the tests.
        let outcome = match backend {
            Some(backend) => run_backend(&file, backend),
            None => run_source(&file),
        };
        match outcome {
            Ok(tests) => {
                for (test, error) in tests {
                    let name = format!("{name}::{test}");
                    if filter.is_none_or(|f| name.contains(f)) {
                        results.push(ResultLine {
                            name,
                            status: if error.is_none() { "passed" } else { "failed" },
                            detail: error.unwrap_or_default(),
                        });
                    }
                }
            }
            Err(detail) if filter.is_none_or(|f| name.contains(f)) => results.push(ResultLine {
                name,
                status: "failed",
                detail,
            }),
            Err(_) => {}
        }
    }
    let passed = results
        .iter()
        .filter(|r| matches!(r.status, "passed"))
        .count();
    let failed = results.len() - passed;
    if json {
        println!(
            "{}",
            serde_json::json!({"tests": results, "passed": passed, "failed": failed, "empty": results.is_empty()})
        );
    } else {
        for r in &results {
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
        println!(
            "{}",
            i18n::t!("test-summary", passed = passed, failed = failed)
        );
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

/// Builds and runs a source file on a backend; the tests its `run_test` lines name.
fn run_backend(path: &Path, backend: &str) -> Result<Vec<(String, Option<String>)>, String> {
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let out = std::process::Command::new(exe)
        .args(["run", "--backend", backend])
        .arg(path)
        .output()
        .map_err(|e| e.to_string())?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let tests = stdout
        .lines()
        .filter_map(|line| line.strip_prefix("test "))
        .filter_map(|rest| {
            if let Some(name) = rest.strip_suffix(" ... ok") {
                Some((name.to_string(), None))
            } else {
                let (name, why) = rest.split_once(" ... FAILED: ")?;
                Some((name.to_string(), Some(why.to_string())))
            }
        })
        .collect();
    if !out.status.success() {
        return Err(String::from_utf8_lossy(&out.stderr).trim().to_string());
    }
    Ok(tests)
}

/// Runs a source file after its check; the named tests it ran, with their errors.
fn run_source(path: &Path) -> Result<Vec<(String, Option<String>)>, String> {
    let report = tauto::report::check_report(path, None)?;
    if !matches!(report.status(), tauto::report::Status::Ok) {
        return Err(report.text());
    }
    let loaded = tauto::program::load_extracted(path)?;
    let rows = loaded.check_rows(false);
    if let Some(error) = rows.errors.first() {
        return Err(error.to_string());
    }
    let out = tauto::eval::run_loaded_with(
        &loaded,
        tauto::eval::DEFAULT_BUDGET,
        tauto::eval::RunOptions {
            check_ownership: true,
            ..Default::default()
        },
    )
    .map_err(|e| e.to_string())?;
    if out.exit.is_some_and(|code| code != 0) {
        return Err(i18n::t!(
            "test-program-exited",
            code = out.exit.unwrap().to_string()
        ));
    }
    Ok(out.tests)
}

const USAGE: &str = "tauto test [PATH] [--filter TEXT] [--json] [--backend rust|javascript]";

fn usage_text() -> String {
    i18n::t!("test-usage", usage = USAGE)
}

fn usage() -> ExitCode {
    eprintln!("{}", usage_text());
    ExitCode::from(2)
}
