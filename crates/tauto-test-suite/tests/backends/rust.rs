//! The Rust backend: generate a crate, build it with Cargo, run it, and
//! compare. A case the generator cannot write is uncovered, never passed.
//! Explicit backend routes fail unless a declared compilation-failure
//! contract matches.

use std::path::{Path, PathBuf};

use tauto_nir::CompileError;
use tauto_rustgen::Sources;
use tauto_test_suite::{RustCase, coverage::status};

enum Result_ {
    Passed,
    /// Not a program the front end accepts (a case about an error).
    Skipped,
    /// Declared `rust = "skip: <reason>"`.
    Declined(String),
    Todo(String),
    Failed(String),
    Partial(String),
}

/// Every successful route observation uses this one accounting gate.
fn checked(case: &RustCase) -> Result_ {
    let gaps = case.assertion_gaps();
    if gaps.is_empty() {
        Result_::Passed
    } else {
        Result_::Partial(gaps.join("; "))
    }
}

/// Compilation failures are assertions only when their stage and message match.
fn compilation_failure(case: &RustCase, stage: &str, message: &str) -> Result_ {
    match case.check_limitation("rust", stage, message) {
        Ok(true) => return Result_::Todo(format!("declared known failure {stage}: {message}")),
        Err(e) => return Result_::Failed(e),
        Ok(false) => {}
    }
    match case.check_compile_error("rust", stage, message) {
        Ok(true) => checked(case),
        Err(e) => Result_::Failed(e),
        Ok(false) => {
            if stage == "build"
                && case
                    .build
                    .as_deref()
                    .and_then(|s| s.strip_prefix("error: "))
                    .is_some_and(|w| message.contains(w))
            {
                return checked(case);
            }
            if stage == "unsupported" && !case.explicit_backend("rust") {
                Result_::Todo(format!("uncovered compiler capability: {message}"))
            } else {
                Result_::Failed(format!("{stage}: {message}"))
            }
        }
    }
}

fn run_case(case: &RustCase, work: &Path, target: &Path) -> Result_ {
    if !case.selects_backend("rust") {
        return Result_::Skipped;
    }
    if let Some(rust) = &case.rust {
        if case.explicit_backend("rust") {
            return Result_::Failed("an explicit Rust route cannot be skipped".into());
        }
        return Result_::Declined(rust.clone());
    }
    let source = match case.compilation_source() {
        Ok(source) => source,
        Err(message) => return compilation_failure(case, "front", &message),
    };
    let package = match case.compile("rust") {
        Ok(p) => p,
        Err(CompileError::Unsupported(u)) => {
            return compilation_failure(case, "unsupported", &u.what);
        }
        Err(CompileError::Build(m)) => return compilation_failure(case, "build", &m),
        Err(CompileError::Front(m)) => return compilation_failure(case, "front", &m),
    };
    let manifest = match case
        .tote
        .as_ref()
        .map(|p| tauto::manifest::load(p))
        .transpose()
    {
        Ok(m) => m,
        Err(m) => return compilation_failure(case, "build", &m),
    };
    // The case host's probe, as every runner gives it.
    let mut manifest = manifest;
    if !package.externs.is_empty() {
        let m = manifest.get_or_insert_with(Default::default);
        for (map, name, rust) in [
            (&mut m.rust.types, "Probe", "tauto_rt::probe::Probe"),
            (&mut m.rust.externs, "Probe.new", "tauto_rt::probe::probe"),
        ] {
            map.entry(name.into())
                .or_insert_with(|| tauto::manifest::Entry {
                    value: rust.into(),
                    file: "case host".into(),
                    line: 0,
                });
        }
    }
    let bindings = match tauto_rustgen::Bindings::resolve(&package, manifest.as_ref(), None) {
        Ok(b) => b,
        Err(e) => return compilation_failure(case, "build", &e),
    };
    let options = manifest
        .as_ref()
        .map(tauto_rustgen::Options::from_manifest)
        .unwrap_or_default();
    let mut ws = tauto_rustgen::workspace(
        "case",
        &package,
        &Sources {
            file: "input.taut",
            text: &source,
        },
        &bindings,
        &options,
    );
    // Keep `show` separate from stdout, as the evaluator's observable contract does.
    let lib = &mut ws
        .files
        .iter_mut()
        .find(|(p, _)| p == "src/lib.rs")
        .unwrap()
        .1;
    let needle = "\"{name} = {}\"";
    if lib.matches(needle).count() != 1 {
        return Result_::Failed("cannot locate the generated show handler".into());
    }
    let at = lib.find(needle).unwrap();
    let start = lib[..at].rfind("println").unwrap();
    let end = at + lib[at..].find(';').unwrap() + 1;
    lib.replace_range(
        start..end,
        r#"{
        use std::io::Write;
        let mut output = std::fs::OpenOptions::new().create(true).append(true)
            .open(std::env::var_os("TAUTO_CASE_SHOWS").expect("case show path")).unwrap();
        writeln!(output, "{name} = {}", value.0).unwrap();
    }"#,
    );
    let bin = match ws.build("case", work, target, false) {
        Ok(b) => b,
        Err(e) => return compilation_failure(case, "build", &e),
    };
    if let Err(e) = case.check_compiled("rust") {
        return Result_::Failed(e);
    }
    if let Some(want) = case
        .build
        .as_deref()
        .and_then(|s| s.strip_prefix("error: "))
    {
        return Result_::Failed(format!("expected build failure {want:?}, but it built"));
    }
    if !case.expects_runtime() {
        return checked(case);
    }
    let show_path = work.join("shows");
    let out_path = work.join("stdout");
    let err_path = work.join("stderr");
    std::fs::write(&show_path, "").unwrap();
    let mut child = match std::process::Command::new(&bin)
        .args(&case.permissions)
        .arg("--")
        .args(&case.args)
        .env("TAUTO_CASE_SHOWS", &show_path)
        .env("TAUTO_REPORT_BUDGET_STEPS", "1")
        .env("TAUTO_REPORT_PROBE_DROPS", "1")
        .stdout(std::fs::File::create(&out_path).unwrap())
        .stderr(std::fs::File::create(&err_path).unwrap())
        .spawn()
    {
        Ok(child) => child,
        Err(e) => return Result_::Failed(e.to_string()),
    };
    let start = std::time::Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                return Result_::Failed(e.to_string());
            }
            Ok(None) => {}
        }
        if start.elapsed() > std::time::Duration::from_secs(30) {
            let _ = child.kill();
            let _ = child.wait();
            return Result_::Failed("runtime exceeded the 30 second safety limit".into());
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    };
    let shows = std::fs::read_to_string(show_path)
        .unwrap()
        .lines()
        .map(str::to_string)
        .collect::<Vec<_>>();
    let stdout = std::fs::read_to_string(out_path).unwrap();
    let stderr = std::fs::read_to_string(err_path).unwrap();
    // The runtime's reports are its last lines; the program's own stderr
    // is the rest.
    let mut steps = None;
    let mut probe_drops = None;
    let stderr: String = stderr
        .split_inclusive('\n')
        .filter(|line| {
            if let Some(n) = line.strip_prefix("tauto-budget-steps: ") {
                steps = n.trim().parse::<u64>().ok();
            } else if let Some(names) = line.strip_prefix("tauto-probe-drops: ") {
                let names = names.trim_end_matches('\n');
                probe_drops = Some(if names.is_empty() {
                    Vec::new()
                } else {
                    names.split(',').map(str::to_string).collect::<Vec<_>>()
                });
            } else {
                return true;
            }
            false
        })
        .collect();
    if let Some(want) = &case.probe_drops {
        if probe_drops.as_ref() != Some(want) {
            return Result_::Failed(format!(
                "probe_drops: expected {want:?}, got {probe_drops:?}"
            ));
        }
    }
    if let Some(want) = case.rust_budget_steps {
        if steps != Some(want) {
            return Result_::Failed(format!("rust_budget_steps: expected {want}, got {steps:?}"));
        }
    }
    if case.backend_known_failure.contains_key("rust") {
        if status.success() {
            return Result_::Failed(
                "declared known failure Rust behavior succeeded; remove the stale limitation"
                    .into(),
            );
        }
        return match case.check_limitation("rust", "runtime", &stderr) {
            Ok(true) => Result_::Todo(format!("declared known failure runtime: {stderr}")),
            Err(e) => Result_::Failed(e),
            Ok(false) => unreachable!(),
        };
    }
    match case.check_output("rust", &shows, &stdout, &stderr, status.code()) {
        Ok(()) => checked(case),
        Err(e) => Result_::Failed(e),
    }
}

/// Builds share one target directory, so one native build lane keeps
/// verification resource-bounded.
pub fn runner() -> impl FnMut(usize, &RustCase) -> String {
    let base: PathBuf = std::env::var_os("CARGO_TARGET_TMPDIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
        .join("tauto-rust-backend");
    let target = base.join("target-0");
    let work = base.join("work-0");
    move |_, case| {
        let _ = std::fs::remove_dir_all(work.join("src"));
        match run_case(case, &work, &target) {
            Result_::Passed => "pass".into(),
            Result_::Skipped => unreachable!("selected cases are not skipped"),
            Result_::Declined(why) => status("declined", &why),
            Result_::Partial(why) => status("partial", &why),
            Result_::Todo(why) => status("todo", &why),
            Result_::Failed(why) => status("fail", &why),
        }
    }
}
