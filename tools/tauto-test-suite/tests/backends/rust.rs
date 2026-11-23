//! The Rust backend: generate a crate, build it with Cargo, run it, and
//! compare. A case the generator cannot write fails unless the case declares
//! the failure.

use std::path::{Path, PathBuf};

use tauto_nibcheck::lower::CompileError;
use tauto_rustgen::Sources;
use tauto_test_suite::{RustCase, coverage::status};

enum Result_ {
    Passed,
    /// Not a program the front end accepts (a case about an error).
    Skipped,
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
            Result_::Failed(format!("{stage}: {message}"))
        }
    }
}

fn run_case(case: &RustCase, work: &Path, target: &Path) -> Result_ {
    if !case.selects_backend("rust") {
        return Result_::Skipped;
    }
    let source = match case.compilation_source() {
        Ok(source) => source,
        Err(message) => return compilation_failure(case, "front", &message),
    };
    let (mut package, files_dir, _files) = match case.compile_with_files("rust") {
        Ok(p) => p,
        Err(CompileError::Unsupported(u)) => {
            return compilation_failure(case, "unsupported", &u.what.to_string());
        }
        Err(CompileError::Build(m)) => return compilation_failure(case, "build", &m),
        Err(CompileError::Front(m) | CompileError::Package(m)) => {
            return compilation_failure(case, "front", &m)
        }
    };
    let manifest = match case
        .tote
        .as_ref()
        .map(|p| tauto::manifest::load(p))
        .transpose()
    {
        Ok(m) => m,
        Err(m) => return compilation_failure(case, "build", &m.to_string()),
    };
    // The dependencies' bindings and bridge crates, as `tauto build` adds them.
    let mut manifest = manifest;
    if let (Some(m), Some(tote)) = (&mut manifest, &case.tote)
        && let Err(e) = tauto::manifest::add_dependency_rust(m, tote)
    {
        return compilation_failure(case, "build", &e.to_string());
    }
    // The case host's probe, as every runner gives it.
    if !package.externs.is_empty() {
        let m = manifest.get_or_insert_with(Default::default);
        for (map, name, rust) in [
            (&mut m.rust.types, "Probe", "tauto_rt::probe::Probe"),
            (&mut m.rust.externs, "Probe::new", "tauto_rt::probe::probe"),
        ] {
            map.entry(name.into())
                .or_insert_with(|| tauto::manifest::Entry {
                    value: rust.into(),
                    file: "case host".into(),
                    line: 0,
                });
        }
    }
    // A tote's own bridge crate, which names an extern the manifest does not bind.
    let bridge = manifest.as_ref().and_then(|m| {
        m.rust
            .bridge
            .as_ref()
            .map(|_| tauto_rustgen::bridge_ident(&m.package.name))
    });
    let bindings = match tauto_rustgen::Bindings::resolve(
        &mut package,
        manifest.as_ref(),
        bridge.as_deref(),
    ) {
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
    let report_path = work.join("report");
    let _ = std::fs::remove_file(&report_path);
    let tests_path = work.join("tests-report");
    let _ = std::fs::remove_file(&tests_path);
    std::fs::write(&show_path, "").unwrap();
    // `{dir}` is the directory that holds the case's files.
    let placed = |s: &String| match &files_dir {
        Some(d) => s.replace("{dir}", d),
        None => s.clone(),
    };
    let mut command = std::process::Command::new(&bin);
    // The cases' messages are the English ones, whatever the machine's locale.
    command.env("TAUTO_LANG", "en");
    // A case's `budget` is the session's step limit, as `TAUTO_STEP_LIMIT` says it.
    if let Some(n) = case.budget {
        command.env("TAUTO_STEP_LIMIT", n.to_string());
    }
    if let Some(mb) = case.rust_stack_mb {
        command.env("TAUTO_STACK_MB", mb.to_string());
    }
    // A case that names its tests runs the bodies of the `test` entries, not
    // `main`: the process is told so as `tauto test` tells a built program.
    if case.tests.is_some() {
        command
            .env("TAUTO_ENTRY", "test")
            .env("TAUTO_TEST_REPORT", &tests_path);
    }
    let mut child = match command
        .args(case.permissions.iter().map(placed))
        .arg("--")
        .args(case.args.iter().map(placed))
        .env("TAUTO_CASE_SHOWS", &show_path)
        .env("TAUTO_REPORT", &report_path)
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
    // The runtime's reports are in their own file, so the program's stderr
    // is compared as it is.
    let report = std::fs::read_to_string(&report_path).unwrap_or_default();
    let mut steps = None;
    let mut probe_drops = None;
    for line in report.lines() {
        if let Some(n) = line.strip_prefix("tauto-budget-steps: ") {
            steps = n.trim().parse::<u64>().ok();
        } else if let Some(names) = line.strip_prefix("tauto-probe-drops: ") {
            probe_drops = Some(if names.is_empty() {
                Vec::new()
            } else {
                names.split(',').map(str::to_string).collect::<Vec<_>>()
            });
        }
    }
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
    if let Some(want) = &case.tests {
        let report = tauto_rt::entry::read(&std::fs::read_to_string(&tests_path).unwrap_or_default());
        if let Some(e) = &report.error {
            return Result_::Failed(format!("tests: {e}"));
        }
        let failed: Vec<String> = report
            .tests
            .iter()
            .filter_map(|(n, o)| match o {
                tauto_rt::entry::Outcome::Passed | tauto_rt::entry::Outcome::Retried(_) => None,
                o => Some(format!("{n}: {o:?}")),
            })
            .collect();
        if !failed.is_empty() {
            return Result_::Failed(format!("tests failed: {failed:?}"));
        }
        let names: Vec<String> = report.tests.iter().map(|(n, _)| n.clone()).collect();
        if &names != want {
            return Result_::Failed(format!("tests: expected {want:?}, got {names:?}"));
        }
    }
    if case.runtime_opt_out("rust") {
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
    match case.check_output("rust", &stdout, &stderr, status.code()) {
        Ok(Some(e)) => Result_::Todo(format!("declared output: {e}")),
        Ok(None) => checked(case),
        Err(e) => Result_::Failed(e),
    }
}

/// Each worker is one native build lane with its own work and target
/// directories: rustc's incremental cache and Cargo's lock make a directory
/// usable by one build at a time. The runtime library is kept once in the
/// build cache and linked into each lane.
pub fn runner(worker: usize) -> impl FnMut(usize, &RustCase) -> String {
    let base: PathBuf = std::env::var_os("CARGO_TARGET_TMPDIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
        .join("tauto-rust-backend");
    let target = base.join(format!("target-{worker}"));
    let work = base.join(format!("work-{worker}"));
    move |_, case| {
        let _ = std::fs::remove_dir_all(work.join("src"));
        match run_case(case, &work, &target) {
            Result_::Passed => "pass".into(),
            Result_::Skipped => unreachable!("selected cases are not skipped"),
            Result_::Partial(why) => status("partial", &why),
            Result_::Todo(why) => status("todo", &why),
            Result_::Failed(why) => status("fail", &why),
        }
    }
}
