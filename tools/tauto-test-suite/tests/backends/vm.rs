//! The bytecode machine written in Tauto (`totes/vm`): compile the case to
//! its bytecode, run it on the machine the Rust backend built, and compare
//! what it shows, writes and ends with. `TAUTO_VM_MACHINE` names a build of
//! the machine to use instead of building it.

use std::path::{Path, PathBuf};

use tauto_rt::permissions::{Grant, Permissions};
use tauto_rustgen::Sources;
use tauto_test_suite::{RustCase, coverage::status};

/// The machine: `totes/vm` built by the Rust backend.
fn build_machine(base: &Path) -> Result<PathBuf, String> {
    if let Some(m) = std::env::var_os("TAUTO_VM_MACHINE") {
        return Ok(PathBuf::from(m));
    }
    let tote = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../totes/vm");
    let loaded = tauto::program::load_tote_for_build(&tote)?;
    let source = loaded.source_text();
    let mut manifest = tauto::manifest::load(&tote)?;
    tauto::manifest::add_dependency_rust(&mut manifest, &tote)?;
    let mut package =
        tauto_nibcheck::lower::compile_loaded_with_observer(&loaded, false, tauto_nir::Target::Rust, |_| {})
            .map_err(|e| format!("{e:?}"))?;
    let bindings = tauto_rustgen::Bindings::resolve(&mut package, Some(&manifest), None)?;
    let options = tauto_rustgen::Options::from_manifest(&manifest);
    let mut ws = tauto_rustgen::workspace(
        "vm",
        &package,
        &Sources {
            file: "vm",
            text: &source,
        },
        &bindings,
        &options,
    );
    // The machine runs another program on its thread, so its own entries are
    // answered apart from the guest's (`tauto-cli-totes` runs it so too).
    // Without that the guest's top-level `perform main` is a second `main`.
    let hosted = "tauto_rt::run_main(vm::run)";
    let mut patched = false;
    for (_, text) in ws.files.iter_mut() {
        if text.contains(hosted) {
            *text = text.replace(hosted, "tauto_rt::run_main(|| tauto_rt::entry::hosting(vm::run))");
            patched = true;
        }
    }
    if !patched {
        return Err("the generated main of the machine does not call `tauto_rt::run_main(vm::run)`".into());
    }
    ws.build("vm", &base.join("ws"), &base.join("target"), true)
}

/// A rejection that a case declares, or `None` when nothing declares it.
fn declared_failure(case: &RustCase, stage: &str, message: &str) -> Option<String> {
    match case.check_limitation("vm", stage, message) {
        Ok(true) => return Some(status("todo", &format!("declared {stage}: {message}"))),
        Err(e) => return Some(status("fail", &e)),
        Ok(false) => {}
    }
    match case.check_compile_error("vm", stage, message) {
        Ok(true) => Some(checked(case, "rejection checked")),
        Err(e) => Some(status("fail", &e)),
        Ok(false) => None,
    }
}

fn checked(case: &RustCase, what: &str) -> String {
    let gaps = case.assertion_gaps();
    if gaps.is_empty() {
        "pass".into()
    } else {
        status("partial", &format!("{what}; {}", gaps.join("; ")))
    }
}

fn unsupported(case: &RustCase, message: &str) -> String {
    if let Some(s) = declared_failure(case, "unsupported", message) {
        return s;
    }
    status("fail", &format!("unexpected unsupported: {message}"))
}

fn run_case(case: &RustCase, machine: &Result<PathBuf, String>, work: &Path) -> String {
    let (pkg, dir, _files) = match case.compile_with_files("vm") {
        Ok(p) => p,
        Err(error) => {
            let (stage, message) = match error {
                tauto_nibcheck::lower::CompileError::Front(m)
                | tauto_nibcheck::lower::CompileError::Package(m) => ("front", m),
                tauto_nibcheck::lower::CompileError::Build(m) => ("build", m),
                tauto_nibcheck::lower::CompileError::Unsupported(u) => {
                    ("unsupported", u.what.to_string())
                }
            };
            if stage == "unsupported" {
                return unsupported(case, &message);
            }
            return declared_failure(case, stage, &message)
                .unwrap_or_else(|| status("fail", &format!("unexpected {stage}: {message}")));
        }
    };
    let bytecode = match tauto_vm::wire::write(&pkg) {
        Ok(b) => b,
        // A refusal the backend decided on, not a gap.
        Err(what) if tauto_vm::wire::refused(&what) => {
            return declared_failure(case, "generate", &what)
                .unwrap_or_else(|| status("fail", &format!("unexpected generate: {what}")));
        }
        Err(what) => return unsupported(case, &what),
    };
    // The machine compiles the bytecode when it runs it, so a declared
    // `unsupported` failure shows only then.
    let unsupported_at_run = case
        .opt_outs
        .get("vm")
        .is_some_and(|w| w.starts_with("unsupported: "));
    if !unsupported_at_run && let Err(e) = case.check_compiled("vm") {
        return status("fail", &e);
    }
    if !case.expects_runtime() {
        return checked(case, "compile checked");
    }
    // `{dir}` is the directory that holds the case's files.
    let placed = |s: &String| match &dir {
        Some(d) => s.replace("{dir}", d),
        None => s.clone(),
    };
    let mut permissions = Permissions::default();
    for flag in case.permissions.iter().map(placed) {
        if let Err(e) = permissions.parse_flag(&flag) {
            return status("fail", &format!("permission flag {flag}: {e}"));
        }
    }
    let missing: Vec<String> = permissions
        .missing(pkg.permissions.iter().map(String::as_str))
        .into_iter()
        .map(String::from)
        .collect();
    // A case's `budget` is the session's step limit, as `--steps` says it.
    let steps = (permissions.div != Grant::All)
        .then_some(case.budget.unwrap_or(tauto_rt::DEFAULT_STEP_LIMIT));
    let (shows, stdout, stderr, exit) = if missing.is_empty() {
        let machine = match machine {
            Ok(m) => m,
            Err(e) => return status("fail", &format!("the machine does not build: {e}")),
        };
        let flags: Vec<String> = case.permissions.iter().map(placed).collect();
        let args: Vec<String> = case.args.iter().map(placed).collect();
        match run_machine(machine, work, &bytecode, &flags, steps, &args) {
            Ok(r) => r,
            Err(e) => {
                return declared_failure(case, "runtime", &e)
                    .unwrap_or_else(|| status("fail", &e));
            }
        }
    } else {
        let missing: Vec<&str> = missing.iter().map(String::as_str).collect();
        let stderr = format!("{}\n", tauto_rt::permissions::missing_message(&missing));
        (Vec::new(), String::new(), stderr, 2)
    };
    // What the machine's compiler cannot compile yet.
    if exit == 3
        && let Some(what) = stderr.strip_prefix("not supported by the vm backend: ")
    {
        return unsupported(case, what.trim_end());
    }
    if case.runtime_opt_out("vm") {
        if exit != 0 {
            return match case.check_limitation("vm", "runtime", &stderr) {
                Ok(true) => status("todo", &format!("declared runtime: {stderr}")),
                Err(e) => status("fail", &e),
                Ok(false) => unreachable!(),
            };
        }
        return status(
            "fail",
            "known failure succeeded; expected precise runtime failure",
        );
    }
    // The machine reports the host values it dropped with what it shows.
    let mut shows = shows;
    let probe_drops = shows
        .iter()
        .position(|l| l.starts_with("tauto-probe-drops: "))
        .map(|i| {
            let line = shows.remove(i);
            let names = &line["tauto-probe-drops: ".len()..];
            if names.is_empty() {
                Vec::new()
            } else {
                names.split(',').map(str::to_string).collect::<Vec<_>>()
            }
        });
    if let Some(want) = &case.probe_drops
        && probe_drops.as_ref().unwrap_or(&Vec::new()) != want
    {
        return status(
            "fail",
            &format!("probe_drops: expected {want:?}, got {probe_drops:?}"),
        );
    }
    match case.check_output("vm", &stdout, &stderr, Some(exit)) {
        Ok(Some(e)) => status("todo", &format!("declared output: {e}")),
        Ok(None) => checked(case, "output checked"),
        Err(e) => status("fail", &e),
    }
}

/// Runs the program on the machine: what it shows goes to a file of its
/// own, apart from what it writes.
fn run_machine(
    machine: &Path,
    work: &Path,
    program: &str,
    flags: &[String],
    steps: Option<u64>,
    args: &[String],
) -> Result<(Vec<String>, String, String, i32), String> {
    std::fs::create_dir_all(work).map_err(|e| e.to_string())?;
    let file = work.join("program.cps");
    let shows = work.join("shows");
    let (out_path, err_path) = (work.join("stdout"), work.join("stderr"));
    std::fs::write(&file, program).map_err(|e| e.to_string())?;
    let _ = std::fs::remove_file(&shows);
    let mut child = std::process::Command::new(machine)
        .args(tauto_vm::wire::machine_args(
            flags,
            &file,
            steps,
            Some(&shows),
            None,
            None,
            args,
        ))
        .stdout(std::fs::File::create(&out_path).map_err(|e| e.to_string())?)
        .stderr(std::fs::File::create(&err_path).map_err(|e| e.to_string())?)
        .spawn()
        .map_err(|e| e.to_string())?;
    let start = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            break status;
        }
        // The machine is slower than the other backends: a run to the host's
        // step limit takes about half a minute.
        if start.elapsed() > std::time::Duration::from_secs(120) {
            let _ = child.kill();
            let _ = child.wait();
            return Err("runtime exceeded the 120 second safety limit".into());
        }
        std::thread::sleep(std::time::Duration::from_millis(5));
    };
    let shows = std::fs::read_to_string(shows)
        .unwrap_or_default()
        .lines()
        .map(str::to_string)
        .collect();
    let stdout = std::fs::read_to_string(out_path).map_err(|e| e.to_string())?;
    let stderr = std::fs::read_to_string(err_path).map_err(|e| e.to_string())?;
    Ok((shows, stdout, stderr, status.code().unwrap_or(1)))
}

/// The machine is built once and shared by every worker (the first to need it
/// builds it, the others wait); each worker runs it in a work directory of its
/// own.
pub fn runner(worker: usize) -> impl FnMut(usize, &RustCase) -> String {
    static MACHINE: std::sync::OnceLock<Result<PathBuf, String>> = std::sync::OnceLock::new();
    let base: PathBuf = std::env::var_os("CARGO_TARGET_TMPDIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
        .join("tauto-vm-backend");
    move |_, case| {
        let machine = MACHINE.get_or_init(|| build_machine(&base.join("machine")));
        run_case(case, machine, &base.join(format!("work-{worker}")))
    }
}
