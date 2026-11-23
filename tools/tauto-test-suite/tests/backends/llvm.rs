//! The LLVM backend through the self-hosted tote (`totes/llvm`): lower to
//! NIR for `Target::Llvm`, run mono / anf / ownership, print the package as
//! NIR text, ask `totes/llvm emit` for the module, link it with `clang`, run
//! it, and compare. The Rust crate `tauto-llvm` is not used here: it is the
//! reference the tote is compared with elsewhere.
//!
//! The tote writes the Linux-on-x86_64 system-call runtime only. The backends
//! harness skips the LLVM scenario before any case runs when the host is not
//! that target.

use std::{
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant},
};

use tauto_rustgen::Sources;
use tauto_test_suite::{RustCase, coverage::status};

/// Seconds a compiled case may run.
const SECONDS: u64 = 30;

/// Whether this host can link and run what the tote emits.
pub fn host_supported() -> bool {
    cfg!(all(target_os = "linux", target_arch = "x86_64"))
}

/// Flags for `clang` on the tote's Linux system-call modules. `--build-id=none`
/// is GNU ld only; it is never passed on other hosts.
fn clang_flags() -> Vec<&'static str> {
    let mut flags = vec!["-O2", "-g0", "-Wno-override-module", "-nostdlib", "-static"];
    if cfg!(target_os = "linux") {
        flags.push("-Wl,--build-id=none");
    }
    flags
}

fn declared_failure(case: &RustCase, stage: &str, message: &str) -> Option<String> {
    match case.check_limitation("llvm", stage, message) {
        Ok(true) => return Some(status("todo", &format!("declared {stage}: {message}"))),
        Err(e) => return Some(status("fail", &e)),
        Ok(false) => {}
    }
    match case.check_compile_error("llvm", stage, message) {
        Ok(true) => Some(checked(case, "rejection checked")),
        Err(e) => Some(status("fail", &e)),
        Ok(false) => None,
    }
}

fn gaps(case: &RustCase) -> Vec<&'static str> {
    let mut gaps = case.assertion_gaps();
    // The tote has no case-host probe; drop order is not observed here.
    if case.probe_drops.is_some() {
        gaps.push("probe_drops");
    }
    gaps
}

fn checked(case: &RustCase, what: &str) -> String {
    let gaps = gaps(case);
    if gaps.is_empty() {
        "pass".into()
    } else {
        status("partial", &format!("{what}; {}", gaps.join("; ")))
    }
}

/// `totes/llvm` built by the Rust backend, as the vm runner builds `totes/vm`.
fn build_emitter(base: &Path) -> Result<PathBuf, String> {
    if let Some(m) = std::env::var_os("TAUTO_LLVM_TOTE") {
        return Ok(PathBuf::from(m));
    }
    let tote = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../totes/llvm");
    let loaded = tauto::program::load_tote_for_build(&tote)?;
    let source = loaded.source_text();
    let mut manifest = tauto::manifest::load(&tote)?;
    tauto::manifest::add_dependency_rust(&mut manifest, &tote)?;
    let mut package = tauto_nibcheck::lower::compile_loaded_with_observer(
        &loaded,
        false,
        tauto_nir::Target::Rust,
        |_| {},
    )
    .map_err(|e| format!("{e:?}"))?;
    let bindings = tauto_rustgen::Bindings::resolve(&mut package, Some(&manifest), None)?;
    let options = tauto_rustgen::Options::from_manifest(&manifest);
    let ws = tauto_rustgen::workspace(
        "llvm",
        &package,
        &Sources {
            file: "llvm",
            text: &source,
        },
        &bindings,
        &options,
    );
    ws.build("llvm", &base.join("ws"), &base.join("target"), true)
}

fn prepare(case: &RustCase) -> Result<tauto_nir::Package, String> {
    let mut pkg = match case.compile_with_files("llvm") {
        Ok((pkg, _, _)) => pkg,
        Err(error) => {
            let (stage, message) = match error {
                tauto_nibcheck::lower::CompileError::Front(m)
                | tauto_nibcheck::lower::CompileError::Package(m) => ("front", m),
                tauto_nibcheck::lower::CompileError::Build(m) => ("build", m),
                tauto_nibcheck::lower::CompileError::Unsupported(u) => {
                    ("unsupported", u.what.to_string())
                }
            };
            return Err(declared_failure(case, stage, &message).unwrap_or_else(|| {
                // Front/build gaps of the case are counted like niri's "not
                // compiled", not as a suite failure, unless the case declared
                // a precise rejection.
                if stage == "unsupported" {
                    status("fail", &format!("unexpected unsupported: {message}"))
                } else {
                    format!("not compiled: {stage}")
                }
            }));
        }
    };
    if let Err(e) = tauto_nir::mono::specialize(&mut pkg) {
        return Err(declared_failure(case, "unsupported", &e)
            .unwrap_or_else(|| status("fail", &format!("unexpected unsupported: {e}"))));
    }
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    Ok(pkg)
}

/// Ask the self-hosted tote for the module of `pkg`.
fn emit_module(emitter: &Path, work: &Path, name: &str, pkg: &tauto_nir::Package) -> Result<String, String> {
    let nir = tauto_nir::text::print(pkg).map_err(|e| e.to_string())?;
    let nir_path = work.join(format!("{name}.nir"));
    std::fs::write(&nir_path, &nir).map_err(|e| e.to_string())?;
    let out = Command::new(emitter)
        .args(["--allow-read", "--allow-write", "--", "emit"])
        .arg(&nir_path)
        .output()
        .map_err(|e| format!("llvm tote: {e}"))?;
    if !out.status.success() {
        let err = String::from_utf8_lossy(&out.stderr);
        return Err(err.trim().to_string());
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    // Answers follow a line `== FILE`, as `totes/llvm` writes them.
    let mut section = String::new();
    let mut in_section = false;
    for line in stdout.split_inclusive('\n') {
        if line.starts_with("== ") {
            in_section = true;
            section.clear();
            continue;
        }
        if in_section {
            section.push_str(line);
        }
    }
    if section.is_empty() {
        return Err("llvm tote wrote no module".into());
    }
    // A refusal is one line naming what is outside what the backend writes.
    let trimmed = section.trim_end();
    if !trimmed.contains('\n')
        && !trimmed.starts_with(';')
        && !trimmed.starts_with("target ")
        && !trimmed.starts_with("source_filename ")
        && !trimmed.starts_with("define ")
        && !trimmed.starts_with("declare ")
        && !trimmed.starts_with('@')
    {
        return Err(trimmed.to_string());
    }
    Ok(section)
}

fn link(module: &str, work: &Path, name: &str) -> Result<PathBuf, String> {
    let ll = work.join(format!("{name}.ll"));
    let exe = work.join(format!("{name}.out"));
    std::fs::write(&ll, module).map_err(|e| e.to_string())?;
    let built = Command::new("clang")
        .args(clang_flags())
        .arg("-o")
        .arg(&exe)
        .arg(&ll)
        .output()
        .map_err(|e| format!("clang: {e}"))?;
    if !built.status.success() {
        return Err(String::from_utf8_lossy(&built.stderr).trim().to_string());
    }
    Ok(exe)
}

fn run_case(
    case: &RustCase,
    i: usize,
    work: &Path,
    emitter: &Result<PathBuf, String>,
) -> String {
    let pkg = match prepare(case) {
        Ok(pkg) => pkg,
        Err(status) => return status,
    };
    let emitter = match emitter {
        Ok(e) => e,
        Err(e) => return status("fail", &format!("the llvm tote does not build: {e}")),
    };
    let module = match emit_module(emitter, work, &format!("{i}"), &pkg) {
        Ok(m) => m,
        Err(e) => {
            return declared_failure(case, "generate", &e)
                .unwrap_or_else(|| status("fail", &format!("unexpected generate: {e}")));
        }
    };
    let exe = match link(&module, work, &format!("{i}")) {
        Ok(exe) => exe,
        Err(e) => {
            return declared_failure(case, "build", &e)
                .unwrap_or_else(|| status("fail", &format!("unexpected build: {e}")));
        }
    };
    if let Err(e) = case.check_compiled("llvm") {
        let _ = std::fs::remove_file(&exe);
        return status("fail", &e);
    }
    if !case.expects_runtime() {
        let _ = std::fs::remove_file(&exe);
        return checked(case, "compile checked");
    }
    let out_path = work.join(format!("{i}-stdout"));
    let err_path = work.join(format!("{i}-stderr"));
    let mut child = match Command::new(&exe)
        .args(&case.args)
        .stdout(std::fs::File::create(&out_path).unwrap())
        .stderr(std::fs::File::create(&err_path).unwrap())
        .spawn()
    {
        Ok(child) => child,
        Err(e) => {
            let _ = std::fs::remove_file(&exe);
            return status("fail", &e.to_string());
        }
    };
    let begin = Instant::now();
    let exit = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = std::fs::remove_file(&exe);
                return status("fail", &e.to_string());
            }
            Ok(None) => {}
        }
        if begin.elapsed() > Duration::from_secs(SECONDS) {
            let _ = child.kill();
            let _ = child.wait();
            let _ = std::fs::remove_file(&exe);
            return if case.runtime_opt_out("llvm") {
                match case.check_limitation("llvm", "runtime", "runtime safety limit exceeded") {
                    Ok(true) => status("todo", "declared runtime: runtime safety limit exceeded"),
                    Err(e) => status("fail", &e),
                    Ok(false) => unreachable!(),
                }
            } else {
                status("fail", "runtime safety limit exceeded")
            };
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let _ = std::fs::remove_file(&exe);
    let stdout = std::fs::read_to_string(&out_path).unwrap_or_default();
    let stderr = std::fs::read_to_string(&err_path).unwrap_or_default();
    let code = exit.and_then(|s| s.code());
    if case.runtime_opt_out("llvm") {
        if code != Some(0) {
            return match case.check_limitation("llvm", "runtime", &stderr) {
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
    match case.check_output("llvm", &stdout, &stderr, code) {
        Ok(Some(e)) => status("todo", &format!("declared output: {e}")),
        Ok(None) => checked(case, "output checked"),
        Err(e) => status("fail", &e),
    }
}

/// The tote is built once and shared; each worker has its own work directory.
pub fn runner(worker: usize) -> impl FnMut(usize, &RustCase) -> String {
    static EMITTER: std::sync::OnceLock<Result<PathBuf, String>> = std::sync::OnceLock::new();
    let base: PathBuf = std::env::var_os("CARGO_TARGET_TMPDIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
        .join("tauto-llvm-backend");
    let work = base.join(format!("work-{}-{worker}", std::process::id()));
    std::fs::create_dir_all(&work).unwrap();
    let scratch = Scratch(work.clone());
    let clang = Command::new("clang").arg("--version").output().is_ok();
    move |i, case| {
        let _keep = &scratch;
        if !clang {
            return status("fail", "clang is not found");
        }
        let emitter = EMITTER.get_or_init(|| build_emitter(&base.join("machine")));
        run_case(case, i, &work, emitter)
    }
}

struct Scratch(PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
