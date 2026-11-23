//! Every case that shows something, compiled through LLVM and run.
//!
//! Each case ends one way: it passes, the backend does not write it yet
//! (with the reason), or it is wrong. A case is wrong when LLVM does not
//! take the module, when the program shows something else than the case
//! says, or when the address sanitizer finds a value used after it is
//! released, released twice or never released. The test fails on a wrong
//! case; cases the backend does not write yet are only counted.
//!
//! Each case is built three times. With the address sanitizer it is built
//! with every block a block of `malloc` (`Sys::Asan`), where the sanitizer
//! sees them. Then it is built on the C library's entry points to the kernel
//! (`Sys::Libc`) and, on Linux on x86_64, as `tauto build --backend llvm`
//! builds it, on system calls with no library (`Sys::Linux`); each must show
//! the same.
//!
//! The test needs `clang`, and a `cc` that links the address sanitizer.
//! Without `clang` the test says so and passes.

use std::path::{Path, PathBuf};
use std::process::Command;

use tauto_test_suite::RustCase;

/// The seconds a compiled case may run.
const SECONDS: u32 = 20;

fn outcome(dir: &Path, index: usize, case: &RustCase) -> String {
    let expected = case
        .stdout
        .as_deref()
        .expect("a case that writes to stdout");
    // A program built by this backend has the authority of whoever runs it:
    // permission flags belong to the host of `tauto run`, which also puts the
    // case's files where `{dir}` points.
    if !case.permissions.is_empty() || case.args.iter().any(|a| a.contains("{dir}")) {
        return "refused: the case needs the permissions and files of the host".into();
    }
    let pkg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| case.compile("llvm")));
    let mut pkg = match pkg {
        Ok(Ok(p)) => p,
        Ok(Err(_)) => return "not compiled".into(),
        Err(_) => return "not compiled: the compiler panicked".into(),
    };
    if let Err(e) = tauto_nir::mono::specialize(&mut pkg) {
        return format!("refused: mono: {}", first_line(&e));
    }
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    let sys = tauto_llvm::Sys::Asan;
    let ir = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tauto_llvm::emit_on(&pkg, sys)
    })) {
        Ok(Ok(ir)) => ir,
        Ok(Err(e)) => return format!("refused: {}", first_line(&e.0)),
        Err(_) => return "wrong: the backend panicked".into(),
    };
    // Every function is checked by the address sanitizer.
    let ir = ir.replace(") {\n", ") sanitize_address {\n");
    let ll = dir.join(format!("{index}.ll"));
    let exe = dir.join(format!("{index}.out"));
    if std::fs::write(&ll, &ir).is_err() {
        return "wrong: the module is not written".into();
    }
    let obj = dir.join(format!("{index}.o"));
    let built = Command::new("clang")
        .args([
            "-O1",
            "-g0",
            "-fsanitize=address",
            "-Wno-override-module",
            "-c",
            "-o",
        ])
        .arg(&obj)
        .arg(&ll)
        .output();
    let built = match built {
        Ok(b) => b,
        Err(e) => return format!("wrong: clang does not start: {e}"),
    };
    if !built.status.success() {
        return format!(
            "wrong: LLVM does not take the module: {}",
            first_line(&String::from_utf8_lossy(&built.stderr))
        );
    }
    // The system's C compiler links the program with its sanitizer.
    let linked = Command::new("cc")
        .args(["-fsanitize=address", "-o"])
        .arg(&exe)
        .arg(&obj)
        .output();
    let _ = std::fs::remove_file(&obj);
    match linked {
        Ok(l) if l.status.success() => {}
        Ok(l) => {
            return format!(
                "wrong: the program is not linked: {}",
                first_line(&String::from_utf8_lossy(&l.stderr))
            );
        }
        Err(e) => return format!("wrong: cc does not start: {e}"),
    }
    let run = Command::new("sh")
        .arg("-c")
        .arg(format!(
            "ulimit -s 1000000 2>/dev/null; exec timeout {SECONDS} \"$0\" \"$@\""
        ))
        .arg(&exe)
        .args(&case.args)
        .env(
            "ASAN_OPTIONS",
            "detect_leaks=1:detect_stack_use_after_return=0",
        )
        .output();
    let _ = std::fs::remove_file(&exe);
    let run = match run {
        Ok(r) => r,
        Err(e) => return format!("wrong: the program does not start: {e}"),
    };
    let out = String::from_utf8_lossy(&run.stdout);
    let err = String::from_utf8_lossy(&run.stderr);
    let exit = case.exit.unwrap_or(0);
    let sanitized = err.contains("Sanitizer");
    if run.status.code() == Some(exit) && !sanitized {
        if out == expected && case.stderr.as_deref().is_none_or(|e| err == e) {
            for sys in [tauto_llvm::Sys::Linux, tauto_llvm::Sys::Libc] {
                if let Some(wrong) = on_system(dir, index, &pkg, case, sys) {
                    return wrong;
                }
            }
            let _ = std::fs::remove_file(&ll);
            "pass".into()
        } else {
            "wrong: it shows something else".into()
        }
    } else if let Some(e) = case
        .run_error
        .as_ref()
        .filter(|_| run.status.code() == Some(1))
    {
        let said = err.lines().next().unwrap_or("");
        if said.strip_prefix("error: ").is_some_and(|m| e.contains(m)) {
            let _ = std::fs::remove_file(&ll);
            "pass".into()
        } else {
            format!("wrong: it stops with: {}", first_line(said))
        }
    } else {
        let why = err
            .lines()
            .find(|l| l.contains("ERROR") || l.starts_with("error"))
            .unwrap_or_else(|| err.lines().next().unwrap_or("no message"));
        format!("wrong: {:?}: {}", run.status.code(), first_line(why))
    }
}

/// The program as built on `sys`, as `tauto build --backend llvm` builds it:
/// what it shows must be what the case says. `None` when it does, or when
/// this machine has no layer of system calls for `Sys::Linux`.
fn on_system(
    dir: &Path,
    index: usize,
    pkg: &tauto_nir::Package,
    case: &RustCase,
    sys: tauto_llvm::Sys,
) -> Option<String> {
    let expected = case.stdout.as_deref().unwrap_or("");
    if sys == tauto_llvm::Sys::Linux && tauto_llvm::Sys::host() != sys {
        return None;
    }
    let ir = match tauto_llvm::emit_on(pkg, sys) {
        Ok(ir) => ir,
        Err(e) => {
            return Some(format!(
                "wrong: the runtime is not written for {sys:?}: {}",
                first_line(&e.0)
            ));
        }
    };
    let ll = dir.join(format!("{index}.{sys:?}.ll"));
    let exe = dir.join(format!("{index}.{sys:?}.out"));
    if std::fs::write(&ll, &ir).is_err() {
        return Some("wrong: the module is not written".into());
    }
    let built = Command::new("clang")
        .args(["-O2", "-g0", "-Wno-override-module", "-Wl,--build-id=none"])
        .args(sys.link_flags())
        .arg("-o")
        .arg(&exe)
        .arg(&ll)
        .output();
    match built {
        Ok(b) if b.status.success() => {}
        Ok(b) => {
            return Some(format!(
                "wrong: on {sys:?}: {}",
                first_line(&String::from_utf8_lossy(&b.stderr))
            ));
        }
        Err(e) => return Some(format!("wrong: clang does not start: {e}")),
    }
    let run = Command::new("sh")
        .arg("-c")
        .arg(format!(
            "ulimit -s 1000000 2>/dev/null; exec timeout {SECONDS} \"$0\" \"$@\""
        ))
        .arg(&exe)
        .args(&case.args)
        .output();
    let _ = std::fs::remove_file(&exe);
    let run = match run {
        Ok(r) => r,
        Err(e) => {
            return Some(format!("wrong: the program on {sys:?} does not start: {e}"));
        }
    };
    if run.status.code() == Some(case.exit.unwrap_or(0))
        && String::from_utf8_lossy(&run.stdout) == expected
        && case
            .stderr
            .as_deref()
            .is_none_or(|e| String::from_utf8_lossy(&run.stderr) == e)
    {
        let _ = std::fs::remove_file(&ll);
        None
    } else {
        Some(format!(
            "wrong: on {sys:?}: {:?}: {}",
            run.status.code(),
            first_line(&String::from_utf8_lossy(&run.stderr))
        ))
    }
}

fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").chars().take(160).collect()
}

fn scratch() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tauto-llvm-cases-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a directory for the modules");
    dir
}

#[test]
fn every_case_passes_or_is_refused() {
    if Command::new("clang").arg("--version").output().is_err() {
        eprintln!("clang is not found: no case is run");
        return;
    }
    tauto_messages::install();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases");
    let only = std::env::var("LLVM_ONLY").ok();
    let cases: Vec<(usize, RustCase)> = tauto_test_suite::rust_cases(&root)
        .unwrap()
        .into_iter()
        .filter(|c| only.as_ref().is_none_or(|o| c.name.contains(o.as_str())))
        .filter(|c| c.stdout.is_some() && c.run_error.is_none())
        .enumerate()
        .collect();
    let dir = scratch();
    let start = std::time::Instant::now();
    let got: Vec<String> = tauto_test_suite::parallel_map(
        &cases,
        |_| (),
        |_, _, (i, c)| format!("{}\t{}", c.name, outcome(&dir, *i, c)),
    );
    let mut counts = std::collections::BTreeMap::<&str, usize>::new();
    for line in &got {
        let status = line.split('\t').nth(1).unwrap_or("");
        *counts
            .entry(status.split(':').next().unwrap_or(status))
            .or_default() += 1;
    }
    eprintln!("{} cases in {:?}: {counts:?}", got.len(), start.elapsed());
    if std::env::var_os("LLVM_LIST").is_some() {
        for line in &got {
            eprintln!("CASE {line}");
        }
    }
    let wrong: Vec<&str> = got
        .iter()
        .filter(|l| l.split('\t').nth(1).is_some_and(|s| s.starts_with("wrong")))
        .map(String::as_str)
        .collect();
    assert!(
        wrong.is_empty(),
        "{} cases are wrong (their modules are kept in {}):\n{}",
        wrong.len(),
        dir.display(),
        wrong.join("\n")
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        got.is_empty() || counts.get("pass").copied().unwrap_or(0) > 0,
        "no case passes: every case is refused or not compiled"
    );
}
