//! `totes/llvm` against `tauto_llvm::emit` (`docs/design/llvm-backend.md`).
//!
//! Every case that shows something is compiled to the package the backend
//! reads. The tote answers each package as NIR text with a module or with
//! what it does not write; the crate answers the same package. The two
//! modules are compared as the tote prints a module, so they differ only
//! where LLVM would read them differently.

use std::path::Path;

use selfhost_harness::{assert_same_dump, root, run_tote_native};

const STEPS: u64 = 2_000_000_000_000;

/// What the crate answers a case: the package as NIR text, and its module or
/// what the crate does not write.
struct Answer {
    name: String,
    nir: String,
    module: Result<String, String>,
}

fn answer(case: &tauto_test_suite::RustCase) -> Option<Answer> {
    let pkg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| case.compile("llvm")));
    let mut pkg = pkg.ok()?.ok()?;
    tauto_nir::mono::specialize(&mut pkg).ok()?;
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    // A package `specialize` did not finish is not the backend's to answer.
    tauto_nir::mono::check(&pkg).ok()?;
    let nir = tauto_nir::text::print(&pkg).ok()?;
    let module = tauto_llvm::emit(&pkg).map_err(|e| e.to_string());
    Some(Answer {
        name: case.name.clone(),
        nir,
        module,
    })
}

/// The answers of a run of the tote, in the order of its arguments: what
/// follows each line `== FILE`.
fn sections(stdout: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for line in stdout.split_inclusive('\n') {
        if line.starts_with("== ") {
            out.push(String::new());
        } else if let Some(last) = out.last_mut() {
            last.push_str(line);
        }
    }
    out
}

fn write(dir: &Path, name: String, text: &str) -> String {
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path.to_string_lossy().into_owned()
}

fn run(mode: &str, paths: Vec<String>) -> Vec<String> {
    let mut args = vec![mode.to_string()];
    let count = paths.len();
    args.extend(paths);
    let out = run_tote_native("llvm", &args, STEPS);
    assert_eq!(out.error, None, "{}", out.stderr);
    let got = sections(&out.stdout);
    assert_eq!(got.len(), count, "`llvm {mode}` answers each file");
    got
}

#[test]
fn llvm_matches_the_crate() {
    tauto_messages::install();
    let cases: Vec<_> = tauto_test_suite::rust_cases(&root().join("cases"))
        .unwrap()
        .into_iter()
        .filter(|c| c.stdout.is_some() && c.run_error.is_none())
        .collect();
    let answers: Vec<Answer> = tauto_test_suite::parallel_map(&cases, |_| (), |_, _, c| answer(c))
        .into_iter()
        .flatten()
        .collect();
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-llvm-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();

    let packages = answers
        .iter()
        .enumerate()
        .map(|(i, a)| write(&dir, format!("{i:05}.nir"), &a.nir))
        .collect();
    let written: Vec<(usize, String)> = answers
        .iter()
        .enumerate()
        .filter_map(|(i, a)| {
            Some((
                i,
                write(&dir, format!("{i:05}.ll"), a.module.as_ref().ok()?),
            ))
        })
        .collect();
    assert!(!written.is_empty(), "the crate writes no case");

    let emitted = run("emit", packages);
    let mut printed = run("print", written.iter().map(|(_, p)| p.clone()).collect()).into_iter();

    let (mut rust, mut tauto) = (String::new(), String::new());
    for (a, emitted) in answers.iter().zip(&emitted) {
        let expected = match &a.module {
            Ok(_) => printed.next().unwrap(),
            Err(refused) => format!("{refused}\n"),
        };
        rust.push_str(&format!("== {}\n{expected}", a.name));
        tauto.push_str(&format!("== {}\n{emitted}", a.name));
    }
    assert_same_dump("llvm", &rust, &tauto);
    same_programs(&dir, &answers, &emitted);
    let _ = std::fs::remove_dir_all(&dir);
}

/// The flags `tauto build --backend llvm` compiles a module with
/// (`crates/tauto-cli/src/llvm.rs`), on the system the tote writes the
/// runtime for.
const CLANG_FLAGS: &[&str] = &[
    "-O2",
    "-g0",
    "-Wno-override-module",
    "-Wl,--build-id=none",
    "-nostdlib",
    "-static",
];

/// The program `clang` makes of `module`, compiled as `main.ll` in `dir` as
/// `tauto build --backend llvm` compiles it; `None` without `clang`.
fn program(dir: &Path, module: &str) -> Option<Vec<u8>> {
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("main.ll"), module).unwrap();
    let built = std::process::Command::new("clang")
        .current_dir(dir)
        .args(CLANG_FLAGS)
        .args(["-o", "main", "main.ll"])
        .output()
        .ok()?;
    assert!(
        built.status.success(),
        "clang: {}",
        String::from_utf8_lossy(&built.stderr)
    );
    let bytes = std::fs::read(dir.join("main")).unwrap();
    let _ = std::fs::remove_dir_all(dir);
    Some(bytes)
}

/// The module the tote writes and the one the crate writes make the same
/// program, byte for byte.
fn same_programs(dir: &Path, answers: &[Answer], emitted: &[String]) {
    if std::process::Command::new("clang")
        .arg("--version")
        .output()
        .is_err()
    {
        eprintln!("clang is not found: the programs are not compared");
        return;
    }
    // The tote writes the runtime for system calls on Linux on x86_64 only.
    if tauto_llvm::Sys::host() != tauto_llvm::Sys::Linux {
        eprintln!("the host is not Linux on x86_64: the programs are not compared");
        return;
    }
    let mut compared = 0;
    for (i, (a, tote)) in answers.iter().zip(emitted).enumerate() {
        let Ok(crate_module) = &a.module else {
            continue;
        };
        let rust = program(&dir.join(format!("rust-{i}")), crate_module).unwrap();
        let tauto = program(&dir.join(format!("tauto-{i}")), tote).unwrap();
        assert!(rust == tauto, "{}: the two programs differ", a.name);
        compared += 1;
    }
    eprintln!("{compared} programs are the same from the crate and the tote");
    assert!(compared > 0, "no program is compared");
}
