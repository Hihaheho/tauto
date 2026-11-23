//! `tauto build --backend llvm` gives a program that shows what the program
//! shows, and the same source gives the same bytes wherever it is built and
//! whatever the file is called. Without `clang` the test says so and passes.

use std::fs;
use std::path::Path;
use std::process::Command;

const SOURCE: &str =
    "struct P { a: i64, b: i64 }\nlet p := P { a: 4, b: 2 }\nshow(&(p.a * 10 + p.b))\n";

fn build(dir: &Path, name: &str) -> Vec<u8> {
    fs::create_dir_all(dir).unwrap();
    fs::write(dir.join(name), SOURCE).unwrap();
    let built = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(dir)
        .args(["build", "--backend", "llvm", "-o", "out", name])
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let run = Command::new(dir.join("out")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&run.stdout), "42\n");
    fs::read(dir.join("out")).unwrap()
}

#[test]
fn llvm_build_is_reproducible() {
    if Command::new("clang").arg("--version").output().is_err() {
        eprintln!("clang is not found: the test is not run");
        return;
    }
    let root = std::env::temp_dir().join(format!("tauto-llvm-build-{}", std::process::id()));
    let a = build(&root.join("a"), "main.taut");
    let b = build(&root.join("b/deeper"), "other.taut");
    fs::remove_dir_all(&root).unwrap();
    assert!(a == b, "the two builds differ");
}
