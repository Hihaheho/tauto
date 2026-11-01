//! A generated package's target owns its intermediate and final artifacts.
#![cfg(unix)]

use std::path::{Path, PathBuf};
use std::process::Command;
use tauto_rustgen::Workspace;

#[test]
fn inherited_build_directory_cannot_mix_runtime_variants() {
    let root = std::env::temp_dir().join(format!("tauto-build-isolation-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let output = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "build_isolation_child",
            "--ignored",
            "--nocapture",
        ])
        .env("TAUTO_ISOLATION_TEST_ROOT", &root)
        .env("CARGO_BUILD_BUILD_DIR", root.join("inherited-build"))
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&root);
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn build(root: &Path, variant: &str) -> (PathBuf, String) {
    let dir = root.join(variant);
    let target = root.join(format!("target-{variant}"));
    let files = vec![
        ("Cargo.toml".into(), "[package]\nname = \"same-package\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n[dependencies]\nruntime = { path = \"runtime\" }\n".into()),
        ("src/main.rs".into(), "fn main() { println!(\"{}:{}\", runtime::VALUE, env!(\"CARGO_MANIFEST_DIR\")); }\n".into()),
        ("runtime/Cargo.toml".into(), "[package]\nname = \"runtime\"\nversion = \"0.1.0\"\nedition = \"2024\"\n".into()),
        ("runtime/src/lib.rs".into(), format!("pub const VALUE: &str = {variant:?};\n")),
    ];
    let bin = Workspace { files }
        .build("same-package", &dir, &target, false)
        .unwrap();
    (bin, format!("{variant}:{}\n", dir.display()))
}

fn output(bin: &Path) -> String {
    let out = Command::new(bin).output().unwrap();
    assert!(out.status.success());
    String::from_utf8(out.stdout).unwrap()
}

#[test]
#[ignore = "subprocess helper with a private environment"]
fn build_isolation_child() {
    let root = PathBuf::from(std::env::var_os("TAUTO_ISOLATION_TEST_ROOT").unwrap());
    let (first, first_expected) = build(&root, "normal");
    assert_eq!(output(&first), first_expected);
    let (second, second_expected) = build(&root, "instrumented");
    assert_eq!(output(&second), second_expected);
    assert_eq!(output(&first), first_expected);
    assert!(!root.join("inherited-build").exists());
}
