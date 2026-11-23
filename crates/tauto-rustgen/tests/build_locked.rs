//! Every `cargo build` of a generated crate passes `--locked`, also without a
//! tote's `Cargo.lock`: the build resolves the workspace's own lock first.
//!
//! This checks the arguments Tauto gives the Cargo it runs, which a
//! test-suite case cannot observe (a case sees a program's output, not the
//! build tool's command line).
#![cfg(unix)]

use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::Command;
use tauto_rustgen::Workspace;

#[test]
fn file_builds_pass_locked_to_cargo() {
    let root = std::env::temp_dir().join(format!("tauto-build-locked-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let real = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let trace = root.join("calls");
    let wrapper = root.join("cargo");
    std::fs::write(
        &wrapper,
        format!(
            "#!/bin/sh\necho \"cargo $*\" >> '{}'\nexec '{real}' \"$@\"\n",
            trace.display()
        ),
    )
    .unwrap();
    std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755)).unwrap();
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "build_locked_child", "--ignored", "--nocapture"])
        .env("TAUTO_LOCKED_TEST_ROOT", &root)
        .env("CARGO", &wrapper)
        .output()
        .unwrap();
    let calls = std::fs::read_to_string(&trace).unwrap_or_default();
    let _ = std::fs::remove_dir_all(&root);
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let builds: Vec<_> = calls
        .lines()
        .filter(|l| l.starts_with("cargo build"))
        .collect();
    assert!(!builds.is_empty(), "no cargo build ran:\n{calls}");
    for b in builds {
        assert!(b.split(' ').any(|a| a == "--locked"), "no --locked: {b}");
    }
}

#[test]
#[ignore = "subprocess helper with a private Cargo"]
fn build_locked_child() {
    let root = PathBuf::from(std::env::var_os("TAUTO_LOCKED_TEST_ROOT").unwrap());
    let files = vec![
        ("Cargo.toml".into(), "[package]\nname = \"locked-pkg\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n".into()),
        ("src/main.rs".into(), "fn main() {}\n".into()),
    ];
    let dir = root.join("ws");
    Workspace { files }
        .build("locked-pkg", &dir, &root.join("target"), false)
        .unwrap();
    assert!(dir.join("Cargo.lock").is_file());
}
