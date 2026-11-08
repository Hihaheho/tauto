//! `tauto run` given neither a file nor `--tote` runs the `run.file` of the
//! nearest `Tauto.eure` (`docs/design/dev.md` 「既定のファイル」).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn project(name: &str, run: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tauto-run-default-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(d.join("app/sub")).unwrap();
    fs::write(
        d.join("Tauto.eure"),
        format!("package {{\n  name = \"demo\"\n  version = \"0.1.0\"\n}}\n{run}"),
    )
    .unwrap();
    fs::write(
        d.join("app/hello.taut"),
        "import std::prelude::Os\n\nprint(\"hello\\n\")\n",
    )
    .unwrap();
    fs::write(
        d.join("app/other.taut"),
        "import std::prelude::Os\n\nprint(\"other\\n\")\n",
    )
    .unwrap();
    d
}

fn tauto(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(dir)
        .env("TAUTO_LANG", "en")
        .args(args)
        .output()
        .unwrap()
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn run_without_a_file_runs_the_manifests_run_file() {
    let d = project("default", "run {\n  file = \"app/hello.taut\"\n}\n");
    for args in [
        &["run"][..],
        &["run", "--backend", "eval"],
        &["run", "--steps", "100000"],
    ] {
        let out = tauto(&d, args);
        assert!(out.status.success(), "{args:?}: {out:?}");
        assert_eq!(stdout(&out).trim(), "hello", "{args:?}");
    }
    // From a directory below the manifest.
    let out = tauto(&d.join("app/sub"), &["run"]);
    assert!(out.status.success(), "{out:?}");
    assert_eq!(stdout(&out).trim(), "hello");
}

#[test]
fn a_file_on_the_command_line_wins() {
    let d = project("explicit", "run {\n  file = \"app/hello.taut\"\n}\n");
    let out = tauto(&d, &["run", "app/other.taut"]);
    assert!(out.status.success(), "{out:?}");
    assert_eq!(stdout(&out).trim(), "other");
}

#[test]
fn without_run_file_a_file_is_still_needed() {
    let d = project("none", "");
    let out = tauto(&d, &["run"]);
    assert!(!out.status.success(), "{out:?}");
}

#[test]
fn an_unknown_run_key_is_an_error() {
    let d = project("unknown", "run {\n  main = \"app/hello.taut\"\n}\n");
    let out = tauto(&d, &["run"]);
    assert_eq!(out.status.code(), Some(2), "{out:?}");
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("unknown run key main"),
        "{out:?}"
    );
}
