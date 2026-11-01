//! `tauto run` and `tauto build` end with a nonzero status whenever they fail,
//! on every backend, so that a script or CI notices; a failure never ends in 0.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn dir(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tauto-exit-status-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    d
}

/// The status of `tauto ARGS…` run in `dir`, and what it printed on the
/// standard error.
fn tauto(dir: &PathBuf, args: &[&str]) -> (Option<i32>, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(dir)
        .env("TAUTO_LANG", "en")
        .args(args)
        .output()
        .unwrap();
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// Programs that fail before they run: a syntax error, a type error.
const BROKEN: [(&str, &str); 2] = [
    ("syntax", "print(1 + )\n"),
    ("type", "print(1 + \"a\")\n"),
];

#[test]
fn a_program_that_does_not_check_fails_on_every_backend() {
    let d = dir("broken");
    for (name, source) in BROKEN {
        let file = format!("{name}.taut");
        fs::write(d.join(&file), source).unwrap();
        for backend in ["vm", "eval", "rust"] {
            let (code, err) = tauto(&d, &["run", "--backend", backend, &file]);
            assert!(
                code.is_some_and(|c| c != 0),
                "run --backend {backend} {name}: {code:?}\n{err}"
            );
            assert!(!err.is_empty(), "run --backend {backend} {name} said nothing");
        }
        // The default backend is the machine written in Tauto.
        let (code, _) = tauto(&d, &["run", &file]);
        assert!(code.is_some_and(|c| c != 0), "run {name}: {code:?}");
        let (code, _) = tauto(&d, &["build", "--backend", "rust", &file]);
        assert!(code.is_some_and(|c| c != 0), "build {name}: {code:?}");
    }
}

#[test]
fn a_missing_file_fails_on_every_backend() {
    let d = dir("missing");
    for backend in ["vm", "eval", "rust"] {
        let (code, err) = tauto(&d, &["run", "--backend", backend, "nothing.taut"]);
        assert!(
            code.is_some_and(|c| c != 0),
            "run --backend {backend}: {code:?}\n{err}"
        );
    }
    let (code, _) = tauto(&d, &["build", "--backend", "rust", "nothing.taut"]);
    assert!(code.is_some_and(|c| c != 0), "build: {code:?}");
}

#[test]
fn the_status_a_program_exits_with_is_the_status_of_run() {
    let d = dir("exit");
    fs::write(d.join("exit.taut"), "perform exit(3)\n").unwrap();
    let (code, err) = tauto(&d, &["run", "--backend", "eval", "exit.taut"]);
    assert_eq!(code, Some(3), "{err}");
}
