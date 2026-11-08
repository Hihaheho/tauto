//! A file that imports `Macro` is checked as strictly as any other file: a type error in one of its
//! plain functions is reported by `tauto check FILE` and by `tauto check --tote`.
use std::{fs, path::PathBuf, process::Command};

struct Fixture(PathBuf);
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn fixture(name: &str) -> Fixture {
    let root = std::env::temp_dir().join(format!("tauto-{name}-{}", std::process::id()));
    let fixture = Fixture(root.clone());
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(
        root.join("Tauto.eure"),
        "package {\n  name = \"app\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    fs::write(root.join("src/main.taut"), "fn main() { }\n").unwrap();
    fs::write(
        root.join("src/macro.taut"),
        "import std::prelude::Macro\n\
         pub macro fn gen(e: SynExpr): List(SynStmt) ! {macro_error, Div} { Nil }\n\
         fn bad(): Nat { true }\n",
    )
    .unwrap();
    fixture
}

fn run(fixture: &Fixture, args: &[&str]) -> (bool, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(args)
        .current_dir(&fixture.0)
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&output.stdout).to_string()
        + &String::from_utf8_lossy(&output.stderr);
    (output.status.success(), text)
}

#[test]
fn check_file_reports_an_error_in_a_file_importing_macro() {
    let f = fixture("macro-strict-file");
    let (ok, text) = run(&f, &["check", "src/macro.taut"]);
    assert!(!ok, "{text}");
    assert!(text.contains("bad"), "{text}");
}

#[test]
fn check_tote_reports_an_error_in_a_file_importing_macro() {
    let f = fixture("macro-strict-tote");
    let (ok, text) = run(&f, &["check", "--tote"]);
    assert!(!ok, "{text}");
    assert!(text.contains("bad"), "{text}");
}
