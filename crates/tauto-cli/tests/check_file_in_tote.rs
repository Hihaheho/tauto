//! `tauto check FILE` for a file of a tote reports the errors in the file's own functions even when
//! the tote as a whole does not load because a macro the file defines is used, and its function
//! does not check.
use std::{fs, path::PathBuf, process::Command};

struct Fixture(PathBuf);
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn a_macro_helper_that_does_not_check_is_reported_in_its_file() {
    let root =
        std::env::temp_dir().join(format!("tauto-check-file-in-tote-{}", std::process::id()));
    let fixture = Fixture(root.clone());
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir_all(root.join("examples")).unwrap();
    fs::write(
        root.join("Tauto.eure"),
        "package {\n  name = \"app\"\n  version = \"0.1.0\"\n  additional-sources = [\"examples\"]\n}\n",
    )
    .unwrap();
    fs::write(
        root.join("src/macro.taut"),
        "import std::prelude::Macro\n\
         fn names(ps: List(SynIdent × SynExpr)): List(SynIdent) {\n  \
           match ps {\n    Nil => Nil\n    Cons(p, rest) => Cons(p.third, names(rest))\n  }\n}\n\
         pub macro fn gen(e: SynExpr, s: SynStmt): List(SynStmt) ! {macro_error, Div} {\n  \
           let n := names(Nil)\n  Cons(s, Nil)\n}\n",
    )
    .unwrap();
    fs::write(root.join("src/main.taut"), "fn main() { }\n").unwrap();
    fs::write(
        root.join("examples/use.taut"),
        "import \"../src/macro.taut\"\n@gen!(0) => fn Foo\nfn foo(): Nat { 0 }\n",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["check", "src/macro.taut"])
        .current_dir(&fixture.0)
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&output.stdout).to_string()
        + &String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{text}");
    assert!(text.contains("has no field `third`"), "{text}");
}
