//! A top-level statement of a dependency's file outside `src` (a `perform test(...)` in its
//! `tests/`) calls a function with a `where` class like any other call: the call gets the
//! dictionary, instead of failing with "a function of 3 values is given 2".
use std::{fs, path::PathBuf, process::Command};

struct Fixture(PathBuf);
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn a_dependency_s_top_level_call_of_a_constrained_function_gets_its_dictionary() {
    let root = std::env::temp_dir().join(format!("tauto-dep-top-level-{}", std::process::id()));
    let fixture = Fixture(root.clone());
    fs::create_dir_all(root.join("lib/src")).unwrap();
    fs::create_dir_all(root.join("lib/tests")).unwrap();
    fs::create_dir_all(root.join("app/src")).unwrap();
    fs::write(
        root.join("lib/Tauto.eure"),
        "package {\n  name = \"lib\"\n  version = \"0.1.0\"\n  additional-sources = [\"tests\"]\n}\n",
    )
    .unwrap();
    fs::write(
        root.join("lib/src/lib.taut"),
        "import std::base\nimport std::data\nimport std::builtin::ord\n\n\
         pub fn same<K: Shared>(a: K, b: K): Bool where Ord(K) {\n  Nat::eq(0, 0)\n}\n",
    )
    .unwrap();
    fs::write(
        root.join("lib/tests/lib.taut"),
        "import std::base\nimport std::data\nimport std::builtin::ord\nimport \"../src/lib.taut\"\n\n\
         perform test(\"same\", () => expect(same(1, 2), \"same\"))\n",
    )
    .unwrap();
    fs::write(
        root.join("app/Tauto.eure"),
        "package {\n  name = \"app\"\n  version = \"0.1.0\"\n}\n\n\
         dependencies {\n  lib { path = \"../lib\" }\n}\n",
    )
    .unwrap();
    fs::write(root.join("app/src/main.taut"), "fn main(): Unit { () }\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["check"])
        .current_dir(root.join("app"))
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&output.stdout).to_string()
        + &String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{text}");
    assert!(!text.contains("values is given"), "{text}");
    drop(fixture);
}
