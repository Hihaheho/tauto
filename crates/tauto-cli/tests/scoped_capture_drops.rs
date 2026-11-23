//! Declaration-time owned captures retain their lexical value and drop at
//! the end of their defining scope, just like an owned lambda capture.

use std::{fs, path::Path, process::Command};

fn write(root: &Path, path: &str, source: &str) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

#[test]
fn named_and_lambda_captures_keep_their_value_and_drop_scope() {
    for (case, expected) in [
        ("owned-capture-drop", "drop captured\n1\n"),
        ("owned-lambda-drop", "drop lambda\n1\n"),
        (
            "generic-owned-capture-drop",
            "drop captured\n1\n",
        ),
        (
            "generic-owned-capture-shadow",
            "1\ndrop original\ndrop shadow\n1\n",
        ),
        (
            "owned-capture-argument-abort",
            "drop captured\n1\n1\n",
        ),
        (
            "owned-lambda-argument-abort",
            "drop captured\n1\n1\n",
        ),
        (
            "owned-capture-shadow",
            "1\ndrop original\ndrop shadow\n1\n",
        ),
        (
            "owned-lambda-shadow",
            "1\ndrop original\ndrop shadow\n1\n",
        ),
    ] {
        let root = std::env::temp_dir().join(format!(
            "tauto-scoped-capture-{}-{case}",
            std::process::id()
        ));
        write(
            &root,
            "Tauto.eure",
            r#"package { name = "scoped-capture" }
rust {
  bridge = "bridge"
  types { Probe = "scoped_capture_bridge::Probe" }
  extern { "Probe::new" = "scoped_capture_bridge::probe" }
}
"#,
        );
        write(
            &root,
            "src/main.taut",
            &case_inputs::fixture("scoped-capture-fixtures.eure", case),
        );
        write(
            &root,
            "bridge/Cargo.toml",
            r#"[package]
name = "scoped-capture-bridge"
version = "0.1.0"
edition = "2024"
"#,
        );
        write(
            &root,
            "bridge/src/lib.rs",
            r#"pub struct Probe(String);
impl Drop for Probe {
    fn drop(&mut self) { println!("drop {}", self.0); }
}
pub fn probe(name: &str) -> Probe { Probe(name.to_string()) }
"#,
        );
        let output = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(["run", "--backend", "rust"])
            .arg(&root)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{case}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            expected,
            "{case}"
        );
        fs::remove_dir_all(root).unwrap();
    }
}

#[test]
fn javascript_capture_resources_drop_at_scope_exit_and_abort() {
    let root = std::env::temp_dir().join(format!("tauto-js-scoped-capture-{}", std::process::id()));
    write(
        &root,
        "Tauto.eure",
        r#"package { name = "scoped-capture" }
rust { bridge = "bridge" types { Probe = "scoped_capture_bridge::Probe" } }
"#,
    );
    write(
        &root,
        "bridge/Cargo.toml",
        r#"[package]
name = "scoped-capture-bridge"
version = "0.1.0"
edition = "2024"
"#,
    );
    write(
        &root,
        "bridge/src/lib.rs",
        r#"use std::sync::atomic::{AtomicI64, Ordering};
static DROPS: AtomicI64 = AtomicI64::new(0);
pub struct Probe(i64);
impl Drop for Probe {
    fn drop(&mut self) { DROPS.fetch_add(self.0, Ordering::SeqCst); }
}
pub fn make(n: i64) -> Probe { Probe(n) }
pub fn dropped() -> i64 { DROPS.load(Ordering::SeqCst) }
"#,
    );
    write(
        &root,
        "src/main.taut",
        &r#"import std::builtin::os { stdout, stdout_flush }
struct(affine) Probe {}
extern { fn make(n: i64): Probe
  fn dropped(): i64 }
effect stop(): Never resume 0
fn named_unused(): Unit ! {stdout, stdout_flush} {
  let captured := make(10)
  { fn unused_named(): Probe { captured }; #() }
  show(&dropped())
}
fn lambda_unused(): Unit ! {stdout, stdout_flush} {
  let captured := make(20)
  { let unused: affine () -> Probe := () => captured; #() }
  show(&dropped())
}
fn named_shadow(): Unit ! {stdout, stdout_flush} {
  let captured := make(40)
  { fn consume_named(): Probe { captured }
    let captured := make(80)
    let result := consume_named()
  }
  show(&dropped())
}
fn lambda_shadow(): Unit ! {stdout, stdout_flush} {
  let captured := make(160)
  { let consume: affine () -> Probe := () => captured
    let captured := make(320)
    let result := consume()
  }
  show(&dropped())
}
fn generic_unused(): Unit ! {stdout, stdout_flush} {
  let captured := make(640)
  { fn unused_generic<A: Shared>(marker: A): Probe { captured }; #() }
  show(&dropped())
}
fn generic_shadow(): Unit ! {stdout, stdout_flush} {
  let captured := make(1280)
  { fn consume_generic<A: Shared>(marker: A): Probe { captured }
    let captured := make(2560)
    let result := consume_generic(7)
  }
  show(&dropped())
}
fn named_abort(): Unit ! {stdout, stdout_flush} {
  let captured := make(5120)
  { fn consume_abort(marker: i64): Probe { captured }
    handle { let result := consume_abort(perform stop()); #() } with { stop() => #() }
    show(&dropped())
  }
}
fn lambda_abort(): Unit ! {stdout, stdout_flush} {
  let captured := make(10240)
  { let consume: affine (i64) -> Probe := (marker) => captured
    handle { let result := consume(perform stop()); #() } with { stop() => #() }
    show(&dropped())
  }
}
perform main(() => {
named_unused()
lambda_unused()
named_shadow()
lambda_shadow()
generic_unused()
generic_shadow()
named_abort()
lambda_abort()
show(&dropped())
})
"#
        .to_string(),
    );
    let output = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["build", "--backend", "javascript", "--target", "node", "-o"])
        .arg(root.join("out"))
        .arg(&root)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = Command::new("node")
        .arg(root.join("out/main.mjs"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "10\n30\n150\n630\n1270\n5110\n10230\n20470\n20470\n"
    );
    fs::remove_dir_all(root).unwrap();
}

/// The inputs these tests read, kept as files under `tests/fixtures`.
mod case_inputs {
    fn read(path: &str) -> String {
        let path = format!("{}/tests/fixtures/{path}", env!("CARGO_MANIFEST_DIR"));
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"))
    }
    pub fn fixture(file: &str, name: &str) -> String {
        read(&format!("{}/{}.taut", file.trim_end_matches(".eure"), name))
    }
}
