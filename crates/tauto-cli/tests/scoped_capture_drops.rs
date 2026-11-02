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
        ("owned-capture-drop", "drop captured\nafter_inner = 1\n"),
        ("owned-lambda-drop", "drop lambda\nafter_inner = 1\n"),
        (
            "generic-owned-capture-drop",
            "drop captured\nafter_inner = 1\n",
        ),
        (
            "generic-owned-capture-shadow",
            "after_call = 1\ndrop original\ndrop shadow\nafter_inner = 1\n",
        ),
        (
            "owned-capture-argument-abort",
            "drop captured\nafter_call = 1\nafter_inner = 1\n",
        ),
        (
            "owned-lambda-argument-abort",
            "drop captured\nafter_call = 1\nafter_inner = 1\n",
        ),
        (
            "owned-capture-shadow",
            "after_call = 1\ndrop original\ndrop shadow\nafter_inner = 1\n",
        ),
        (
            "owned-lambda-shadow",
            "after_call = 1\ndrop original\ndrop shadow\nafter_inner = 1\n",
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
  extern { "Probe.new" = "scoped_capture_bridge::probe" }
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
        &r#"affine struct Probe {}
extern { fn make(n: i64): Probe
  fn dropped(): i64 }
effect stop(): Never resume 0
fn named_unused(): Unit {
  let captured := make(10)
  { fn unused_named(): Probe { captured }; #() }
  perform show("named_unused", dropped())
}
fn lambda_unused(): Unit {
  let captured := make(20)
  { let unused: affine () -> Probe := () => captured; #() }
  perform show("lambda_unused", dropped())
}
fn named_shadow(): Unit {
  let captured := make(40)
  { fn consume_named(): Probe { captured }
    let captured := make(80)
    let result := consume_named()
  }
  perform show("named_shadow", dropped())
}
fn lambda_shadow(): Unit {
  let captured := make(160)
  { let consume: affine () -> Probe := () => captured
    let captured := make(320)
    let result := consume()
  }
  perform show("lambda_shadow", dropped())
}
fn generic_unused(): Unit {
  let captured := make(640)
  { fn unused_generic<A: Shared>(marker: A): Probe { captured }; #() }
  perform show("generic_unused", dropped())
}
fn generic_shadow(): Unit {
  let captured := make(1280)
  { fn consume_generic<A: Shared>(marker: A): Probe { captured }
    let captured := make(2560)
    let result := consume_generic(7)
  }
  perform show("generic_shadow", dropped())
}
fn named_abort(): Unit {
  let captured := make(5120)
  { fn consume_abort(marker: i64): Probe { captured }
    handle { let result := consume_abort(perform stop()); #() } with { stop() => #() }
    perform show("named_abort", dropped())
  }
}
fn lambda_abort(): Unit {
  let captured := make(10240)
  { let consume: affine (i64) -> Probe := (marker) => captured
    handle { let result := consume(perform stop()); #() } with { stop() => #() }
    perform show("lambda_abort", dropped())
  }
}
named_unused()
lambda_unused()
named_shadow()
lambda_shadow()
generic_unused()
generic_shadow()
named_abort()
lambda_abort()
perform show("finished", dropped())
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
        "named_unused = 10\nlambda_unused = 30\nnamed_shadow = 150\nlambda_shadow = 630\ngeneric_unused = 1270\ngeneric_shadow = 5110\nnamed_abort = 10230\nlambda_abort = 20470\nfinished = 20470\n"
    );
    fs::remove_dir_all(root).unwrap();
}

/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn fixture_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
            ("scoped-capture-fixtures.eure", "generic-owned-capture-drop") => {
                r#"affine struct Probe {}
module Probe {
  extern { fn new(&name: Text): Probe }
}
fn outer(): Unit {
  let captured := Probe::new("captured")
  {
    fn unused<A: Shared>(marker: A): Probe { captured }
    #()
  }
  perform show("after_inner", 1)
}
outer()
"#
            }
            ("scoped-capture-fixtures.eure", "owned-lambda-argument-abort") => {
                r#"affine struct Probe {}
module Probe { extern { fn new(&name: Text): Probe } }
effect stop(): Never resume 0
fn outer(): Unit {
  let captured := Probe::new("captured")
  {
    let consume: affine (i64) -> Probe := (marker) => captured
    handle { let result := consume(perform stop()); #() } with { stop() => #() }
    perform show("after_call", 1)
  }
  perform show("after_inner", 1)
}
outer()
"#
            }
            ("scoped-capture-fixtures.eure", "owned-capture-drop") => {
                r#"affine struct Probe {}
module Probe {
  extern { fn new(&name: Text): Probe }
}
fn outer(): Unit {
  let captured := Probe::new("captured")
  {
    fn unused(): Probe { captured }
    #()
  }
  perform show("after_inner", 1)
}
outer()
"#
            }
            ("scoped-capture-fixtures.eure", "generic-owned-capture-shadow") => {
                r#"affine struct Probe {}
module Probe { extern { fn new(&name: Text): Probe } }
fn outer(): Unit {
  let captured := Probe::new("original")
  {
    fn consume<A: Shared>(marker: A): Probe { captured }
    let captured := Probe::new("shadow")
    let result := consume(7)
    perform show("after_call", 1)
  }
  perform show("after_inner", 1)
}
outer()
"#
            }
            ("scoped-capture-fixtures.eure", "owned-lambda-shadow") => {
                r#"affine struct Probe {}
module Probe { extern { fn new(&name: Text): Probe } }
fn outer(): Unit {
  let captured := Probe::new("original")
  {
    let consume: affine () -> Probe := () => captured
    let captured := Probe::new("shadow")
    let result := consume()
    perform show("after_call", 1)
  }
  perform show("after_inner", 1)
}
outer()
"#
            }
            ("scoped-capture-fixtures.eure", "owned-capture-argument-abort") => {
                r#"affine struct Probe {}
module Probe { extern { fn new(&name: Text): Probe } }
effect stop(): Never resume 0
fn outer(): Unit {
  let captured := Probe::new("captured")
  {
    fn consume(marker: i64): Probe { captured }
    handle { let result := consume(perform stop()); #() } with { stop() => #() }
    perform show("after_call", 1)
  }
  perform show("after_inner", 1)
}
outer()
"#
            }
            ("scoped-capture-fixtures.eure", "owned-capture-shadow") => {
                r#"affine struct Probe {}
module Probe { extern { fn new(&name: Text): Probe } }
fn outer(): Unit {
  let captured := Probe::new("original")
  {
    fn consume(): Probe { captured }
    let captured := Probe::new("shadow")
    let result := consume()
    perform show("after_call", 1)
  }
  perform show("after_inner", 1)
}
outer()
"#
            }
            ("scoped-capture-fixtures.eure", "owned-lambda-drop") => {
                r#"affine struct Probe {}
module Probe {
  extern { fn new(&name: Text): Probe }
}
fn outer(): Unit {
  let captured := Probe::new("lambda")
  {
    let unused: affine () -> Probe := () => captured
    #()
  }
  perform show("after_inner", 1)
}
outer()
"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn fixture(file: &str, name: &str) -> String {
        fixture_static(file, name).to_string()
    }
}
