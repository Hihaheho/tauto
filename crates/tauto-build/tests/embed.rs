//! A crate that depends on `tauto-embed` runs its tote on the machine and
//! gets the same answers as from the Rust backend; on the machine, a changed
//! tote is compiled again by `reload()`.

mod support;

use std::path::{Path, PathBuf};
use support::{Fixture, cargo_with, scratch, write};

fn crates_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_path_buf()
}

const SOURCE: &str = r#"import std::prelude::Affine
struct Point { x: i64, y: i64 }
enum Shape { Dot(Point), Line(Point, Point), Empty }
fn add_one(n: i64): i64 { n + 1 }
fn shift(p: Point, d: i64): Point { Point { x: p.x + d, y: p.y + d } }
fn width(s: Shape): i64 {
  match s {
    Dot(p) => 0,
    Line(a, b) => b.x - a.x,
    Empty => 0 - 1
  }
}
fn greet(name: Text): Text { name }
fn wrap(xs: Vec(u64)): Vec(u64) { xs }
fn pick(o: Option(u64)): u64 { match o { Some(v) => v, None => 0 } }
fn check(n: i64): Result(i64, Text) { if n > 0 { Ok(n) } else { Err("negative") } }
"#;

fn host(name: &str) -> Fixture {
    let dir = scratch(name);
    let c = crates_dir();
    let root = c.parent().unwrap();
    for f in ["Cargo.lock", ".cargo/config.toml", "rust-toolchain.toml"] {
        write(&dir, f, &std::fs::read_to_string(root.join(f)).unwrap());
    }
    write(
        &dir,
        "Cargo.toml",
        &format!(
            "[package]\nname = \"host-{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
             [dependencies]\ntauto-rt = {{ path = {:?} }}\ntauto-embed = {{ path = {:?} }}\n\n\
             [build-dependencies]\ntauto-build = {{ path = {:?} }}\n\n[workspace]\n",
            c.join("tauto-rt"),
            c.join("tauto-embed"),
            c.join("tauto-build"),
        ),
    );
    write(
        &dir,
        "build.rs",
        "fn main() {\n    tauto_build::compile(\"logic/Tauto.eure\").unwrap();\n}\n",
    );
    write(
        &dir,
        "logic/Tauto.eure",
        "package {\n  name = \"logic\"\n  version = \"0.1.0\"\n}\n",
    );
    write(&dir, "logic/src/main.taut", SOURCE);
    write(
        &dir,
        "src/lib.rs",
        r#"pub mod logic {
    include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs"));
}

#[cfg(test)]
mod tests {
use super::logic::*;

#[test]
fn answers() {
    assert_eq!(add_one(41), 42);
    let p = shift(Point { x: 1, y: 2 }, 3);
    assert_eq!((p.x, p.y), (4, 5));
    assert_eq!(width(Shape::Line(Point { x: 1, y: 0 }, Point { x: 5, y: 0 })), 4);
    assert_eq!(width(Shape::Empty), -1);
    assert_eq!(greet(tauto_rt::Text::from("vm")).to_string(), "vm");
    assert_eq!(wrap(vec![7, 8]), vec![7, 8]);
    assert_eq!(pick(Some(7)), 7);
    assert_eq!(pick(None), 0);
    assert_eq!(check(8).map_err(|e| e.to_string()), Ok(8));
    assert_eq!(check(-3).map_err(|e| e.to_string()), Err("negative".to_string()));
    println!("backend={}", env!("HOST_BACKEND"));
}

/// The tote's source, beside this crate.
fn source() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("logic/src/main.taut")
}

#[test]
fn reloads() {
    let original = std::fs::read_to_string(source()).unwrap();
    assert_eq!(add_one(1), 2);
    assert_eq!(reload(), Ok(false));
    let changed = original.replace("n + 1", "n + 100");
    write_newer(&changed);
    let reloaded = reload();
    if env!("HOST_BACKEND") == "vm" {
        assert_eq!(reloaded, Ok(true));
        assert_eq!(add_one(1), 101);
        // A changed signature needs a rebuild: the running code stays.
        write_newer(&changed.replace("fn add_one(n: i64): i64", "fn add_one(n: i64, m: i64): i64"));
        let err = reload().unwrap_err();
        assert!(err.contains("rebuild"), "{err}");
        assert_eq!(add_one(1), 101);
        // A type error keeps the running code too.
        write_newer(&changed.replace("n + 100", "n + true"));
        assert!(reload().is_err());
        assert_eq!(add_one(1), 101);
    } else {
        assert_eq!(reloaded, Ok(false));
        assert_eq!(add_one(1), 2);
    }
    write_newer(&original);
}

/// Writes the source with a modification time after the last one.
fn write_newer(text: &str) {
    let before = std::fs::metadata(source()).unwrap().modified().unwrap();
    std::fs::write(source(), text).unwrap();
    let f = std::fs::File::options().write(true).open(source()).unwrap();
    f.set_modified(before + std::time::Duration::from_secs(1)).unwrap();
}
}
"#,
    );
    dir
}

/// The tests that build a fixture set its backend in this process's
/// environment, so they take turns.
static ENV: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn test_with(dir: &Fixture, backend: &str) -> String {
    let args = ["test", "--quiet", "--lib"];
    cargo_with(dir, &args, |_, out| {
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(out.status.success(), "TAUTO_BACKEND={backend}:\n{text}");
        text
    })
}

#[test]
fn the_machine_and_the_rust_backend_answer_alike() {
    tauto_messages::install();
    let _turn = ENV.lock().unwrap_or_else(|e| e.into_inner());
    for backend in ["vm", "rust"] {
        let dir = host(&format!("embed-{backend}"));
        // The fixture's own build reads the backend from the environment.
        unsafe {
            std::env::set_var("TAUTO_BACKEND", backend);
            std::env::set_var("HOST_BACKEND", backend);
            // Both tests of the fixture write its source.
            std::env::set_var("RUST_TEST_THREADS", "1");
            std::env::set_var("RUST_TEST_NOCAPTURE", "1");
        }
        let text = test_with(&dir, backend);
        assert!(text.contains(&format!("backend={backend}")), "{text}");
    }
}

#[test]
fn the_machine_facade_is_written_for_the_tote() {
    tauto_messages::install();
    let dir = std::env::temp_dir().join(format!("tauto-embed-facade-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Tauto.eure"),
        "package {\n  name = \"logic\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    std::fs::write(dir.join("src/main.taut"), SOURCE).unwrap();
    let out = tauto_build::generate_for(&dir.join("Tauto.eure"), None, tauto_build::Backend::Vm);
    std::fs::remove_dir_all(&dir).unwrap();
    let (_, text, warnings) = out.unwrap();
    assert!(text.contains("static TOTE"), "{warnings:?}");
    // The build compiled the program: the facade holds its bytes.
    let at = text.find("static TOTE").unwrap();
    assert!(
        text[at..].contains("TAUTOVM2"),
        "{warnings:?} {}",
        &text[at..(at + 300).min(text.len())]
    );
    assert!(warnings.is_empty(), "{warnings:?}");
}

const EXTERN_SOURCE: &str = r#"extern {
  type Counter
  fn counter_new(start: i64): Counter
  fn counter_get(&c: Counter): i64
  fn upper(&t: Text): Text
}
fn shouted(&t: Text): Text { upper(&t) }
fn counted(n: i64): i64 {
  let c := counter_new(n)
  counter_get(&c)
}
"#;

/// A tote with extern functions and an extern type, bound in a bridge crate.
fn extern_host(name: &str) -> Fixture {
    let dir = host(name);
    let manifest = dir.read("Cargo.toml").replace(
        "[build-dependencies]",
        "logic-bridge = { path = \"logic/bridge\" }\n\n[build-dependencies]",
    );
    write(&dir, "Cargo.toml", &manifest);
    write(
        &dir,
        "logic/Tauto.eure",
        "package {\n  name = \"logic\"\n  version = \"0.1.0\"\n}\n\nrust {\n  bridge = \"bridge\"\n  types {\n    Counter = \"logic_bridge::Counter\"\n  }\n  extern {\n    counter_new = \"logic_bridge::Counter::new\"\n    counter_get = \"logic_bridge::counter_get\"\n    upper = \"logic_bridge::upper\"\n  }\n}\n",
    );
    write(&dir, "logic/src/main.taut", EXTERN_SOURCE);
    write(
        &dir,
        "logic/bridge/Cargo.toml",
        "[package]\nname = \"logic-bridge\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[dependencies]\n",
    );
    write(
        &dir,
        "logic/bridge/src/lib.rs",
        "pub struct Counter(i64);\nimpl Counter {\n    pub fn new(start: i64) -> Counter {\n        Counter(start * 2)\n    }\n}\npub fn counter_get(c: &Counter) -> i64 {\n    c.0\n}\npub fn upper(t: &str) -> String {\n    t.to_uppercase()\n}\n",
    );
    write(
        &dir,
        "src/lib.rs",
        r#"pub mod logic {
    include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs"));
}

#[cfg(test)]
mod tests {
    use super::logic::*;

    #[test]
    fn calls_the_bridge() {
        assert_eq!(shouted(&tauto_rt::Text::from("hi")).to_string(), "HI");
        assert_eq!(counted(21), 42);
        println!("backend={}", env!("HOST_BACKEND"));
    }
}
"#,
    );
    dir
}

#[test]
fn extern_functions_answer_alike_on_the_machine() {
    tauto_messages::install();
    let _turn = ENV.lock().unwrap_or_else(|e| e.into_inner());
    for backend in ["vm", "rust"] {
        let dir = extern_host(&format!("embed-extern-{backend}"));
        unsafe {
            std::env::set_var("TAUTO_BACKEND", backend);
            std::env::set_var("HOST_BACKEND", backend);
            std::env::set_var("RUST_TEST_THREADS", "1");
            std::env::set_var("RUST_TEST_NOCAPTURE", "1");
        }
        let text = test_with(&dir, backend);
        assert!(text.contains(&format!("backend={backend}")), "{text}");
    }
}

#[test]
fn the_machine_facade_binds_the_externs() {
    tauto_messages::install();
    let dir = std::env::temp_dir().join(format!("tauto-embed-externs-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("src")).unwrap();
    let fixture = extern_host("embed-extern-facade");
    std::fs::write(dir.join("Tauto.eure"), fixture.read("logic/Tauto.eure")).unwrap();
    std::fs::write(dir.join("src/main.taut"), EXTERN_SOURCE).unwrap();
    let out = tauto_build::generate_for(&dir.join("Tauto.eure"), None, tauto_build::Backend::Vm);
    std::fs::remove_dir_all(&dir).unwrap();
    let (_, text, warnings) = out.unwrap();
    assert!(warnings.is_empty(), "{warnings:?}");
    assert!(text.contains("fn tauto_externs"), "{text}");
}
