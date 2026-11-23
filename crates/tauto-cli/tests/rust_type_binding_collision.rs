//! `rust.types` binds an extern type by the name `Tauto.eure` writes, also
//! when another file of the program declares a type of the same name. The
//! declarations are then told apart by their full names, and the key means
//! the extern type: it is the only one a Rust type can stand for.
//!
//! This is a Rust test, not a case: the case runner has no way to give a
//! program a `rust` section with a bridge crate and read the Rust that is
//! generated for it.

use std::fs;
use std::process::Command;

fn write(root: &std::path::Path, path: &str, text: &str) {
    let file = root.join(path);
    fs::create_dir_all(file.parent().unwrap()).unwrap();
    fs::write(file, text).unwrap();
}

/// A program whose `native.taut` declares the extern type `Device` and
/// whose `plain.taut` declares an ordinary struct of the same name.
fn program(name: &str, extra_plain: &str, manifest_types: &str) -> std::path::PathBuf {
    let root = std::env::temp_dir().join(format!("tauto-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    write(
        &root,
        "Tauto.eure",
        &format!(
            "package {{\n  name = \"example\"\n  version = \"0.1.0\"\n}}\nrust {{\n  bridge = \"bridge\"\n  types {{ {manifest_types} }}\n}}\n"
        ),
    );
    write(
        &root,
        "src/main.taut",
        "import std::builtin::os\nimport \"native.taut\"\nimport \"plain.taut\"\nperform main(() => {\n  let d := acquire()\n  if number() == 1 { perform stdout(\"ok\\n\") } else { () }\n})\n",
    );
    write(
        &root,
        "src/native.taut",
        "pub struct(affine) Device {}\nextern { pub fn acquire(): Device }\n",
    );
    write(
        &root,
        "src/plain.taut",
        &format!("pub(open) struct Device {{ value: u32 }}\npub fn number(): u32 {{ Device {{ value: 1 }}.value }}\n{extra_plain}"),
    );
    write(
        &root,
        "bridge/Cargo.toml",
        "[package]\nname = \"example-bridge\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    );
    write(
        &root,
        "bridge/src/lib.rs",
        "pub struct Device;\npub fn acquire() -> Device { Device }\n",
    );
    root
}

fn emit(root: &std::path::Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["build", "--backend", "rust", "--emit", "rust", "-o"])
        .arg(root.join("out"))
        .arg(root)
        .output()
        .unwrap()
}

fn emitted(root: &std::path::Path) -> String {
    let mut text = String::new();
    let mut stack = vec![root.join("out")];
    while let Some(p) = stack.pop() {
        if p.is_dir() {
            stack.extend(fs::read_dir(&p).unwrap().map(|e| e.unwrap().path()));
        } else if p.extension().is_some_and(|e| e == "rs") {
            text.push_str(&fs::read_to_string(&p).unwrap());
        }
    }
    text
}

#[test]
fn a_bare_key_binds_the_extern_type_when_another_type_has_the_name() {
    let root = program("type-collision", "", "Device = \"example_bridge::Device\"");
    let out = emit(&root);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let rust = emitted(&root);
    assert!(
        rust.contains("= example_bridge::Device;"),
        "{rust}"
    );
    assert!(!rust.contains("struct example__src__native__Device"), "{rust}");
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn a_full_name_key_binds_the_extern_type() {
    let root = program(
        "type-collision-full",
        "",
        "\"example::src::native::Device\" = \"example_bridge::Device\"",
    );
    let out = emit(&root);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(emitted(&root).contains("= example_bridge::Device;"));
    let _ = fs::remove_dir_all(&root);
}

/// Both declarations of the name are in an extern function's signature, so the
/// bare key does not say which it binds.
#[test]
fn a_bare_key_two_extern_types_share_is_ambiguous() {
    let root = program(
        "type-collision-ambiguous",
        "extern { pub fn make(): Device }\n",
        "Device = \"example_bridge::Device\"",
    );
    let out = emit(&root);
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("example::src::native::Device")
            && stderr.contains("example::src::plain::Device"),
        "{stderr}"
    );
    let _ = fs::remove_dir_all(&root);
}
