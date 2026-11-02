//! A dependency tote's `rust` section counts in the project's build: its
//! `extern` bindings, its bridge crate, and its `rust.dependencies`, whose
//! paths are the dependency tote's.

use std::fs;
use std::process::Command;

fn write(root: &std::path::Path, path: &str, text: &str) {
    let file = root.join(path);
    fs::create_dir_all(file.parent().unwrap()).unwrap();
    fs::write(file, text).unwrap();
}

fn cargo(name: &str, deps: &str) -> String {
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[dependencies]\n{deps}"
    )
}

#[test]
fn a_dependency_binds_its_own_externs() {
    let root = std::env::temp_dir().join(format!("tauto-dependency-rust-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    write(
        &root,
        "lib/Tauto.eure",
        r#"package {
  name = "lib"
  version = "0.1.0"
}

rust {
  bridge = "bridge"
  extern {
    twice = "doubling::twice"
  }
  dependencies {
    doubling {
      path = "doubling"
    }
  }
}
"#,
    );
    write(
        &root,
        "lib/src/lib.taut",
        "extern {\n  fn twice(n: i64): i64\n  fn thrice(n: i64): i64\n}\n\npub fn six(n: i64): i64 {\n  twice(n) + thrice(n)\n}\n",
    );
    write(&root, "lib/doubling/Cargo.toml", &cargo("doubling", ""));
    write(
        &root,
        "lib/doubling/src/lib.rs",
        "pub fn twice(n: i64) -> i64 {\n    n * 20\n}\n",
    );
    write(
        &root,
        "lib/bridge/Cargo.toml",
        &cargo("lib-bridge", "three = { path = \"../three\" }\n"),
    );
    write(
        &root,
        "lib/bridge/src/lib.rs",
        "pub fn thrice(n: i64) -> i64 {\n    n * three::three()\n}\n",
    );
    write(&root, "lib/three/Cargo.toml", &cargo("three", ""));
    write(
        &root,
        "lib/three/src/lib.rs",
        "pub fn three() -> i64 {\n    3\n}\n",
    );
    write(
        &root,
        "app/Tauto.eure",
        r#"package {
  name = "app"
  version = "0.1.0"
}

dependencies {
  lib {
    path = "../lib"
  }
}

trust {
  extern = ["lib"]
}
"#,
    );
    write(
        &root,
        "app/src/main.taut",
        "import lib::lib\n\nperform show(\"six\", six(1))\n",
    );
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["run", "--backend", "rust", "--approve-trust"])
        .arg(root.join("app"))
        .env("TAUTO_HOME", root.join("home"))
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "six = 23");
    let _ = fs::remove_dir_all(&root);
}

/// An extern type (`extern { type T }`) a dependency does not bind in
/// `rust.types` is its bridge crate's type of the same name, as its unbound
/// externs are the bridge's functions.
#[test]
fn a_dependency_bridge_gives_its_extern_types() {
    let root = std::env::temp_dir().join(format!(
        "tauto-dependency-bridge-types-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&root);
    write(
        &root,
        "lib/Tauto.eure",
        r#"package {
  name = "lib"
  version = "0.1.0"
}

rust {
  bridge = "bridge"
}
"#,
    );
    write(
        &root,
        "lib/src/lib.taut",
        "extern {\n  affine type Tally\n  fn tally_new(n: i64): Tally\n  fn tally_get(t: Tally): i64\n}\n\npub fn tally(n: i64): i64 {\n  tally_get(tally_new(n))\n}\n",
    );
    write(&root, "lib/bridge/Cargo.toml", &cargo("lib-bridge", ""));
    write(
        &root,
        "lib/bridge/src/lib.rs",
        "pub struct Tally(i64);\n\npub fn tally_new(n: i64) -> Tally {\n    Tally(n * 7)\n}\n\npub fn tally_get(t: Tally) -> i64 {\n    t.0\n}\n",
    );
    write(
        &root,
        "app/Tauto.eure",
        r#"package {
  name = "app"
  version = "0.1.0"
}

dependencies {
  lib {
    path = "../lib"
  }
}

trust {
  extern = ["lib"]
}
"#,
    );
    write(
        &root,
        "app/src/main.taut",
        "import lib::lib\n\nperform show(\"tally\", tally(6))\n",
    );
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["run", "--backend", "rust", "--approve-trust"])
        .arg(root.join("app"))
        .env("TAUTO_HOME", root.join("home"))
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "tally = 42");
    let _ = fs::remove_dir_all(&root);
}
