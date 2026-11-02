//! `Tauto.eure`.

use std::path::Path;

use tauto::manifest::{merge_bindings, parse};

const MANIFEST: &str = r#"
package {
  name = "files-demo"
  version = "0.1.0"
}

rust {
  bridge = "bridge"
  bindings = ["bind/regex.eure"]
  types {
    File = "std::fs::File"
  }
  extern {
    file_open = "std::fs::File::open"
    file_read_to_buf = "files_demo_bridge::read_to_buf"
  }
  dependencies {
    regex = "1.11.1"
  }
}
"#;

#[test]
fn reads_the_rust_section() {
    tauto_messages::install();
    let m = parse(MANIFEST, Path::new("Tauto.eure")).unwrap();
    assert_eq!(m.package.name, "files-demo");
    assert!(m.package.additional_sources.is_empty());
    assert_eq!(m.package.source_paths(), vec!["src"]);
    assert_eq!(m.rust.bridge.as_deref(), Some("bridge"));
    assert_eq!(m.rust.bindings, vec!["bind/regex.eure"]);
    assert_eq!(m.rust.types["File"].value, "std::fs::File");
    assert_eq!(m.rust.externs["file_open"].value, "std::fs::File::open");
    assert_eq!(m.rust.externs["file_open"].line, 14);
    assert_eq!(m.rust.dependencies["regex"].value, "\"1.11.1\"");
}

#[test]
fn an_unknown_key_is_an_error() {
    tauto_messages::install();
    let e = parse(
        "rust {\n  extrn {\n    f = \"a::b\"\n  }\n}\n",
        Path::new("Tauto.eure"),
    )
    .unwrap_err();
    assert!(e.contains("unknown key extrn"), "{e}");
    let e = parse(
        "package {\n  name = \"x\"\n  color = \"red\"\n}\n",
        Path::new("Tauto.eure"),
    )
    .unwrap_err();
    assert!(e.contains("unknown key color"), "{e}");
    let e = parse("rusty {\n}\n", Path::new("Tauto.eure")).unwrap_err();
    assert!(e.contains("unknown key rusty"), "{e}");
}

#[test]
fn the_same_extern_in_two_bindings_is_an_error() {
    tauto_messages::install();
    let mut m = parse(MANIFEST, Path::new("Tauto.eure")).unwrap();
    merge_bindings(
        &mut m.rust,
        "extern {\n  regex_new = \"regex::Regex::new\"\n}\n",
        Path::new("bind/a.eure"),
    )
    .unwrap();
    let e = merge_bindings(
        &mut m.rust,
        "extern {\n  regex_new = \"regex::Regex::new\"\n}\n",
        Path::new("bind/b.eure"),
    )
    .unwrap_err();
    assert_eq!(
        e,
        "error: regex_new is bound twice: bind/a.eure and bind/b.eure"
    );
}

#[test]
fn tauto_eure_wins_over_a_bindings_file() {
    tauto_messages::install();
    let mut m = parse(MANIFEST, Path::new("Tauto.eure")).unwrap();
    merge_bindings(
        &mut m.rust,
        "extern {\n  file_open = \"other::open\"\n}\n",
        Path::new("bind/a.eure"),
    )
    .unwrap();
    assert_eq!(m.rust.externs["file_open"].value, "std::fs::File::open");
}

#[test]
fn nonresuming_contracts_are_absent_by_default() {
    tauto_messages::install();
    let m = parse(MANIFEST, Path::new("Tauto.eure")).unwrap();
    assert!(m.rust.nonresuming_externs.is_empty());
    assert!(m.rust.nonresuming_entries.is_empty());
}

#[test]
fn nonresuming_contracts_keep_explicit_names_values_and_assertion_places() {
    tauto_messages::install();
    let text = r#"rust {
  extern {
    native_read = "bridge::read"
  }
  nonresuming {
    extern {
      native_read = "closed-host-v1"
    }
    entries {
      run_with_nonresuming_contract = "run"
    }
  }
}
"#;
    let file = Path::new("logic/Tauto.eure");
    let m = parse(text, file).unwrap();
    let host = &m.rust.nonresuming_externs["native_read"];
    assert_eq!(host.value, "closed-host-v1");
    assert_eq!(host.file, file);
    assert_eq!(host.line, 7);
    let entry = &m.rust.nonresuming_entries["run_with_nonresuming_contract"];
    assert_eq!(entry.value, "run");
    assert_eq!(entry.file, file);
    assert_eq!(entry.line, 10);
    assert_eq!(m.rust.externs["native_read"].value, "bridge::read");
}

#[test]
fn nonresuming_contract_keys_and_entry_values_are_strict() {
    tauto_messages::install();
    let unknown = parse(
        "rust { nonresuming { unsafe_all = true } }",
        Path::new("Tauto.eure"),
    )
    .unwrap_err();
    assert!(
        unknown.contains("unknown rust.nonresuming key unsafe_all"),
        "{unknown}"
    );
    let callback_key = parse(
        "rust { nonresuming { callbacks { run_with_nonresuming_contract = \"run:read\" } } }",
        Path::new("Tauto.eure"),
    )
    .unwrap_err();
    assert!(
        callback_key.contains("unknown rust.nonresuming key callbacks"),
        "{callback_key}"
    );
    let wrong_type = parse(
        "rust { nonresuming { extern { native_read = true } } }",
        Path::new("Tauto.eure"),
    )
    .unwrap_err();
    assert!(wrong_type.contains("expected a text"), "{wrong_type}");
    let wrong_entry_type = parse(
        "rust { nonresuming { entries { run_with_nonresuming_contract = true } } }",
        Path::new("Tauto.eure"),
    )
    .unwrap_err();
    assert!(
        wrong_entry_type.contains("expected a text"),
        "{wrong_entry_type}"
    );
}

#[test]
fn generated_bindings_cannot_add_nonresuming_trust() {
    tauto_messages::install();
    let mut m = parse(MANIFEST, Path::new("Tauto.eure")).unwrap();
    let before = m.rust.clone();
    let error = merge_bindings(
        &mut m.rust,
        "nonresuming { extern { file_open = \"closed-host-v1\" } }",
        Path::new("bind/generated.eure"),
    )
    .unwrap_err();
    assert!(error.contains("unknown key nonresuming"), "{error}");
    assert_eq!(m.rust, before);
    let entry_error = merge_bindings(
        &mut m.rust,
        "nonresuming { entries { run_with_nonresuming_contract = \"run\" } }",
        Path::new("bind/generated.eure"),
    )
    .unwrap_err();
    assert!(
        entry_error.contains("unknown key nonresuming"),
        "{entry_error}"
    );
    assert_eq!(m.rust, before);
}

#[test]
fn duplicate_nonresuming_facade_keys_are_errors() {
    tauto_messages::install();
    let error = parse(
        "rust { nonresuming { entries { trusted = \"first\" trusted = \"second\" } } }",
        Path::new("Tauto.eure"),
    )
    .unwrap_err();
    assert!(error.contains("trusted"), "{error}");
}

#[test]
fn reads_commands_and_what_the_project_grants_them() {
    tauto_messages::install();
    let m = parse(
        r#"
package {
  name = "app"
  version = "0.1.0"
}
commands {
  bk {
    main = "cmd/bk.taut"
    about = "Runs the app"
  }
}
trust {
  extern = ["regex"]
  commands {
    bk {
      tote = "app"
      read = ["src"]
      net = true
    }
  }
}
"#,
        Path::new("Tauto.eure"),
    )
    .unwrap();
    assert_eq!(m.commands["bk"].main, "cmd/bk.taut");
    assert_eq!(m.commands["bk"].about, "Runs the app");
    assert_eq!(m.trust_extern, vec!["regex"]);
    let grant = &m.trust_commands["bk"];
    assert_eq!(grant.tote, "app");
    assert_eq!(
        grant.allow,
        vec![
            ("read".to_string(), Some(vec!["src".to_string()])),
            ("net".to_string(), None),
        ]
    );
}

#[test]
fn a_command_is_written_strictly() {
    tauto_messages::install();
    for (text, expected) in [
        (
            "commands { Bk { main = \"cmd/bk.taut\"\n about = \"a\" } }",
            "Bk is not a command name",
        ),
        (
            "commands { bk { main = \"../bk.taut\"\n about = \"a\" } }",
            "main is a .taut or .tauto file inside the tote",
        ),
        (
            "commands { bk { main = \"cmd/bk.txt\"\n about = \"a\" } }",
            "main is a .taut or .tauto file inside the tote",
        ),
        (
            "commands { bk { main = \"cmd/bk.taut\" } }",
            "about is one line",
        ),
        (
            "commands { bk { main = \"cmd/bk.taut\"\n about = \"a\"\n allow = true } }",
            "unknown key allow",
        ),
        (
            "trust { commands { bk { read = [\"src\"] } } }",
            "tote names the tote whose command this is",
        ),
        (
            "trust { commands { bk { tote = \"a\"\n all = true } } }",
            "all is not granted to a command",
        ),
        (
            "trust { commands { bk { tote = \"a\"\n read = [] } } }",
            "an empty list grants nothing",
        ),
        (
            "trust { commands { bk { tote = \"a\"\n clipboard = [\"x\"] } } }",
            "clipboard is `true`",
        ),
    ] {
        let e = parse(text, Path::new("Tauto.eure")).unwrap_err();
        assert!(e.contains(expected), "{text}: {e}");
    }
}
