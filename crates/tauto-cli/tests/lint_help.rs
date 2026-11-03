//! `tauto lint` over directories and several files, and `tauto COMMAND --help`.

use std::process::Command;

fn tauto(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(args)
        .output()
        .unwrap()
}

#[test]
fn lint_reads_the_taut_files_under_a_directory() {
    let dir = std::env::temp_dir().join(format!("tauto-lint-dir-{}", std::process::id()));
    let nested = dir.join("src");
    std::fs::create_dir_all(&nested).unwrap();
    std::fs::write(
        dir.join("Clean.taut"),
        r#"fn one(): Nat { Succ(Zero) }
"#,
    )
    .unwrap();
    std::fs::write(
        nested.join("Hole.taut"),
        r#"theorem t(): Nat { ?h }
"#,
    )
    .unwrap();
    std::fs::write(nested.join("notes.md"), "?h\n").unwrap();
    let out = tauto(&["lint", dir.to_str().unwrap()]);
    let shown = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1), "{shown}");
    assert!(shown.contains("Hole.taut:1:"), "{shown}");
    assert!(!shown.contains("notes.md"), "{shown}");
    let out = tauto(&["lint", "--json", dir.to_str().unwrap()]);
    let json = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1), "{json}");
    assert!(json.starts_with(r#"[{"file":""#), "{json}");
    assert!(json.contains(r#"Hole.taut","line":1,"col":"#), "{json}");
    assert!(json.contains(r#""kind":"lint"}"#), "{json}");
    let clean = dir.join("Clean.taut");
    let out = tauto(&["lint", "--json", clean.to_str().unwrap()]);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "[]\n");

    let out = tauto(&["lint", clean.to_str().unwrap(), clean.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(0));
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn help_after_a_command_shows_its_usage() {
    let out = tauto(&["lint", "--help"]);
    assert_eq!(out.status.code(), Some(0));
    assert_eq!(
        String::from_utf8_lossy(&out.stdout).trim(),
        "usage: tauto lint [--json] [--fix] PATH…"
    );
    let out = tauto(&["check", "--help"]);
    let shown = String::from_utf8_lossy(&out.stdout);
    assert!(shown.starts_with("usage: tauto check FILE"), "{shown}");
    assert!(!shown.contains("tauto goals"), "{shown}");
    let out = tauto(&["macro", "-h"]);
    let shown = String::from_utf8_lossy(&out.stdout);
    assert!(shown.contains("(expand | trace | inspect)"), "{shown}");
}
