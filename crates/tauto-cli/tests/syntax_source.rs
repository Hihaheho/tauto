//! Grammar export preserves literal bytes and never chooses an ambiguous declaration.
use std::{fs, path::PathBuf, process::Command};

fn run(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(args)
        .output()
        .unwrap()
}

#[test]
fn compiler_grammar_exports_verbatim_without_loading_generated_types() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let dir = root.join("totes/grammar");
    let out = run(&["syntax", "source", dir.to_str().unwrap(), "tauto"]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(out.stderr.is_empty());
    assert_eq!(
        out.stdout,
        fs::read(root.join("crates/tauto-parol/tauto.par")).unwrap()
    );
}

#[test]
fn source_requires_a_unique_declared_name() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("tauto-syntax-source-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let grammar = r#"syntax!(tiny, ```par
%start Start
%%
Start: 'a';
```) => struct Start, fn parse
"#;
    fs::write(dir.join("a.taut"), grammar).unwrap();
    let path = dir.to_str().unwrap();
    let out = run(&["syntax", "source", path, "tiny"]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(out.stdout, b"%start Start\n%%\nStart: 'a';\n");
    let out = run(&["syntax", "source", path, "missing"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(out.stdout.is_empty());
    fs::write(dir.join("b.taut"), grammar).unwrap();
    let out = run(&["syntax", "source", path, "tiny"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(out.stdout.is_empty());
    assert!(String::from_utf8_lossy(&out.stderr).contains("more than one"));
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn package_sources_limit_discovery_and_match_the_compiler() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("tauto-syntax-package-{}", std::process::id()));
    fs::create_dir_all(dir.join("src/nested")).unwrap();
    fs::create_dir_all(dir.join("outside")).unwrap();
    let source = r#"syntax!(tiny, ```par
%start Start
%%
Start: 'a';
```) => struct Start, fn parse
"#;
    fs::write(dir.join("src/nested/grammar.taut"), source).unwrap();
    fs::create_dir_all(dir.join("extra")).unwrap();
    fs::create_dir_all(dir.join("legacy")).unwrap();
    fs::write(dir.join("legacy/old.nib"), r#"syntax = broken"#).unwrap();
    fs::write(dir.join("extra/extra.taut"), r#"pub fn extra(): i64 { 1 }"#).unwrap();
    // Both malformed syntax and a legacy extension outside sources must be ignored.
    fs::write(dir.join("outside/broken.taut"), r#"syntax = broken"#).unwrap();
    fs::write(dir.join("outside/old.nib"), r#"syntax = broken"#).unwrap();
    fs::write(
        dir.join("Tauto.eure"),
        "package { name = \"test\" additional-sources = [\"extra\"] }",
    )
    .unwrap();
    assert_eq!(
        tauto::program::package_source_files(&dir).unwrap(),
        vec![
            dir.join("extra/extra.taut"),
            dir.join("src/nested/grammar.taut")
        ]
    );
    let path = dir.to_str().unwrap();
    let out = run(&["syntax", "source", path, "tiny"]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(out.stdout, b"%start Start\n%%\nStart: 'a';\n");
    let out = run(&["syntax", "gen", "--check", path]);
    assert_eq!(out.status.code(), Some(1));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("src/nested/grammar.taut"), "{err}");
    assert!(err.contains("tables of syntax tiny are missing"), "{err}");
    // Invalid selected inputs must not silently fall back to recursive discovery.
    for manifest in [
        "package { name = \"test\" additional-sources = [\"missing\"] }",
        "package { name = \"test\" additional-sources = [\"legacy\"] }",
        "not a manifest",
    ] {
        fs::write(dir.join("Tauto.eure"), manifest).unwrap();
        assert!(tauto::program::package_source_files(&dir).is_err());
        assert_eq!(
            run(&["syntax", "gen", "--check", path]).status.code(),
            Some(2)
        );
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn force_is_explicit_and_incompatible_flags_are_rejected() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("tauto-syntax-force-{}", std::process::id()));
    fs::create_dir_all(dir.join(".tauto-syntax")).unwrap();
    let grammar = "%start Root\n%%\nRoot: 'true' | 'false';\n";
    fs::write(
        dir.join("main.taut"),
        format!(
            r#"syntax!(words, ```par
{}```) => enum Root, fn parse
"#,
            grammar
        ),
    )
    .unwrap();
    let table = dir
        .join(".tauto-syntax")
        .join(format!("{}.tables", tauto::syntax::grammar_sha(grammar)));
    fs::write(&table, "old cached table").unwrap();
    let path = dir.to_str().unwrap();
    for flags in [
        vec!["syntax", "gen", path],
        vec!["syntax", "gen", "--check", path],
    ] {
        assert!(run(&flags).status.success());
        assert_eq!(fs::read_to_string(&table).unwrap(), "old cached table");
    }
    for flags in [
        vec!["syntax", "gen", "--check", "--force", path],
        vec!["syntax", "gen", "--force", "--check", path],
    ] {
        assert_eq!(run(&flags).status.code(), Some(2));
        assert_eq!(fs::read_to_string(&table).unwrap(), "old cached table");
    }
    let result = run(&["syntax", "gen", "--force", path]);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let regenerated = fs::read_to_string(&table).unwrap();
    assert!(regenerated.contains("true_field"));
    assert!(regenerated.contains("false_field"));
    let shown = run(&["syntax", "show", path, "words"]);
    assert!(
        shown.status.success(),
        "{}",
        String::from_utf8_lossy(&shown.stderr)
    );
    let shown = String::from_utf8(shown.stdout).unwrap();
    assert!(shown.contains("true_field: SynToken"));
    assert!(shown.contains("false_field: SynToken"));
    let result = run(&["syntax", "gen", "--force", path]);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(fs::read_to_string(&table).unwrap(), regenerated);
    fs::remove_dir_all(dir).unwrap();
}
