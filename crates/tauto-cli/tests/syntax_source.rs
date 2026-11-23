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
    let path = dir.to_str().unwrap();
    // A current table that differs from what the generator writes: only
    // `--force` replaces it.
    assert!(run(&["syntax", "gen", path]).status.success());
    let current = fs::read_to_string(&table).unwrap();
    let cached = current.replacen("title -", "title cached", 1);
    assert_ne!(cached, current);
    fs::write(&table, &cached).unwrap();
    for flags in [
        vec!["syntax", "gen", path],
        vec!["syntax", "gen", "--check", path],
    ] {
        assert!(run(&flags).status.success());
        assert_eq!(fs::read_to_string(&table).unwrap(), cached);
    }
    for flags in [
        vec!["syntax", "gen", "--check", "--force", path],
        vec!["syntax", "gen", "--force", "--check", path],
    ] {
        assert_eq!(run(&flags).status.code(), Some(2));
        assert_eq!(fs::read_to_string(&table).unwrap(), cached);
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
    // A table the current generator did not make is regenerated without `--force`.
    fs::write(&table, "old cached table").unwrap();
    assert_eq!(run(&["syntax", "gen", "--check", path]).status.code(), Some(1));
    assert!(run(&["syntax", "gen", path]).status.success());
    assert_eq!(fs::read_to_string(&table).unwrap(), regenerated);
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn tables_of_a_subdirectory_are_kept_beside_its_file_and_checked_from_the_root() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("tauto-syntax-subdir-{}", std::process::id()));
    fs::create_dir_all(dir.join("src/sub")).unwrap();
    fs::write(dir.join("Tauto.eure"), "package { name = \"test\" }").unwrap();
    fs::write(
        dir.join("src/sub/g.taut"),
        r#"syntax!(tiny, ```par
%start Start
%%
Start: 'a';
```) => struct Start, fn parse
"#,
    )
    .unwrap();
    let path = dir.to_str().unwrap();
    let out = run(&["syntax", "gen", path]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(dir.join("src/sub/.tauto-syntax").is_dir());
    assert!(!dir.join(".tauto-syntax").exists());
    let out = run(&["syntax", "gen", "--check", path]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn a_caret_drops_a_token_non_terminal_from_the_typed_tree() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("tauto-syntax-caret-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let grammar = r#"syntax!(clause, ```par
%start Clause
%%
Clause: Word {Piece} Dot^;
Piece: Word Comma^ Word;
Word: /[a-z]+/;
Dot: '.';
Comma: ',';
```) => struct Clause, struct Piece, struct Clause_Rep1, fn parse
"#;
    fs::write(dir.join("main.taut"), grammar).unwrap();
    let path = dir.to_str().unwrap();
    let generated = run(&["syntax", "gen", path]);
    assert!(
        generated.status.success(),
        "{}",
        String::from_utf8_lossy(&generated.stderr)
    );
    let shown = run(&["syntax", "show", path, "clause"]);
    assert!(
        shown.status.success(),
        "{}",
        String::from_utf8_lossy(&shown.stderr)
    );
    let shown = String::from_utf8(shown.stdout).unwrap();
    assert!(shown.contains("word: SynToken"), "{shown}");
    assert!(!shown.contains("dot"), "{shown}");
    assert!(!shown.contains("comma"), "{shown}");
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn a_non_terminal_defined_twice_is_reported_by_name() {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("tauto-syntax-twice-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let grammar = r#"syntax!(twice, ```par
%start Tick
%%
Tick: KwTick^ TickOf;
TickOf: /[a-z]+/;
KwTick: 'tick';
Tick: /'/;
```) => struct Tick, fn parse
"#;
    fs::write(dir.join("main.taut"), grammar).unwrap();
    let out = run(&["syntax", "gen", dir.to_str().unwrap()]);
    assert!(!out.status.success());
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("the non-terminal Tick is defined twice"), "{err}");
    assert!(!err.contains("conflict"), "{err}");
    fs::remove_dir_all(dir).unwrap();
}
