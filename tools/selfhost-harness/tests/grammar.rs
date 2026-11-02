//! The compiler grammar is a `syntax` declaration, not a parallel example grammar.
use selfhost_harness::{materialize, root, run_tote};

#[test]
fn bootstrap_grammar_and_declared_parser_share_the_source_and_tables() {
    let source = std::fs::read_to_string(root().join("totes/grammar/src/grammar.taut")).unwrap();
    let parsed = tauto::surface::parse_program_unresolved_at(&source, 0).unwrap();
    let declarations: Vec<_> = parsed
        .stmts
        .iter()
        .filter_map(|stmt| match stmt {
            tauto::surface::Stmt::Syntax { name, grammar, .. } => Some((name, grammar)),
            _ => None,
        })
        .collect();
    assert_eq!(declarations.len(), 1);
    let (name, grammar) = declarations[0];
    assert_eq!(name, "tauto");
    for path in [
        "crates/tauto-parol/tauto.par",
        "crates/tauto-syntax/tests/data/tauto.par",
    ] {
        assert_eq!(
            grammar.text,
            std::fs::read_to_string(root().join(path)).unwrap(),
            "{path}"
        );
    }
    let sha = tauto_syntax::sha256_hex(grammar.text.as_bytes());
    let table =
        std::fs::read_to_string(root().join(format!("totes/grammar/.tauto-syntax/{sha}.tables")))
            .unwrap();
    assert_eq!(
        table,
        std::fs::read_to_string(root().join("crates/tauto-syntax/tests/data/tauto.tables"))
            .unwrap()
    );
    assert_eq!(
        tauto_syntax::Tables::read(&table).unwrap().grammar_sha256(),
        sha
    );
}

#[test]
fn generated_parser_really_parses_tauto_including_its_own_declaration() {
    let mut inputs: Vec<(String, String)> = [
        ("empty", r#""#),
        (
            "function",
            r#"fn identity(n: i64): i64 { n }
"#,
        ),
        (
            "comment",
            r#"/* a */ let x := 1 // b
"#,
        ),
        (
            "nested-comment",
            r#"/* a /* b */ c */ let x := 1
"#,
        ),
        (
            "unicode",
            r#"let 日本語 := 1 // 😀
"#,
        ),
        (
            "plaintext",
            r#"let s := plaintext`a\n 'b`
"#,
        ),
        (
            "syntax-literal",
            r#"let x := math`1 + 2`
"#,
        ),
        (
            "syntax-multiline",
            r#"let x := ```math
1 + 2
```
"#,
        ),
        (
            "syntax-long-fence",
            r#"let x := ````math
`foo`
````
"#,
        ),
        ("unclosed-function", r#"fn f("#),
        ("unclosed-comment", r#"/* a"#),
        ("unclosed-string", r#"let s := "a"#),
        ("unclosed-literal", r#"let x := math`a"#),
        (
            "wrong-fence",
            r#"let x := ````math
1
```
"#,
        ),
        (
            "stray",
            r#"let x := 1 $ 2
"#,
        ),
    ]
    .into_iter()
    .map(|(name, text)| (name.into(), text.into()))
    .collect();
    inputs.push((
        "self".into(),
        std::fs::read_to_string(root().join("totes/grammar/src/grammar.taut")).unwrap(),
    ));
    for (name, source) in &inputs {
        let accepted = !matches!(
            name.as_str(),
            "nested-comment"
                | "unclosed-function"
                | "unclosed-comment"
                | "unclosed-string"
                | "unclosed-literal"
                | "wrong-fence"
                | "stray"
        );
        assert_eq!(tauto_parol::parse(source).is_ok(), accepted, "{name}");
    }
    let expected: String = inputs
        .iter()
        .map(|(_, source)| {
            if tauto_parol::parse(source).is_ok() {
                "ok\n"
            } else {
                "error\n"
            }
        })
        .collect();
    // Ensure the comparison exercises both successful parsing and rejection.
    assert!(expected.starts_with("ok\nok\n"));
    assert!(expected.contains("error\n"));
    let files = materialize("declared-grammar", &inputs);
    let out = run_tote("grammar", &files.paths, 1_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_eq!(out.stdout, expected);
}

#[test]
fn generated_tree_has_typed_fields_and_original_tokens() {
    let source = std::fs::read_to_string(root().join("totes/grammar/src/grammar.taut")).unwrap();
    let source = source
        + r#"
fn inspect(source: std.prelude.Text): Unit {
  match tauto::parse(source) {
    Ok(tree) => perform show("tree", tree.stmts)
    Err(diag) => perform show("error", diag)
  }
}
inspect("let answer = 42")
"#;
    let out = tauto::syntax::with_search_dirs(vec![root().join("totes/grammar")], || {
        tauto::eval::run(&source)
    })
    .unwrap();
    assert_eq!(out.outputs.len(), 1);
    assert_eq!(out.outputs[0].0, "tree");
    let tree = &out.outputs[0].1;
    assert!(tree.starts_with("tauto.Stmts {"), "{tree}");
    assert!(tree.contains("text: \"answer\""), "{tree}");
    assert!(tree.contains("text: \"42\""), "{tree}");
}

#[test]
fn generated_parser_acceptance_matches_repository_corpus() {
    let inputs = selfhost_harness::corpus();
    assert!(!inputs.is_empty());
    let expected: String = inputs
        .iter()
        .map(|(_, source)| {
            if tauto_parol::parse(source).is_ok() {
                "ok\n"
            } else {
                "error\n"
            }
        })
        .collect();
    let files = materialize("declared-grammar-corpus", &inputs);
    let out = run_tote("grammar", &files.paths, 1_000_000_000);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let actual: Vec<_> = out.stdout.lines().collect();
    let expected: Vec<_> = expected.lines().collect();
    assert_eq!(actual.len(), inputs.len());
    for ((actual, expected), (name, _)) in actual.iter().zip(expected).zip(inputs) {
        assert_eq!(*actual, expected, "{name}");
    }
}
