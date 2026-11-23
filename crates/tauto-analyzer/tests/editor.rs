//! What an editor gets inside a syntax literal (`tauto_analyzer::editor`).

use std::path::{Path, PathBuf};

fn project(name: &str, case: &str) -> (PathBuf, String) {
    let dir = std::env::temp_dir().join(format!("tauto-editor-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let tables =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../tauto/tests/syntax_fixtures/.tauto-syntax");
    std::os::unix::fs::symlink(tables, dir.join(".tauto-syntax")).unwrap();
    std::fs::write(
        dir.join("math.nib"),
        tauto_case_inputs::file("aux-analyzer.eure", case, "math.nib"),
    )
    .unwrap();
    let text = tauto_case_inputs::file("aux-analyzer.eure", case, "main.nib");
    std::fs::write(dir.join("main.nib"), &text).unwrap();
    (dir.join("main.nib"), text)
}

#[test]
fn the_completion_lists_what_the_grammar_goes_on_with() {
    let (path, text) = project("complete", "editor_completion");
    let cursor = text.find("+ `").unwrap() + 2;
    let mut terms = tauto_analyzer::editor::dsl_completion(&path, &text, cursor).expect("reads");
    terms.sort();
    assert_eq!(terms, ["LParen", "Num"]);
    // Outside a literal there is nothing to offer.
    let outside = tauto_analyzer::editor::dsl_completion(&path, &text, 3).expect("reads");
    assert!(outside.is_empty(), "{outside:?}");
}

#[test]
fn a_tokens_function_of_the_syntax_says_what_the_literal_is_coloured_as() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../tauto/tests/syntax_fixtures/registered/main.taut");
    let text = std::fs::read_to_string(&fixtures).unwrap();
    let (tokens, _) = tauto_analyzer::editor::dsl_tokens(&fixtures, &text).expect("reads");
    let seen: Vec<(&str, &str)> = tokens
        .iter()
        .map(|t| (&text[t.start..t.end], t.kind))
        .collect();
    assert_eq!(
        seen,
        [
            ("a", "function"),
            ("b", "function"),
            ("c", "function"),
            ("1", "number"),
            ("2", "number"),
            ("x", "function"),
            ("y", "function"),
            ("3", "number"),
            ("a", "type"),
            ("1", "number"),
        ]
    );
}
