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
        case_inputs::file("aux-analyzer.eure", case, "math.nib"),
    )
    .unwrap();
    let text = case_inputs::file("aux-analyzer.eure", case, "main.nib");
    std::fs::write(dir.join("main.nib"), &text).unwrap();
    (dir.join("main.nib"), text)
}

#[test]
fn the_tokens_of_a_literal_are_coloured_by_the_grammar() {
    let (path, text) = project("tokens", "editor_tokens");
    let tokens = tauto_analyzer::editor::dsl_tokens(&path, &text).expect("reads");
    let seen: Vec<(&str, &str)> = tokens
        .iter()
        .map(|t| (&text[t.start..t.end], t.kind))
        .collect();
    assert_eq!(
        seen,
        [
            ("1", "number"),
            ("+", "operator"),
            ("2", "number"),
            ("=", "operator"),
            ("3", "number")
        ]
    );
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
    let tokens = tauto_analyzer::editor::dsl_tokens(&fixtures, &text).expect("reads");
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

/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn file_static(file: &str, name: &str, input: &str) -> &'static str {
        match (file, name, input) {
        ("aux-analyzer.eure", "editor_completion", "math.nib") => r#"syntax!(math, ```par
%start Eqn
%title "math"
%%
Eqn: Sum Equals Sum;
Sum: Term { Plus Term };
Term: Num | Paren;
Paren: LParen Sum RParen;
Num: /[0-9]+/;
Equals: '=';
Plus: '+';
LParen: '(';
RParen: ')';
```) => struct Eqn, struct Paren, struct Sum, struct Sum_Rep1, enum Term,
  fn parse
pub macro fn math(e: math::Eqn): SynExpr ! {macro_error, Div} { quote { Eq(Nat, 1, 1) } }
"#,
        ("aux-analyzer.eure", "editor_completion", "main.nib") => r#"import "math.nib"
theorem t(): math!(`1 + `) { Refl(Nat, 3) }
"#,
        ("aux-analyzer.eure", "editor_tokens", "math.nib") => r#"syntax!(math, ```par
%start Eqn
%title "math"
%%
Eqn: Sum Equals Sum;
Sum: Term { Plus Term };
Term: Num | Paren;
Paren: LParen Sum RParen;
Num: /[0-9]+/;
Equals: '=';
Plus: '+';
LParen: '(';
RParen: ')';
```) => struct Eqn, struct Paren, struct Sum, struct Sum_Rep1, enum Term,
  fn parse
pub macro fn math(e: math::Eqn): SynExpr ! {macro_error, Div} { quote { Eq(Nat, 1, 1) } }
"#,
        ("aux-analyzer.eure", "editor_tokens", "main.nib") => r#"import "math.nib"
theorem t(): math!(`1 + 2 = 3`) { Refl(Nat, 3) }
"#,
        _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn file(file: &str, name: &str, input: &str) -> String {
        file_static(file, name, input).to_string()
    }
}
