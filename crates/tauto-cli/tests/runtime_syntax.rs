//! A tote's runtime syntax parser is usable through the Rust CLI backend.
use std::{fs, path::Path, process::Command};

#[test]
fn rust_backend_runs_a_runtime_parser_tote() {
    let dir = std::env::temp_dir()
        .join(format!("tauto-cli-runtime-syntax-{}", std::process::id()))
        .join("runtime-parser");
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::create_dir_all(dir.join(".tauto-syntax")).unwrap();
    fs::write(
        dir.join("Tauto.eure"),
        "package {\n name = \"runtime-parser\"\n version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tauto/tests/syntax_fixtures");
    let grammar = fs::read_to_string(fixtures.join("math.par")).unwrap();
    let tables =
        tauto::syntax::with_search_dirs(vec![fixtures], || tauto::syntax::load_tables(&grammar))
            .unwrap();
    fs::write(
        dir.join(".tauto-syntax")
            .join(format!("{}.tables", tables.grammar_sha256())),
        tables.source(),
    )
    .unwrap();
    let source = r#"import std::prelude::Macro

syntax!(math, ```par
{grammar}```) {}
perform show("tree", math::parse("(1+2)=3"))
perform show("error", math::parse("1+="))
"#
    .replacen(
        "{}",
        &tauto::syntax::generated_clause("math", &tables, false),
        1,
    )
    .replace("{grammar}", &grammar);
    assert_eq!(
        source,
        r#"import std::prelude::Macro

syntax!(math, ```par
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
```) => struct Eqn, struct Paren, struct Sum, struct Sum_Rep1, enum Term, fn parse
perform show("tree", math::parse("(1+2)=3"))
perform show("error", math::parse("1+="))
"#
    );
    fs::write(dir.join("src/main.taut"), &source).unwrap();
    let run = |backend: &str| {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_tauto"));
        if backend == "rust" {
            cmd.args(["run", "--backend", "rust"]);
        } else {
            cmd.args(["run", "--backend", "eval", "--tote"]);
        }
        let out = cmd
            .arg(&dir)
            .env("TAUTO_TARGET_DIR", dir.join("target"))
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{backend}: {}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        out.stdout
    };
    assert_eq!(run("rust"), run("eval"));
    fs::remove_dir_all(dir).unwrap();
}
