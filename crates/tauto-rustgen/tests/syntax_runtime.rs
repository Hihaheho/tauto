//! Runtime syntax parsers use embedded tables, not compiler-side filesystem state.
use std::path::{Path, PathBuf};
use std::process::Command;
use tauto_rustgen::{Bindings, Options, Sources, workspace};

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../tauto/tests/syntax_fixtures")
}

#[test]
fn runtime_trees_and_diagnostics_match_the_evaluator_without_sources() {
    tauto_messages::install();
    let dir = std::env::temp_dir().join(format!("tauto-runtime-syntax-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("input/.tauto-syntax")).unwrap();
    let mut source = String::new();
    for name in ["math", "lists", "ident", "records", "alias", "keywords"] {
        let fixture = if name == "alias" { "ident" } else { name };
        let grammar = std::fs::read_to_string(fixtures().join(format!("{fixture}.par"))).unwrap();
        let tables = tauto::syntax::with_search_dirs(vec![fixtures()], || {
            tauto::syntax::load_tables(&grammar)
        })
        .unwrap();
        std::fs::write(
            dir.join("input/.tauto-syntax")
                .join(format!("{}.tables", tables.grammar_sha256())),
            tables.source(),
        )
        .unwrap();
        source.push_str(
            &r#"syntax!({name}, ```par
{grammar}```) {clause}
"#
            .replace("{name}", name)
            .replace(
                "{clause}",
                &tauto::syntax::generated_clause(name, &tables, false),
            )
            .replace("{grammar}", &grammar),
        );
    }
    source.push_str(
        r#"
fn keyword_text(root: keywords::Root): Text {
  match root {
    keywords::Root { span: root_span, value: node } => match node {
      True { span: true_span, true_field: yes } => yes.text
      False { span: false_span, false_field: no } => no.text
    }
  }
}
fn keyword_result(text: Text): Text {
  match keywords::parse(text) {
    Ok(root) => keyword_text(root)
    Err(diag) => diag.code
  }
}
perform show("true_field", keyword_result("[true]"))
perform show("false_field", keyword_result("[false]"))
perform show("keyword_error", keyword_result("[maybe]"))
perform show("alias", alias::parse("別名=3"))
perform show("alias_error", alias::parse("別名="))
perform show("record", records::parse("((日本語:値))"))
perform show("single", records::parse("!"))
perform show("recursive", math::parse("((1+2)+3)=6"))
perform show("list_some", lists::parse("head first one:two three !"))
perform show("list_none", lists::parse("~"))
perform show("japanese", ident::parse("日本語=12"))
perform show("syntax_error", math::parse("1+=3"))
perform show("eof", math::parse("1="))
perform show("lexical", ident::parse("日本語=@"))
"#,
    );
    assert_eq!(
        source,
        r#"syntax!(math, ```par
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
syntax!(lists, ```par
%start Doc
%title "lists"
%%
Doc: [ Head ] { Item } ( Bang | Tilde );
Head: KwHead Name;
Item: Name [ Colon Name ];
KwHead: 'head';
Name: /[a-z]+/;
Colon: ':';
Bang: '!';
Tilde: '~';
```) => struct Doc, enum Doc_Group1, struct Head, struct Item, struct Item_Opt1, fn parse
syntax!(ident, ```par
%start Decl
%title "ident"
%%
Decl: Name Equals Value;
Name: /[\p{L}_][\p{L}\p{N}_]*/;
Equals: '=';
Value: /[0-9]+/;
```) => struct Decl, fn parse
syntax!(records, ```par
%start Expr
%title "records"
%%
Expr: Name Colon Name | LParen Expr RParen | Bang;
Name: /[\p{L}_][\p{L}\p{N}_]*/;
Colon: ':';
LParen: '(';
RParen: ')';
Bang: '!';
```) => enum Expr, fn parse
syntax!(alias, ```par
%start Decl
%title "ident"
%%
Decl: Name Equals Value;
Name: /[\p{L}_][\p{L}\p{N}_]*/;
Equals: '=';
Value: /[0-9]+/;
```) => struct Decl, fn parse
syntax!(keywords, ```par
%start Root
%title "keyword fields"
%%
Root: '['^ Value ']'^;
Value: 'true' | 'false';
```) => struct Root, enum Value, fn parse

fn keyword_text(root: keywords::Root): Text {
  match root {
    keywords::Root { span: root_span, value: node } => match node {
      True { span: true_span, true_field: yes } => yes.text
      False { span: false_span, false_field: no } => no.text
    }
  }
}
fn keyword_result(text: Text): Text {
  match keywords::parse(text) {
    Ok(root) => keyword_text(root)
    Err(diag) => diag.code
  }
}
perform show("true_field", keyword_result("[true]"))
perform show("false_field", keyword_result("[false]"))
perform show("keyword_error", keyword_result("[maybe]"))
perform show("alias", alias::parse("別名=3"))
perform show("alias_error", alias::parse("別名="))
perform show("record", records::parse("((日本語:値))"))
perform show("single", records::parse("!"))
perform show("recursive", math::parse("((1+2)+3)=6"))
perform show("list_some", lists::parse("head first one:two three !"))
perform show("list_none", lists::parse("~"))
perform show("japanese", ident::parse("日本語=12"))
perform show("syntax_error", math::parse("1+=3"))
perform show("eof", math::parse("1="))
perform show("lexical", ident::parse("日本語=@"))
"#
    );
    std::fs::write(dir.join("input/main.taut"), &source).unwrap();
    let (pkg, expected) = tauto::syntax::with_search_dirs(vec![dir.join("input")], || {
        (
            tauto_nir::compile(&source).unwrap(),
            tauto::eval::run(&source).unwrap().outputs,
        )
    });
    let literal_source = r#"syntax!(math, ```par
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
syntax!(lists, ```par
%start Doc
%title "lists"
%%
Doc: [ Head ] { Item } ( Bang | Tilde );
Head: KwHead Name;
Item: Name [ Colon Name ];
KwHead: 'head';
Name: /[a-z]+/;
Colon: ':';
Bang: '!';
Tilde: '~';
```) => struct Doc, enum Doc_Group1, struct Head, struct Item, struct Item_Opt1, fn parse
syntax!(ident, ```par
%start Decl
%title "ident"
%%
Decl: Name Equals Value;
Name: /[\p{L}_][\p{L}\p{N}_]*/;
Equals: '=';
Value: /[0-9]+/;
```) => struct Decl, fn parse
syntax!(records, ```par
%start Expr
%title "records"
%%
Expr: Name Colon Name | LParen Expr RParen | Bang;
Name: /[\p{L}_][\p{L}\p{N}_]*/;
Colon: ':';
LParen: '(';
RParen: ')';
Bang: '!';
```) => enum Expr, fn parse
syntax!(alias, ```par
%start Decl
%title "ident"
%%
Decl: Name Equals Value;
Name: /[\p{L}_][\p{L}\p{N}_]*/;
Equals: '=';
Value: /[0-9]+/;
```) => struct Decl, fn parse
syntax!(keywords, ```par
%start Root
%title "keyword fields"
%%
Root: '['^ Value ']'^;
Value: 'true' | 'false';
```) => struct Root, enum Value, fn parse

fn keyword_text(root: keywords::Root): Text {
  match root {
    keywords::Root { span: root_span, value: node } => match node {
      True { span: true_span, true_field: yes } => yes.text
      False { span: false_span, false_field: no } => no.text
    }
  }
}
fn keyword_result(text: Text): Text {
  match keywords::parse(text) {
    Ok(root) => keyword_text(root)
    Err(diag) => diag.code
  }
}
perform show("true_field", keyword_result("[true]"))
perform show("false_field", keyword_result("[false]"))
perform show("keyword_error", keyword_result("[maybe]"))
perform show("alias", alias::parse("別名=3"))
perform show("alias_error", alias::parse("別名="))
perform show("record", records::parse("((日本語:値))"))
perform show("single", records::parse("!"))
perform show("recursive", math::parse("((1+2)+3)=6"))
perform show("list_some", lists::parse("head first one:two three !"))
perform show("list_none", lists::parse("~"))
perform show("japanese", ident::parse("日本語=12"))
perform show("syntax_error", math::parse("1+=3"))
perform show("eof", math::parse("1="))
perform show("lexical", ident::parse("日本語=@"))

perform show("literal", keyword_text(keywords`[true]`))
"#;
    assert!(literal_source.starts_with(&source));
    let literal = tauto::syntax::with_search_dirs(vec![dir.join("input")], || {
        tauto::eval::run(&literal_source).unwrap().outputs
    });
    assert_eq!(
        literal.last().unwrap().1,
        expected
            .iter()
            .find(|(label, _)| label == "true_field")
            .unwrap()
            .1
    );
    let ws = workspace(
        "runtime-syntax",
        &pkg,
        &Sources {
            file: "main.taut",
            text: &source,
        },
        &Bindings::default(),
        &Options::default(),
    );
    let binary = ws
        .build(
            "runtime-syntax",
            &dir.join("generated"),
            &dir.join("target"),
            false,
        )
        .unwrap();
    // Only a copied binary remains; neither original inputs nor generated Rust/table sources exist.
    let standalone = dir.join("standalone");
    std::fs::copy(binary, &standalone).unwrap();
    std::fs::remove_dir_all(dir.join("input")).unwrap();
    std::fs::remove_dir_all(dir.join("generated")).unwrap();
    let out = Command::new(&standalone)
        .current_dir(&dir)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let actual = String::from_utf8(out.stdout).unwrap();
    let expected = expected
        .into_iter()
        .map(|(label, value)| format!("{label} = {value}\n"))
        .collect::<String>();
    assert_eq!(actual, expected);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn runtime_parser_identity_and_result_are_checked_before_codegen() {
    tauto_messages::install();
    let grammar = std::fs::read_to_string(fixtures().join("ident.par")).unwrap();
    let tables =
        tauto::syntax::with_search_dirs(vec![fixtures()], || tauto::syntax::load_tables(&grammar))
            .unwrap();
    let decl = r#"syntax!({name}, ```par
{grammar}```) {clause}
"#
    .replace("{name}", "ident")
    .replace(
        "{clause}",
        &tauto::syntax::generated_clause("ident", &tables, false),
    )
    .replace("{grammar}", &grammar);
    for (source, error) in [
        (
            r#"syntax!(ident, ```par
%start Decl
%title "ident"
%%
Decl: Name Equals Value;
Name: /[\p{L}_][\p{L}\p{N}_]*/;
Equals: '=';
Value: /[0-9]+/;
```) => struct Decl, fn parse
fn bad(name: Text): Result(ident::Decl, SynDiag) { Syn::parse(name, "68042a765101c218e18f2287df9e40744f0c82afa9e33fa7f1a5150c5dd6e011", "x=1") }
perform show("x", bad("ident"))"#,
            "literal syntax name",
        ),
        (
            r#"syntax!(ident, ```par
%start Decl
%title "ident"
%%
Decl: Name Equals Value;
Name: /[\p{L}_][\p{L}\p{N}_]*/;
Equals: '=';
Value: /[0-9]+/;
```) => struct Decl, fn parse
fn bad(): Result(i64, SynDiag) { Syn::parse("ident", "68042a765101c218e18f2287df9e40744f0c82afa9e33fa7f1a5150c5dd6e011", "x=1") }
perform show("x", bad())"#,
            "result must match",
        ),
    ] {
        assert!(source.starts_with(&decl));
        assert!(source.contains(tables.grammar_sha256()));
        let result =
            tauto::syntax::with_search_dirs(vec![fixtures()], || tauto_nir::compile(source));
        let message = format!("{:?}", result.unwrap_err());
        assert!(message.contains(error), "{message}");
    }
}

#[test]
fn handwritten_ast_with_the_right_name_is_not_a_valid_runtime_schema() {
    tauto_messages::install();
    let grammar = std::fs::read_to_string(fixtures().join("ident.par")).unwrap();
    let tables =
        tauto::syntax::with_search_dirs(vec![fixtures()], || tauto::syntax::load_tables(&grammar))
            .unwrap();
    let source = r#"struct ident_Decl { value: i64 }
fn bad(): Result(ident::Decl, SynDiag) { Syn::parse("ident", "68042a765101c218e18f2287df9e40744f0c82afa9e33fa7f1a5150c5dd6e011", "x=1") }
perform show("x", bad())"#;
    assert!(source.contains(tables.grammar_sha256()));
    let result = tauto::syntax::with_search_dirs(vec![fixtures()], || tauto_nir::compile(&source));
    assert!(format!("{:?}", result.unwrap_err()).contains("schema does not match"));
}

#[test]
fn runtime_expression_holes_are_an_explicit_build_error() {
    tauto_messages::install();
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases/macro");
    let grammar = std::fs::read_to_string(dir.join("grammars/math.par")).unwrap();
    let tables =
        tauto::syntax::with_search_dirs(vec![dir.clone()], || tauto::syntax::load_tables(&grammar))
            .unwrap();
    let source = r#"syntax!(math, ```par
%start Eqn
%title "math"
%%
Eqn: Sum Equals Sum;
Sum: Term { Plus Term };
Term: Num | Paren | Embed;
Paren: LParen Sum RParen;
Embed: TautoExpr;
Num: /[0-9]+/;
Equals: '=';
Plus: '+';
LParen: '(';
RParen: ')';
```) => struct Eqn, struct Paren, struct Sum, struct Sum_Rep1, enum Term, fn parse
perform show("x", math::parse("1=1"))"#;
    assert!(source.contains(&tauto::syntax::generated_clause("math", &tables, false)));
    let result = tauto::syntax::with_search_dirs(vec![dir], || tauto_nir::compile(&source));
    let message = format!("{:?}", result.unwrap_err());
    assert!(message.contains("TautoExpr holes"), "{message}");
}

#[test]
fn keyword_syntax_literal_compiles_natively() {
    tauto_messages::install();
    let grammar = std::fs::read_to_string(fixtures().join("keywords.par")).unwrap();
    let tables =
        tauto::syntax::with_search_dirs(vec![fixtures()], || tauto::syntax::load_tables(&grammar))
            .unwrap();
    let source = r#"syntax!(keywords, ```par
%start Root
%title "keyword fields"
%%
Root: '['^ Value ']'^;
Value: 'true' | 'false';
```) => struct Root, enum Value, fn parse
perform show("literal", keywords`[true]`)
"#;
    assert!(source.contains(&tauto::syntax::generated_clause("keywords", &tables, false)));
    let pkg =
        tauto::syntax::with_search_dirs(vec![fixtures()], || tauto_nir::compile(&source)).unwrap();
    let dir = std::env::temp_dir().join(format!("tauto-keyword-literal-{}", std::process::id()));
    let ws = workspace(
        "keyword-literal",
        &pkg,
        &Sources {
            file: "main.taut",
            text: &source,
        },
        &Bindings::default(),
        &Options::default(),
    );
    ws.build(
        "keyword-literal",
        &dir.join("generated"),
        &dir.join("target"),
        false,
    )
    .unwrap();
    std::fs::remove_dir_all(dir).unwrap();
}
