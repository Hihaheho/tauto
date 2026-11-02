//! Syntax metadata, search-directory isolation, and block agreement with Eure.

use std::path::{Path, PathBuf};
use tauto::eval::{RunError, run};
use tauto::syntax::{load_tables, set_search_dirs, types_text, with_search_dirs};
use tauto::types::check_types;

const MATH: &str = include_str!("syntax_fixtures/math.par");

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/syntax_fixtures")
}

fn shown(source: &str) -> Result<Vec<(String, String)>, RunError> {
    with_search_dirs(vec![fixtures()], || run(source).map(|o| o.outputs))
}

fn text_of(doc: &eure_document::document::EureDocument, key: &str) -> String {
    use eure_document::document::node::NodeValue;
    use eure_document::value::PrimitiveValue as P;
    let NodeValue::Map(map) = &doc.node(doc.get_root_id()).content else {
        panic!("a map")
    };
    let id = map.get_node_id(&key.into()).expect("key");
    match &doc.node(id).content {
        NodeValue::Primitive(P::Text(t)) => t.as_str().to_string(),
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_syntax_makes_the_types_of_the_design() {
    tauto_messages::install();
    let tables = with_search_dirs(vec![fixtures()], || load_tables(MATH)).unwrap();
    assert_eq!(
        types_text("math", &tables),
        r#"struct math::Eqn { span: SynSpan, sum: math::Sum, equals: SynToken, sum_2: math::Sum }
struct math::Paren { span: SynSpan, l_paren: SynToken, sum: math::Sum, r_paren: SynToken }
struct math::Sum { span: SynSpan, term: math::Term, rep: List(math::Sum_Rep1) }
struct math::Sum_Rep1 { span: SynSpan, plus: SynToken, term: math::Term }
enum math::Term {
  Num(SynToken)
  Paren(math::Paren)
}
"#
    );
}

#[test]
fn tables_of_another_place_are_not_found() {
    tauto_messages::install();
    let source = r#"syntax!(math, ```par
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
let e := math`1 = 1`
"#
    .to_string();
    let none = set_search_dirs(Vec::new());
    let errors = check_types(&source).unwrap().errors;
    set_search_dirs(none);
    assert!(
        errors[0]
            .message
            .contains("tables of this syntax are missing"),
        "{errors:?}"
    );
}

#[test]
fn a_block_matches_what_eure_makes_of_the_same_block() {
    tauto_messages::install();
    // The body is the same text, read by Eure's rule for an indented block.
    let body = "    alpha\n      beta\n\n    gamma\n";
    let eure = format!("a = ```text\n{body}    ```\n");
    let doc = eure_reader::parse_to_document(&eure, "block.eure")
        .map_err(|e| e.to_string())
        .unwrap();
    let want = text_of(&doc, "a");
    let source = r#"let a := ```plaintext
    alpha
      beta

    gamma
    ```
perform show("a", a)
"#
    .to_string();
    let out = shown(&source).unwrap();
    assert_eq!(out[0].1, format!("{want:?}"));
}

#[test]
fn the_literal_has_the_type_of_the_start_symbol() {
    tauto_messages::install();
    let tables = with_search_dirs(vec![fixtures()], || load_tables(MATH)).unwrap();
    let clause = tauto::syntax::generated_clause("math", &tables, false);
    let source = r#"syntax!(math, ```par
{MATH}```) {clause}
let e := math`1 + 2 = 3`
"#
    .replace("{clause}", &clause)
    .replace("{MATH}", MATH);
    let report = with_search_dirs(vec![fixtures()], || check_types(&source)).unwrap();
    assert!(report.errors.is_empty(), "{:?}", report.errors);
    assert!(
        report
            .lets
            .contains(&("e".to_string(), "math::Eqn".to_string())),
        "{:?}",
        report.lets
    );
}
