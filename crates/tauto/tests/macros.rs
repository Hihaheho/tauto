//! Check reports expose macro expansion metadata and source locations.

use std::path::{Path, PathBuf};

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tauto-macros-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let tables = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/syntax_fixtures/.tauto-syntax");
    std::os::unix::fs::symlink(tables, dir.join(".tauto-syntax")).unwrap();
    dir
}

fn math_lib() -> (&'static str, String) {
    (
        "math.nib",
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
```) => struct Eqn, struct Paren, struct Sum, struct Sum_Rep1, enum Term,
  fn parse

pub fn math_term(t: math::Term): SynExpr ! {macro_error, Div} {
  match t {
    Num(tok) => Syn::nat(tok)
    Paren(p) => math_sum(p.sum)
  }
}

pub fn math_rest(acc: SynExpr, rest: List(math::Sum_Rep1)): SynExpr ! {macro_error, Div} {
  match rest {
    Nil => acc
    Cons(r, more) => {
      let t := math_term(r.term)
      math_rest(quote { $acc + $t }, more)
    }
  }
}

pub fn math_sum(s: math::Sum): SynExpr ! {macro_error, Div} {
  math_rest(math_term(s.term), s.rep)
}

pub macro fn math(e: math::Eqn): SynExpr ! {macro_error, Div} {
  let l := math_sum(e.sum)
  let r := math_sum(e.sum_2)
  quote { Eq(Nat, $l, $r) }
}
"#
        .to_string(),
    )
}

#[test]
fn check_json_lists_the_macro_runs_with_where_they_were_called() {
    tauto_messages::install();
    let dir = scratch("json");
    let (lib, lib_text) = math_lib();
    std::fs::write(dir.join(lib), lib_text).unwrap();
    let main = r#"import "math.nib"
theorem one_plus_two(): math!(`1 + 2 = 3`) { Refl(Nat, 3) }
"#;
    std::fs::write(dir.join("main.nib"), main).unwrap();
    let report = tauto::report::check_report(&dir.join("main.nib"), None).expect("reads");
    let json = report.json().render();
    assert!(json.contains("\"expansions\":["), "{json}");
    assert!(json.contains("\"macro\":\"math\""), "{json}");
    assert!(json.contains("\"line\":2"), "{json}");
    assert!(json.contains("\"kind\":\"syntax\""), "{json}");
}

#[test]
fn a_typed_macro_may_be_in_a_theorems_statement() {
    tauto_messages::install();
    let dir = scratch("typed-statement");
    std::fs::write(
        dir.join("lib.nib"),
        r#"import std::prelude::Macro
pub macro fn keep(c: Judgement): SynExpr { Judgement::term(c) }
"#,
    )
    .unwrap();
    std::fs::write(
        dir.join("main.nib"),
        r#"import "lib.nib"
theorem in_type(n: Nat): keep!(n = n) { Refl(Nat, n) }
theorem in_param(n: keep!(Nat)): n = n { Refl(Nat, n) }
"#,
    )
    .unwrap();
    let report = tauto::report::check_report(&dir.join("main.nib"), None).expect("reads");
    assert_eq!(report.status(), tauto::report::Status::Ok);
    let json = report.json().render();
    assert!(!json.contains("macro.code"), "{json}");
    assert!(json.contains("\"kind\":\"typed\""), "{json}");
}
