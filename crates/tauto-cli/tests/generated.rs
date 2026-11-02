//! `tauto fmt --fill-generated` writes the list of what a declaration makes
//! (`docs/design/macro.md`, "作る宣言の一覧").

use std::fs;
use std::path::PathBuf;
use std::process::Command;

const STD: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../std");

fn dir(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tauto-generated-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    d
}

fn tauto(args: &[&str]) -> (String, bool) {
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(args)
        .output()
        .unwrap();
    (
        String::from_utf8(out.stdout).unwrap() + &String::from_utf8(out.stderr).unwrap(),
        out.status.success(),
    )
}

fn wf_source() -> &'static str {
    r#"fn id_nat(n: Nat): Nat { n }

fn half(n: Nat): Nat decreasing_by measure(id_nat) {
  match n: Nat {
    Zero => Zero
    Succ(m) => match m: Nat {
      Zero => Zero
      Succ(k) => Succ(half(k, Nat::le_succ(k)))
    }
  }
}
"#
}

#[test]
fn the_list_of_a_decreasing_by_is_written_and_then_the_file_checks() {
    let wf = wf_source();
    let d = dir("wf");
    let file = d.join("main.taut");
    let source = format!(
        r#"import "{}/Base.taut"
import "{}/WellFounded.taut"
import "{}/Nat.taut"
{}"#,
        STD, STD, STD, wf
    );
    fs::write(&file, &source).unwrap();
    let path = file.to_str().unwrap();

    let (shown, ok) = tauto(&["check", path]);
    assert!(
        !ok && shown.contains("made but not listed: theorem half::eq"),
        "{shown}"
    );

    let (shown, ok) = tauto(&["fmt", "--fill-generated", path]);
    assert!(ok, "{shown}");
    let written = fs::read_to_string(&file).unwrap();
    assert!(
        written.contains("decreasing_by measure(id_nat) => theorem half::eq {"),
        "{written}"
    );
    assert_eq!(written.replace(" => theorem half::eq", ""), source);

    let (shown, ok) = tauto(&["check", path]);
    assert!(ok, "{shown}");
    // Writing it again changes nothing.
    tauto(&["fmt", "--fill-generated", path]);
    assert_eq!(fs::read_to_string(&file).unwrap(), written);
}

#[test]
fn a_wrong_list_is_replaced() {
    let d = dir("wrong");
    let file = d.join("main.taut");
    let source = format!(
        r#"import "{}/Base.taut"
import "{}/WellFounded.taut"
import "{}/Nat.taut"
{}"#,
        STD,
        STD,
        STD,
        wf_source().replace(
            r#"{
  match n"#,
            r#"=> theorem other {
  match n"#,
        )
    );
    fs::write(&file, &source).unwrap();
    let path = file.to_str().unwrap();
    let (shown, ok) = tauto(&["fmt", "--fill-generated", path]);
    assert!(ok, "{shown}");
    let written = fs::read_to_string(&file).unwrap();
    assert!(written.contains("=> theorem half::eq {"), "{written}");
    assert!(!written.contains("other"), "{written}");
}

#[test]
fn formatting_keeps_a_list_where_it_was_broken() {
    let d = dir("long");
    let file = d.join("main.taut");
    let source = r#"inductive_syntax!(arith, ```par
%start Expr
%%
Expr: Prod;
```) => struct Expr, struct Prod, fn parse, inductive Expr::I,
  inductive Prod::I
"#;
    fs::write(&file, source).unwrap();
    let path = file.to_str().unwrap();
    let (shown, ok) = tauto(&["fmt", "--check", path]);
    assert!(ok, "{shown}");
}
