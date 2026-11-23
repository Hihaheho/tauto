//! `tauto check FILE` of a file that uses what another file of the tote makes with
//! `inductive_syntax!`: a macro of that file, or a type declared after the syntax. The tables of
//! the grammars are the fixtures of `crates/tauto/tests/syntax_fixtures`: each grammar is its
//! `.par` file there, so `scripts/generate-syntax-fixtures.taut` writes and checks its table.
use std::{fs, path::PathBuf, process::Command};

struct Fixture(PathBuf);
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn check_ok(name: &str, files: &[(&str, &str)], table: &str, entry: &str) {
    let root = std::env::temp_dir().join(format!(
        "tauto-inductive-syntax-across-files-{name}-{}",
        std::process::id()
    ));
    let fixture = Fixture(root.clone());
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("src")).unwrap();
    fs::create_dir_all(root.join(".tauto-syntax")).unwrap();
    fs::write(
        root.join("Tauto.eure"),
        "package {\n  name = \"app\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    for (path, text) in files {
        fs::write(root.join(path), text).unwrap();
    }
    let tables = format!("{table}.tables");
    fs::copy(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../tauto/tests/syntax_fixtures/.tauto-syntax")
            .join(&tables),
        root.join(".tauto-syntax").join(&tables),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["check", entry])
        .current_dir(&fixture.0)
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&output.stdout).to_string()
        + &String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{text}");
    assert!(text.trim_end().ends_with("ok"), "{text}");
}

/// The grammar has a hole, an alternative of `Atom` that `Atom::I` has no constructor for: `Atom::to_i` is `None` on it.
#[test]
fn an_embedded_expression_in_the_grammar_of_a_macro_of_another_file() {
    check_ok(
        "an_embedded_expression_in_the_grammar_of_a_macro_of_another_file",
        &[
            (
                "src/a.taut",
                concat!(
                    r#"import std::builtin::macro { SynExpr }
import std::text { Text }

inductive_syntax!(g, ```par
"#,
                    include_str!("../../tauto/tests/syntax_fixtures/atom_embed.par"),
                    r#"```) => enum Atom, fn parse, inductive Atom::I, fn Atom::to_i

pub macro fn f(s: g::Atom): SynExpr {
  quote { 0 }
}
"#
                ),
            ),
            (
                "src/b.taut",
                r#"import "a.taut" { f }

fn t(): Nat { f!(`x`) }
"#,
            ),
        ],
        "04fd73754f1d8c7ec923626288fee01c6aecd10113d81c963d1a94dd371551dc",
        "src/b.taut",
    );
}

/// `count` is not defined by a `match` and calls itself through `one`: the macro of the other file runs, and writing out `count` ends.
#[test]
fn a_mutual_block_with_a_function_not_by_match_that_a_macro_of_another_file_calls() {
    check_ok(
        "a_mutual_block_with_a_function_not_by_match_that_a_macro_of_another_file_calls",
        &[
            (
                "src/defs.taut",
                concat!(
                    r#"import std::builtin::macro { SynExpr }
import std::text { Text }
inductive_syntax!(ab, ```par
"#,
                    include_str!("../../tauto/tests/syntax_fixtures/ab_word.par"),
                    r#"```) =>
  enum Letter, struct Word, fn parse, inductive Letter::I, inductive Word::I,
  fn Letter::to_i, fn Word::to_i, fn Letter_list::to_i

mutual {
  fn count(ls: List(ab::Letter)): SynExpr {
    let none := quote { 0 }
    match ls {
      [] => none
      [l, ..rest] => one(l, rest)
    }
  }
  fn one(l: ab::Letter, rest: List(ab::Letter)): SynExpr {
    match l {
      A(_) => {
        let r := count(rest)
        quote { 1 + $r }
      }
      B(_) => count(rest)
    }
  }
}

pub macro fn count_a(w: ab::Word): SynExpr { count(w.letter) }
"#
                ),
            ),
            (
                "src/use.taut",
                r#"import "defs.taut" { count_a }
theorem t(): count_a!(`aba`) = 2 { Refl }
"#,
            ),
        ],
        "a46f41972cba9ee3fc3b4750b73baabbc9620ed0401bbe6bd0e9b88fe1f8cd05",
        "src/use.taut",
    );
}

/// What `inductive_syntax!` makes is read from a text longer than the declaration: the executable source of `a.taut` keeps the declarations after it, and every character whole.
#[test]
fn a_file_with_an_inductive_syntax_and_characters_of_several_bytes_after_it_is_imported() {
    check_ok(
        "a_file_with_an_inductive_syntax_and_characters_of_several_bytes_after_it_is_imported",
        &[
            (
                "src/a.taut",
                concat!(
                    r#"import std::builtin::macro { Syn, SynExpr, SynTok, SynToken }
import std::syn_tree
import std::text { Text }

// 命題論理の論理式の文法。
// 結合の強さは ¬ > ∧ > ∨ > → の順。∧ と ∨ は左結合、→ は右結合。
// P0, P1, … は原子命題、⊥ は矛盾。小文字の名前は論理式の変数（メタ変数）、$e は Tauto の式の埋め込み。
inductive_syntax!(nd, ```par
"#,
                    include_str!("../../tauto/tests/syntax_fixtures/formula_embed.par"),
                    r#"```, with(fmt: nd_fmt)) =>
  enum Atom, struct Conj, struct Conj_Rep1, struct Disj, struct Disj_Rep1, struct Formula,
  struct Formula_Opt1, struct Neg, struct Paren, enum Unary, fn parse,
  inductive Atom::I, inductive Conj::I, inductive Conj_Rep1::I, inductive Disj::I,
  inductive Disj_Rep1::I, inductive Formula::I, inductive Formula_Opt1::I, inductive Neg::I,
  inductive Paren::I, inductive Unary::I,
  fn Atom::to_i, fn Conj::to_i, fn Conj_Rep1::to_i, fn Disj::to_i, fn Disj_Rep1::to_i,
  fn Formula::to_i, fn Formula_Opt1::to_i, fn Neg::to_i, fn Paren::to_i, fn Unary::to_i,
  fn Conj_Rep1_list::to_i, fn Disj_Rep1_list::to_i, fn Formula_Opt1_opt::to_i

// 論理式。
pub(open) inductive 論理式: Type {
  原子(n: Nat): 論理式
  矛盾: 論理式
  否定(a: 論理式): 論理式
  かつ(a: 論理式, b: 論理式): 論理式
  または(a: 論理式, b: 論理式): 論理式
  ならば(a: 論理式, b: 論理式): 論理式
}

// 論理式を書くためのマクロ。f!(`a ∧ b → a`) のように書く。
mutual {
  fn 式(f: nd::Formula): SynExpr {
    let l := 選言(f.disj)
    match f.opt {
      None => l
      Some(o) => {
        let r := 式(o.formula)
        quote { ならば($l, $r) }
      }
    }
  }
  fn 選言(d: nd::Disj): SynExpr {
    選言の続き(連言(d.conj), d.rep)
  }
  fn 選言の続き(l: SynExpr, rest: List(nd::Disj_Rep1)): SynExpr {
    match rest {
      [] => l
      [x, ..xs] => {
        let r := 連言(x.conj)
        選言の続き(quote { または($l, $r) }, xs)
      }
    }
  }
  fn 連言(c: nd::Conj): SynExpr {
    連言の続き(単項(c.unary), c.rep)
  }
  fn 連言の続き(l: SynExpr, rest: List(nd::Conj_Rep1)): SynExpr {
    match rest {
      [] => l
      [x, ..xs] => {
        let r := 単項(x.unary)
        連言の続き(quote { かつ($l, $r) }, xs)
      }
    }
  }
  fn 単項(u: nd::Unary): SynExpr {
    match u {
      Neg(n) => {
        let a := 単項(n.unary)
        quote { 否定($a) }
      }
      Atom(a) => 原子式(a)
    }
  }
  fn 原子式(a: nd::Atom): SynExpr {
    match a {
      Bot(_) => quote { 矛盾 }
      Prop(t) => {
        let digits := SynToken { text: Text::slice_or_empty(t.text, 1, Text::len(t.text)), span: t.span, ctx: t.ctx }
        let n := Syn::nat(digits)
        quote { 原子($n) }
      }
      Var(t) => ExVar(Syn::ident(t))
      Paren(p) => 式(p.formula)
      Embed(e) => e
    }
  }
}

pub macro fn f(s: nd::Formula): SynExpr {
  式(s)
}

// `tauto fmt` が f!(`…`) の中を整える。二項の記号の前後に空白を一つ置き、ほかの空白は取る。
pub fn nd_fmt(ts: List(SynTok), width: u64): Option(Text) ! {div} {
  Some(並べる(ts))
}

fn 並べる(ts: List(SynTok)): Text ! {div} {
  match ts {
    Nil => ""
    Cons(t, rest) => if t.skipped { 並べる(rest) } else if t.kind == "AndTok" || t.kind == "OrTok" || t.kind == "Arrow" {
      Text::concat(" ", Text::concat(t.text, Text::concat(" ", 並べる(rest))))
    } else { Text::concat(t.text, 並べる(rest)) }
  }
}

// 論理式を文字列にする。f! で読み戻せる形で、括弧は必要なところにだけ付ける。
pub fn 表示(a: 論理式): Text {
  fmt_at(a, 0)
}

// 結合の強さ: 0 が →、1 が ∨、2 が ∧、3 が ¬ と原子。
fn 強さ(a: 論理式): Nat {
  match a {
    原子(_) => 3
    矛盾 => 3
    否定(_) => 3
    かつ(_, _) => 2
    または(_, _) => 1
    ならば(_, _) => 0
  }
}

fn 括弧(t: Text, need: Bool): Text {
  match need {
    true => Text::concat("(", Text::concat(t, ")"))
    false => t
  }
}

// ctx は周りが求める結合の強さ。a の方が弱ければ括弧で囲む。
fn fmt_at(a: 論理式, ctx: Nat): Text {
  let need := Nat::lt(強さ(a), ctx)
  match a {
    原子(n) => Text::concat("P", Text::of_nat(n))
    矛盾 => "⊥"
    否定(b) => Text::concat("¬", fmt_at(b, 3))
    かつ(b, c) => 括弧(Text::concat(fmt_at(b, 2), Text::concat(" ∧ ", fmt_at(c, 3))), need)
    または(b, c) => 括弧(Text::concat(fmt_at(b, 1), Text::concat(" ∨ ", fmt_at(c, 2))), need)
    ならば(b, c) => 括弧(Text::concat(fmt_at(b, 1), Text::concat(" → ", fmt_at(c, 0))), need)
  }
}
"#
                ),
            ),
            (
                "src/b.taut",
                r#"import "a.taut" { 論理式 }

fn t(): 論理式 { 矛盾 }
"#,
            ),
        ],
        "1fbd4c3cb9c3a62a453448c220629bda7fabf4a87d9525b43bcfd79dd0631fd2",
        "src/b.taut",
    );
}

/// `Proved` is a rule of the grammar and a declaration of `std::builtin::macro` the file does not import: the pattern on a `g::Stmt` is its constructor.
#[test]
fn a_rule_named_as_a_declaration_of_a_file_not_imported_is_the_matched_types_constructor() {
    check_ok(
        "a_rule_named_as_a_declaration_of_a_file_not_imported_is_the_matched_types_constructor",
        &[
            (
                "src/a.taut",
                concat!(
                    r#"import std::builtin::macro { SynExpr }
import std::text { Text }

inductive_syntax!(g, ```par
"#,
                    include_str!("../../tauto/tests/syntax_fixtures/proved_stmt.par"),
                    r#"```) => enum Stmt, struct Proved, fn parse, inductive Stmt::I, inductive Proved::I, fn Stmt::to_i, fn Proved::to_i

pub macro fn f(s: g::Stmt): SynExpr {
  match s {
    Proved(p) => {
      let b := quote { 0 }
      quote { Some($b) }
    }
    Other(_) => quote { None }
  }
}
"#
                ),
            ),
            (
                "src/b.taut",
                r#"import "a.taut" { f }

fn t(): Option(Nat) { f!(`po`) }
"#,
            ),
        ],
        "7fde99fa5796565882999e2f84170dad5b511b1025a154b0cce79f92446c3777",
        "src/b.taut",
    );
}

/// A `mutual` block of macro functions over a grammar of formulas, where `式` is not defined by a
/// `match` and is reached again through `原子式`: a later file that uses the macro checks,
/// instead of overflowing the stack while `式` is written out at its calls.
#[test]
fn a_macro_over_formulas_written_with_a_mutual_block_is_used_by_another_file() {
    check_ok(
        "a_macro_over_formulas_written_with_a_mutual_block_is_used_by_another_file",
        &[
            (
                "src/a.taut",
                concat!(
                    r#"import std::builtin::macro { Syn, SynExpr, SynTok, SynToken }
import std::syn_tree
import std::text { Text }

// 命題論理の論理式の文法。
// 結合の強さは ¬ > ∧ > ∨ > → の順。∧ と ∨ は左結合、→ は右結合。
// P0, P1, … は原子命題、⊥ は矛盾。小文字の名前は論理式の変数（メタ変数）、$e は Tauto の式の埋め込み。
inductive_syntax!(nd, ```par
"#,
                    include_str!("../../tauto/tests/syntax_fixtures/formula.par"),
                    r#"```) =>
  enum Atom, struct Conj, struct Conj_Rep1, struct Disj, struct Disj_Rep1, struct Formula,
  struct Formula_Opt1, struct Neg, struct Paren, enum Unary, fn parse,
  inductive Atom::I, inductive Conj::I, inductive Conj_Rep1::I, inductive Disj::I,
  inductive Disj_Rep1::I, inductive Formula::I, inductive Formula_Opt1::I, inductive Neg::I,
  inductive Paren::I, inductive Unary::I,
  fn Atom::to_i, fn Conj::to_i, fn Conj_Rep1::to_i, fn Disj::to_i, fn Disj_Rep1::to_i,
  fn Formula::to_i, fn Formula_Opt1::to_i, fn Neg::to_i, fn Paren::to_i, fn Unary::to_i,
  fn Conj_Rep1_list::to_i, fn Disj_Rep1_list::to_i, fn Formula_Opt1_opt::to_i

// 論理式。
pub(open) inductive 論理式: Type {
  原子(n: Nat): 論理式
  矛盾: 論理式
  否定(a: 論理式): 論理式
  かつ(a: 論理式, b: 論理式): 論理式
  または(a: 論理式, b: 論理式): 論理式
  ならば(a: 論理式, b: 論理式): 論理式
}

// 論理式を書くためのマクロ。f!(`a ∧ b → a`) のように書く。
mutual {
  fn 式(f: nd::Formula): SynExpr {
    let l := 選言(f.disj)
    match f.opt {
      None => l
      Some(o) => {
        let r := 式(o.formula)
        quote { ならば($l, $r) }
      }
    }
  }
  fn 選言(d: nd::Disj): SynExpr {
    選言の続き(連言(d.conj), d.rep)
  }
  fn 選言の続き(l: SynExpr, rest: List(nd::Disj_Rep1)): SynExpr {
    match rest {
      [] => l
      [x, ..xs] => {
        let r := 連言(x.conj)
        選言の続き(quote { または($l, $r) }, xs)
      }
    }
  }
  fn 連言(c: nd::Conj): SynExpr {
    連言の続き(単項(c.unary), c.rep)
  }
  fn 連言の続き(l: SynExpr, rest: List(nd::Conj_Rep1)): SynExpr {
    match rest {
      [] => l
      [x, ..xs] => {
        let r := 単項(x.unary)
        連言の続き(quote { かつ($l, $r) }, xs)
      }
    }
  }
  fn 単項(u: nd::Unary): SynExpr {
    match u {
      Neg(n) => {
        let a := 単項(n.unary)
        quote { 否定($a) }
      }
      Atom(a) => 原子式(a)
    }
  }
  fn 原子式(a: nd::Atom): SynExpr {
    match a {
      Bot(_) => quote { 矛盾 }
      Prop(t) => quote { 矛盾 }
      Var(t) => ExVar(Syn::ident(t))
      Paren(p) => 式(p.formula)
    }
  }
}

pub macro fn f(s: nd::Formula): SynExpr {
  式(s)
}

"#
                ),
            ),
            (
                "src/b.taut",
                r#"import "a.taut" { 論理式, f }

fn t(): 論理式 { f!(`⊥`) }
"#,
            ),
        ],
        "188ac08cf9074c6b74f8760edd3f7a6a68a2daeacc7c6cfd3a25472f00b9aa24",
        "src/b.taut",
    );
}
