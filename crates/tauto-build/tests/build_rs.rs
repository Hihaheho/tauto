//! A Rust crate that compiles a tote from its `build.rs` and tests the
//! functions it gets.

mod support;

use std::path::{Path, PathBuf};
use std::process::Command;
use support::{Fixture, cargo, scratch, write};

fn callback_budget_source() -> &'static str {
    r#"import std::prelude::Shared

fn sum(&read: (u64) -> u64, size: u64): u64 ! {Div} {
  var i: u64 := 0
  var total: u64 := 0
  while i < size {
    total := total + read(i)
    i := i + 1
  }
  total
}

fn run(&read: (u64) -> u64, size: u64): Result(u64, Text) {
  handle {
    budget(steps: 1000) {
      Ok(sum(&(i) => read(i), size))
    }
  } with {
    exceeded(info), k => Err("exhausted")
  }
}

fn run_array(values: Array(u64)): Result(u64, Text) {
  handle {
    budget(steps: 1000) {
      Ok(sum(
        &(i) => match Array::get(values, i) {
          None => 0,
          Some(v) => v
        },
        Array::len(values)
      ))
    }
  } with {
    exceeded(info), k => Err("exhausted")
  }
}
"#
}

fn borrowed_callbacks_forward_through_budgeted_helpers() -> Fixture {
    let dir = scratch("callback-budget");
    host_crate(&dir, "");
    write(
        &dir,
        "build.rs",
        "fn main() { tauto_build::compile(\"callback-budget/Tauto.eure\").unwrap(); }\n",
    );
    write(
        &dir,
        "callback-budget/Tauto.eure",
        r#"
package { name = "callback-budget"
 version = "0.1.0" }
rust { exports = ["run", "run_array"] }
"#,
    );
    write(
        &dir,
        "callback-budget/src/main.taut",
        callback_budget_source(),
    );
    let (_, generated, warnings) =
        tauto_build::generate(&dir.join("callback-budget/Tauto.eure"), None).unwrap();
    assert!(warnings.is_empty(), "{warnings:?}");
    assert!(generated.contains("pub fn sum__o<'a>"));
    assert!(generated.contains("tauto_rt::budget::tick("));
    write(&dir, "src/lib.rs", "");
    write(
        &dir,
        "src/main.rs",
        r#"
include!(concat!(env!("OUT_DIR"), "/tauto_callback_budget.rs"));
fn main() {
    let values = [10_u64, 20, 30];
    let calls = std::cell::Cell::new(0);
    let read = |index: u64| {
        calls.set(calls.get() + 1);
        values[index as usize % values.len()]
    };
    assert_eq!(run(&read, 0).unwrap(), 0);
    assert_eq!(calls.get(), 0);
    assert_eq!(run(&read, 3).unwrap(), 60);
    assert_eq!(calls.get(), 3);
    calls.set(0);
    assert_eq!(&*run(&read, 10_000).unwrap_err(), "exhausted");
    assert!(calls.get() > 0 && calls.get() < 10_000);
    assert_eq!(run(&read, 3).unwrap(), 60);
    assert_eq!(run_array(tauto_rt::stdlib::vec_into_array(vec![])).unwrap(), 0);
    assert_eq!(run_array(tauto_rt::stdlib::vec_into_array(values.to_vec())).unwrap(), 60);
    assert_eq!(&*run_array(tauto_rt::stdlib::vec_into_array(vec![1; 10_000])).unwrap_err(), "exhausted");
    println!("borrowed callbacks retain budget checks");
}

"#,
    );
    dir
}

fn budgeted_callbacks_keep_each_invocation_borrow_local() -> Fixture {
    let dir = scratch("callback-budget-lifetimes");
    host_crate(&dir, "");
    write(
        &dir,
        "logic/Tauto.eure",
        r#"
package { name = "logic"
 version = "0.1.0" }
rust { exports = ["direct", "direct_loop", "nested", "text_direct", "text_forwarded", "text_owned"] }
"#,
    );
    let source = r#"import std::prelude::Shared

fn sum(&read: (u64) -> u64, size: u64): u64 ! {Div} {
  var i: u64 := 0
  var total: u64 := 0
  while i < size {
    total := total + read(i)
    i := i + 1
  }
  total
}

fn run(&read: (u64) -> u64, size: u64): Result(u64, Text) {
  handle {
    budget(steps: 1000) {
      Ok(sum(&(i) => read(i), size))
    }
  } with {
    exceeded(info), k => Err("exhausted")
  }
}

fn run_array(values: Array(u64)): Result(u64, Text) {
  handle {
    budget(steps: 1000) {
      Ok(sum(
        &(i) => match Array::get(values, i) {
          None => 0,
          Some(v) => v
        },
        Array::len(values)
      ))
    }
  } with {
    exceeded(info), k => Err("exhausted")
  }
}

fn r#direct(&read: (u64) -> u64, size: u64): Result(u64, Text) {
  handle { budget(steps: 1000) { Ok(sum(read, size)) } } with { exceeded(info), k => Err("exhausted") }
}
fn direct_loop(&read: (u64) -> u64, size: u64): Result(u64, Text) {
  handle { budget(steps: 1000) {
    var i: u64 := 0
    var total: u64 := 0
    while i < size {
      total := total + read(i)
      i := i + 1
    }
    Ok(total)
  } } with { exceeded(info), k => Err("exhausted") }
}
fn apply(&f: (u64) -> u64, value: u64): u64 { f(value) }
fn nested(&read: (u64) -> u64, size: u64): Result(u64, Text) {
  handle { budget(steps: 1000) {
    Ok(sum(&(i) => apply((j) => read(i + j), 0), size))
  } } with { exceeded(info), k => Err("exhausted") }
}
fn sum_text(&read: (&Text) -> u64, size: u64): u64 ! {Div} {
  var i: u64 := 0
  var total: u64 := 0
  while i < size {
    let text := concat("local", " text")
    total := total + read(&text)
    i := i + 1
  }
  total
}
fn sum_owned_text(&read: (Text) -> u64, size: u64): u64 ! {Div} {
  var i: u64 := 0
  var total: u64 := 0
  while i < size {
    total := total + read(concat("local", " text"))
    i := i + 1
  }
  total
}
fn text_owned(&read: (&Text) -> u64, size: u64): Result(u64, Text) {
  handle { budget(steps: 1000) {
    Ok(sum_owned_text((&text) => read(&text), size))
  } } with { exceeded(info), k => Err("exhausted") }
}
fn text_direct(&read: (&Text) -> u64, size: u64): Result(u64, Text) {
  handle { budget(steps: 1000) { Ok(sum_text(read, size)) } } with { exceeded(info), k => Err("exhausted") }
}
fn text_forwarded(&read: (&Text) -> u64, size: u64): Result(u64, Text) {
  handle { budget(steps: 1000) {
    Ok(sum_text((&text) => read(&text), size))
  } } with { exceeded(info), k => Err("exhausted") }
}
"#;
    write(&dir, "logic/src/main.taut", &source);
    write(&dir, "src/lib.rs", "");
    write(
        &dir,
        "src/main.rs",
        r#"
include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs"));
fn main() {
    let values = [10_u64, 20, 30];
    let read = |index: u64| values[index as usize % values.len()];
    for run in [direct, direct_loop, nested] {
        assert_eq!(run(&read, 3).unwrap(), 60);
        assert_eq!(&*run(&read, 10_000).unwrap_err(), "exhausted");
    }
    let calls = std::cell::Cell::new(0);
    let suffix = String::from("text");
    let read_text = |text: &tauto_rt::Text| {
        assert!(text.ends_with(&suffix));
        calls.set(calls.get() + 1);
        text.len() as u64
    };
    for run in [text_direct, text_forwarded, text_owned] {
        calls.set(0);
        assert_eq!(run(&read_text, 3).unwrap(), 30);
        assert_eq!(calls.get(), 3);
        calls.set(0);
        assert_eq!(&*run(&read_text, 10_000).unwrap_err(), "exhausted");
        assert!(calls.get() > 0 && calls.get() < 10_000);
    }
}
"#,
    );
    dir
}

#[test]
fn borrowed_budget_callback_cannot_escape_in_owned_data() {
    tauto_messages::install();
    let dir = scratch("callback-budget-no-escape");
    host_crate(&dir, "");
    write(
        &dir,
        "logic/Tauto.eure",
        r#"
package { name = "logic"
 version = "0.1.0" }
rust { exports = ["leak"] }
"#,
    );
    write(
        &dir,
        "logic/src/main.taut",
        r#"
struct Holder { callback: (u64) -> u64 ! {} }
fn leak(&read: (u64) -> u64 ! {}): Holder {
  Holder { callback: (i) => handle { budget(steps: 1000) { read(i) } } with { exceeded(info), k => 0 } }
}
"#,
    );
    write(
        &dir,
        "src/lib.rs",
        r#"
include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs"));
"#,
    );
    // Ordinary data results are checked by Rust, including borrows hidden
    // in callback fields; generation alone is not a no-escape check.
    let out = cargo(&dir, &["check", "--quiet", "--locked", "--offline"]);
    assert!(
        !out.status.success(),
        "an owned result must not retain the callback borrow"
    );
    let error = String::from_utf8_lossy(&out.stderr);
    assert!(
        error.contains("lifetime") && error.contains("'static"),
        "{error}"
    );
}

fn crates_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_path_buf()
}

fn host_crate(dir: &Fixture, deps: &str) {
    let c = crates_dir();
    // The versions and the cooldown of this repository.
    let root = c.parent().unwrap();
    for f in ["Cargo.lock", ".cargo/config.toml", "rust-toolchain.toml"] {
        write(dir, f, &std::fs::read_to_string(root.join(f)).unwrap());
    }
    write(
        dir,
        "Cargo.toml",
        &format!(
            "[package]\nname = \"host-{}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
             [dependencies]\ntauto-rt = {{ path = {:?} }}\n{deps}\n\
             [build-dependencies]\ntauto-build = {{ path = {:?} }}\n\n[workspace]\n",
            dir.name(),
            c.join("tauto-rt"),
            c.join("tauto-build"),
        ),
    );
    write(
        dir,
        "build.rs",
        "fn main() {\n    tauto_build::compile(\"logic/Tauto.eure\").unwrap();\n}\n",
    );
    write(
        dir,
        "src/lib.rs",
        "mod logic {\n    include!(concat!(env!(\"OUT_DIR\"), \"/tauto_logic.rs\"));\n}\n\
         pub use logic::*;\n\n\
         #[cfg(test)]\nmod tests {\n    #[test]\n    fn calls_the_tote() {\n        assert_eq!(super::add_one(41), 42);\n        assert_eq!(super::checked_value(41), 41);\n        assert_eq!(super::exported_identity(tauto_rt::Nat::from_u64(7)), tauto_rt::Nat::from_u64(7));\n        assert_eq!(super::shouted(&tauto_rt::Text::from(\"hi\")).to_string(), \"HI\");\n    }\n}\n",
    );
    write(
        dir,
        "logic/Tauto.eure",
        "package {\n  name = \"logic\"\n  version = \"0.1.0\"\n}\n\nrust {\n  bridge = \"bridge\"\n  extern {\n    upper = \"logic_bridge::upper\"\n  }\n}\n",
    );
    write(
        dir,
        "logic/src/main.taut",
        r#"extern {
  fn upper(&t: Text): Text
}
fn exported_identity(n: Nat): Nat { n }
fn identity(n: Nat): Nat { n }
theorem identity_zero(): identity(Zero) = Zero { Refl }
fn checked_value(n: u64): u64 { U64::of_nat(identity(Nat::of_u64(n))) }
fn add_one(n: i64): i64 { n + 1 }
fn shouted(&t: Text): Text { upper(&t) }
"#,
    );
    write(
        dir,
        "logic/bridge/Cargo.toml",
        "[package]\nname = \"logic-bridge\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[dependencies]\n",
    );
    write(
        dir,
        "logic/bridge/src/lib.rs",
        "pub fn upper(t: &str) -> String {\n    t.to_uppercase()\n}\n",
    );
}

fn a_crate_calls_the_functions_of_a_tote() -> Fixture {
    let dir = scratch("works");
    host_crate(&dir, "logic-bridge = { path = \"logic/bridge\" }\n");
    dir
}

#[test]
fn a_missing_dependency_is_an_error() {
    tauto_messages::install();
    let dir = scratch("missing-bridge");
    host_crate(&dir, "");
    let out = cargo(&dir, &["build", "--quiet"]);
    assert!(!out.status.success());
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("Tauto.eure needs the rust dependency logic-bridge; add it to Cargo.toml"),
        "{err}"
    );
}

#[test]
fn a_rust_host_reads_runtime_ast_and_diagnostics_without_tote_files() {
    tauto_messages::install();
    let dir = scratch("syntax-runtime");
    host_crate(&dir, "");
    write(
        &dir,
        "logic/Tauto.eure",
        "package {\n name = \"logic\"\n version = \"0.1.0\"\n}\n",
    );
    let fixtures = crates_dir().join("tauto/tests/syntax_fixtures");
    let grammar = std::fs::read_to_string(fixtures.join("ident.par")).unwrap();
    let tables =
        tauto::syntax::with_search_dirs(vec![fixtures], || tauto::syntax::load_tables(&grammar))
            .unwrap();
    write(
        &dir,
        &format!("logic/.tauto-syntax/{}.tables", tables.grammar_sha256()),
        tables.source(),
    );
    let declarations = r#"import std::prelude::Macro
syntax!(ident, ```par
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
"#;
    assert!(declarations.contains(&tauto::syntax::generated_clause("ident", &tables, false)));
    let keyword_grammar =
        std::fs::read_to_string(crates_dir().join("tauto/tests/syntax_fixtures/keywords.par"))
            .unwrap();
    let keyword_tables = tauto::syntax::with_search_dirs(
        vec![crates_dir().join("tauto/tests/syntax_fixtures")],
        || tauto::syntax::load_tables(&keyword_grammar),
    )
    .unwrap();
    write(
        &dir,
        &format!(
            "logic/.tauto-syntax/{}.tables",
            keyword_tables.grammar_sha256()
        ),
        keyword_tables.source(),
    );
    assert!(declarations.contains(&tauto::syntax::generated_clause(
        "keywords",
        &keyword_tables,
        false
    )));
    write(&dir, "logic/src/main.taut", declarations);
    write(&dir, "src/lib.rs", "");
    write(
        &dir,
        "src/main.rs",
        r#"
mod logic { include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs")); }
fn main() {
    let text = tauto_rt::Text::from("日本語=12");
    let ast = logic::ident__parse(text).unwrap();
    assert_eq!(&*ast.name.text, "日本語");
    assert_eq!(ast.name.span.id, 0);
    assert!(format!("{:?}", ast.name.span).contains("0"));
    assert_eq!(&*ast.value.text, "12");
    assert_eq!(ast.value.span.id, 10);
    let bad = tauto_rt::Text::from("日本語=@");
    let diag = match logic::ident__parse(bad) { Err(diag) => diag, Ok(_) => panic!("invalid input") };
    assert!(format!("{diag:?}").contains(&*diag.message));
    assert_eq!(diag.at, 10);
    assert_eq!(&*diag.code, "macro.syntax_error");
    assert_eq!(&*diag.message, "macro-syntax-not-a-token");
    assert!(matches!(diag.expected, logic::List::Nil));
    let eof = tauto_rt::Text::from("日本語=");
    let diag = match logic::ident__parse(eof) { Err(diag) => diag, Ok(_) => panic!("missing value") };
    assert_eq!(diag.at, 10);
    match diag.expected { logic::List::Cons(name, _) => assert_eq!(&*name, "Value"), _ => panic!("expected terminal") }
    for (input, expected) in [("[true]", "true"), ("[false]", "false")] {
        let parsed = match logic::keywords__parse(tauto_rt::Text::from(input)) { Ok(tree) => tree, Err(_) => panic!("valid keyword") };
        let token = match &*parsed.value {
            logic::keywords__Value::True { span: _, true_field } => true_field,
            logic::keywords__Value::False { span: _, false_field } => false_field,
        };
        assert_eq!(&*token.text, expected);
        assert_eq!(token.span.id, 1);
    }
    assert!(logic::keywords__parse(tauto_rt::Text::from("[maybe]")).is_err());
    println!("native AST and diagnostics are readable");
}
"#,
    );
    let out = support::cargo_with(
        &dir,
        &["build", "--quiet", "--message-format=json"],
        |path, out| {
            assert!(
                out.status.success(),
                "{}\n{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            let binary = String::from_utf8(out.stdout)
                .unwrap()
                .lines()
                .filter_map(|line| {
                    let message: serde_json::Value = serde_json::from_str(line).ok()?;
                    if message["reason"] == "compiler-artifact"
                        && message["target"]["kind"]
                            .as_array()
                            .is_some_and(|kinds| kinds.iter().any(|kind| kind == "bin"))
                    {
                        message["executable"].as_str().map(PathBuf::from)
                    } else {
                        None
                    }
                })
                .next()
                .expect("Cargo reported the host executable");
            let invocation = support::invocation_dir();
            let standalone = invocation.join("standalone");
            std::fs::copy(binary, &standalone).unwrap();
            let sources = path.join("logic");
            let hidden = invocation.join("logic");
            std::fs::rename(&sources, &hidden).unwrap();
            let out = Command::new(&standalone).current_dir(path).output();
            std::fs::rename(hidden, sources).unwrap();
            std::fs::remove_dir_all(invocation).unwrap();
            out.unwrap()
        },
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "native AST and diagnostics are readable\n"
    );
}

fn selected_budget_wrapper_is_callable_without_helper_warnings() -> Fixture {
    let dir = scratch("selected-exports");
    host_crate(&dir, "");
    write(
        &dir,
        "logic/Tauto.eure",
        r#"
package { name = "logic"
 version = "0.1.0" }
rust { exports = ["parse_with_budget"] }
"#,
    );
    write(
        &dir,
        "logic/src/main.taut",
        r#"
fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
fn parse_with_budget(steps: i64): Result(i64, Text) {
  handle { budget(steps: steps) { visit(2); Ok(42) } } with { exceeded(info), k => Err("exceeded") }
}
"#,
    );
    let (_, generated, warnings) =
        tauto_build::generate(&dir.join("logic/Tauto.eure"), None).unwrap();
    assert!(warnings.is_empty(), "{warnings:?}");
    assert!(
        !generated
            .split("pub mod api")
            .nth(1)
            .unwrap()
            .contains("pub fn visit")
    );
    write(
        &dir,
        "src/lib.rs",
        r#"
include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs"));
#[test]
fn budget_is_preserved() {
    assert_eq!(parse_with_budget(1000).unwrap(), 42);
    assert_eq!(&*parse_with_budget(0).unwrap_err(), "exceeded");
}
"#,
    );
    dir
}

fn rust_borrows_callbacks_for_one_call_without_static_captures() -> Fixture {
    let dir = scratch("borrowed-callbacks");
    host_crate(&dir, "");
    write(
        &dir,
        "logic/Tauto.eure",
        r#"
package { name = "logic"
 version = "0.1.0" }
rust { exports = ["apply", "read_first", "read_if", "twice", "both", "produce", "notify", "text_value", "borrow_text", "names"] }
"#,
    );
    write(
        &dir,
        "logic/src/main.taut",
        r#"
fn names(callback: u64, &arg0: (u64) -> u64): u64 { arg0(callback) }
fn apply(&f: (u64) -> u64, value: u64): u64 { f(value) }
fn read_first(&f: (u64) -> u64): u64 { f(0) }
fn read_if(&f: (u64) -> u64, enabled: Bool): u64 { if enabled { f(0) } else { 0 } }
fn twice(&f: (u64) -> u64, value: u64): u64 { f(value) + f(value) }
fn both(&left: (u64) -> u64, &right: (u64, u64) -> u64): u64 { right(left(0), left(1)) }
fn produce(&f: () -> u64): u64 { f() }
fn notify(&f: () -> Unit, value: u64): u64 { f(); value }
fn text_value(&f: (Option(Text)) -> Option(Text), value: Option(Text)): Option(Text) { f(value) }
fn borrow_text(&f: (&Text) -> Text, &value: Text): Text { f(&value) }
"#,
    );
    write(
        &dir,
        "src/lib.rs",
        r#"
mod logic { include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs")); }
pub use logic::*;
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn stack_borrow_and_lazy_reads() {
        let values = [10_u64, 20, 30];
        let read = |index: u64| values[index as usize];
        assert_eq!(names(1, &read), 20);
        assert_eq!(apply(&read, 1), 20);
        assert_eq!(apply(&read, 2), 30);
        assert_eq!(twice(&read, 0), 20);
        assert_eq!(both(&read, &|a, b| a + b), 30);
        let calls = std::cell::Cell::new(0);
        let lazy = |index: u64| {
            calls.set(calls.get() + 1);
            assert_eq!(index, 0, "only the required prefix may be read");
            values[index as usize]
        };
        assert_eq!(read_if(&lazy, false), 0);
        assert_eq!(calls.get(), 0);
        assert_eq!(read_first(&lazy), 10);
        assert_eq!(calls.get(), 1);
        assert_eq!(produce(&|| values[1]), 20);
        assert_eq!(notify(&|| (), 1), 1);
        let text = tauto_rt::Text::from("日本語");
        assert_eq!(text_value(&|value| value, Some(text.clone())).unwrap().to_string(), "日本語");
        assert!(text_value(&|value| value, None).is_none());
        assert_eq!(borrow_text(&|value| value.clone(), &text).to_string(), "日本語");
    }
}
"#,
    );
    dir
}

#[test]
fn rust_rejects_a_callback_requiring_a_mutable_receiver() {
    tauto_messages::install();
    let dir = rust_borrows_callbacks_for_one_call_without_static_captures();
    // The facade accepts Fn, not a callback requiring a mutable receiver.
    write(
        &dir,
        "src/lib.rs",
        r#"
mod logic { include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs")); }
fn rejected() {
    let mut count = 0_u64;
    let mut callback = |_: u64| { count += 1; count };
    logic::apply(&mut callback, 0);
}
"#,
    );
    let out = cargo(&dir, &["check", "--quiet"]);
    assert!(!out.status.success());
    let error = String::from_utf8_lossy(&out.stderr);
    assert!(error.contains("FnMut") && error.contains("Fn"), "{error}");
}

/// Independent generated modules share one host build, not a language namespace.
#[test]
fn positive_hosts_compile_and_run_together() {
    tauto_messages::install();
    let fixtures = [
        a_crate_calls_the_functions_of_a_tote(),
        borrowed_callbacks_forward_through_budgeted_helpers(),
        budgeted_callbacks_keep_each_invocation_borrow_local(),
        selected_budget_wrapper_is_callable_without_helper_warnings(),
        rust_borrows_callbacks_for_one_call_without_static_captures(),
    ];
    let host = scratch("positive-hosts");
    host_crate(&host, "logic-bridge = { path = \"works/logic/bridge\" }\n");
    host.remove_prefix("logic/");
    let mut build = String::from("fn main() {\n");
    let mut source = String::new();
    for fixture in fixtures {
        let name = fixture.name();
        let module = name.replace('-', "_");
        let package = if name == "works" { "logic" } else { name };
        let tote = if name == "callback-budget" {
            "callback-budget"
        } else {
            "logic"
        };
        for (path, mut text) in fixture.files() {
            if path.starts_with(&format!("{tote}/"))
                && (name == "works" || !path.starts_with(&format!("{tote}/bridge/")))
            {
                if path == format!("{tote}/Tauto.eure") {
                    text = text.replace("name = \"logic\"", &format!("name = {package:?}"));
                }
                write(&host, &format!("{name}/{path}"), &text);
            }
        }
        build.push_str(&format!(
            "tauto_build::compile({:?}).unwrap();\n",
            format!("{name}/{tote}/Tauto.eure")
        ));
        let mut body = fixture.read("src/lib.rs");
        if let Some(main) = fixture.get("src/main.rs") {
            body.push_str(&main.replace("fn main()", "#[test] fn runs_the_host()"));
        }
        body = body.replace(
            "tauto_logic.rs",
            &format!("tauto_{}.rs", package.replace('-', "_")),
        );
        source.push_str(&format!("mod {module} {{\n{body}\n}}\n"));
    }
    build.push_str("}\n");
    write(&host, "build.rs", &build);
    write(&host, "src/lib.rs", &source);
    let out = cargo(&host, &["test", "--quiet", "--locked", "--offline"]);
    assert!(
        out.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(!String::from_utf8_lossy(&out.stderr).contains("not exposed to Rust"));
}
