//! `tauto check --tote DIR`: the tote's own declarations with its
//! dependencies, and of the dependencies only what did not check. The tote's
//! own declarations include its files outside `sources`, such as proofs.

use std::path::{Path, PathBuf};

use tauto::report::{Status, check_tote_report};

fn tote(base: &Path, name: &str, deps: &str, src: &str) -> PathBuf {
    let dir = base.join(name);
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Tauto.eure"),
        format!(
            "package {{\n  name = \"{name}\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}}\n{deps}"
        ),
    )
    .unwrap();
    std::fs::write(dir.join("src").join(format!("{name}.taut")), src).unwrap();
    dir
}

fn base(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tauto-tote-check-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

const DEP: &str = "dependencies {\n  lib { path = \"../lib\" }\n}\n";

#[test]
fn own_declarations_are_listed_and_dependencies_counted() {
    tauto_messages::install();
    let b = base("own");
    tote(
        &b,
        "lib",
        "",
        r#"import std::Nat
theorem lib_t(): Nat::max(Zero, Zero) = Zero { Refl }
"#,
    );
    let app = tote(
        &b,
        "app",
        DEP,
        r#"theorem app_t(): lib_one() = Succ(Zero) { Refl }
"#,
    );
    std::fs::write(
        b.join("lib/src/one.taut"),
        r#"def lib_one(): Nat := Succ(Zero)
"#,
    )
    .ok();
    let r = check_tote_report(&app).unwrap();
    let text = r.text(false);
    assert!(text.contains("ok      app_t"), "{text}");
    assert!(!text.contains("lib_t"), "{text}");
    assert!(text.contains("not shown (--verbose shows them)"), "{text}");
    assert!(r.text(true).contains("lib_t"));
}

#[test]
fn a_failure_in_a_dependency_is_shown() {
    tauto_messages::install();
    let b = base("fail");
    tote(
        &b,
        "lib",
        "",
        r#"theorem lib_bad(): Succ(Zero) = Zero { Refl }
"#,
    );
    let app = tote(
        &b,
        "app",
        DEP,
        r#"theorem app_t(): Zero = Zero { Refl }
"#,
    );
    let r = check_tote_report(&app).unwrap();
    assert_eq!(r.report.status(), Status::Failed);
    let text = r.text(false);
    assert!(text.contains("FAILED  lib_bad"), "{text}");
    assert!(text.ends_with("1 ok, 1 failed, 0 incomplete\n"), "{text}");
}

#[test]
fn files_outside_sources_are_checked() {
    tauto_messages::install();
    let b = base("others");
    let app = tote(
        &b,
        "app",
        "",
        r#"theorem app_t(): Zero = Zero { Refl }
"#,
    );
    for (dir, name, fixture) in [
        ("proof", "p.taut", "tote-check-proof"),
        ("examples", "e.taut", "tote-check-example-bad"),
    ] {
        std::fs::create_dir_all(app.join(dir)).unwrap();
        std::fs::write(
            app.join(dir).join(name),
            case_inputs::fixture_static("inputs/tauto.eure", fixture),
        )
        .unwrap();
    }
    // A nested tote is not part of this one.
    tote(
        &app,
        "nested",
        "",
        r#"theorem lib_bad(): Succ(Zero) = Zero { Refl }
"#,
    );
    let r = check_tote_report(&app).unwrap();
    let text = r.text(false);
    assert!(text.contains("ok      proof_t"), "{text}");
    assert!(text.contains("FAILED  example_bad"), "{text}");
    assert!(!text.contains("lib_bad"), "{text}");
    assert_eq!(r.report.status(), Status::Failed);
}

#[test]
fn a_copied_std_file_does_not_take_the_language_type() {
    tauto_messages::install();
    let b = base("std-copy");
    let app = tote(
        &b,
        "app",
        "",
        r#"import std::Text
theorem smoke(): Text::concat("a", "b") = "ab" { Refl }
"#,
    );
    std::fs::create_dir_all(app.join("std")).unwrap();
    std::fs::write(
        app.join("std/Text.taut"),
        r#"inductive Text: Type =>
  fn Text::beq, theorem Text::beq_refl, theorem Text::beq_sound, theorem Text::deq {
  Mk(bytes: List(Nat)): Text
}
"#,
    )
    .unwrap();
    let r = check_tote_report(&app).unwrap();
    let text = r.text(true);
    assert!(text.contains("ok      smoke"), "{text}");
    assert!(!text.contains("FAILED  std::"), "{text}");
    assert!(!text.contains("FAILED  Text"), "{text}");
    assert_eq!(r.report.status(), Status::Ok, "{text}");
}

#[test]
fn a_skipped_declaration_is_not_counted_as_ok() {
    tauto_messages::install();
    let b = base("skipped");
    let app = tote(&b, "app", "", "fn greet(n: Nat): Text {\n  \"hi\"\n}\n");
    let r = check_tote_report(&app).unwrap();
    let text = r.text(false);
    assert!(text.contains("skipped greet"), "{text}");
    assert!(!text.contains("ok      greet"), "{text}");
    assert!(
        text.contains("0 ok, 0 failed, 0 incomplete, 1 skipped (not checked by the kernel)"),
        "{text}"
    );
}

#[test]
fn a_builtin_whose_std_model_is_not_imported_here_is_warned() {
    tauto_messages::install();
    // The dependency imports `std::Text`; the tote does not, so its
    // `text_len` is the prelude's and `len` runs as written.
    let b = base("unchecked-builtin");
    tote(
        &b,
        "lib",
        "",
        "import std::Text\nfn size(s: Text): Nat { Text::len(s) }\n",
    );
    let app = tote(
        &b,
        "app",
        DEP,
        "import lib::lib\nfn len(s: Text): Nat { Text::len(s) }\nfn twice(s: Text): Nat { len(s) }\n",
    );
    let text = check_tote_report(&app).unwrap().text(false);
    assert!(text.contains("warning unchecked_builtin: "), "{text}");
    assert!(
        text.contains("`len` runs as written and is not checked by the kernel: it calls the prelude's built-in `text_len`, not `std::Text::text_len`"),
        "{text}"
    );
    assert!(text.contains("`import std::Text` in this file"), "{text}");
    // Only where the chain starts: `twice` runs as written because of `len`.
    assert_eq!(
        text.matches("warning unchecked_builtin").count(),
        1,
        "{text}"
    );
    // Importing the model there has the kernel check it, and says nothing.
    tote(
        &b,
        "app",
        DEP,
        "import std::Text\nimport lib::lib\nfn len(s: Text): Nat { Text::len(s) }\n",
    );
    let text = check_tote_report(&app).unwrap().text(false);
    assert!(text.contains("ok      len"), "{text}");
    assert!(!text.contains("unchecked_builtin"), "{text}");
}

#[test]
fn a_program_reading_no_std_model_is_not_warned() {
    tauto_messages::install();
    // A program that means the prelude's `text_len` and reads no model of it.
    let b = base("prelude-builtin");
    let app = tote(&b, "app", "", "fn len(s: Text): u64 { Text::len(s) }\n");
    let text = check_tote_report(&app).unwrap().text(false);
    assert!(text.contains("skipped len"), "{text}");
    assert!(!text.contains("unchecked_builtin"), "{text}");
}

#[test]
fn a_dependency_runs_with_names_the_tote_declares_too() {
    tauto_messages::install();
    // The tote declares `Style`, `AStart`, `AEnd` and `rect` as its dependency
    // does: the dependency's are renamed to their full names, and its
    // effectful code, which runs as written, still means them.
    let b = base("clash");
    let lib = tote(
        &b,
        "lib",
        "",
        r#"pub(open) inductive Style: Type {
  Mk(w: Nat): Style
}

pub(open) inductive Rect: Type {
  Mk(x: Nat, y: Nat): Rect
}

pub(open) inductive Align: Type {
  AStart: Align
  AEnd: Align
}

pub fn st_w(s: Style): Nat {
  match s: Nat {
    Mk(w) => w
  }
}
"#,
    );
    std::fs::write(
        lib.join("src/use.taut"),
        r#"import "lib.taut"

fn width(s: Style): Nat ! {io} {
  st_w(s)
}

fn left(r: Rect): Nat ! {io} {
  match r {
    Mk(x, y) => x
  }
}

fn start(a: Align): Nat ! {io} {
  match a {
    AStart => Zero
    AEnd => Succ(Zero)
  }
}
"#,
    )
    .unwrap();
    let app = tote(&b, "app", DEP, "");
    std::fs::remove_file(app.join("src/app.taut")).unwrap();
    std::fs::write(
        app.join("src/main.taut"),
        r#"enum Style {
  Plain,
}

enum Pos {
  AStart,
  AEnd,
}

fn rect(x: nat): nat {
  x
}

fn main(): Nat {
  Zero
}
"#,
    )
    .unwrap();
    let r = check_tote_report(&app).unwrap();
    let text = r.text(true);
    assert!(!text.contains("FAILED"), "{text}");
    assert!(
        text.contains("ok      width") || text.contains("skipped width"),
        "{text}"
    );
}

#[test]
fn a_file_of_the_tote_that_does_not_import_the_std_model_is_warned() {
    // `app.taut` imports `std::Text`; `other.taut` of the same tote does
    // not, so its `text_len` is the prelude's and `len` runs as written.
    let b = base("unchecked-builtin-same-tote");
    let app = tote(
        &b,
        "app",
        "",
        "import std::Text\nfn size(s: Text): Nat { Text::len(s) }\n",
    );
    std::fs::write(
        app.join("src/other.taut"),
        "fn len(s: Text): Nat { Text::len(s) }\n",
    )
    .unwrap();
    let text = check_tote_report(&app).unwrap().text(false);
    assert!(text.contains("ok      size"), "{text}");
    assert!(
        text.contains("`len` runs as written and is not checked by the kernel: it calls the prelude's built-in `text_len`, not `std::Text::text_len`"),
        "{text}"
    );
    assert_eq!(
        text.matches("warning unchecked_builtin").count(),
        1,
        "{text}"
    );
}

#[test]
fn a_std_declaration_another_file_of_the_tote_imports_is_not_seen_here() {
    // `text_concat` is the standard library's only, not a built-in of the
    // prelude: `app.taut` imports it, `other.taut` does not and so does not
    // mean it.
    let b = base("std-not-imported-same-tote");
    let app = tote(
        &b,
        "app",
        "",
        "import std::Text\nfn twice(s: Text): Text { Text::concat(s, s) }\n",
    );
    std::fs::write(
        app.join("src/other.taut"),
        "fn cat(s: Text): Text { Text::concat(s, s) }\n",
    )
    .unwrap();
    let r = check_tote_report(&app).unwrap();
    let text = r.text(false);
    assert!(text.contains("ok      twice"), "{text}");
    assert_eq!(
        text.matches("`text_concat` is declared by `std::Text`, which this file does not import")
            .count(),
        1,
        "{text}"
    );
    assert_eq!(r.report.status(), Status::Failed, "{text}");
    // Importing it there has the kernel check it.
    std::fs::write(
        app.join("src/other.taut"),
        "import std::Text\nfn cat(s: Text): Text { Text::concat(s, s) }\n",
    )
    .unwrap();
    let text = check_tote_report(&app).unwrap().text(false);
    assert!(text.contains("ok      cat"), "{text}");
    assert!(text.contains("ok      twice"), "{text}");
}

#[test]
fn a_std_declaration_a_dependency_imports_is_not_seen_here() {
    let b = base("std-not-imported-dependency");
    tote(
        &b,
        "lib",
        "",
        "import std::Text\npub fn twice(s: Text): Text { Text::concat(s, s) }\n",
    );
    let app = tote(
        &b,
        "app",
        DEP,
        "import lib::lib\nfn cat(s: Text): Text { Text::concat(s, s) }\n",
    );
    let r = check_tote_report(&app).unwrap();
    let text = r.text(false);
    assert_eq!(
        text.matches("`text_concat` is declared by `std::Text`, which this file does not import")
            .count(),
        1,
        "{text}"
    );
    assert_eq!(r.report.status(), Status::Failed, "{text}");
}

#[test]
fn text_equality_of_a_dependency_checks_when_the_tote_declares_text_eq_too() {
    // The tote's own `text_eq` has `std::Text`'s renamed to its full name;
    // the dependency's `==` on `Text` still means the standard library's.
    let b = base("text-eq-renamed");
    tote(
        &b,
        "lib",
        "",
        "import std::Text\npub fn same(a: Text, b: Text): Bool { a == b }\n",
    );
    let app = tote(
        &b,
        "app",
        DEP,
        "import lib::lib\nfn Text::eq(a: Nat): Nat { a }\nfn f(s: Text): Bool { same(s, s) }\n",
    );
    let text = check_tote_report(&app).unwrap().text(true);
    assert!(!text.contains("FAILED"), "{text}");
    assert!(text.contains("ok      same"), "{text}");
    assert!(text.contains("ok      f"), "{text}");
}

#[test]
fn what_a_dependency_imports_does_not_reach_the_totes_that_use_it() {
    // `mid` imports `deep`, which declares `Node`, `Key` and the prelude's
    // `text_of_bytes` too. `app` declares `Node` and `Key` and depends on
    // `mid`; `top` depends on `app`. Neither sees what `mid` imports, and
    // `mid`'s `Node` stays `deep`'s.
    let b = base("leak");
    tote(
        &b,
        "deep",
        "",
        "pub(open) struct Node { x: u64 }\npub(open) enum Key {\n  kstr(u64)\n}\npub fn Text::of_bytes(n: u64): Option(Text) { None }\npub fn mk(n: u64): Node { Node { x: n } }\n",
    );
    tote(
        &b,
        "mid",
        "dependencies {\n  deep { path = \"../deep\" }\n}\n",
        "import deep::deep\npub fn mid_x(n: Node): u64 { n.x }\npub fn mid_full(n: deep::src::deep::Node): u64 { n.x }\npub fn mid_go(n: u64): u64 { mid_x(mk(n)) + mid_full(mk(n)) }\n",
    );
    let app = tote(
        &b,
        "app",
        "dependencies {\n  mid { path = \"../mid\" }\n}\n",
        "pub(open) struct Node { y: u64 }\npub(open) enum Key {\n  key(u64)\n}\npub fn node_y(n: Node): u64 { n.y }\n",
    );
    std::fs::write(
        app.join("src/cli.taut"),
        "import \"app.taut\"\nimport mid::mid\npub fn run(n: Node): u64 { node_y(n) + mid_go(1) }\npub fn readable(b: Bytes): Bool {\n  match Text::of_bytes(b) {\n    Some(t) => true\n    None => false\n  }\n}\n",
    )
    .unwrap();
    let top = tote(
        &b,
        "top",
        "dependencies {\n  app { path = \"../app\" }\n}\n",
        "import app::app\npub fn scene(): List(Node) { [Node { y: 1 }] }\npub fn same(k: Key): Key { k }\n",
    );
    for dir in [&app, &top] {
        let text = check_tote_report(dir).unwrap().text(true);
        assert!(!text.contains("FAILED"), "{text}");
    }
}

/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn fixture_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
        ("inputs/tauto.eure", "tote-check-proof") => r#"import "../src/app.taut"
theorem proof_t(): Zero = Zero { Refl }
"#,
        ("inputs/tauto.eure", "tote-check-example-bad") => r#"theorem example_bad(): Succ(Zero) = Zero { Refl }
"#,
        _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn fixture(file: &str, name: &str) -> String {
        fixture_static(file, name).to_string()
    }
}
