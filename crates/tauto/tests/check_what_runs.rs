//! `tauto check` rejects what `tauto run` rejects before running: the kernel
//! accepts a `Nat` where the program's Nib wants a `u64`, and only the
//! extracted program says it does not fit.

use std::path::PathBuf;

use tauto::check::Verdict;
use tauto::report::{Report, Status, check_report, check_tote_report};

const NAT_IN_U64_FIELD: &str = "struct Box { n: u64 }\n\n\
fn count(k: Nat): Nat {\n  k\n}\n\n\
let b := Box { n: count(3) }\n\
show(&b.n)\n";

/// The same mistake inside `main`: the top level of a tote's module may not
/// perform (`show` writes to stdout), so a tote's source puts it in an entry.
const NAT_IN_U64_FIELD_IN_MAIN: &str = "struct Box { n: u64 }\n\n\
fn count(k: Nat): Nat {\n  k\n}\n\n\
fn main(): Unit {\n  let b := Box { n: count(3) }\n  show(&b.n)\n}\n";

fn dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tauto-check-runs-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn failure(report: &Report) -> String {
    report
        .entries
        .iter()
        .find_map(|e| match &e.entry.verdict {
            Verdict::Failed(d) => Some(d.message.to_string()),
            _ => None,
        })
        .unwrap_or_default()
}

#[test]
fn a_nat_put_in_a_u64_field_is_rejected() {
    tauto_messages::install();
    let path = dir("field").join("main.taut");
    std::fs::write(&path, NAT_IN_U64_FIELD).unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
    assert!(
        failure(&report).contains("field `n`: expected u64, found nat, a different type"),
        "{}",
        report.json().render()
    );
}

#[test]
fn a_nat_passed_for_a_u64_is_rejected() {
    tauto_messages::install();
    let path = dir("argument").join("main.taut");
    std::fs::write(
        &path,
        "fn count(k: Nat): Nat {\n  k\n}\n\n\
         fn f(x: u64): u64 {\n  x\n}\n\n\
         show(&f(count(3)))\n",
    )
    .unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
    assert!(failure(&report).contains("expected u64, found nat, a different type"));
}

#[test]
fn a_nat_kept_in_a_nat_field_checks() {
    tauto_messages::install();
    let path = dir("ok").join("main.taut");
    std::fs::write(
        &path,
        "struct Box { n: Nat }\n\n\
         fn count(k: Nat): Nat {\n  k\n}\n\n\
         let b := Box { n: count(3) }\n\
         show(&b.n)\n",
    )
    .unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok, "{}", report.json().render());
}

#[test]
fn a_tote_is_rejected_as_run_reads_it() {
    tauto_messages::install();
    let root = dir("tote").join("box-tote");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("Tauto.eure"),
        "package {\n  name = \"box-tote\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    std::fs::write(root.join("src/main.taut"), NAT_IN_U64_FIELD_IN_MAIN).unwrap();
    let report = check_tote_report(&root).unwrap().report;
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
    assert!(failure(&report).contains("field `n`: expected u64, found nat, a different type"));
}

/// An effect the file declares is read in proofs whatever its name: one
/// named like a prelude function (`expect`) is the file's effect, not taken
/// for that function and left to run as written.
#[test]
fn an_effect_named_like_a_prelude_function_is_read_in_proofs() {
    tauto_messages::install();
    let path = dir("effect-name").join("main.taut");
    std::fs::write(
        &path,
        "effect expect(n: Nat): Unit\n\n\
         fn a(n: Nat): Unit ! {expect} { perform expect(n) }\n",
    )
    .unwrap();
    let report = check_report(&path, None).unwrap();
    let a = report
        .entries
        .iter()
        .find(|e| e.entry.name.as_str() == "a")
        .expect("a is reported");
    assert!(
        matches!(a.entry.verdict, Verdict::Checked { .. }),
        "{}",
        report.json().render()
    );
}

#[test]
fn a_top_level_let_does_not_take_a_name_of_an_imported_file() {
    tauto_messages::install();
    let d = dir("let-leak");
    std::fs::write(
        d.join("lib.taut"),
        "inductive Mark: Type {\n  Marked: Mark\n  Unmarked: Mark\n}\n\n\
         fn mark_of(y: Bool): Mark {\n  ⊢ Mark from match y {\n    true => Marked\n    false => Unmarked\n  }\n}\n\n\
         theorem mark_true(): mark_of(true) = Marked {\n  Refl\n}\n",
    )
    .unwrap();
    let path = d.join("main.taut");
    std::fs::write(
        &path,
        "import \"lib.taut\"\n\nlet marked := 1\nshow(&marked)\n",
    )
    .unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok, "{}", report.json().render());
}

const NAT_FOR_U64: &str = "fn count(k: Nat): Nat {\n  k\n}\n\n\
pub fn f(n: Nat): U8 {\n  U8::of_u64(count(n))\n}\n";

/// A file with only a `main` function is a program `run FILE` takes, in a
/// tote or not.
#[test]
fn a_file_with_a_main_function_is_checked_as_run_reads_it() {
    let path = dir("main-fn").join("main.taut");
    std::fs::write(
        &path,
        format!("{NAT_FOR_U64}\nfn main(): Unit {{\n  ()\n}}\n"),
    )
    .unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
    assert!(
        failure(&report).contains("expected u64, found nat, a different type"),
        "{}",
        report.json().render()
    );
}

/// A tote's file without a program of its own is checked as part of the
/// tote's program, for the errors written in it.
#[test]
fn a_file_of_a_tote_is_checked_as_its_program() {
    let tote = dir("tote-file").join("tote-file");
    std::fs::create_dir_all(tote.join("src")).unwrap();
    std::fs::write(
        tote.join("Tauto.eure"),
        "package {\n  name = \"tote-file\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    std::fs::write(tote.join("src/handler.taut"), NAT_FOR_U64).unwrap();
    std::fs::write(tote.join("src/main.taut"), "fn main(): Unit {\n  ()\n}\n").unwrap();
    let report = check_report(&tote.join("src/handler.taut"), None).unwrap();
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
    assert!(
        failure(&report).contains("expected u64, found nat, a different type"),
        "{}",
        report.json().render()
    );
    // The program's file is checked alone, as `run FILE` reads it.
    let main = check_report(&tote.join("src/main.taut"), None).unwrap();
    assert_eq!(main.status(), Status::Ok, "{}", main.json().render());
}

/// A stray `pub` before a comment is not a declaration; `run` reads it as a
/// name, and a keyword is not one, so `check` stops at reading it too.
#[test]
fn a_stray_pub_is_rejected() {
    tauto_messages::install();
    let path = dir("stray-pub").join("main.taut");
    std::fs::write(&path, "pub // a comment\nfn main(): Unit {\n  ()\n}\n").unwrap();
    // A file that does not parse is a failed report of its own, at the place of the error.
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Failed, "a stray `pub` was checked");
    let json = report.json().render();
    assert!(
        json.contains("`pub` is a keyword and cannot be used as a name"),
        "{json}"
    );
}

#[test]
fn invalid_native_type_function_is_reported_by_check() {
    tauto_messages::install();
    let path = dir("native-type-function").join("main.taut");
    std::fs::write(&path, "struct Payload { value: nat }\nfn Broken(A: Type): Type { Payload { value: 0 } }\nshow(&0)\n").unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
    assert!(
        failure(&report).contains("native type function body must be a type expression"),
        "{}",
        report.json().render()
    );
}

/// A class method used at a type parameter the instance needs to be shared is
/// found in the call the program writes, not in the code the class expansion
/// makes for it: the error has a place in the file.
#[test]
fn an_affine_type_parameter_for_an_instance_is_placed_at_its_call() {
    tauto_messages::install();
    let path = dir("instance-bound").join("main.taut");
    std::fs::write(
        &path,
        "import std::base\n\n\
         pub(open) class Merge(A: Type) {\n  fn merge(a: A, b: A): A\n}\n\n\
         pub(open) inductive Box(K: Type): Type {\n  Mk(items: List(K)): Box(K)\n}\n\n\
         instance<K: Shared> Merge(Box(K)) {\n  fn merge(a: Box(K), b: Box(K)): Box(K) {\n    a\n  }\n}\n\n\
         pub fn put<K>(a: Box(K), b: Box(K)): Box(K) {\n  Merge::merge(a, b)\n}\n",
    )
    .unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
    let entry = report
        .entries
        .iter()
        .find_map(|e| match &e.entry.verdict {
            Verdict::Failed(d) => Some(d),
            _ => None,
        })
        .expect("a failed entry");
    assert!(
        entry
            .message
            .to_string()
            .contains("affine does not fit shared: K for a type parameter"),
        "{}",
        report.json().render()
    );
    let at = entry.span.expect("the error has a place");
    let source = std::fs::read_to_string(&path).unwrap();
    assert_eq!(
        source[at.start as usize..]
            .lines()
            .next()
            .unwrap()
            .trim_start(),
        "Merge::merge(a, b)"
    );
}

/// A text literal in a file that does not import `std::text` runs as
/// written, though another file imports it: the file is checked with the
/// files it imports only, so its kernel has no `Text`, whether the files are
/// declared one at a time or side by side.
#[test]
fn a_text_literal_in_a_file_without_std_text_runs_as_written() {
    tauto_messages::install();
    let root = dir("text-without-import").join("tables-tote");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("Tauto.eure"),
        "package {\n  name = \"tables-tote\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    std::fs::write(
        root.join("src/tables.taut"),
        "pub fn Tables::words(): List(Text) {\n  Cons(\"a\", Cons(\"b\", Nil))\n}\n",
    )
    .unwrap();
    std::fs::write(
        root.join("src/main.taut"),
        "import std::base\nimport std::list\nimport std::text\nimport \"tables.taut\"\n\
         pub fn n(): Nat { List::length(Tables::words()) }\n\
         pub fn start(): Unit { () }\n\
         start()\n",
    )
    .unwrap();
    let checked = check_tote_report(&root).unwrap();
    assert_eq!(
        checked.report.status(),
        Status::Ok,
        "{}",
        checked.report.json().render()
    );
}
