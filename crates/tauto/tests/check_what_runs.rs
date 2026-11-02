//! `tauto check` rejects what `tauto run` rejects before running: the kernel
//! accepts a `Nat` where the program's Nib wants a `u64`, and only the
//! extracted program says it does not fit.

use std::path::PathBuf;

use tauto::check::Verdict;
use tauto::report::{Report, Status, check_report, check_tote_report};

const NAT_IN_U64_FIELD: &str = "struct Box { n: u64 }\n\n\
fn count(k: Nat): Nat {\n  k\n}\n\n\
let b := Box { n: count(3) }\n\
perform show(\"n\", b.n)\n";

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
        failure(&report).contains("field `n`: nat does not fit u64"),
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
         perform show(\"n\", f(count(3)))\n",
    )
    .unwrap();
    let report = check_report(&path, None).unwrap();
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
    assert!(failure(&report).contains("nat does not fit u64"));
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
         perform show(\"n\", b.n)\n",
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
    std::fs::write(root.join("src/main.taut"), NAT_IN_U64_FIELD).unwrap();
    let report = check_tote_report(&root).unwrap().report;
    assert_eq!(
        report.status(),
        Status::Failed,
        "{}",
        report.json().render()
    );
    assert!(failure(&report).contains("field `n`: nat does not fit u64"));
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
        .find(|e| e.entry.name == "a")
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
         fn mark_of(y: Bool): Mark {\n  match y: Mark {\n    true => Marked\n    false => Unmarked\n  }\n}\n\n\
         theorem mark_true(): mark_of(true) = Marked {\n  Refl\n}\n",
    )
    .unwrap();
    let path = d.join("main.taut");
    std::fs::write(
        &path,
        "import \"lib.taut\"\n\nlet marked := 1\nperform show(\"marked\", marked)\n",
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
        failure(&report).contains("nat does not fit u64"),
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
        failure(&report).contains("nat does not fit u64"),
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
    let Err(message) = check_report(&path, None) else {
        panic!("a stray `pub` was checked");
    };
    assert!(
        message.contains("`pub` is a keyword and cannot be used as a name"),
        "{message}"
    );
}
