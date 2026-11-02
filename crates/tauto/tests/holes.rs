//! A proof written a step at a time: the goals of holes, a candidate checked
//! without being written, and a filled hole written back.

use std::path::PathBuf;

use tauto::report::{Status, check_report, try_fill};

fn source() -> &'static str {
    r#"theorem swap<A: Prop, B: Prop>(p: And(A, B)): And(B, A) {
  AndIntro(?l, ?r)
}
"#
}

fn file(name: &str, text: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tauto-holes-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(&path, text).unwrap();
    path
}

#[test]
fn a_hole_reports_its_goal_and_context() {
    tauto_messages::install();
    let path = file("goal", source());
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Incomplete);
    let holes = report.holes();
    assert_eq!(holes.len(), 2);
    assert_eq!(holes[0].goal.name, "l");
    let text = report.goal_text(&holes[0]);
    assert!(text.contains("A : Prop"), "{text}");
    assert!(text.contains("p : And(A, B)"), "{text}");
    assert!(text.contains("⊢ B"), "{text}");
    let json = report.json().render();
    assert!(json.starts_with("{\"status\":\"incomplete\""), "{json}");
    assert!(json.contains("\"goal\":\"B\""), "{json}");
    assert!(json.contains("\"line\":2,\"col\":13"), "{json}");
}

#[test]
fn a_candidate_is_checked_and_the_file_is_not_written() {
    tauto_messages::install();
    let path = file("try", source());
    let attempt = try_fill(&path, "l", "And::right(p)").unwrap();
    assert!(attempt.accepted);
    assert_eq!(attempt.report.holes().len(), 1, "only ?r is left");
    assert_eq!(std::fs::read_to_string(&path).unwrap(), source());

    let wrong = try_fill(&path, "l", "And::left(p)").unwrap();
    assert!(!wrong.accepted);
    assert_eq!(wrong.report.status(), Status::Failed);
}

#[test]
fn filling_every_hole_makes_the_declaration_checked() {
    tauto_messages::install();
    let path = file("fill", source());
    for (hole, term) in [("l", "And::right(p)"), ("r", "And::left(p)")] {
        let attempt = try_fill(&path, hole, term).unwrap();
        assert!(attempt.accepted);
        std::fs::write(&path, &attempt.candidate).unwrap();
    }
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok);
    assert!(report.holes().is_empty());
}

#[test]
fn an_unknown_hole_is_an_error() {
    tauto_messages::install();
    let path = file("unknown", source());
    assert!(try_fill(&path, "nope", "p").is_err());
}

/// An `extern` signature is trusted: `tauto check` lists it with the
/// axioms.
#[test]
fn a_trusted_extern_is_listed() {
    tauto_messages::install();
    let path = file(
        "extern",
        r#"affine struct File {}
affine struct IoError {}
extern {
  fn file_open(&path: Text): Result(File, IoError)
}
"#,
    );
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok);
    let listed = report.externs();
    assert_eq!(listed.len(), 1);
    assert!(listed[0].starts_with("extern file_open ("), "{listed:?}");
    assert!(listed[0].ends_with("main.taut:4)"), "{listed:?}");
    assert!(
        report.text().contains("trusted extern file_open ("),
        "{}",
        report.text()
    );
}
