//! What an editor asks of a hole: its goal as a tree, the terms that fit it,
//! its skeleton, and where a type mismatch is.

use std::path::PathBuf;

use tauto::check::describe;
use tauto::report::{Status, check_report, try_fill};
use tauto_analyzer::assist::{By, expand, suggest};

fn file(name: &str, text: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tauto-assist-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(&path, text).unwrap();
    path
}

fn swap_source() -> &'static str {
    r#"theorem swap<A: Prop, B: Prop>(p: And(A, B)): And(B, A) {
  ?top
}
"#
}

#[test]
fn a_goal_is_given_as_a_tree_beside_its_text() {
    let path = file("goal", swap_source());
    let report = check_report(&path, None).unwrap();
    let json = report.json().render();
    assert!(
        json.contains(
            "\"goal_term\":{\"kind\":\"app\",\"function\":{\"kind\":\"var\",\"name\":\"And\"},\"arguments\":[{\"kind\":\"var\",\"name\":\"B\"},{\"kind\":\"var\",\"name\":\"A\"}]}"
        ),
        "{json}"
    );
    assert!(json.contains("\"origin\":\"parameter\""), "{json}");
    assert!(json.contains("\"unresolved_metas\":[]"), "{json}");
    assert!(json.contains("\"declaration_type\":"), "{json}");
    assert!(json.contains("\"end_line\":2"), "{json}");
}

#[test]
fn the_library_lists_constants_with_their_types() {
    let path = file("library", swap_source());
    let report = check_report(&path, None).unwrap();
    let json = report.library_json().render();
    assert!(
        json.contains("\"name\":\"AndIntro\",\"kind\":\"constructor\""),
        "{json}"
    );
    assert!(
        json.contains("\"name\":\"Nat\",\"kind\":\"inductive\""),
        "{json}"
    );
    assert!(
        json.contains("\"name\":\"Zero\",\"kind\":\"constructor\""),
        "{json}"
    );
    // The declaration being proved is known, as incomplete.
    assert!(
        json.contains("\"name\":\"swap\"") && json.contains("\"state\":\"incomplete\""),
        "{json}"
    );
}

#[test]
fn suggest_lists_what_fits_and_each_is_accepted_by_try() {
    let path = file("suggest", swap_source());
    let report = check_report(&path, None).unwrap();
    let hole = report.holes().remove(0);
    let found = suggest(&report, &hole, 50);
    let intro = found
        .iter()
        .find(|s| s.name == "AndIntro")
        .expect("AndIntro fits And(B, A)");
    assert_eq!(intro.term, "AndIntro(?top_a, ?top_b)");
    assert_eq!(intro.args.len(), 2);
    assert_eq!(describe(&intro.args[0].ty), "B");
    assert!(!found.iter().any(|s| s.name == "swap"), "not itself");
    // What was suggested is a term `try` can check, premises left as holes.
    let attempt = try_fill(&path, "top", &intro.term).unwrap();
    assert!(attempt.accepted);
    assert_eq!(attempt.report.holes().len(), 2);
}

#[test]
fn a_hypothesis_that_is_the_goal_comes_first() {
    let path = file(
        "hyp",
        r#"theorem t<A: Prop>(a: A): A {
  ?h
}
"#,
    );
    let report = check_report(&path, None).unwrap();
    let hole = report.holes().remove(0);
    let found = suggest(&report, &hole, 5);
    assert_eq!(found[0].name, "a");
    assert!(found[0].exact());
    assert_eq!(found[0].term, "a");
}

#[test]
fn an_unknown_nothing_fixes_is_marked_not_guessed() {
    let path = file("meta", swap_source());
    let report = check_report(&path, None).unwrap();
    let hole = report.holes().remove(0);
    let found = suggest(&report, &hole, 200);
    let left = found.iter().find(|s| s.name == "And::left").unwrap();
    assert_eq!(left.args[0].unresolved_metas, vec!["?B".to_string()]);
    assert!(left.generic);
}

#[test]
fn expand_by_match_writes_an_arm_for_each_constructor() {
    let path = file(
        "match",
        r#"theorem t(n: Nat, m: Nat): n + m = m + n {
  ?whole
}
"#,
    );
    let report = check_report(&path, None).unwrap();
    let hole = report.holes().remove(0);
    let e = expand(&report, &hole, &By::parse("induction(n)").unwrap()).unwrap();
    assert!(e.text.starts_with("match n {"), "{}", e.text);
    let names: Vec<&str> = e.pieces.iter().map(|p| p.hole.as_str()).collect();
    assert_eq!(names, ["whole_zero", "whole_succ"]);
    assert_eq!(e.pieces[1].recursive.len(), 1);
    let attempt = try_fill(&path, "whole", &e.text.replace('\n', "\n  ")).unwrap();
    assert!(attempt.accepted, "{}", attempt.report.text());
    assert_eq!(attempt.report.status(), Status::Incomplete);
    assert_eq!(attempt.report.holes().len(), 2);
}

#[test]
fn expand_by_intro_binds_the_argument() {
    let path = file(
        "intro",
        r#"theorem t<A: Prop, B: Prop>(): (A) -> (B) -> A {
  ?f
}
"#,
    );
    let report = check_report(&path, None).unwrap();
    let hole = report.holes().remove(0);
    let e = expand(&report, &hole, &By::Intro).unwrap();
    assert_eq!(e.text, "x => ?f_body");
    assert!(expand(&report, &hole, &By::Match("nope".into())).is_err());
    assert!(By::parse("auto").is_err());
}

/// A `match` on a variable that has arguments after it records each of its
/// holes once.
#[test]
fn a_match_before_other_arguments_keeps_its_holes() {
    let path = file(
        "twice",
        r#"theorem add_comm(n: Nat, m: Nat): n + m = m + n {
  match n {
    Zero => ?base
    Succ(k) => ?step
  }
}
"#,
    );
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Incomplete, "{}", report.text());
    let holes = report.holes();
    assert_eq!(holes.len(), 2);
    // The generalized argument is shown under its own name.
    let text = report.goal_text(&holes[0]);
    assert!(text.contains("⊢ Zero + m = m + Zero"), "{text}");
    assert!(!text.contains("m'"), "{text}");
}

#[test]
fn a_mismatch_points_at_the_argument_and_has_its_parts() {
    let path = file(
        "mismatch",
        r#"theorem swap<A: Prop, B: Prop>(p: And(A, B)): And(B, A) {
  AndIntro(And::right(p), And::right(p))
}
"#,
    );
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Failed);
    let json = report.json().render();
    // Line 2, the second argument, all of it.
    assert!(
        json.contains(
            "\"line\":2,\"col\":27,\"end_line\":2,\"end_col\":40,\"code\":\"type_mismatch\""
        ),
        "{json}"
    );
    assert!(json.contains("\"expected\":\"A\""), "{json}");
    assert!(json.contains("\"found\":\"B\""), "{json}");
    assert!(
        json.contains("\"argument\":{\"callee\":\"AndIntro\",\"index\":1}"),
        "{json}"
    );
}

#[test]
fn a_plain_mismatch_has_expected_found_and_the_differing_part() {
    let path = file(
        "plain",
        r#"theorem wrong(): Eq(Nat, 3, 4) { Refl(Nat, 3) }
"#,
    );
    let report = check_report(&path, None).unwrap();
    let json = report.json().render();
    assert!(json.contains("\"code\":\"type_mismatch\""), "{json}");
    assert!(json.contains("\"expected\":\"3 = 4\""), "{json}");
    assert!(json.contains("\"differing\":{\"expected\":\"4\""), "{json}");
}

#[test]
fn closing_a_hole_leaves_the_names_of_the_others() {
    let path = file(
        "stable",
        r#"theorem swap<A: Prop, B: Prop>(p: And(A, B)): And(B, A) {
  AndIntro(?l, ?r)
}
"#,
    );
    let attempt = try_fill(&path, "l", "And::right(p)").unwrap();
    let json = attempt.json().render();
    assert!(json.contains("\"closed_holes\":[\"l\"]"), "{json}");
    assert!(json.contains("\"new_holes\":[]"), "{json}");
    assert_eq!(attempt.report.holes()[0].goal.name, "r");
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tauto-assist-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn std_file(name: &str) -> String {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../std")
        .join(name)
        .canonicalize()
        .unwrap()
        .display()
        .to_string()
}

#[test]
fn expand_writes_the_arms_the_tactic_leaves() {
    // expand_step reads the step's messages in English.
    tauto_messages::install();
    let base = std_file("Base.taut");
    let nat = std_file("Nat.taut");
    let tactic = std_file("Tactic.taut");
    let dir = scratch("expand");
    let path = dir.join("main.taut");
    let head = format!(
        r#"import "{}"
import "{}"
import "{}"
"#,
        base, nat, tactic
    );
    std::fs::write(
        &path,
        format!(
            "{head}{}",
            r#"theorem t(k: Nat, a: Nat): Nat::add(Succ(k), a) = Succ(Nat::add(k, a)) {
  ?h
}
"#
        ),
    )
    .unwrap();
    let (e, a) =
        tauto_analyzer::assist::expand_step(&path, "h", "rewrite", "Nat::add_succ_left(k, a)")
            .unwrap();
    assert!(a.accepted);
    assert_eq!(
        e.text,
        "by rewrite!(Nat::add_succ_left(k, a)): Nat::add(Succ(k), a) = Succ(Nat::add(k, a)) {\n  ⊢ Succ(Nat::add(k, a)) = Succ(Nat::add(k, a)) from ?h_1\n}"
    );
    assert_eq!(e.pieces.len(), 1);
    // A step's arm: its goal is the arm's, and `-> G` is left out.
    std::fs::write(&path, a.candidate.replace("?h_1", "?g")).unwrap();
    let (e, a) = tauto_analyzer::assist::expand_step(&path, "g", "exact", "Refl").unwrap();
    assert!(!a.accepted, "there is no tactic exact here");
    assert!(e.text.starts_with("by exact!(Refl) {}"), "{}", e.text);
}

#[test]
fn expand_by_rewrite_reads_the_goal_written_with_operators() {
    // expand_step reads the step's messages in English.
    tauto_messages::install();
    // The equation is about `Nat::add(b, a)`, the goal is written `b + a`: they are the same term.
    let dir = scratch("expand-operators");
    let path = dir.join("main.taut");
    std::fs::write(
        &path,
        format!(
            r#"import "{}"
import "{}"
import "{}"
theorem t(a: Nat, b: Nat, c: Nat, h: a + b = c): b + a = c {{
  ?g
}}
"#,
            std_file("Base.taut"),
            std_file("Nat.taut"),
            std_file("Tactic.taut")
        ),
    )
    .unwrap();
    let (e, a) =
        tauto_analyzer::assist::expand_step(&path, "g", "rewrite", "Nat::add_comm(b, a)").unwrap();
    assert!(a.accepted);
    assert_eq!(
        e.text,
        "by rewrite!(Nat::add_comm(b, a)): b + a = c {\n  ⊢ Nat::add(a, b) = c from ?g_1\n}"
    );
}
