//! The points where a function may stop, how often each continuation may
//! run, and the locals it keeps.

use tauto::nir::compile;
use tauto_nir::anf;
use tauto_nir::effects::{Resumes, points};

fn of(source: &str, name: &str) -> Vec<tauto_nir::effects::Point> {
    tauto_messages::install();
    let mut pkg = compile(source).unwrap();
    anf::normalize(&mut pkg);
    let f = pkg
        .fns
        .iter()
        .find(|f| f.source.to_string().ends_with(name))
        .unwrap_or_else(|| panic!("no {name}"));
    points(f)
}

fn names(p: &tauto_nir::effects::Point) -> Vec<String> {
    p.live.iter().map(|(l, _)| l.name.clone()).collect()
}

#[test]
fn a_continuation_keeps_what_is_read_after_it() {
    let ps = of(
        r#"
effect ask(): u64
fn sum(a: u64, b: Text): u64 ! {ask, overflow} {
  let x := perform ask()
  let unused := 5
  x + a
}
// The arm is not a tail form, so `ask` is not lowered as `direct`.
show(&(handle { sum(1, "t") } with { ask(), k => { let v := k(2); v } }))
"#,
        "sum",
    );
    let p = ps
        .iter()
        .find(|p| p.resumes == Resumes::Once)
        .expect("a point");
    assert_eq!(names(p), ["a"], "{ps:#?}");
}

#[test]
fn resume_many_and_resume_zero_are_told_apart() {
    let many = of(
        r#"
effect choose(): Bool resume ω
fn pick(t: Text): Text ! {choose} { if perform choose() { t } else { "no" } }
show(&(handle { pick("yes") } with { choose(), k => k(true) }))
"#,
        "pick",
    );
    assert!(
        many.iter()
            .any(|p| p.resumes == Resumes::Many && names(p) == ["t"]),
        "{many:#?}"
    );
    let never = of(
        r#"
effect stop(): Never resume 0
fn halt(t: Text): Text ! {stop} { perform stop() }
show(&(handle { halt("x") } with { stop() => "stopped" }))
"#,
        "halt",
    );
    assert!(
        never
            .iter()
            .any(|p| p.resumes == Resumes::Never && p.live.is_empty()),
        "{never:#?}"
    );
}
