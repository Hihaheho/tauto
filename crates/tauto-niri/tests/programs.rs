//! The programs run to the end with no broken rule and show what they
//! should; a program with a known NIR error stops at that error and no
//! other (the list is fixed: a change either way fails).

mod common;

use tauto_niri::Outcome;

#[test]
fn programs_run_clean_or_stop_at_their_known_error() {
    let mut failed = Vec::new();
    for p in common::PROGRAMS {
        let pkg = common::prepared(p.source);
        let run = tauto_niri::run(&pkg);
        let outcome = run.against(p.shown);
        let ok = match (&outcome, p.known) {
            (Outcome::Ok, None) => true,
            (Outcome::Violation(v), Some(k)) => v.to_string().contains(k),
            _ => false,
        };
        if !ok {
            failed.push(format!(
                "{}: {outcome:?} (known: {:?})\n  shown {:?}",
                p.name, p.known, run.shown
            ));
        }
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}
