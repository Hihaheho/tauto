//! A package not in A-normal form is reported at the entry (V7), not run.

use tauto_niri::{Outcome, ViolationKind};

#[test]
fn a_package_not_normalized_is_not_run() {
    tauto_messages::install();
    let mut pkg = tauto::nir::compile(
        r#"
import std::prelude::collections
fn twice(t: Text): Text { concat(t, t) }
show(&Text::len(twice("ab")))
"#,
    )
    .unwrap();
    tauto_nir::ownership::insert(&mut pkg);
    let run = tauto_niri::run(&pkg);
    assert!(run.shown.is_empty());
    assert!(
        matches!(&run.outcome, Outcome::Violation(v) if v.kind == ViolationKind::NotAnf),
        "{:?}",
        run.outcome
    );
}
