//! `(x: A) -> B` is a dependent function type, as `∀ x: A. B` is.

use std::path::PathBuf;

use tauto::report::{Status, check_report};

fn file(name: &str, text: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tauto-dep-arrow-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(&path, text).unwrap();
    path
}

#[test]
fn a_named_parameter_is_in_scope_in_the_result() {
    tauto_messages::install();
    let path = file(
        "ok",
        "theorem refl_all(): (n: Nat) -> (n = n) {\n  (n: Nat) => Refl\n}\n\n\
         theorem use_it(h: (n: Nat) -> (n = n)): Eq(Nat, 0, 0) {\n  h(0)\n}\n",
    );
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Ok, "{}", report.json().render());
}

#[test]
fn the_named_parameter_is_checked() {
    tauto_messages::install();
    let path = file(
        "bad",
        "theorem bad(): (n: Nat) -> (n = 0) {\n  (n: Nat) => Refl\n}\n",
    );
    let report = check_report(&path, None).unwrap();
    assert_eq!(report.status(), Status::Failed);
}
