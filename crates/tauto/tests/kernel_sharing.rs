//! An argument used more than once is reduced once: `m` below uses its
//! argument three times, so without sharing `m` nested 40 deep takes 3^40
//! steps to reduce.

use std::time::Duration;

use tauto::check::{Kernel, Verdict, declare_prelude};

#[test]
fn an_argument_used_three_times_is_reduced_once() {
    tauto_messages::install();
    let mut nested = "3".to_string();
    for _ in 0..40 {
        nested = format!("m({nested})");
    }
    let source = format!(
        r#"fn m(n: Nat): Nat {{
  n + n - n
}}
theorem r#shared(): Eq(Nat, {}, 3) {{ Refl }}
"#,
        nested
    );
    let dir = std::env::temp_dir().join(format!("tauto-sharing-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(&path, source).unwrap();
    let loaded = tauto::program::load(&path).unwrap();
    assert!(
        loaded.program.errors.is_empty(),
        "{:?}",
        loaded.program.errors
    );
    let mut k = Kernel::new();
    declare_prelude(&mut k).unwrap();
    k.set_timeout(Some(Duration::from_secs(20)));
    let entries = k.declare_program(&loaded.program);
    let verdict = &entries.iter().find(|e| e.name == "shared").unwrap().verdict;
    assert!(matches!(verdict, Verdict::Checked { .. }), "{verdict:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A sum with an unknown operand is not a numeral: `nat_lt` of it is not
/// computed, and its `Succ`s are not unfolded one by one to find out.
#[test]
fn a_sum_with_an_unknown_operand_is_not_unfolded() {
    tauto_messages::install();
    let source = "fn f(n: Nat): Bool {\n  Nat::lt(n + 1000000000, 3)\n}\n\
                  theorem same(n: Nat): f(n) = Nat::lt(n + 1000000000, 3) { Refl }\n";
    let dir = std::env::temp_dir().join(format!("tauto-sum-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(&path, source).unwrap();
    let loaded = tauto::program::load(&path).unwrap();
    assert!(
        loaded.program.errors.is_empty(),
        "{:?}",
        loaded.program.errors
    );
    let mut k = Kernel::new();
    declare_prelude(&mut k).unwrap();
    k.set_timeout(Some(Duration::from_secs(10)));
    let entries = k.declare_program(&loaded.program);
    let verdict = &entries.iter().find(|e| e.name == "same").unwrap().verdict;
    assert!(matches!(verdict, Verdict::Checked { .. }), "{verdict:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A numeral written with constructors (`Succ(Zero)`), or a product with
/// `Zero`, is a number to `+` and `*`: the other operand is not counted
/// down one by one.
#[test]
fn a_numeral_written_with_constructors_is_computed_at_once() {
    tauto_messages::install();
    let source = "theorem one_times(): Eq(Nat, Succ(Zero) * 1000000000000, 1000000000000) { Refl }\n\
                  theorem nested(): Eq(Nat, 1000000000000 * Zero + 1000000000000, 1000000000000) { Refl }\n";
    let dir = std::env::temp_dir().join(format!("tauto-ctor-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(&path, source).unwrap();
    let loaded = tauto::program::load(&path).unwrap();
    assert!(
        loaded.program.errors.is_empty(),
        "{:?}",
        loaded.program.errors
    );
    let mut k = Kernel::new();
    declare_prelude(&mut k).unwrap();
    k.set_timeout(Some(Duration::from_secs(10)));
    let entries = k.declare_program(&loaded.program);
    for name in ["one_times", "nested"] {
        let verdict = &entries.iter().find(|e| e.name == name).unwrap().verdict;
        assert!(
            matches!(verdict, Verdict::Checked { .. }),
            "{name}: {verdict:?}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
