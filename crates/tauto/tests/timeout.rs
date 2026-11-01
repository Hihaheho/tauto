//! A declaration that runs out of time (`Kernel::set_timeout`) is rejected,
//! the declarations after it are not checked, and each declaration's time is
//! recorded (`Kernel::timings`).

use std::time::Duration;

use tauto::check::{Kernel, Verdict, declare_prelude};

/// `p` counts a numeral down one at a time, so `p(10^12)` does not finish.
fn source() -> String {
    r#"fn p(n: Nat): Nat {
  match n: Nat {
    Zero => 0
    Succ(k) => p(k)
  }
}
theorem slow(): p(1000000000000) = 0 { Refl }
theorem after(): Eq(Nat, 1, 1) { Refl }
"#.to_string()
}

#[test]
fn a_declaration_that_runs_out_of_time_is_rejected_and_nothing_after_it_is_checked() {
    tauto_messages::install();
    let dir = std::env::temp_dir().join(format!("tauto-timeout-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(&path, source()).unwrap();
    let loaded = tauto::program::load(&path).unwrap();
    assert!(
        loaded.program.errors.is_empty(),
        "{:?}",
        loaded.program.errors
    );
    let mut k = Kernel::new();
    declare_prelude(&mut k).unwrap();
    k.set_timeout(Some(Duration::from_millis(200)));
    let entries = k.declare_program(&loaded.program);
    let verdict = |name: &str| &entries.iter().find(|e| e.name == name).unwrap().verdict;
    assert!(matches!(verdict("p"), Verdict::Checked { .. }));
    match verdict("slow") {
        Verdict::Failed(d) => assert!(
            d.message.to_string().starts_with("gave up after"),
            "{}",
            d.message
        ),
        other => panic!("{other:?}"),
    }
    assert!(matches!(verdict("after"), Verdict::Skipped(_)));
    let slow = k.timings().iter().find(|t| t.name == "slow").unwrap();
    assert!(slow.elapsed >= Duration::from_millis(200));
    assert_eq!(slow.top.first().map(|(n, _)| n.as_str()), Some("p"));
    let _ = std::fs::remove_dir_all(&dir);
}
