//! A divergent function value made outside a budget is called inside one,
//! and one made inside is called outside: in a program that runs a budget it
//! is held at the O tier, which counts whichever steps it runs under.
use std::process::Command;
use tauto_rustgen::{Bindings, Options, Sources, workspace};

fn run_and_compare(name: &str, source: &str) -> String {
    static NATIVE: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _native = NATIVE
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    tauto_messages::install();
    let expected = tauto::exec::run(source).unwrap().stdout;
    let pkg = tauto::nir::compile(source).unwrap();
    let dir = std::env::temp_dir().join(format!(
        "tauto-fn-value-budget-{name}-{}",
        std::process::id()
    ));
    let ws = workspace(
        name,
        &pkg,
        &Sources {
            file: "main.taut",
            text: source,
        },
        &Bindings::default(),
        &Options::default(),
    );
    let target = std::env::var_os("TAUTO_NATIVE_TEST_TARGET")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| dir.join("target"));
    let binary = ws
        .build(name, &dir.join("generated"), &target, false)
        .unwrap();
    let out = Command::new(binary).output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let actual = String::from_utf8(out.stdout).unwrap();
    assert_eq!(actual, expected);
    std::fs::remove_dir_all(dir).unwrap();
    actual
}

#[test]
fn a_field_made_outside_a_budget_counts_its_steps() {
    let actual = run_and_compare(
        "field-outside",
        r#"
struct(shared) Tool { run: (u64) -> u64 ! {div, overflow} }
fn count(n: u64): u64 ! {div, overflow} {
  var i: u64 := 0
  while i < n { i := i + 1 }
  i
}
fn apply(f: (u64) -> u64 ! {div, overflow}, x: u64): u64 ! {div, overflow} { f(x) }
fn make(): Tool { Tool { run: (x: u64) => count(x) } }
let t := make()
show(&(apply(t.run, 3) + (t.run)(4)))
let r := handle { perform budget(50, () => { apply(t.run, 10) + apply(t.run, 1000) }) } with {
  exceeded(info), k => k(7)
}
show(&r)
let s := handle { perform budget(50, () => { (t.run)(1000) }) } with {
  exceeded(info), k => info.more(10000)
}
show(&s)
"#,
    );
    assert!(actual.contains("7\n7\n1000\n"), "{actual}");
}

#[test]
fn a_generic_field_read_into_a_local_is_called_at_its_tier() {
    run_and_compare(
        "generic-local",
        r#"
import std::prelude::collections
struct Q(T: Shared) { same: (T, T) -> Bool ! {div, overflow}, pick: Option((T) -> T ! {div, overflow}) }
fn mk(): Q(u64) { Q { same: (a: u64, b: u64) => a == b, pick: Some((a: u64) => U64::wrapping_add(a, 1)) } }
fn use_it(q: Q(u64)): Bool ! {div, overflow} {
  let same := q.same
  match q.pick {
    Some(p) => same(p(1), 2)
    None => false
  }
}
show(&use_it(mk()))
let r := handle { perform budget(50, () => { use_it(mk()) }) } with { exceeded(info), k => k(false) }
show(&r)
"#,
    );
}

#[test]
fn a_closure_made_outside_a_budget_runs_out_inside_one() {
    let actual = run_and_compare(
        "local-outside",
        r#"
fn visit(n: i64): Unit ! {div, overflow} { if n > 0 { visit(n - 1) } }
let f := (n: i64) => visit(n)
f(3)
let r := handle { perform budget(0, () => { f(3)
true }) } with { exceeded(info), k => false }
show(&r)
"#,
    );
    assert_eq!(actual, "false\n");
}
