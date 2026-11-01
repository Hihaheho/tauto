//! Divergent callbacks suspend in the budget driver without restarting their body.
use std::process::Command;
use tauto_rustgen::{Bindings, Options, Sources, workspace};

#[test]
fn divergent_callbacks_preserve_budgets_captures_and_resumption() {
    tauto_messages::install();
    let source = &r#"
fn visit(n: i64): Unit ! {Div} {
  if n > 0 { visit(n - 1) }
}
fn apply<!e>(&f: (i64) -> Unit ! e, n: i64): Unit ! e {
  each(Cons(n, Nil), &f)
}
fn apply_div(&f: (i64) -> Unit ! {Div}, n: i64): Unit ! {Div} {
  f(n)
}
fn concrete(steps: i64): Bool {
  handle { budget(steps: steps) {
    apply_div((n) => visit(n), 3)
    true
  } } with { exceeded(info), k => false }
}
fn borrowed_parameter(steps: i64): Bool {
  handle { budget(steps: steps) {
    apply_div((&n) => visit(n), 3)
    true
  } } with { exceeded(info), k => false }
}
fn borrowed_parameter_resume(): i64 {
  var count := 0
  handle { budget(steps: 0) {
    apply_div((&n) => {
      count := count + 1
      visit(n)
    }, 3)
    count
  } } with { exceeded(info), k => info.more(2) }
}
fn run(steps: i64): Bool {
  handle { budget(steps: steps) {
    each(Cons(3, Nil), (n) => visit(n))
    true
  } } with { exceeded(info), k => false }
}
fn captured(steps: i64): Bool {
  let offset := 4
  handle { budget(steps: steps) {
    apply((n) => visit(n + offset), 3)
    true
  } } with { exceeded(info), k => false }
}
fn resume_more(): i64 {
  var count := 0
  handle { budget(steps: 0) {
    each(Cons(3, Cons(2, Nil)), (n) => {
      count := count + 1
      visit(n)
    })
    count
  } } with { exceeded(info), k => info.more(2) }
}
fn resume_unbounded(): i64 {
  var count := 0
  handle { budget(steps: 0) {
    each(Cons(3, Cons(2, Nil)), (n) => {
      count := count + 1
      visit(n)
    })
    count
  } } with { exceeded(info), k => info.unbounded() }
}
fn loop_callback(steps: i64): Bool {
  var count := 0
  handle { budget(steps: steps) {
    each(Cons(8, Nil), (n) => {
      while count < n { count := count + 1 }
    })
    count == 8
  } } with { exceeded(info), k => false }
}
fn inner_zero(): Bool {
  handle { budget(steps: 1000) {
    budget(steps: 0) {
      each(Cons(8, Nil), (n) => visit(n))
      true
    }
  } } with { exceeded(info), k => false }
}
fn nested(steps: i64): Bool {
  handle { budget(steps: steps) {
    budget(steps: 1000) {
      apply((n) => visit(n), 10)
      true
    }
    true
  } } with { exceeded(info), k => false }
}
apply((n) => visit(n), 2)
perform show("large", run(1000))
perform show("zero", run(0))
perform show("small", run(1))
perform show("captured", captured(1000))
perform show("captured_zero", captured(0))
perform show("more", resume_more())
perform show("unbounded", resume_unbounded())
perform show("nested", nested(1000))
perform show("nested_zero", nested(0))
perform show("inner_zero", inner_zero())
perform show("loop", loop_callback(1000))
perform show("loop_zero", loop_callback(0))
let pure := handle { budget(steps: 1000) {
  each(Cons(3, Nil), (n) => #())
  true
} } with { exceeded(info), k => false }
perform show("pure", pure)
perform show("concrete", concrete(1000))
perform show("concrete_zero", concrete(0))
perform show("borrowed_parameter", borrowed_parameter(1000))
perform show("borrowed_parameter_zero", borrowed_parameter(0))
perform show("borrowed_parameter_resume", borrowed_parameter_resume())
let widened := handle { budget(steps: 1000) {
  apply_div((n) => #(), 3)
  true
} } with { exceeded(info), k => false }
perform show("widened", widened)

"#
    .to_string();
    let actual = run_and_compare(source);
    assert!(actual.contains("large = true\nzero = false\nsmall = false\n"));
    assert!(actual.contains("more = 2\nunbounded = 2\n"));
}

fn run_and_compare(source: &str) -> String {
    static NATIVE: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _native = NATIVE
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let expected = tauto::eval::run(source).unwrap().outputs;
    let pkg = tauto_nir::compile(source).unwrap();
    let dir = std::env::temp_dir().join(format!(
        "tauto-budget-closures-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let ws = workspace(
        "budget-closures",
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
        .build("budget-closures", &dir.join("generated"), &target, false)
        .unwrap();
    let out = Command::new(binary).output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let actual = String::from_utf8(out.stdout).unwrap();
    let expected = expected
        .into_iter()
        .map(|(label, value)| format!("{label} = {value}\n"))
        .collect::<String>();
    assert_eq!(actual, expected);
    std::fs::remove_dir_all(dir).unwrap();
    actual
}

#[test]
fn uninstrumented_and_escaping_divergent_values_stay_explicitly_unsupported() {
    tauto_messages::install();
    for (source, expected) in [
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
let f := (n) => visit(n)
let r := handle { budget(steps: 0) { f(3)
true } } with { exceeded(info), k => false }"#,
            "created outside a budget",
        ),
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
let f := (n) => visit(n)
let r := handle { budget(steps: 0) { each(Cons(3, Nil), &f)
true } } with { exceeded(info), k => false }"#,
            "f is borrowed in a budget, whose stopped body may outlive it",
        ),
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
let r := handle { budget(steps: 0) { each(Cons(3, Nil), visit)
true } } with { exceeded(info), k => false }"#,
            "divergent named function",
        ),
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
fn wrap(&f: (i64) -> Unit ! {Div}): Bool { handle { budget(steps: 0) { f(3)
true } } with { exceeded(info), k => false } }
perform show("r", wrap((n) => visit(n)))"#,
            "created outside a budget",
        ),
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
fn wrap<!e>(&f: (i64) -> Unit ! e): Bool ! e { handle { budget(steps: 0) { f(3)
true } } with { exceeded(info), k => false } }
perform show("r", wrap((n) => visit(n)))"#,
            "created outside a budget",
        ),
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
effect choose(): Bool resume ω
let r := handle { budget(steps: 0) { each(Cons(3, Nil), (n) => { if perform choose() { visit(n) } })
true } } with { exceeded(info), k => false
choose(), k => k(true) }"#,
            "multi-shot closure",
        ),
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
fn outer(): Bool { let f := (n) => visit(n)
fn inner(): Unit ! {Div} { f(3) }
handle { budget(steps: 0) { inner()
true } } with { exceeded(info), k => false } }
perform show("r", outer())"#,
            "not a plain name",
        ),
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
fn apply_div(&f: (i64) -> Unit ! {Div}): Unit ! {Div} { f(3) }
let r := handle { budget(steps: 10) { let f := (n) => #()
apply_div(&f)
true } } with { exceeded(info), k => false }"#,
            "synchronous function value",
        ),
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
extern { fn native(&f: (i64) -> Unit ! {Div}): Unit }
let r := handle { budget(steps: 10) { native((n) => #())
true } } with { exceeded(info), k => false }"#,
            "callback through an extern",
        ),
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
fn ignore_div(&f: (i64) -> Unit ! {Div}, n: i64): Unit { #() }
let r := handle { budget(steps: 10) { each(Cons(1, Nil), (n) => ignore_div((k) => #(), n))
true } } with { exceeded(info), k => false }"#,
            "absent from the helper's effect row",
        ),
        (
            r#"fn visit(n: i64): Unit ! {Div} { if n > 0 { visit(n - 1) } }
fn ignore<!e>(&f: (i64) -> Unit ! e, n: i64): Unit { #() }
let r := handle { budget(steps: 10) { each(Cons(1, Nil), (n) => ignore((k) => visit(k), n))
true } } with { exceeded(info), k => false }"#,
            "absent from the helper's effect row",
        ),
    ] {
        let error = tauto_nir::compile(source).unwrap_err().to_string();
        assert!(error.contains(expected), "expected {expected}, got {error}");
    }
}

#[test]
fn existing_abort_continuation_and_borrowed_callback_flows_still_match() {
    tauto_messages::install();
    let cases = include_str!("../../../cases/rust/programs.eure");
    for name in [
        "a-resume-zero-effect-through-a-handler",
        "resume-1-and-resume-0-handlers",
        "fail-raise-catch-and-forwarding",
        "a-closure-that-performs-a-resume-once-effect",
        "a-borrowing-closure-performs-an-effect-across-an-await",
        "a-borrowing-closure-calls-a-captured-function",
        "a-borrowing-closure-calls-a-borrowed-function",
        "a-divergent-callback-inside-a-multi-shot-handler",
        "a-divergent-callback-runs-out-inside-a-multi-shot-handler",
    ] {
        let section = cases.split(&format!("@ cases.{name}\n")).nth(1).unwrap();
        let source = section
            .split("source = ```nib\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        run_and_compare(source);
    }
}
