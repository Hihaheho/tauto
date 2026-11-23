//! Divergent callbacks suspend in the budget driver without restarting their body.
use std::process::Command;
use tauto_rustgen::{Bindings, Options, Sources, workspace};

#[test]
fn divergent_callbacks_preserve_budgets_captures_and_resumption() {
    tauto_messages::install();
    let source = &r#"
fn visit(n: i64): Unit ! {div, overflow} {
  if n > 0 { visit(n - 1) }
}
fn apply<!e>(f: &((i64) -> Unit ! e), n: i64): Unit ! e {
  each(Cons(n, Nil), &f)
}
fn apply_div(f: &((i64) -> Unit ! {div, overflow}), n: i64): Unit ! {div, overflow} {
  f(n)
}
fn concrete(steps: u64): Bool ! {budget} {
  handle { perform budget(steps, () => {
    apply_div((n) => visit(n), 3)
    true
  }) } with { exceeded(info), k => false }
}
fn borrowed_parameter(steps: u64): Bool ! {budget} {
  handle { perform budget(steps, () => {
    apply_div((n) => visit(n), 3)
    true
  }) } with { exceeded(info), k => false }
}
fn borrowed_parameter_resume(): i64 ! {budget} {
  var count := 0
  handle { perform budget(0, () => {
    apply_div((n) => {
      count := count + 1
      visit(n)
    }, 3)
    count
  }) } with { exceeded(info), k => info.more(2) }
}
fn run(steps: u64): Bool ! {budget} {
  handle { perform budget(steps, () => {
    each(Cons(3, Nil), (n) => visit(n))
    true
  }) } with { exceeded(info), k => false }
}
fn captured(steps: u64): Bool ! {budget} {
  let offset := 4
  handle { perform budget(steps, () => {
    apply((n) => visit(n + offset), 3)
    true
  }) } with { exceeded(info), k => false }
}
fn resume_more(): i64 ! {budget} {
  var count := 0
  handle { perform budget(0, () => {
    each(Cons(3, Cons(2, Nil)), (n) => {
      count := count + 1
      visit(n)
    })
    count
  }) } with { exceeded(info), k => info.more(2) }
}
fn resume_unbounded(): i64 ! {budget} {
  var count := 0
  handle { perform budget(0, () => {
    each(Cons(3, Cons(2, Nil)), (n) => {
      count := count + 1
      visit(n)
    })
    count
  }) } with { exceeded(info), k => info.unbounded() }
}
fn loop_callback(steps: u64): Bool ! {budget} {
  var count := 0
  handle { perform budget(steps, () => {
    each(Cons(8, Nil), (n) => {
      while count < n { count := count + 1 }
    })
    count == 8
  }) } with { exceeded(info), k => false }
}
fn inner_zero(): Bool ! {budget} {
  handle { perform budget(1000, () => {
    perform budget(0, () => {
      each(Cons(8, Nil), (n) => visit(n))
      true
    })
  }) } with { exceeded(info), k => false }
}
fn nested(steps: u64): Bool ! {budget} {
  handle { perform budget(steps, () => {
    perform budget(1000, () => {
      apply((n) => visit(n), 10)
      true
    })
    true
  }) } with { exceeded(info), k => false }
}
apply((n) => visit(n), 2)
show(&run(1000))
show(&run(0))
show(&run(1))
show(&captured(1000))
show(&captured(0))
show(&resume_more())
show(&resume_unbounded())
show(&nested(1000))
show(&nested(0))
show(&inner_zero())
show(&loop_callback(1000))
show(&loop_callback(0))
let pure := handle { perform budget(1000, () => {
  each(Cons(3, Nil), (n) => #())
  true
}) } with { exceeded(info), k => false }
show(&pure)
show(&concrete(1000))
show(&concrete(0))
show(&borrowed_parameter(1000))
show(&borrowed_parameter(0))
show(&borrowed_parameter_resume())
let widened := handle { perform budget(1000, () => {
  apply_div((n) => #(), 3)
  true
}) } with { exceeded(info), k => false }
show(&widened)

"#
    .to_string();
    let actual = run_and_compare(source);
    assert!(actual.contains("true\nfalse\nfalse\n"));
    assert!(actual.contains("2\n2\n"));
}

fn run_and_compare(source: &str) -> String {
    // The directory name must stay free of parentheses and other shell
    // metacharacters: jemalloc's configure script evals its own build path.
    static NEXT_DIR: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    static NATIVE: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _native = NATIVE
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let expected = tauto::exec::run(source).unwrap().outputs;
    let pkg = tauto::nir::compile(source).unwrap();
    let dir = std::env::temp_dir().join(format!(
        "tauto-budget-closures-{}-{}",
        std::process::id(),
        NEXT_DIR.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
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
fn escaping_divergent_values_stay_explicitly_unsupported() {
    tauto_messages::install();
    for (source, expected) in [
        (
            r#"fn visit(n: i64): Unit ! {div, overflow} { if n > 0 { visit(n - 1) } }
enum(affine) R { Done(Bool), Paused(Info(R)) }
let f := (n) => visit(n)
let r := handle { Done(perform budget(0, () => { each(Cons(3, Nil), &f)
true })) } with { exceeded(info), k => Paused(info) }"#,
            "f is borrowed in a budget, whose stopped body may outlive it",
        ),
        (
            r#"fn visit(n: i64): Unit ! {div, overflow} { if n > 0 { visit(n - 1) } }
let r := handle { perform budget(0, () => { each(Cons(3, Nil), visit)
true }) } with { exceeded(info), k => false }"#,
            "divergent named function",
        ),
        (
            r#"fn visit(n: i64): Unit ! {div, overflow} { if n > 0 { visit(n - 1) } }
fn wrap<!e>(f: &((i64) -> Unit ! e)): Bool ! {budget} ∪ e { handle { perform budget(0, () => { f(3)
true }) } with { exceeded(info), k => false } }
show(&wrap((n) => visit(n)))"#,
            "created outside a budget",
        ),
        (
            r#"fn visit(n: i64): Unit ! {div, overflow} { if n > 0 { visit(n - 1) } }
effect choose(): Bool resume ω
let r := handle { perform budget(0, () => { each(Cons(3, Nil), (n) => { if perform choose() { visit(n) } })
true }) } with { exceeded(info), k => false
choose(), k => k(true) }"#,
            "multi-shot closure",
        ),
        (
            r#"fn visit(n: i64): Unit ! {div, overflow} { if n > 0 { visit(n - 1) } }
fn outer(): Bool ! {budget} { let f := (n) => visit(n)
fn inner(): Unit ! {div, overflow} { f(3) }
handle { perform budget(0, () => { inner()
true }) } with { exceeded(info), k => false } }
show(&outer())"#,
            "not a plain name",
        ),
        (
            r#"fn visit(n: i64): Unit ! {div, overflow} { if n > 0 { visit(n - 1) } }
fn apply_div(f: &((i64) -> Unit ! {div, overflow})): Unit ! {div, overflow} { f(3) }
let r := handle { perform budget(10, () => { let f := (n) => #()
apply_div(&f)
true }) } with { exceeded(info), k => false }"#,
            "synchronous function value",
        ),
        (
            r#"fn visit(n: i64): Unit ! {div, overflow} { if n > 0 { visit(n - 1) } }
extern { fn native(f: &((i64) -> Unit ! {div, overflow})): Unit }
let r := handle { perform budget(10, () => { native((n) => #())
true }) } with { exceeded(info), k => false }"#,
            "callback through an extern",
        ),
    ] {
        let error = match tauto::nir::compile(source) {
            Ok(_) => panic!("expected {expected}, compiled:\n{source}"),
            Err(e) => e.to_string(),
        };
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
            .split("```nib\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        run_and_compare(source);
    }
}

#[test]
fn an_uncalled_divergent_callback_adds_no_effect_under_a_budget() {
    tauto_messages::install();
    // A callback that is received but never called adds no effect.
    let source = r#"fn visit(n: i64): Unit ! {div, overflow} { if n > 0 { visit(n - 1) } }
fn ignore<!e>(f: &((i64) -> Unit ! e), n: i64): Unit { #() }
let r := handle { perform budget(10, () => { ignore((k) => visit(k), 1)
true }) } with { exceeded(info), k => false }
show(&r)"#;
    tauto::nir::compile(source).unwrap_or_else(|e| panic!("{e}"));
}
