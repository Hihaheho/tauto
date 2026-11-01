//! Tick-only budgets specialize without changing their handler or step boundaries.

use std::process::Command;
use tauto_rustgen::{Bindings, Options, Sources, emit_module, workspace};

fn emit(source: &str) -> String {
    let pkg = tauto_nir::compile(source).unwrap();
    emit_module(
        &pkg,
        &Sources {
            file: "main.taut",
            text: source,
        },
        &Bindings::default(),
    )
}

#[test]
fn synchronous_specializations_keep_original_functions_and_guarded_fallback() {
    let source = r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

let r := handle { budget(steps: 20) { descend(count(5)) } } with { exceeded(info), k => -1 }
perform show("r", r)"#;
    let rust = emit(&source);
    assert!(rust.contains("budget_sync"), "{rust}");
    assert!(rust.contains("can_run_nonresuming"));
    assert!(rust.contains("run_nonresuming"));
    let compact: String = rust.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(compact.contains("budget::run("));
    assert!(compact.contains("budget::tick("));
    assert!(compact.contains("__tauto_fuel.tick()?"));
}

#[test]
fn local_resume_zero_and_budget_exhaustion_use_original_handler_arms() {
    let source = &r#"effect stop(value: i64): Never resume 0
fn stop_at(n: i64): i64 ! {stop} { perform stop(n) }
fn visit(n: i64): i64 ! {Div, stop} {
  var i := 0
  while i < n { i := i + 1 }
  stop_at(i)
}
fn run(steps: i64): Result(i64, Text) {
  handle { budget(steps: steps) { Ok(visit(3)) } } with {
    stop(value) => Ok(value)
    exceeded(info), k => Err("exhausted")
  }
}
var fuel := 0
while fuel < 10 { perform show("result", run(fuel))
  fuel := fuel + 1 }
"#
    .to_string();
    assert!(emit(source).contains("run_nonresuming"));
    let output = run_both_paths_observed(source, Some(34), true, Some(0));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8_lossy(&output.stdout);
    assert!(text.contains("Err"), "{text}");
    assert!(text.contains("Ok(3)"), "{text}");
}

#[test]
fn closed_shared_callback_alone_keeps_exact_fuel_and_invocation_counts() {
    let source = &r#"fn value(index: u64): u64 { index + 1 }
fn sum(&read: (u64) -> u64, size: u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size { total := total + read(index)
    index := index + 1 }
  total
}
fn forward(&read: (u64) -> u64, size: u64): u64 ! {Div} {
  sum(&(index) => read(index), size)
}
fn run(steps: i64): Result(u64, Text) {
  handle { budget(steps: steps) { Ok(forward(&(index) => value(index), 4)) } } with {
    exceeded(info), k => Err("exhausted")
  }
}
var fuel := 0
while fuel < 12 { perform show("result", run(fuel))
  fuel := fuel + 1 }
"#
    .to_string();
    assert!(emit(source).contains("run_nonresuming"));
    let output = run_both_paths_observed(source, Some(57), false, Some(30));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("Ok(10)"));
}

#[test]
fn closed_shared_callbacks_forward_through_helpers_and_compose_with_abort() {
    let source = &r#"effect stop(value: u64): Never resume 0
fn value(index: u64): u64 { index + 1 }
fn scan(&read: (u64) -> u64, size: u64, abort_at: u64): u64 ! {Div, stop} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size {
    if index == abort_at { perform stop(total) }
    total := total + read(index)
    index := index + 1
  }
  total
}
fn forward(&read: (u64) -> u64, size: u64, abort_at: u64): u64 ! {Div, stop} {
  scan(&(index) => read(index), size, abort_at)
}
fn run(steps: i64, abort_at: u64): Result(u64, Text) {
  handle { budget(steps: steps) { Ok(forward(&value, 4, abort_at)) } } with {
    stop(total) => Ok(total)
    exceeded(info), k => Err("exhausted")
  }
}
var fuel := 0
while fuel < 12 {
  perform show("abort", run(fuel, 2))
  perform show("normal", run(fuel, 9))
  fuel := fuel + 1
}
"#
    .to_string();
    let rust = emit(source);
    assert!(rust.contains("run_nonresuming"), "{rust}");
    assert!(rust.contains("budget_sync"));
    let output = run_both_paths_observed(source, Some(107), true, Some(47));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8_lossy(&output.stdout);
    assert!(text.contains("Ok(3)"), "{text}");
    assert!(text.contains("Ok(10)"), "{text}");
}

#[test]
fn resumptions_nested_control_and_callbacks_keep_the_future_path() {
    for source in [
        r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

let r := handle { budget(steps: 0) { count(5) } } with { exceeded(info), k => info.more(2) }
perform show("r", r)"#,
        r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

let r := handle { budget(steps: 0) { count(5) } } with { exceeded(info), k => info.unbounded() }
perform show("r", r)"#,
        r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

let r := handle { budget(steps: 0) { count(5) } } with { exceeded(info), k => k(7) }
perform show("r", r)"#,
        r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

let r := handle { budget(steps: 20) { budget(steps: 10) { count(5) } } } with { exceeded(info), k => -1 }
perform show("r", r)"#,
        r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

let r := handle { budget(steps: 20) { each(Cons(5, Nil), (n) => { count(n)
() })
1 } } with { exceeded(info), k => -1 }
perform show("r", r)"#,
        r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

let r := handle { budget(steps: 20) { handle { count(5) } with { return x => x } } } with { exceeded(info), k => -1 }
perform show("r", r)"#,
    ] {
        let rust = emit(source);
        assert!(
            !rust.contains("run_nonresuming"),
            "unexpected specialization: {source}"
        );
    }
}

#[test]
fn boundaries_mutation_return_arms_and_outer_resumption_match_original_path() {
    let source = r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

fn run(steps: i64): i64 {
  handle { budget(steps: steps) { descend(count(5)) } } with {
    exceeded(info), k => -1
    return value => value + 100
  }
}
fn inner(steps: i64): i64 {
  handle { budget(steps: steps) { count(5) } } with { exceeded(info), k => -9 }
}
fn argument_order(steps: i64): i64 {
  var visited := 0
  let result := handle { budget(steps: steps) { descend({ visited := visited + 10
5 }) } } with { exceeded(info), k => -10 }
  result * 100 + visited
}
fn mutation(steps: i64): i64 {
  var visited := 0
  let result := handle { budget(steps: steps) {
    while visited < 5 { visited := visited + 1 }
    visited
  } } with { exceeded(info), k => -10 }
  result * 100 + visited
}
var fuel := 0
while fuel < 15 {
  perform show("run", run(fuel))
  perform show("mutation", mutation(fuel))
  perform show("argument_order", argument_order(fuel))
  fuel := fuel + 1
}
let outer := handle { budget(steps: 0) { handle { budget(steps: 100) { count(5) } } with { exceeded(info), discarded => -9 } } } with { exceeded(info), k => info.more(2) }
perform show("outer_resume", outer)
let nested := handle { budget(steps: 0) { budget(steps: 0) { count(5) } } } with { exceeded(info), k => -88 }
perform show("nested_zero", nested)
let no_ticks := handle { budget(steps: 0) { 42 } } with { exceeded(info), k => -1 }
perform show("no_ticks", no_ticks)
"#;
    let output = run_both_paths(&source);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let actual = String::from_utf8(output.stdout).unwrap();
    assert!(actual.contains("outer_resume ="), "{actual}");
    assert!(actual.contains("no_ticks = 42\n"));
}

#[test]
fn captured_refcell_temporaries_keep_the_future_path() {
    let source = &r#"fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn first(label: Text, value: i64): i64 { value }
var text := "before"
let saved := () => text
let result := handle { budget(steps: 0) {
  first(text, count(5))
} } with {
  exceeded(info), discarded => {
    text := "after"
    -9
  }
}
perform show("result", result)
perform show("text", saved())
"#
    .to_string();
    assert!(!emit(source).contains("run_nonresuming"));
}

#[test]
fn unknown_generic_values_and_body_returns_keep_the_future_path() {
    for source in [
        r#"fn choose<T>(value: T, n: i64): T ! {Div} {
          var i := 0
          while i < n { i := i + 1 }
          value
        }
        let result := handle { budget(steps: 20) { choose(42, 3) } } with { exceeded(info), k => -1 }
        perform show("result", result)"#,
        r#"fn body_return(): i64 {
          handle { budget(steps: 20) { return 7
 1 } } with { exceeded(info), k => -1 }
        }
        perform show("result", body_return())"#,
    ] {
        assert!(!emit(source).contains("run_nonresuming"), "{source}");
    }
}

#[test]
fn mutual_recursion_and_function_local_returns_preserve_steps() {
    let source = &r#"fn even(n: i64): i64 ! {Div} {
      if n == 0 { return 1 }
      odd(n - 1)
    }
    fn odd(n: i64): i64 ! {Div} {
      if n == 0 { return 0 }
      even(n - 1)
    }
    fn run(steps: i64): i64 {
      handle { budget(steps: steps) { even(6) } } with { exceeded(info), k => -1 }
    }
    var fuel := 0
    while fuel < 10 { perform show("result", run(fuel))
 fuel := fuel + 1 }
    "#
    .to_string();
    assert!(emit(source).contains("budget_sync"));
    let output = run_both_paths(source);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn ample_fuel_and_nonresuming_error_values_match_evaluator() {
    let source = r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

fn run(steps: i64): Result(i64, Text) {
  handle { budget(steps: steps) { Ok(descend(count(5))) } } with { exceeded(info), k => Err("fuel exhausted") }
}
perform show("value", run(1000))
perform show("error", run(0))
"#;
    run_and_compare(&source);
}

#[test]
fn noncopy_host_augmentable_data_keeps_array_projection_but_not_sync_budget() {
    let source = &r#"struct Entry { tag: i64, payload: Text }
fn scan(values: Array(Entry), n: i64): i64 ! {Div} {
  var i := 0
  var total := 0
  while i < n {
    total := total + match Array::get(values, 0) {
      Some(Entry { tag, payload: _ }) => tag
      None => 0
    }
    i := i + 1
  }
  total
}
fn run(steps: i64): i64 {
  var entries := Vec::new()
  Vec::push(&mut entries, Entry { tag: 7, payload: "kept" })
  let values := Vec::into_array(entries)
  handle { budget(steps: steps) { scan(values, 5) } } with { exceeded(info), k => -1 }
}
var fuel := 0
while fuel < 9 { perform show("result", run(fuel))
 fuel := fuel + 1 }
"#
    .to_string();
    let rust = emit(source);
    assert!(!rust.contains("budget_sync"));
    assert!(rust.contains("strong_count"));
    let output = run_both_paths(source);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_and_compare(source: &str) -> String {
    let expected = tauto::eval::run(source)
        .unwrap()
        .outputs
        .into_iter()
        .map(|(label, value)| format!("{label} = {value}\n"))
        .collect::<String>();
    let output = run_both_paths(source);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let actual = String::from_utf8(output.stdout).unwrap();
    assert_eq!(actual, expected);
    actual
}

fn run_both_paths(source: &str) -> std::process::Output {
    run_both_paths_with_host(source, &Bindings::default(), "")
}

fn run_both_paths_observed(
    source: &str,
    ticks: Option<u64>,
    abort: bool,
    callbacks: Option<u64>,
) -> std::process::Output {
    run_both_paths_checked(
        source,
        &Bindings::default(),
        "",
        Some((true, ticks, abort, callbacks)),
    )
}

fn run_both_paths_with_host(source: &str, bindings: &Bindings, host: &str) -> std::process::Output {
    run_both_paths_checked(source, bindings, host, None)
}

fn run_both_paths_checked(
    source: &str,
    bindings: &Bindings,
    host: &str,
    observed: Option<(bool, Option<u64>, bool, Option<u64>)>,
) -> std::process::Output {
    run_both_paths_variant(source, bindings, host, observed, false)
}

fn run_both_paths_variant(
    source: &str,
    bindings: &Bindings,
    host: &str,
    observed: Option<(bool, Option<u64>, bool, Option<u64>)>,
    runtime_sync: bool,
) -> std::process::Output {
    static NATIVE: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _native = NATIVE.lock().unwrap_or_else(|p| p.into_inner());
    let pkg = tauto_nir::compile(source).unwrap();
    let mut ws = workspace(
        "nonresuming-budget",
        &pkg,
        &Sources {
            file: "main.taut",
            text: source,
        },
        bindings,
        &Options::default(),
    );
    ws.files
        .iter_mut()
        .find(|(path, _)| path == "src/lib.rs")
        .unwrap()
        .1
        .push_str(host);
    if observed.is_some() {
        instrument_execution(&mut ws);
        let lib = &mut ws
            .files
            .iter_mut()
            .find(|(path, _)| path == "src/lib.rs")
            .unwrap()
            .1;
        for function in pkg.fns.iter().filter(|f| f.source == "value") {
            let signature = format!("fn {}", function.rust_name);
            assert_eq!(
                lib.matches(&signature).count(),
                1,
                "callback instrumentation signature"
            );
            let start = lib.find(&signature).unwrap();
            let body = start + lib[start..].find('{').unwrap() + 1;
            lib.insert_str(body, "tauto_rt::budget::CALLBACK_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);");
        }
    }
    if runtime_sync {
        let manifest = &mut ws
            .files
            .iter_mut()
            .find(|(p, _)| p == "Cargo.toml")
            .unwrap()
            .1;
        replace_once(
            manifest,
            "tauto-rt = { path = \"tauto-rt\" }",
            "tauto-rt = { path = \"tauto-rt\", features = [\"sync\"] }",
        );
    }
    // Different runtime sources never share native incremental artifacts.
    use std::hash::{Hash, Hasher};
    let mut fingerprint = std::collections::hash_map::DefaultHasher::new();
    ws.files.hash(&mut fingerprint);
    let variant = format!("{:016x}", fingerprint.finish());
    let dir = std::env::temp_dir().join(format!("tauto-nonresuming-{}", std::process::id()));
    let target = std::env::var_os("TAUTO_NATIVE_TEST_TARGET")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| dir.join("target"))
        .join(variant);
    let binary = ws
        .build(
            "nonresuming-budget",
            &dir.join("generated"),
            &target.join("nonresuming-equivalence/fast"),
            false,
        )
        .unwrap();
    let mut actual = Command::new(binary).output().unwrap();
    let fast_counts = observed.map(|_| execution_counts(&mut actual));
    force_future_path(&mut ws);
    let binary = ws
        .build(
            "nonresuming-budget",
            &dir.join("generated"),
            &target.join("nonresuming-equivalence/original"),
            false,
        )
        .unwrap();
    let mut baseline = Command::new(binary).output().unwrap();
    if let Some((fast, expected_ticks, abort, expected_callbacks)) = observed {
        let original_counts = execution_counts(&mut baseline);
        let counts = fast_counts.unwrap();
        assert_eq!(counts[0] > 0, fast, "fast entry count: {counts:?}");
        assert_eq!(
            original_counts[0], 0,
            "forced Future path entered fast adapter"
        );
        assert!(
            original_counts[1] > 0,
            "ordinary budget adapter was not entered"
        );
        assert_eq!(
            counts[2], original_counts[2],
            "attempted budget tick counts differ"
        );
        if let Some(ticks) = expected_ticks {
            assert_eq!(counts[2], ticks, "unexpected NIR step count");
        }
        assert_eq!(counts[3] > 0, abort, "abort exit count: {counts:?}");
        assert_eq!(
            counts[5], original_counts[5],
            "callback invocation counts differ"
        );
        if let Some(calls) = expected_callbacks {
            assert_eq!(counts[5], calls, "unexpected callback count");
        }
        if fast && expected_ticks.is_some() {
            assert!(counts[4] > 0, "no exhaustion was exercised");
        }
    }
    assert_eq!(actual.status.code(), baseline.status.code());
    assert_eq!(actual.stdout, baseline.stdout);
    assert_eq!(actual.stderr, baseline.stderr);
    std::fs::remove_dir_all(dir).unwrap();
    actual
}

fn replace_once(text: &mut String, from: &str, to: &str) {
    assert_eq!(
        text.matches(from).count(),
        1,
        "instrumentation site: {from}"
    );
    *text = text.replace(from, to);
}

fn instrument_execution(ws: &mut tauto_rustgen::Workspace) {
    let budget = &mut ws
        .files
        .iter_mut()
        .find(|(path, _)| path == "tauto-rt/src/budget.rs")
        .unwrap()
        .1;
    replace_once(
        budget,
        "    let result = {\n        let _active = ActiveBudget::enter(id, fuel.left.clone(), false);",
        "    FAST_ENTRIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n    let result = {\n        let _active = ActiveBudget::enter(id, fuel.left.clone(), false);",
    );
    replace_once(
        budget,
        "    let left = Rc::new(Cell::new(keep));",
        "    FUTURE_ENTRIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n    let left = Rc::new(Cell::new(keep));",
    );
    // A body that resumes from a handler arm runs its budgets in the CPS
    // machine, which is the ordinary path too.
    let cps = &mut ws
        .files
        .iter_mut()
        .find(|(path, _)| path == "tauto-rt/src/cps.rs")
        .unwrap()
        .1;
    replace_once(
        cps,
        "        M(Some(Rc::new(Frame {\n            ops: &[],\n            budget: Some(BudgetFrame {",
        "        crate::budget::FUTURE_ENTRIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n        M(Some(Rc::new(Frame {\n            ops: &[],\n            budget: Some(BudgetFrame {",
    );
    let budget = &mut ws
        .files
        .iter_mut()
        .find(|(path, _)| path == "tauto-rt/src/budget.rs")
        .unwrap()
        .1;
    replace_once(
        budget,
        "        let out = STACK.with",
        "        ATTEMPTED_TICKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n        let out = STACK.with",
    );
    replace_once(
        budget,
        "        if self.left.get() == 0 {",
        "        ATTEMPTED_TICKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n        if self.left.get() == 0 {",
    );
    replace_once(
        budget,
        "Err(Interrupted::Abort(abort)) => o::reraise(abort).await,",
        "Err(Interrupted::Abort(abort)) => { ABORT_EXITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed); o::reraise(abort).await },",
    );
    replace_once(
        budget,
        "        Err(Interrupted::Exhausted) => {",
        "        Err(Interrupted::Exhausted) => {\n            EXHAUSTED_EXITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);",
    );
    budget.push_str(
        r#"
pub static FAST_ENTRIES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static FUTURE_ENTRIES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static ATTEMPTED_TICKS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static ABORT_EXITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static EXHAUSTED_EXITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static CALLBACK_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
"#,
    );
    ws.files.iter_mut().find(|(path, _)| path == "src/main.rs").unwrap().1 = r#"fn main() -> std::process::ExitCode {
        let result = tauto_rt::run_main(nonresuming_budget::run);
        use std::sync::atomic::Ordering::Relaxed;
        use tauto_rt::budget::*;
        eprintln!("BUDGET_COUNTS:{},{},{},{},{},{}", FAST_ENTRIES.load(Relaxed), FUTURE_ENTRIES.load(Relaxed), ATTEMPTED_TICKS.load(Relaxed), ABORT_EXITS.load(Relaxed), EXHAUSTED_EXITS.load(Relaxed), CALLBACK_CALLS.load(Relaxed));
        result
    }"#.into();
}

fn execution_counts(output: &mut std::process::Output) -> [u64; 6] {
    let stderr = String::from_utf8(std::mem::take(&mut output.stderr)).unwrap();
    let mut reports = stderr
        .lines()
        .filter_map(|line| line.strip_prefix("BUDGET_COUNTS:"));
    let report = reports.next().expect("one execution counter report");
    assert!(reports.next().is_none());
    let counts: Vec<u64> = report.split(',').map(|n| n.parse().unwrap()).collect();
    output.stderr = stderr
        .split_inclusive('\n')
        .filter(|line| !line.starts_with("BUDGET_COUNTS:"))
        .collect::<String>()
        .into_bytes();
    counts.try_into().unwrap()
}

#[test]
fn host_refcount_observer_retains_suspended_values_until_original_arm_finishes() {
    let source = r#"extern { fn refs(): i64
 fn tracked(): Text }
fn hold(value: Text, n: i64): Text ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  value
}
fn observed(steps: i64): Text {
  let text := tracked()
  handle { budget(steps: steps) { hold(text, 5) } } with {
    exceeded(info), k => Text::of_i64(refs())
  }
}
var fuel := 0
while fuel < 9 { perform show("observed", observed(fuel))
  fuel := fuel + 1 }
"#;
    let mut bindings = Bindings::default();
    bindings.externs.insert(
        "refs".into(),
        tauto_rustgen::Binding {
            rust: "host::refs".into(),
            at: "test host".into(),
            marks: String::new(),
        },
    );
    bindings.externs.insert(
        "tracked".into(),
        tauto_rustgen::Binding {
            rust: "host::tracked".into(),
            at: "test host".into(),
            marks: String::new(),
        },
    );
    let pkg = tauto_nir::compile(source).unwrap();
    let sources = Sources {
        file: "main.taut",
        text: source,
    };
    let reports = tauto_rustgen::budget_diagnostics(&pkg, &sources, &bindings);
    assert!(
        reports
            .iter()
            .flat_map(|r| &r.reasons)
            .any(|r| r.code == "observable-handler")
    );
    assert!(!emit_module(&pkg, &sources, &bindings).contains("run_nonresuming"));
    let output = run_both_paths_checked(
        source,
        &bindings,
        r#"
mod host {
    thread_local! { static TRACKED: std::cell::RefCell<Option<std::rc::Weak<str>>> = const { std::cell::RefCell::new(None) }; }
    pub fn tracked() -> tauto_rt::Text {
        let text: std::rc::Rc<str> = std::rc::Rc::from("heldvalue");
        TRACKED.with(|slot| *slot.borrow_mut() = Some(std::rc::Rc::downgrade(&text)));
        tauto_rt::Text::Shared(text)
    }
    pub fn refs() -> i64 {
        TRACKED.with(|slot| slot.borrow().as_ref().unwrap().strong_count() as i64)
    }
}
"#,
        Some((false, None, false, Some(0))),
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("heldvalue"));
}

#[test]
fn nested_synchronous_helper_preserves_original_result_or_diagnostic() {
    let source = &r#"fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn inner(steps: i64): i64 {
  handle { budget(steps: steps) { count(5) } } with { exceeded(info), discarded => -9 }
}
let result := handle { budget(steps: 0) { inner(100) } } with { exceeded(info), resume_outer => info.more(2) }
perform show("result", result)
"#.to_string();
    // This boundary can fail on the original runtime; the optimization must
    // neither hide that diagnostic nor bypass the outer resumable budget.
    run_both_paths(source);
}

#[test]
fn an_outer_resumable_budget_records_only_future_entries() {
    let source = r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

let result := handle { budget(steps: 0) {
  handle { budget(steps: 100) { count(5) } } with { exceeded(info), discarded => -9 }
} } with { exceeded(info), resume_outer => info.more(2) }
perform show("result", result)
"#;
    let output = run_both_paths_checked(
        &source,
        &Bindings::default(),
        "",
        Some((false, None, false, Some(0))),
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn steps_are_evaluated_once_before_each_runtime_branch_choice() {
    let source = r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

fn run(steps: i64): i64 {
  var visits := 0
  let result := handle { budget(steps: { visits := visits + 1
    steps }) { count(4) } } with { exceeded(info), k => -1 }
  result + visits * 100
}
perform show("empty", run(0))
perform show("ample", run(100))
"#;
    let output = run_both_paths_observed(&source, None, false, Some(0));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "empty = 99\nample = 104\n"
    );
}

#[test]
fn a_host_panic_hook_observes_the_same_active_outer_fuel() {
    let source = r#"extern { fn install_hook(): Unit }
fn divide(n: i64): i64 ! {Div} { div(1, n) }
install_hook()
let result := handle { budget(steps: 1) { divide(0) } } with { exceeded(info), k => -1 }
perform show("result", result)
"#;
    let mut bindings = Bindings::default();
    bindings.externs.insert(
        "install_hook".into(),
        tauto_rustgen::Binding {
            rust: "host::install_hook".into(),
            at: "test host".into(),
            marks: String::new(),
        },
    );
    let output = run_both_paths_checked(
        source,
        &bindings,
        r#"
mod host {
    pub fn install_hook() {
        std::panic::set_hook(Box::new(|_| {
            let at = tauto_rt::Loc { file: "host hook", line: 1, col: 1 };
            let mut nested_tick = std::pin::pin!(tauto_rt::budget::tick(at));
            let blocked = tauto_rt::o::poll_once(nested_tick.as_mut()).is_pending();
            let id = if blocked { Some(tauto_rt::o::take_budget()) } else { None };
            eprintln!("host hook outer budget: {id:?}");
        }));
    }
}
"#,
        Some((true, None, false, Some(0))),
    );
    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("host hook outer budget: Some("), "{stderr}");
    assert!(stderr.contains("division by zero"), "{stderr}");
}

#[test]
fn runtime_error_location_and_negative_fuel_match_original_path() {
    let failing = &r#"fn divide(n: i64): i64 ! {Div} { div(1, n) }
let result := handle { budget(steps: 10) { divide(0) } } with { exceeded(info), k => -1 }
perform show("result", result)"#
        .to_string();
    let output = run_both_paths(failing);
    assert!(!output.status.success());
    let diagnostic = String::from_utf8(output.stderr).unwrap();
    assert!(diagnostic.contains("main.taut:1:"), "{diagnostic}");
    let negative = r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

let result := handle { budget(steps: -3) { count(2) } } with { exceeded(info), k => -9 }
perform show("result", result)"#;
    let output = run_both_paths(&negative);
    assert!(output.status.success());
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "result = -9\n");
}

#[test]
fn suspended_step_expression_rechecks_the_surrounding_budget() {
    let source = &r#"effect request_steps(): i64 resume <=1
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn inner(): i64 ! {request_steps} {
  handle { budget(steps: perform request_steps()) { count(5) } } with {
    exceeded(info), discarded => -9
  }
}
let result := handle { inner() } with {
  request_steps(), resume_inner => handle { budget(steps: 0) { resume_inner(100) } } with {
    exceeded(info), discarded_outer => -77
  }
}
perform show("result", result)
"#
    .to_string();
    let output = run_both_paths_checked(
        source,
        &Bindings::default(),
        "",
        Some((false, None, false, Some(0))),
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let actual = String::from_utf8(output.stdout).unwrap();
    let expected = tauto::eval::run(source)
        .unwrap()
        .outputs
        .into_iter()
        .map(|(label, value)| format!("{label} = {value}\n"))
        .collect::<String>();
    assert_eq!(actual, expected);
    assert_eq!(actual, "result = -77\n");
}

#[test]
fn runtime_sync_feature_unification_compiles_and_selects_future_path() {
    let source = r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

let result := handle { budget(steps: 100) { count(5) } } with { exceeded(info), k => -1 }
perform show("result", result)"#;
    assert!(emit(&source).contains("run_nonresuming"));
    let output = run_both_paths_variant(
        &source,
        &Bindings::default(),
        "",
        Some((false, None, false, Some(0))),
        true,
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "result = 5\n");
}

#[test]
fn host_added_drop_on_generated_noncopy_data_keeps_original_order() {
    let source = r#"struct Held { text: Text }
fn hold(value: Held, n: i64): Held ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  value
}
fn run(steps: i64): Held {
  handle { budget(steps: steps) { hold(Held { text: "body" }, 5) } } with {
    exceeded(info), k => { let temporary := Held { text: "arm" }
      Held { text: "handler" } }
  }
}
perform show("result", run(1))
"#;
    assert!(!emit(source).contains("run_nonresuming"));
    let output = run_both_paths_checked(
        source,
        &Bindings::default(),
        r#"
impl Drop for Held {
    fn drop(&mut self) { eprintln!("drop:{}", self.text); }
}
"#,
        Some((false, None, false, Some(0))),
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let drops = String::from_utf8(output.stderr).unwrap();
    let arm = drops.find("drop:arm").expect("handler-local destructor");
    let body = drops.find("drop:body").expect("suspended-body destructor");
    let result = drops.find("drop:handler").expect("result destructor");
    assert!(arm < body && body < result, "{drops}");
}

#[test]
fn nested_external_and_linear_data_do_not_specialize() {
    let source = r#"
fn count(n: i64): i64 ! {Div} {
  var i := 0
  while i < n { i := i + 1 }
  i
}
fn descend(n: i64): i64 ! {Div} {
  if n > 0 { descend(n - 1) + 1 } else { 0 }
}

struct Token { value: i64 }
struct Nested { token: Option(Token) }
let result := handle { budget(steps: 20) { Nested { token: Some(Token { value: count(5) }) } } } with { exceeded(info), k => Nested { token: None } }
perform show("result", result)
"#;
    let mut pkg = tauto_nir::compile(&source).unwrap();
    let sources = Sources {
        file: "main.taut",
        text: &source,
    };
    assert!(emit_module(&pkg, &sources, &Bindings::default()).contains("run_nonresuming"));
    let mut bindings = Bindings::default();
    bindings.types.insert(
        "Token".into(),
        tauto_rustgen::Binding {
            rust: "bridge::Token".into(),
            at: "test".into(),
            marks: String::new(),
        },
    );
    assert!(!emit_module(&pkg, &sources, &bindings).contains("run_nonresuming"));
    pkg.datas
        .iter_mut()
        .find(|d| d.name == "Token")
        .unwrap()
        .linear = true;
    assert!(!emit_module(&pkg, &sources, &Bindings::default()).contains("run_nonresuming"));
}

/// Builds both paths from the same NIR, runtime sources and release settings.
/// The baseline forces the guarded original Future path; counters are measured
/// separately from timing because their wrapper deliberately adds overhead.
#[test]
#[ignore = "builds and times native release executables"]
fn native_release_comparison() {
    fn source_source() -> &'static str {
        r#"
fn mix(n: i64): i64 ! {Div} { mod(n * 17 + 23, 1000003) }
fn fold(n: i64): i64 ! {Div} {
  var i := 0
  var total := 0
  while i < n {
    total := mod(total + mix(i), 1000003)
    i := i + 1
  }
  total
}
let result := handle { budget(steps: 6000000) { fold(2500000) } } with {
  exceeded(info), discarded => -1
}
perform show("checksum", result)
"#
    }
    let pkg = tauto_nir::compile(source_source()).unwrap();
    let ws = workspace(
        "nonresuming-cost",
        &pkg,
        &Sources {
            file: "main.taut",
            text: source_source(),
        },
        &Bindings::default(),
        &Options::default(),
    );
    let dir = std::env::var_os("TAUTO_NONRESUMING_BENCH_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::env::temp_dir().join(format!("tauto-nonresuming-cost-{}", std::process::id()))
        });
    std::fs::create_dir_all(&dir).unwrap();
    let target = std::env::var_os("TAUTO_NATIVE_TEST_TARGET")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| dir.join("target"));
    let expected = format!(
        "checksum = {}\n",
        (0..2_500_000_i64).fold(0, |total, i| (total + (i * 17 + 23) % 1_000_003)
            % 1_000_003)
    );
    let mut timed = Vec::new();
    let mut counters = Vec::new();
    for instrument in [false, true] {
        for fast in [false, true] {
            let name = format!(
                "{}-{}",
                if fast { "fast" } else { "baseline" },
                if instrument { "counts" } else { "time" }
            );
            let mut variant = tauto_rustgen::Workspace {
                files: ws.files.clone(),
            };
            if !fast {
                force_future_path(&mut variant);
            }
            if instrument {
                instrument_futures(&mut variant);
            }
            // A shared Cargo target must not reuse one executable path for
            // independently cached workspaces with different runtime sources.
            let package = format!("nonresuming-cost-{name}");
            let crate_name = package.replace('-', "_");
            for (path, text) in &mut variant.files {
                if path == "Cargo.toml" {
                    *text = text.replace(
                        "name = \"nonresuming-cost\"",
                        &format!("name = \"{package}\""),
                    );
                } else if path == "src/main.rs" {
                    *text = text.replace("nonresuming_cost", &crate_name);
                }
            }
            let built = variant
                .build(
                    &package,
                    &dir.join(&name),
                    &target.join("nonresuming-cost").join(&name),
                    true,
                )
                .unwrap();
            let retained = dir.join(format!("{name}-bin"));
            std::fs::copy(built, &retained).unwrap();
            let output = Command::new(&retained).output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
            if instrument {
                let line = String::from_utf8(output.stderr).unwrap();
                let values: Vec<u64> = line.trim().split(',').map(|n| n.parse().unwrap()).collect();
                assert_eq!(values.len(), 3);
                println!(
                    "{name}: o::pin creations={}, boxed-future polls={}, attempted budget ticks={}",
                    values[0], values[1], values[2]
                );
                counters.push(values);
            } else {
                assert!(output.stderr.is_empty());
                timed.push(retained);
            }
        }
    }
    assert_eq!(counters[0][2], 5_000_001);
    assert_eq!(counters[0][2], counters[1][2]);
    assert!(counters[1][0] < counters[0][0]);
    assert!(counters[1][1] < counters[0][1]);
    if std::env::var_os("TAUTO_NONRESUMING_BUILD_ONLY").is_some() {
        println!("retained executables: {}", dir.display());
        return;
    }
    let mut samples = [Vec::new(), Vec::new()];
    for sample in 0..11 {
        for index in if sample % 2 == 0 { [0, 1] } else { [1, 0] } {
            let start = std::time::Instant::now();
            let output = Command::new(&timed[index]).output().unwrap();
            let elapsed = start.elapsed().as_secs_f64();
            assert!(output.status.success());
            assert!(output.stderr.is_empty());
            assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
            samples[index].push(elapsed);
        }
    }
    for (name, values) in ["baseline", "fast"].into_iter().zip(samples.iter_mut()) {
        println!("{name}: ordered samples {values:?}");
        values.sort_by(f64::total_cmp);
        println!(
            "{name}: median {:.6}s; p95 {:.6}s; samples {values:?}",
            values[5], values[10]
        );
    }
    println!("retained executables: {}", dir.display());
}

fn force_future_path(ws: &mut tauto_rustgen::Workspace) {
    let runtime = &mut ws
        .files
        .iter_mut()
        .find(|(p, _)| p == "tauto-rt/src/budget.rs")
        .unwrap()
        .1;
    let guard = "    !cfg!(feature = \"sync\") && STACK.with(|s| s.borrow().is_empty())";
    assert_eq!(
        runtime.matches(guard).count(),
        1,
        "expected exactly one runtime eligibility guard"
    );
    *runtime = runtime.replace(guard, "    false");
    assert!(!runtime.contains(guard));
}

#[test]
fn forced_original_path_does_not_depend_on_generated_rust_formatting() {
    let mut ws = tauto_rustgen::Workspace {
        files: vec![
            (
                "src/lib.rs".into(),
                "tauto_rt :: budget :: can_run_nonresuming ()".into(),
            ),
            (
                "tauto-rt/src/budget.rs".into(),
                include_str!("../../tauto-rt/src/budget.rs").into(),
            ),
        ],
    };
    force_future_path(&mut ws);
    assert!(
        ws.files[1]
            .1
            .contains("pub fn can_run_nonresuming() -> bool {\n    false\n}")
    );
}

fn instrument_futures(ws: &mut tauto_rustgen::Workspace) {
    let o = &mut ws
        .files
        .iter_mut()
        .find(|(p, _)| p == "tauto-rt/src/o.rs")
        .unwrap()
        .1;
    let pin = "    Box::pin(f)";
    assert_eq!(o.matches(pin).count(), 1);
    *o = o.replace(pin, "    FUTURES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n    Box::pin(Counted { inner: Box::pin(f) })");
    o.push_str(
        r#"
pub static FUTURES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static POLLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static TICKS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
struct Counted<F> { inner: Pin<Box<F>> }
impl<F: Future> Future for Counted<F> {
    type Output = F::Output;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        POLLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.inner.as_mut().poll(cx)
    }
}
"#,
    );
    let budget = &mut ws
        .files
        .iter_mut()
        .find(|(p, _)| p == "tauto-rt/src/budget.rs")
        .unwrap()
        .1;
    assert_eq!(budget.matches("        let out = STACK.with").count(), 1);
    assert_eq!(
        budget.matches("        if self.left.get() == 0 {").count(),
        1
    );
    *budget = budget.replace("        let out = STACK.with", "        crate::o::TICKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n        let out = STACK.with")
        .replace("        if self.left.get() == 0 {", "        crate::o::TICKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n        if self.left.get() == 0 {");
    let main = &mut ws
        .files
        .iter_mut()
        .find(|(p, _)| p == "src/main.rs")
        .unwrap()
        .1;
    *main = r#"fn main() -> std::process::ExitCode {
        let result = tauto_rt::run_main(nonresuming_cost::run);
        use std::sync::atomic::Ordering::Relaxed;
        eprintln!("{},{},{}", tauto_rt::o::FUTURES.load(Relaxed), tauto_rt::o::POLLS.load(Relaxed), tauto_rt::o::TICKS.load(Relaxed));
        result
    }"#.into();
}

#[test]
fn qualified_host_entries_preserve_results_ticks_and_call_counts() {
    let source = r#"effect stop(value: u64): Never resume 0
extern { fn native(value: u64): u64
  fn __tauto_budget_contract_0(value: u64): u64 }
fn extern_name_probe(value: u64): u64 { __tauto_budget_contract_0(value) }
fn sum(&read: (u64) -> u64, size: u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size { total := total + read(index)
    index := index + 1 }
  total
}
fn value(index: u64): u64 { index + 1 }
fn inner(): u64 {
  handle { budget(steps: 100) { sum(&value, 1) } } with { exceeded(info), k => 0 }
}
fn ext_sum(size: u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size { total := total + native(index)
    index := index + 1 }
  total
}
fn scan(&read: (u64) -> u64, size: u64, stop_at: u64): u64 ! {Div, stop} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size {
    if index == stop_at { perform stop(total) }
    total := total + native(read(index))
    index := index + 1
  }
  total
}
fn callback_run(steps: i64, &read: (u64) -> u64, size: u64): Result(u64, Text) {
  handle { budget(steps: steps) { Ok(sum(&(index) => read(index), size)) } } with {
    exceeded(info), k => Err("exhausted")
  }
}
fn extern_run(steps: i64, size: u64): Result(u64, Text) {
  handle { budget(steps: steps) { Ok(ext_sum(size)) } } with {
    exceeded(info), k => Err("exhausted")
  }
}
fn combined_run(steps: i64, &read: (u64) -> u64, size: u64, stop_at: u64): Result(u64, Text) {
  handle { budget(steps: steps) { Ok(scan(&(index) => read(index), size, stop_at)) } } with {
    stop(total) => Ok(total)
    exceeded(info), k => Err("exhausted")
  }
}
struct TrustedBudgetHost { value: u64 }
fn token_named_data(value: TrustedBudgetHost): u64 { value.value }
struct Held { text: Text }
fn hold(value: Held, size: u64): Held ! {Div} {
  var index: u64 := 0
  while index < size { index := index + 1 }
  value
}
fn data_run(steps: i64): Held {
  handle { budget(steps: steps) { hold(Held { text: "body" }, 4) } } with {
    exceeded(info), k => Held { text: "handler" }
  }
}
"#;
    let package = tauto_nir::compile_with(source, true).unwrap();
    let internal_name = package.fns[package
        .exports
        .iter()
        .find(|e| e.name == "callback_run")
        .unwrap()
        .inst]
        .rust_name
        .clone();
    let manifest_text =
        r#"rust {
  extern { native = "host::native" __tauto_budget_contract_0 = "host::native" }
  nonresuming {
    extern { native = "closed-host-v1" }
    entries {
      callback_trusted = "callback_run"
      extern_trusted = "extern_run"
      combined_trusted = "combined_run"
      data_trusted = "data_run"
    }
  }
}"#.replace("entries {", &format!("entries {{ __tauto_budget_contract_1 = \"callback_run\" {internal_name} = \"callback_run\" "));
    let manifest =
        tauto::manifest::parse(&manifest_text, std::path::Path::new("Tauto.eure")).unwrap();
    let bindings = Bindings::resolve(&package, Some(&manifest), None).unwrap();
    let sources = Sources {
        file: "main.taut",
        text: source,
    };
    let reports = tauto_rustgen::budget_diagnostics(&package, &sources, &bindings);
    for name in [
        "callback_trusted",
        "extern_trusted",
        "combined_trusted",
        "data_trusted",
    ] {
        let report = reports.iter().find(|r| r.variant == name).unwrap();
        assert!(report.eligible(), "{report:?}");
        assert!(report.assumptions.iter().any(|a| a.kind == "embedding"));
    }
    for name in ["callback_run", "extern_run", "combined_run", "data_run"] {
        let report = reports
            .iter()
            .find(|r| r.variant == "ordinary" && r.function == name)
            .unwrap();
        assert!(!report.eligible(), "{report:?}");
        assert!(report.assumptions.is_empty());
    }
    let mut ws = workspace(
        "nonresuming-budget",
        &package,
        &sources,
        &bindings,
        &Options::default(),
    );
    ws.files
        .iter_mut()
        .find(|(p, _)| p == "src/lib.rs")
        .unwrap()
        .1
        .push_str(
            r#"
pub mod host {
    // Test-only ghost instrumentation, not a proof of a Rust Fn's contract.
    pub static CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    pub fn native(value: u64) -> u64 {
        CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        value + 1
    }
}
"#,
        );
    instrument_execution(&mut ws);
    ws.files.iter_mut().find(|(p,_)| p == "src/main.rs").unwrap().1 = r#"
use nonresuming_budget::{api, host};
use tauto_rt::budget::*;
use std::sync::atomic::Ordering::Relaxed;
fn snapshot() -> [u64; 6] {
    [FAST_ENTRIES.swap(0, Relaxed), FUTURE_ENTRIES.swap(0, Relaxed), ATTEMPTED_TICKS.swap(0, Relaxed), ABORT_EXITS.swap(0, Relaxed), host::CALLS.swap(0, Relaxed), EXHAUSTED_EXITS.swap(0, Relaxed)]
}
fn check(base: [u64; 6], trusted: [u64; 6], abort: bool, exhausted: bool, ticks: u64) {
    assert_eq!(base[0], 0, "ordinary facade acquired host assumptions");
    assert!(base[1] > 0);
    assert_eq!(trusted[0] > 0, EXPECT_FAST);
    assert_eq!(base[2], trusted[2], "tick boundaries");
    assert_eq!(base[2], ticks, "independent source tick count");
    assert_eq!(trusted[3], u64::from(EXPECT_FAST && abort), "abort terminal exit");
    assert_eq!(trusted[5], u64::from(EXPECT_FAST && exhausted), "exhausted terminal exit");
    assert_eq!(base[4], trusted[4], "extern invocation count");
    println!("ticks={} extern={}", base[2], base[4]);
}
const EXPECT_FAST: bool = true;
fn main() {
    assert_eq!(api::extern_name_probe(7), 8);
    let _ = snapshot();
    let token = tauto_rt::budget_contract::TrustedBudgetHost::assert_contract();
    assert_eq!(api::token_named_data(api::TrustedBudgetHost { value: 7 }), 7);
    let calls = std::cell::Cell::new(0_u64);
    // Test-only callback telemetry, independently compared across both paths.
    let read = |index| { calls.set(calls.get()+1); index+1 };
    for steps in 0..16 {
        let base = api::callback_run(steps, &read, 4); let a = snapshot(); let n = calls.replace(0);
        let trusted = api::callback_trusted(&token, steps, &read, 4); let b = snapshot();
        assert_eq!(base, trusted); assert_eq!(n, calls.replace(0));
        assert_eq!(base, if steps >= 5 { Ok(10) } else { Err(tauto_rt::Text::Static("exhausted")) });
        check(a,b,false,steps<5,(steps as u64+1).min(5));
        let base = api::extern_run(steps, 4); let a = snapshot();
        let trusted = api::extern_trusted(&token, steps, 4); let b = snapshot();
        assert_eq!(base, trusted);
        assert_eq!(base, if steps >= 5 { Ok(10) } else { Err(tauto_rt::Text::Static("exhausted")) });
        check(a,b,false,steps<5,(steps as u64+1).min(5));
        for stop_at in [2, 9] {
            let base = api::combined_run(steps, &read, 4, stop_at); let a = snapshot(); let n = calls.replace(0);
            let trusted = api::combined_trusted(&token, steps, &read, 4, stop_at); let b = snapshot();
            assert_eq!(base, trusted); assert_eq!(n, calls.replace(0));
            let boundary = if stop_at == 2 { 4 } else { 5 };
            assert_eq!(base, if steps >= boundary { Ok(if stop_at == 2 { 5 } else { 14 }) } else { Err(tauto_rt::Text::Static("exhausted")) });
            check(a,b,stop_at==2 && steps>=4,steps<boundary,(steps as u64+1).min(boundary as u64));
        }
        let base = api::data_run(steps); let a = snapshot();
        let trusted = api::data_trusted(&token, steps); let b = snapshot();
        assert!(base == trusted);
        assert_eq!(&*base.text, if steps>=5 { "body" } else { "handler" });
        check(a,b,false,steps<5,(steps as u64+1).min(5));
    }
    // Bare host Fn remains unqualified even when it reenters an eligible export.
    let reenter = |index| api::inner() + index;
    assert_eq!(api::callback_run(100, &reenter, 4).unwrap(), 10);
    let reentrant = snapshot();
    assert_eq!(reentrant[0], 0, "reentrant ordinary facade entered fast adapter");
    assert_eq!(reentrant[1], 5, "one outer and four nested ordinary budgets");
    assert_eq!(reentrant[2], 13, "nested ticks debit the active ordinary outer budget");
    println!("reentry ticks={}", reentrant[2]);
    for alias in [api::__tauto_budget_contract_1, api::INTERNAL_SHADOW_NAME] {
        let base = api::callback_run(100, &read, 4); let a = snapshot();
        let trusted = alias(&token, 100, &read, 4); let b = snapshot();
        assert_eq!(base, Ok(10)); assert_eq!(base, trusted);
        check(a,b,false,false,5);
    }
    let at = tauto_rt::Loc { file: "outer host budget", line: 1, col: 1 };
    let mut outer = std::pin::pin!(tauto_rt::budget::run(901, 1000, tauto_rt::o::pin(async {
        api::combined_trusted(&token, 100, &read, 4, 9)
    }), at));
    assert!(matches!(tauto_rt::o::poll_once(outer.as_mut()), std::task::Poll::Ready(Ok(14))));
    let nested = snapshot();
    assert_eq!(nested[0], 0, "trusted entry bypassed an active outer budget");
    assert_eq!(nested[1], 2);
    assert_eq!(nested[2], 5);
    println!("trusted outer ticks={}", nested[2]);
}
"#.replace("INTERNAL_SHADOW_NAME", &internal_name);
    let dir = std::env::temp_dir().join(format!("tauto-qualified-budget-{}", std::process::id()));
    use std::hash::{Hash, Hasher};
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    ws.files.hash(&mut hash);
    let target = std::env::var_os("TAUTO_NATIVE_TEST_TARGET")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| dir.join("target"))
        .join(format!("qualified-{:016x}", hash.finish()));
    let binary = ws
        .build("nonresuming-budget", &dir, &target.join("fast"), false)
        .unwrap();
    let fast = Command::new(binary).output().unwrap();
    assert!(
        fast.status.success(),
        "{}",
        String::from_utf8_lossy(&fast.stderr)
    );
    force_future_path(&mut ws);
    let main = &mut ws
        .files
        .iter_mut()
        .find(|(p, _)| p == "src/main.rs")
        .unwrap()
        .1;
    replace_once(
        main,
        "const EXPECT_FAST: bool = true;",
        "const EXPECT_FAST: bool = false;",
    );
    let binary = ws
        .build("nonresuming-budget", &dir, &target.join("future"), false)
        .unwrap();
    let baseline = Command::new(binary).output().unwrap();
    assert!(
        baseline.status.success(),
        "{}",
        String::from_utf8_lossy(&baseline.stderr)
    );
    assert_eq!(fast.stdout, baseline.stdout);
    assert_eq!(fast.stderr, baseline.stderr);
    std::fs::remove_dir_all(dir).unwrap();
}
