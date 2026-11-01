//! Native fuel and source-location equivalence for typed projection paths.

use std::hash::{Hash, Hasher};
use std::path::Path;
use std::process::Command;

use tauto_rustgen::{Bindings, Options, Sources, Workspace, workspace};

fn source_source() -> &'static str {
    r#"
struct Inner { values: List(u64) }
struct Outer { inner: Inner }
struct Deep { outer: Outer }
shared struct Wrapped(T: Shared) { item: T }
fn count(xs: List(u64)): u64 ! {Div} {
  match xs {
    Nil => 0
    Cons(head, tail) => 1 + count(tail)
  }
}
fn count_generic<T: Shared>(xs: List(T)): u64 ! {Div} {
  match xs {
    Nil => 0
    Cons(head, tail) => 1 + count_generic(tail)
  }
}
fn inspect(value: Outer): u64 ! {Div} { count(value.inner.values) }
fn inspect_split(value: Outer): u64 ! {Div} {
  let inner := value.inner
  count(inner.values)
}
fn inspect_deep(value: Deep): u64 ! {Div} { count(value.outer.inner.values) }
fn inspect_generic<T: Shared>(value: Wrapped(Wrapped(List(T)))): u64 ! {Div} {
  count_generic(value.item.item)
}
fn inspect_borrowed(&value: Outer): u64 ! {Div} { count(value.inner.values) }
fn run(value: Outer): u64 {
  handle { budget(steps: 100) { inspect(value) } } with { exceeded(info), k => 0 }
}
fn nested_run(steps: i64, value: Outer): u64 {
  handle { budget(steps: steps) { inspect(value) } } with { exceeded(info), k => 0 }
}
fn split_run(steps: i64, value: Outer): u64 {
  handle { budget(steps: steps) { inspect_split(value) } } with { exceeded(info), k => 0 }
}
fn deep_run(steps: i64, value: Deep): u64 {
  handle { budget(steps: steps) { inspect_deep(value) } } with { exceeded(info), k => 0 }
}
fn generic_run(steps: i64, value: Wrapped(Wrapped(List(u64)))): u64 {
  handle { budget(steps: steps) { inspect_generic(value) } } with { exceeded(info), k => 0 }
}
fn borrowed_run(steps: i64, &value: Outer): u64 {
  handle { budget(steps: steps) { inspect_borrowed(value) } } with { exceeded(info), k => 0 }
}
"#
}

const ENTRIES: &[(&str, &str)] = &[
    ("run", "run_trusted"),
    ("nested_run", "nested_trusted"),
    ("split_run", "split_trusted"),
    ("deep_run", "deep_trusted"),
    ("generic_run", "generic_trusted"),
    ("borrowed_run", "borrowed_trusted"),
];

const MAIN: &str = r#"
use budget_nested_projection::api;
use std::sync::atomic::Ordering::Relaxed;
use tauto_rt::budget::*;
use tauto_rt::budget_contract::TrustedBudgetHost;
const EXPECT_FAST: bool = true;
#[derive(Debug)]
struct Snapshot {
    fast: u64,
    future: u64,
    ticks: u64,
    exhausted: u64,
    requests: Vec<(u32, String, u32, u32, u64)>,
}
fn snapshot() -> Snapshot {
    Snapshot {
        fast: FAST_ENTRIES.swap(0, Relaxed),
        future: FUTURE_ENTRIES.swap(0, Relaxed),
        ticks: ATTEMPTED_TICKS.swap(0, Relaxed),
        exhausted: EXHAUSTED_EXITS.swap(0, Relaxed),
        requests: std::mem::take(&mut *REQUESTS.lock().unwrap()),
    }
}
fn list(length: u64) -> api::List<u64> {
    (0..length).fold(api::List::Nil, |tail, head| api::List::Cons(head, tauto_rt::Rc::new(tail).into()))
}
fn input(length: u64) -> api::Outer {
    api::Outer { inner: api::Inner { values: list(length) } }
}
fn generic_input(length: u64) -> api::Wrapped<api::Wrapped<api::List<u64>>> {
    api::Wrapped { item: api::Wrapped { item: list(length) } }
}
fn check(
    name: &str,
    steps: i64,
    length: u64,
    ordinary: impl FnOnce() -> u64,
    trusted: impl FnOnce() -> u64,
) {
    let value = ordinary();
    let base = snapshot();
    let qualified_value = trusted();
    let qualified = snapshot();
    let boundary = length + 2;
    let exhausted = (steps as u64) < boundary;
    assert_eq!(value, if exhausted { 0 } else { length }, "{name}: count/fuel boundary");
    assert_eq!(value, qualified_value, "{name}: ordinary/trusted result");
    assert_eq!(base.fast, 0, "{name}: ordinary entry stays conservative");
    assert_eq!(base.future, 1);
    assert_eq!(qualified.fast, u64::from(EXPECT_FAST), "{name}: {qualified:?}");
    assert_eq!(qualified.future, u64::from(!EXPECT_FAST), "{name}: {qualified:?}");
    assert_eq!(base.ticks, (steps as u64 + 1).min(boundary), "{name}: attempted ticks");
    assert_eq!(base.ticks, qualified.ticks, "{name}: ordinary/trusted ticks");
    assert_eq!(base.exhausted, 0);
    assert_eq!(qualified.exhausted, u64::from(EXPECT_FAST && exhausted));
    assert_eq!(base.requests, qualified.requests, "{name}: operation payload site and order");
    let expected_requests = if exhausted {
        let (line, col) = expected_location(name);
        vec![(OP_EXCEEDED.id, "nested-projection.taut".to_owned(), line, col, base.ticks)]
    } else { Vec::new() };
    assert_eq!(base.requests, expected_requests, "{name}: own budget source location");
    println!("{name}:{steps}:{length}:value={value}:ticks={}:requests={:?}", base.ticks, base.requests);
}
fn main() {
    let token = TrustedBudgetHost::assert_contract();
    for length in [0, 1, 3, 7, 96, 98, 99] {
        check("run", 100, length, || api::run(input(length)), || api::run_trusted(&token, input(length)));
        for steps in 0..=(length as i64 + 3) {
            check("nested_run", steps, length, || api::nested_run(steps, input(length)), || api::nested_trusted(&token, steps, input(length)));
            check("split_run", steps, length, || api::split_run(steps, input(length)), || api::split_trusted(&token, steps, input(length)));
            check("deep_run", steps, length, || api::deep_run(steps, api::Deep { outer: input(length) }), || api::deep_trusted(&token, steps, api::Deep { outer: input(length) }));
            check("generic_run", steps, length, || api::generic_run(steps, generic_input(length)), || api::generic_trusted(&token, steps, generic_input(length)));
            let borrowed = input(length);
            check("borrowed_run", steps, length, || api::borrowed_run(steps, &borrowed), || api::borrowed_trusted(&token, steps, &borrowed));
            assert_eq!(api::borrowed_run(1000, &borrowed), length, "borrowed source remains reusable");
            let _ = snapshot();
        }
    }
}
"#;

fn file<'a>(workspace: &'a mut Workspace, path: &str) -> &'a mut String {
    &mut workspace
        .files
        .iter_mut()
        .find(|(name, _)| name == path)
        .unwrap()
        .1
}

fn replace_once(text: &mut String, from: &str, to: &str) {
    assert_eq!(
        text.matches(from).count(),
        1,
        "instrumentation site: {from}"
    );
    *text = text.replace(from, to);
}

fn instrument(workspace: &mut Workspace) {
    let budget = file(workspace, "tauto-rt/src/budget.rs");
    for (from, to) in [
        (
            "    let result = {",
            "    FAST_ENTRIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n    let result = {",
        ),
        (
            "    let left = Rc::new(Cell::new(",
            "    FUTURE_ENTRIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n    let left = Rc::new(Cell::new(",
        ),
        (
            "        let out = STACK.with",
            "        ATTEMPTED_TICKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n        let out = STACK.with",
        ),
        (
            "        if self.left.get() == 0 {",
            "        ATTEMPTED_TICKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n        if self.left.get() == 0 {",
        ),
        (
            "        Err(Interrupted::Exhausted) => {",
            "        Err(Interrupted::Exhausted) => {\n            EXHAUSTED_EXITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);",
        ),
    ] {
        replace_once(budget, from, to);
    }
    budget.push_str(r#"
pub static FAST_ENTRIES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static FUTURE_ENTRIES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static ATTEMPTED_TICKS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static EXHAUSTED_EXITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static REQUESTS: std::sync::Mutex<Vec<(u32, String, u32, u32, u64)>> = std::sync::Mutex::new(Vec::new());
"#);
    replace_once(
        file(workspace, "tauto-rt/src/o.rs"),
        "            self.sent = true;",
        "            self.sent = true;\n            crate::budget::REQUESTS.lock().unwrap().push((op.id, at.file.into(), at.line, at.col, crate::budget::ATTEMPTED_TICKS.load(std::sync::atomic::Ordering::Relaxed)));",
    );
}

#[test]
fn nested_split_generic_and_borrowed_projections_execute_with_identical_fuel() {
    let package = tauto_nir::compile_with(source_source(), true).unwrap();
    let entries = ENTRIES
        .iter()
        .map(|(function, facade)| format!("{facade} = \"{function}\"\n"))
        .collect::<String>();
    let manifest = tauto::manifest::parse(
        &format!("rust {{ nonresuming {{ entries {{ {entries} }} }} }}"),
        Path::new("Tauto.eure"),
    )
    .unwrap();
    let bindings = Bindings::resolve(&package, Some(&manifest), None).unwrap();
    let sources = Sources {
        file: "nested-projection.taut",
        text: source_source(),
    };
    let reports = tauto_rustgen::budget_diagnostics(&package, &sources, &bindings);
    let mut locations =
        String::from("\nfn expected_location(name: &str) -> (u32, u32) { match name {\n");
    for (function, facade) in ENTRIES {
        let qualified = reports.iter().find(|r| r.variant == *facade).unwrap();
        assert!(qualified.eligible(), "{function}: {qualified:?}");
        let ordinary = reports
            .iter()
            .find(|r| r.variant == "ordinary" && r.function == *function)
            .unwrap();
        assert!(!ordinary.eligible(), "{function}: {ordinary:?}");
        assert!(ordinary.assumptions.is_empty());
        let before = &source_source()[..ordinary.span.start as usize];
        let line = before.matches('\n').count() + 1;
        let col = before.rsplit('\n').next().unwrap().chars().count() + 1;
        locations.push_str(&format!("{function:?} => ({line}, {col}),\n"));
    }
    locations.push_str("_ => panic!(\"unknown fixture\"), } }\n");
    let mut generated = workspace(
        "budget-nested-projection",
        &package,
        &sources,
        &bindings,
        &Options::default(),
    );
    *file(&mut generated, "src/main.rs") = format!("{MAIN}{locations}");
    instrument(&mut generated);
    let mut fingerprint = std::collections::hash_map::DefaultHasher::new();
    generated.files.hash(&mut fingerprint);
    let root = std::env::temp_dir().join(format!("tauto-nested-projection-{}", std::process::id()));
    let target = std::env::var_os("TAUTO_NATIVE_TEST_TARGET")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| root.join("target"))
        .join(format!("{:016x}", fingerprint.finish()));
    let mut outputs = Vec::new();
    for variant in ["qualified", "forced-future", "runtime-sync"] {
        if variant == "forced-future" {
            replace_once(
                file(&mut generated, "tauto-rt/src/budget.rs"),
                "    !cfg!(feature = \"sync\") && STACK.with(|s| s.borrow().is_empty())",
                "    false",
            );
            replace_once(
                file(&mut generated, "src/main.rs"),
                "const EXPECT_FAST: bool = true;",
                "const EXPECT_FAST: bool = false;",
            );
        } else if variant == "runtime-sync" {
            replace_once(
                file(&mut generated, "tauto-rt/src/budget.rs"),
                "pub fn can_run_nonresuming() -> bool {\n    false\n}",
                "pub fn can_run_nonresuming() -> bool {\n    !cfg!(feature = \"sync\") && STACK.with(|s| s.borrow().is_empty())\n}",
            );
            replace_once(
                file(&mut generated, "Cargo.toml"),
                "tauto-rt = { path = \"tauto-rt\" }",
                "tauto-rt = { path = \"tauto-rt\", features = [\"sync\"] }",
            );
        }
        let binary = generated
            .build(
                "budget-nested-projection",
                &root.join("generated"),
                &target.join(variant),
                false,
            )
            .unwrap();
        let output = Command::new(binary).output().unwrap();
        assert!(
            output.status.success(),
            "{variant}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            output.stderr.is_empty(),
            "{variant}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        outputs.push(output.stdout);
    }
    assert_eq!(outputs[0], outputs[1], "forced original path");
    assert_eq!(outputs[0], outputs[2], "runtime feature fallback");
    std::fs::remove_dir_all(root).unwrap();
}
