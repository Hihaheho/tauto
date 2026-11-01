//! Native comparisons of concrete trusted inputs and internal callable origins.

use std::hash::{Hash, Hasher};
use std::path::Path;
use std::process::Command;

use tauto_rustgen::{Bindings, Options, Sources, Workspace, workspace};

fn source_source() -> &'static str {
    r#"
effect stop(total: u64): Never resume 0
extern {
  fn native_owned(value: Text): Text
  fn native_borrowed(&value: Text): Text
  fn native_option(&value: Text, present: Bool): Option(Text)
}
fn text_owned_loop(value: Text): Text ! {Div} {
  var index := 0
  while index < 3 { index := index + 1 }
  native_owned(value)
}
fn text_borrowed_loop(value: Text): Text ! {Div} {
  var index := 0
  while index < 3 { index := index + 1 }
  native_borrowed(&value)
}
fn text_option_loop(value: Text, present: Bool): Option(Text) ! {Div} {
  var index := 0
  while index < 3 { index := index + 1 }
  native_option(&value, present)
}
fn linger<T>(value: T, size: i64): T ! {Div} {
  var index := 0
  while index < size { index := index + 1 }
  value
}
fn linger_list<T: Shared>(items: List(T), size: i64): List(T) ! {Div} {
  var index := 0
  while index < size { index := index + 1 }
  items
}
fn offset(value: u64): u64 { value + 1 }
fn repeat(&read: (u64) -> u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < 3 {
    total := total + read(index)
    index := index + 1
  }
  total
}
fn repeat_owned(read: (u64) -> u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < 3 {
    total := total + read(index)
    index := index + 1
  }
  total
}
fn text_owned_run(steps: i64): Text {
  handle { budget(steps: steps) { text_owned_loop(concat("a", "b")) } } with {
    exceeded(info), k => "exhausted"
  }
}
fn text_borrowed_run(steps: i64): Text {
  handle { budget(steps: steps) { text_borrowed_loop(concat("a", "b")) } } with {
    exceeded(info), k => "exhausted"
  }
}
fn text_option_run(steps: i64, present: Bool): Option(Text) {
  handle { budget(steps: steps) { text_option_loop(concat("a", "b"), present) } } with {
    exceeded(info), k => None
  }
}
fn scalar_run(steps: i64): i64 {
  handle { budget(steps: steps) { linger(42, 3) } } with {
    exceeded(info), k => -1
  }
}
fn list_run(steps: i64): u64 {
  handle { budget(steps: steps) {
    match linger_list(Cons("ab", Nil), 3) {
      Nil => 0
      Cons(item, tail) => Text::len(item)
    }
  } } with { exceeded(info), k => 0 }
}
fn borrowed_named_run(steps: i64): u64 {
  handle { budget(steps: steps) { repeat(&offset) } } with {
    exceeded(info), k => 0
  }
}
fn borrowed_literal_run(steps: i64): u64 {
  handle { budget(steps: steps) { repeat(&(value) => offset(value)) } } with {
    exceeded(info), k => 0
  }
}
fn alias_named_run(steps: i64): u64 {
  handle { budget(steps: steps) {
    let local_read := offset
    repeat(&local_read)
  } } with { exceeded(info), k => 0 }
}
fn alias_literal_run(steps: i64): u64 {
  handle { budget(steps: steps) {
    let local_read := (value: u64) => value + 1
    repeat(&local_read)
  } } with { exceeded(info), k => 0 }
}
fn owned_named_run(steps: i64): u64 {
  handle { budget(steps: steps) { repeat_owned(offset) } } with {
    exceeded(info), k => 0
  }
}
fn error_run(steps: i64, divisor: i64): i64 {
  handle { budget(steps: steps) { div(linger(12, 1), divisor) } } with {
    exceeded(info), k => -1
  }
}
fn scan(&read: (Text) -> u64, items: List(Text), abort_at: u64): u64 ! {Div, stop} {
  var index: u64 := 0
  var total: u64 := 0
  var rest := items
  while index < 3 {
    if index == abort_at { perform stop(total) }
    match rest {
      Nil => #()
      Cons(item, tail) => {
        total := total + read(item)
        rest := tail
      }
    }
    index := index + 1
  }
  total
}
fn composed_run(steps: i64, abort_at: u64): Result(u64, Text) {
  handle { budget(steps: steps) {
    let local_read := (value: Text) => match native_option(&value, true) {
      None => 0
      Some(result) => Text::len(result)
    }
    Ok(scan(&local_read, linger_list(Cons("a", Cons("bb", Nil)), 1), abort_at))
  } } with {
    stop(total) => Ok(total)
    exceeded(info), k => Err("exhausted")
  }
}
"#
}

const ENTRIES: &[(&str, bool)] = &[
    ("text_owned", false),
    ("text_borrowed", false),
    ("text_option", false),
    ("scalar", false),
    ("list", false),
    ("borrowed_named", true),
    ("borrowed_literal", true),
    ("alias_named", false),
    ("alias_literal", false),
    ("owned_named", false),
    ("error", false),
    ("composed", false),
];

const HOST: &str = r#"
pub mod host {
    use std::sync::Mutex;
    use std::sync::atomic::Ordering::Relaxed;
    // Harness-only scalar telemetry records codes, lengths and test fuel counts only.
    // It keeps no borrows, values or callbacks and observes no lifetimes.
    // The harness reads it after invocation; it never feeds program results.
    // These finite fixtures do not establish the contract for arbitrary hosts.
    pub static EVENTS: Mutex<Vec<(u64, u64, u64)>> = Mutex::new(Vec::new());
    fn event(kind: u64, value: u64) {
        EVENTS.lock().unwrap().push((kind, value, tauto_rt::budget::ATTEMPTED_TICKS.load(Relaxed)));
    }
    pub struct TextOutput(pub String);
    impl From<TextOutput> for tauto_rt::Text {
        fn from(value: TextOutput) -> Self {
            event(9, value.0.len() as u64);
            Self::from(value.0)
        }
    }
    pub fn native_owned(value: tauto_rt::Text) -> TextOutput {
        event(1, value.len() as u64);
        TextOutput(format!("{}!", &*value))
    }
    pub fn native_borrowed(value: &str) -> TextOutput {
        event(2, value.len() as u64);
        TextOutput(format!("{value}!"))
    }
    pub fn native_option(value: &str, present: bool) -> Option<TextOutput> {
        event(3, value.len() as u64);
        present.then(|| TextOutput(format!("{value}!")))
    }
}
"#;

const MAIN: &str = r#"
use budget_type_extension::{api, host};
use std::sync::atomic::Ordering::Relaxed;
use tauto_rt::budget::*;
const EXPECT_FAST: bool = true;
#[derive(Debug)]
struct Snapshot {
    fast: u64,
    future: u64,
    ticks: u64,
    aborts: u64,
    exhausted: u64,
    events: Vec<(u64, u64, u64)>,
    requests: Vec<(u32, u32, u32, u64)>,
}
fn snapshot() -> Snapshot {
    Snapshot {
        fast: FAST_ENTRIES.swap(0, Relaxed),
        future: FUTURE_ENTRIES.swap(0, Relaxed),
        ticks: ATTEMPTED_TICKS.swap(0, Relaxed),
        aborts: ABORT_EXITS.swap(0, Relaxed),
        exhausted: EXHAUSTED_EXITS.swap(0, Relaxed),
        events: std::mem::take(&mut *host::EVENTS.lock().unwrap()),
        requests: std::mem::take(&mut *REQUESTS.lock().unwrap()),
    }
}
fn check(name: &str, steps: i64, base: Snapshot, qualified: Snapshot, ordinary_fast: bool) {
    assert_eq!(base.fast > 0, EXPECT_FAST && ordinary_fast, "{name}: {base:?}");
    assert_eq!(qualified.fast > 0, EXPECT_FAST, "{name}: {qualified:?}");
    assert_eq!(base.future > 0, !EXPECT_FAST || !ordinary_fast, "{name}: {base:?}");
    assert_eq!(base.ticks, qualified.ticks, "{name}: fuel boundary");
    assert_eq!(base.events, qualified.events, "{name}: call/conversion prefix and order");
    assert_eq!(base.requests, qualified.requests, "{name}: operation and source location");
    if !ordinary_fast { assert_eq!(base.aborts + base.exhausted, 0); }
    println!("{name}:{steps}:ticks={}:events={:?}:requests={:?}", base.ticks, base.events, base.requests);
}
fn error_value(f: impl FnOnce() -> i64) -> Result<i64, (String, Option<(String, u32, u32)>)> {
    // Install a hook without observations before entering either facade.
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    std::panic::set_hook(previous);
    result.map_err(|error| {
        let error = error.downcast::<tauto_rt::TautoError>().expect("runtime arithmetic error");
        (error.message, error.at.map(|at| (at.file.into(), at.line, at.col)))
    })
}
fn main() {
    let token = tauto_rt::budget_contract::TrustedBudgetHost::assert_contract();
    for steps in 0..16 {
        for (name, ordinary, trusted) in [
            ("text_owned", api::text_owned_run as fn(i64)->tauto_rt::Text, api::text_owned_trusted as fn(&tauto_rt::budget_contract::TrustedBudgetHost, i64)->tauto_rt::Text),
            ("text_borrowed", api::text_borrowed_run, api::text_borrowed_trusted),
        ] {
            let a = ordinary(steps); let x = snapshot();
            let b = trusted(&token, steps); let y = snapshot();
            assert_eq!(a, b);
            assert_eq!(&*a, if steps >= 4 { "ab!" } else { "exhausted" });
            assert_eq!(x.ticks, (steps as u64 + 1).min(4));
            assert_eq!(x.events.len(), if steps >= 4 { 2 } else { 0 });
            check(name, steps, x, y, false);
        }
        for present in [false, true] {
            let a = api::text_option_run(steps, present); let x = snapshot();
            let b = api::text_option_trusted(&token, steps, present); let y = snapshot();
            assert_eq!(a, b);
            assert_eq!(a.as_deref(), if steps >= 4 && present { Some("ab!") } else { None });
            assert_eq!(x.ticks, (steps as u64 + 1).min(4));
            assert_eq!(x.events.len(), if steps >= 4 { if present { 2 } else { 1 } } else { 0 });
            check("text_option", steps, x, y, false);
        }
        let a = api::scalar_run(steps); let x = snapshot();
        let b = api::scalar_trusted(&token, steps); let y = snapshot();
        assert_eq!(a, b); assert_eq!(a, if steps >= 4 { 42 } else { -1 });
        assert_eq!(x.ticks, (steps as u64 + 1).min(4));
        check("scalar", steps, x, y, false);
        for (name, ordinary, trusted, expected, ordinary_fast) in [
            ("list", api::list_run as fn(i64)->u64, api::list_trusted as fn(&tauto_rt::budget_contract::TrustedBudgetHost, i64)->u64, 2, false),
            ("borrowed_named", api::borrowed_named_run, api::borrowed_named_trusted, 6, true),
            ("borrowed_literal", api::borrowed_literal_run, api::borrowed_literal_trusted, 6, true),
            ("alias_named", api::alias_named_run, api::alias_named_trusted, 6, false),
            ("alias_literal", api::alias_literal_run, api::alias_literal_trusted, 6, false),
            ("owned_named", api::owned_named_run, api::owned_named_trusted, 6, false),
        ] {
            let a = ordinary(steps); let x = snapshot();
            let b = trusted(&token, steps); let y = snapshot();
            assert_eq!(a, b); assert_eq!(a, if steps >= 4 { expected } else { 0 });
            assert_eq!(x.ticks, (steps as u64 + 1).min(4));
            check(name, steps, x, y, ordinary_fast);
        }
        for divisor in [0, 3] {
            let a = error_value(|| api::error_run(steps, divisor)); let x = snapshot();
            let b = error_value(|| api::error_trusted(&token, steps, divisor)); let y = snapshot();
            assert_eq!(a, b, "arithmetic result/message/location");
            assert_eq!(a.is_err(), steps >= 2 && divisor == 0);
            if steps < 2 { assert_eq!(a, Ok(-1)); }
            assert_eq!(x.ticks, (steps as u64 + 1).min(2));
            check("error", steps, x, y, false);
        }
        for abort_at in [0, 1, 9] {
            let a = api::composed_run(steps, abort_at); let x = snapshot();
            let b = api::composed_trusted(&token, steps, abort_at); let y = snapshot();
            assert_eq!(a, b);
            if steps == 0 { assert!(a.is_err()); }
            let boundary = match abort_at { 0 => 4, 1 => 5, _ => 6 };
            assert_eq!(x.ticks, (steps as u64 + 1).min(boundary));
            assert_eq!(a.is_err(), (steps as u64) < boundary);
            if steps as u64 >= boundary { assert_eq!(a.unwrap(), match abort_at { 0 => 0, 1 => 2, _ => 5 }); }
            assert_eq!(y.aborts, u64::from(EXPECT_FAST && abort_at != 9 && steps as u64 >= boundary));
            assert_eq!(y.exhausted, u64::from(EXPECT_FAST && (steps as u64) < boundary));
            check("composed", steps, x, y, false);
        }
    }
    let at = tauto_rt::Loc { file: "outer host budget", line: 1, col: 1 };
    let mut outer = std::pin::pin!(run(901, 1000, tauto_rt::o::pin(async {
        api::composed_trusted(&token, 100, 9)
    }), at));
    assert!(matches!(tauto_rt::o::poll_once(outer.as_mut()), std::task::Poll::Ready(Ok(5))));
    let nested = snapshot();
    assert_eq!(nested.fast, 0, "active outer budget must force fallback");
    assert_eq!(nested.future, 2);
    println!("outer:ticks={}:events={:?}", nested.ticks, nested.events);
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
            "Err(Interrupted::Abort(abort)) => o::reraise(abort).await,",
            "Err(Interrupted::Abort(abort)) => { ABORT_EXITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed); o::reraise(abort).await },",
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
pub static ABORT_EXITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static EXHAUSTED_EXITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static REQUESTS: std::sync::Mutex<Vec<(u32, u32, u32, u64)>> = std::sync::Mutex::new(Vec::new());
"#);
    replace_once(
        file(workspace, "tauto-rt/src/o.rs"),
        "            self.sent = true;",
        "            self.sent = true;\n            crate::budget::REQUESTS.lock().unwrap().push((op.id, at.line, at.col, crate::budget::ATTEMPTED_TICKS.load(std::sync::atomic::Ordering::Relaxed)));",
    );
}

#[test]
fn concrete_trusted_boundaries_execute_both_generated_paths() {
    let package = tauto_nir::compile_with(source_source(), true).unwrap();
    let entries = ENTRIES
        .iter()
        .map(|(name, _)| format!("{name}_trusted = \"{name}_run\"\n"))
        .collect::<String>();
    let manifest_text = format!(
        r#"rust {{
  extern {{ native_owned = "host::native_owned" native_borrowed = "host::native_borrowed" native_option = "host::native_option" }}
  nonresuming {{
    extern {{ native_owned = "closed-host-v1" native_borrowed = "closed-host-v1" native_option = "closed-host-v1" }}
    entries {{ {entries} }}
  }}
}}"#
    );
    let manifest = tauto::manifest::parse(&manifest_text, Path::new("Tauto.eure")).unwrap();
    let bindings = Bindings::resolve(&package, Some(&manifest), None).unwrap();
    let sources = Sources {
        file: "type-boundaries.taut",
        text: source_source(),
    };
    let reports = tauto_rustgen::budget_diagnostics(&package, &sources, &bindings);
    for (name, ordinary_fast) in ENTRIES {
        let qualified = reports
            .iter()
            .find(|r| r.variant == format!("{name}_trusted"))
            .unwrap();
        assert!(qualified.eligible(), "{name}: {qualified:?}");
        let ordinary = reports
            .iter()
            .find(|r| r.variant == "ordinary" && r.function == format!("{name}_run"))
            .unwrap();
        assert_eq!(ordinary.eligible(), *ordinary_fast, "{name}: {ordinary:?}");
        assert!(ordinary.assumptions.is_empty());
    }
    let mut generated = workspace(
        "budget-type-extension",
        &package,
        &sources,
        &bindings,
        &Options::default(),
    );
    file(&mut generated, "src/lib.rs").push_str(HOST);
    *file(&mut generated, "src/main.rs") = MAIN.into();
    instrument(&mut generated);
    let mut fingerprint = std::collections::hash_map::DefaultHasher::new();
    generated.files.hash(&mut fingerprint);
    let root = std::env::temp_dir().join(format!("tauto-type-boundaries-{}", std::process::id()));
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
                "budget-type-extension",
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
