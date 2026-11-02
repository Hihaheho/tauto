//! A field whose function performs an effect that resumes once: the
//! generated type holds it for any handlers, and a call through the field
//! (by a pattern or by `s.field`) waits for it. So does one in a type
//! argument, and one a field holds from a parameter.

use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

fn run(args: &[&str], source: &str) -> String {
    let dir = std::env::temp_dir().join(format!("tauto-effectful-fields-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    // Tests run at once: each source gets a file of its own.
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let file = dir.join(format!(
        "fields-{}.taut",
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&file, source).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(args)
        .arg(&file)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

fn source() -> &'static str {
    r#"
effect ask(i: i64): i64 resume 1

struct Src { get: (i: i64) -> i64 ! {ask}, pure: () -> i64 ! {ask} }

enum Lazy { More(i64, () -> Lazy ! {ask, Div}), Done }

fn use_src(s: Src): i64 ! {ask} {
  s.get(2) + s.pure()
}

fn lazy(i: i64): Lazy ! {ask, Div} {
  if i == 3 { Done } else { More(perform ask(i), () => lazy(i + 1)) }
}

fn total(l: Lazy): i64 ! {ask, Div} {
  match l {
    More(x, rest) => x + total(rest())
    Done => 0
  }
}

let r := handle { use_src(Src { get: (i: i64) => perform ask(i) + 1, pure: () => 5 }) } with {
  ask(i), k => k(i * 100)
  return v => v
}

let t := handle { total(lazy(0)) } with {
  ask(i), k => k(i + 10)
  return v => v
}

perform show("r", r)
perform show("t", t)
"#
}

#[test]
fn effectful_fields_agree_on_both_backends() {
    let eval = run(&["run"], source());
    assert_eq!(eval, "r = 206\nt = 33\n");
    assert_eq!(eval, run(&["run", "--backend", "rust"], source()));
}

#[test]
fn suspending_function_values_agree_on_both_backends() {
    let source = r#"
import std::prelude::Par

effect ask(i: i64): i64 resume 1

struct Job { run: () -> Unit ! {ask, Div} }

fn first(l: List(Job)): Option(() -> Unit ! {ask, Div}) {
  match l {
    Nil => None
    Cons(j, t) => Some(j.run)
  }
}

fn keep(log: Ref(List(i64)), f: () -> Unit ! {ask, Div}): List(Job) {
  Cons(Job { run: () => f() }, Nil)
}

fn run_first(l: List(Job)): Unit ! {ask, Div} {
  match first(l) {
    None => #()
    Some(f) => f()
  }
}

let log := Ref::new(Nil)
let jobs := keep(log, () => Ref::set(log, Cons(perform ask(1), Ref::get(log))))
handle { run_first(jobs) } with {
  ask(i), k => k(i + 41)
  return v => v
}
perform show("log", Ref::get(log))
perform show("cell", Ref::new(7))
"#;
    let eval = run(&["run"], source);
    assert_eq!(eval, "log = Cons(42, Nil)\ncell = Ref(7)\n");
    assert_eq!(eval, run(&["run", "--backend", "rust"], source));
}

#[test]
fn literal_none_effect_arguments_agree_on_both_backends() {
    let source = r#"
effect ask(i: i64, n: Option(i64)): i64 resume 1
effect stop(n: Option(i64)): Never resume 0

fn pick(i: i64, n: Option(i64)): i64 {
  match n { None => i + 41, Some(x) => x }
}

let r := handle { perform ask(1, None) } with {
  ask(i, n), k => k(pick(i, n))
  return v => v
}

let s := handle { perform stop(None) } with {
  stop(n) => pick(0, n)
  return v => v
}

perform show("r", r)
perform show("s", s)
"#;
    let eval = run(&["run"], source);
    assert_eq!(eval, "r = 42\ns = 41\n");
    assert_eq!(eval, run(&["run", "--backend", "rust"], source));
}

#[test]
fn effectful_function_items_as_callbacks_agree_on_both_backends() {
    let source = r#"
import std::prelude::Os

effect log(m: Text): Unit resume 1

fn hello(): Unit ! {log, stdout} {
  perform log("hi")
  perform stdout(" hello\n")
}

fn apply(g: () -> Unit ! {log, stdout}): Unit ! {log, stdout} { g() }

handle { apply(hello) } with {
  log(m), k => { perform stdout("direct ")
 perform stdout(m)
 k(#()) }
  return v => v
}

handle {
  let f := hello
  apply(f)
} with {
  log(m), k => { perform stdout("bound ")
 perform stdout(m)
 k(#()) }
  return v => v
}
"#;
    let eval = run(&["run"], source);
    assert_eq!(eval, "direct hi hello\nbound hi hello\n");
    assert_eq!(eval, run(&["run", "--backend", "rust"], source));
}
