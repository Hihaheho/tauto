//! A program of several files (`docs/design/self-host.md`): `import` for `run`,
//! the spans of each file, and `--steps`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use tauto::eval::{RunError, RunOptions, run_program_with};
use tauto::program::load;

fn dir(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tauto-programs-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    d
}

fn shows(entry: &Path) -> Result<Vec<String>, String> {
    let loaded = load(entry)?;
    let outcome = run_program_with(&loaded.program, 1_000_000, RunOptions::default())
        .map_err(|e| e.to_string())?;
    Ok(outcome
        .outputs
        .iter()
        .map(|(n, v)| format!("{n} = {v}"))
        .collect())
}

fn tauto(args: &[&str]) -> (String, String, bool) {
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(args)
        .output()
        .unwrap();
    (
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
        out.status.success(),
    )
}

#[test]
fn import_twice_reads_once() {
    let d = dir("twice");
    fs::write(d.join("a.nib"), &r#"pub fn one(): i64 { 1 }"#.to_string()).unwrap();
    fs::write(
        d.join("b.nib"),
        &r#"import "a.nib"
pub fn two(): i64 { one() + 1 }"#
            .to_string(),
    )
    .unwrap();
    fs::write(
        d.join("main.nib"),
        &r#"import "a.nib"
import "b.nib"
perform show("x", two())"#
            .to_string(),
    )
    .unwrap();
    assert_eq!(shows(&d.join("main.nib")).unwrap(), ["x = 2"]);
    let loaded = load(&d.join("main.nib")).unwrap();
    assert_eq!(loaded.files.len(), 3);
    let fns = loaded
        .program
        .stmts
        .iter()
        .filter(|s| matches!(s, tauto::surface::Stmt::Fn(f) if f.name == "one"))
        .count();
    assert_eq!(fns, 1);
}

/// Each file declares its own `f`; the full name says which one is meant.
#[test]
fn error_is_located_in_its_file() {
    let d = dir("located");
    fs::write(
        d.join("b.nib"),
        &r#"pub fn ok(): i64 { 1 }

let x: i64 := true
"#
        .to_string(),
    )
    .unwrap();
    fs::write(
        d.join("main.nib"),
        &r#"import "b.nib"
perform show("x", 1)"#
            .to_string(),
    )
    .unwrap();
    let main = d.join("main.nib");
    let (_, stderr, success) = tauto(&["run", main.to_str().unwrap()]);
    assert!(!success);
    let want = format!("{}:3:", d.join("b.nib").display());
    assert!(stderr.starts_with(&want), "{stderr}");
}

#[test]
fn the_spans_of_files_do_not_overlap() {
    let d = dir("spans");
    fs::write(
        d.join("a.nib"),
        &r#"pub fn one(): i64 { 1 }
"#
        .to_string(),
    )
    .unwrap();
    fs::write(
        d.join("main.nib"),
        &r#"import "a.nib"
perform show("x", one())"#
            .to_string(),
    )
    .unwrap();
    let loaded = load(&d.join("main.nib")).unwrap();
    let [a, main] = loaded.files.as_slice() else {
        panic!("two files");
    };
    assert_eq!(a.base, 0);
    assert_eq!(main.base, a.text.len() as u32 + 1);
    assert_eq!(loaded.locate(main.base + 16).unwrap().1, 2);
    assert_eq!(loaded.locate(3).unwrap().1, 1);
}

#[test]
fn the_step_limit_is_given_by_steps() {
    let d = dir("steps");
    fs::write(d.join("main.nib"), r#"while true { }"#).unwrap();
    let main = d.join("main.nib");
    let (_, stderr, success) = tauto(&["run", "--steps", "1000", main.to_str().unwrap()]);
    assert!(!success);
    assert!(
        stderr.contains("interrupted: the step limit ran out"),
        "{stderr}"
    );
    let loaded = load(&main).unwrap();
    assert_eq!(
        run_program_with(&loaded.program, 1000, RunOptions::default()),
        Err(RunError::Interrupted)
    );
}

#[test]
fn steps_still_limit_a_run_that_allows_div() {
    let d = dir("allow-div");
    fs::write(d.join("main.nib"), r#"while true { }"#).unwrap();
    let main = d.join("main.nib");
    let (_, stderr, success) = tauto(&[
        "run",
        "--steps",
        "1000",
        "--allow-div",
        main.to_str().unwrap(),
    ]);
    assert!(!success);
    assert!(
        stderr.contains("interrupted: the step limit ran out"),
        "{stderr}"
    );
    assert!(stderr.contains("`--allow-div` lifts it"), "{stderr}");
}

/// The machine of `tauto-vm` in `tauto` itself (`TAUTO_VM=rust`) stops at
/// `--steps` with the same message as the tote machine.
#[test]
fn steps_still_limit_an_in_process_vm_run_that_allows_div() {
    let d = dir("allow-div-in-process");
    fs::write(d.join("main.nib"), r#"while true { }"#).unwrap();
    let main = d.join("main.nib");
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .env("TAUTO_LANG", "en")
        .env("TAUTO_VM", "rust")
        .args([
            "run",
            "--steps",
            "1000",
            "--allow-div",
            main.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(!out.status.success(), "{stderr}");
    assert!(
        stderr.contains("interrupted: the step limit ran out after 1000 steps;"),
        "{stderr}"
    );
    assert!(stderr.contains("`--allow-div` lifts it"), "{stderr}");
}

/// A single file runs code written with inductive types, as a tote does: the
/// proof-language declarations are extracted first.
#[test]
fn a_file_runs_proof_language_functions() {
    let d = dir("inductive");
    let base = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std/Base.taut");
    let file = d.join("main.taut");
    fs::write(
        &file,
        format!(
            r#"import "{}"
fn plus2(n: Nat): Nat {{ Succ(Succ(n)) }}
perform show("a", Nat::add(plus2(1), 2))
"#,
            base.canonicalize().unwrap().display().to_string()
        ),
    )
    .unwrap();
    let (out, err, ok) = tauto(&["run", file.to_str().unwrap()]);
    assert!(ok, "{err}");
    assert_eq!(out, "a = 5\n");
    let (out, err, ok) = tauto(&["test", d.to_str().unwrap()]);
    assert!(ok, "{out}{err}");
}

// What `tauto run` prints for code with effects and handlers is what the
// checker computes from the same code read as computation trees.
#[test]
fn running_and_proving_effects_agree() {
    let d = dir("effect-agreement");
    let source = EFFECT_PROGRAMS;
    let names = ["r", "s", "ticked", "summed"];
    let run = d.join("run.taut");
    let shows: String = names
        .iter()
        .map(|n| format!("perform show(\"{n}\", {n}())\n"))
        .collect();
    fs::write(&run, format!("{source}{shows}")).unwrap();
    let (out, err, ok) = tauto(&["run", run.to_str().unwrap()]);
    assert!(ok, "{err}");
    let values: Vec<(String, String)> = out
        .lines()
        .map(|l| {
            let (n, v) = l.split_once(" = ").unwrap();
            (n.to_string(), v.to_string())
        })
        .collect();
    assert_eq!(values.len(), names.len(), "{out}");
    let check = |values: &[(String, String)]| {
        let file = d.join("check.taut");
        let theorems: String = values
            .iter()
            .map(|(n, v)| format!("theorem {n}_is(): Eq(Nat, {n}(), {v}) {{ Refl }}\n"))
            .collect();
        fs::write(&file, format!("{source}{theorems}")).unwrap();
        tauto(&["check", file.to_str().unwrap()])
    };
    let (out, err, ok) = check(&values);
    assert!(
        ok && out.contains(" 0 failed") && out.contains(" 0 skipped"),
        "{out}{err}"
    );
    let mut wrong = values.clone();
    wrong[2].1 = format!("{}0", wrong[2].1);
    let (_, _, ok) = check(&wrong);
    assert!(!ok);
}

const EFFECT_PROGRAMS: &str = r#"import std.Nat
effect tick(): Unit
effect flip(): Bool resume ω
fn g(n: Nat): Nat { Succ(n) }
fn f(n: Nat): Nat ! {tick} {
  perform tick()
  Succ(g(n))
}
fn h(n: Nat): Nat ! {flip} {
  let b := perform flip()
  if b { Succ(n) } else { n }
}
fn both(n: Nat): Nat ! {tick, flip} {
  perform tick()
  let m := h(n)
  perform tick()
  m + h(m)
}
fn r(): Nat { handle { f(Zero) } with { tick(), k => k(Star) } }
fn s(): Nat { handle { h(Succ(Zero)) } with { flip(), k => k(true) + k(false) } }
fn ticked(): Nat {
  var c: Nat := Zero
  handle {
    handle { both(2) } with { flip(), k => k(true) + k(false) }
  } with {
    tick(), k => {
      c := Succ(c)
      k(Star)
    }
  }
  c
}
fn summed(): Nat {
  handle {
    handle { both(1) } with { flip(), k => k(true) + k(false) }
  } with {
    tick(), k => k(Star)
    return v => v + 10
  }
}
"#;

#[test]
fn text_of_bytes_runs() {
    let d = dir("text-bytes");
    let f = d.join("t.taut");
    fs::write(
        &f,
        "import std.Text\nimport std.TextOps\n\
         fn bytes(): Text { Text.Mk(Cons(104, Cons(195, Cons(169, Nil)))) }\n\
         fn slice(): Text { Text.slice_or_empty(\"héllo\", 1, 3) }\n\
         fn joined(): Text { Text.join(\"-\", Text.split_on(\"a,b,c\", 44)) }\n\
         fn decoded(): Option(Text) { Text.of_utf8(Cons(195, Cons(169, Nil))) }\n\
         perform show(\"bytes\", bytes())\n\
         perform show(\"slice\", slice())\n\
         perform show(\"joined\", joined())\n\
         perform show(\"decoded\", decoded())\n",
    )
    .unwrap();
    let (out, err, ok) = tauto(&["run", f.to_str().unwrap()]);
    assert!(ok, "{err}");
    assert_eq!(
        out,
        "bytes = \"hé\"\nslice = \"é\"\njoined = \"a-b-c\"\ndecoded = Some(\"é\")\n"
    );
    // Bytes that are not UTF-8 have no `Text` to run as: the program stops.
    fs::write(
        &f,
        "import std.Text\nfn bad(): Text { Text.Mk(Cons(255, Nil)) }\nperform show(\"bad\", bad())\n",
    )
    .unwrap();
    let (_, _, ok) = tauto(&["run", f.to_str().unwrap()]);
    assert!(!ok);
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn text_of_bytes_in_a_function_value_runs() {
    let d = dir("text-bytes-lambda");
    let f = d.join("t.taut");
    fs::write(
        &f,
        "import std.Text\n\
         fn then_<A, B>(o: Option(A), f: (x: A) -> Option(B)): Option(B) {\n\
         match o: Option(B) {\n None => None\n Some(a) => f(a)\n }\n}\n\
         fn mk(o: Option(List(Nat))): Option(Text) {\n\
         then_(o, (bs: List(Nat)) => Some(Text.Mk(bs)))\n}\n\
         fn go(): Option(Text) { mk(Some(Cons(104, Cons(105, Nil)))) }\n\
         perform show(\"r\", go())\n",
    )
    .unwrap();
    let (out, err, ok) = tauto(&["run", f.to_str().unwrap()]);
    assert!(ok, "{err}");
    assert_eq!(out, "r = Some(\"hi\")\n");
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn an_undefined_name_in_a_checked_function_is_given_by_line_and_column() {
    let d = dir("undefined-line-col");
    let f = d.join("e.taut");
    fs::write(
        &f,
        "fn ones(n: Nat): Nat {\n    match n: Nat {\n        Zero => 0\n        Succ(rest) => nope(rest)\n    }\n}\nperform show(\"x\", ones(2))\n",
    )
    .unwrap();
    let (_, err, ok) = tauto(&["run", f.to_str().unwrap()]);
    assert!(!ok);
    let want = format!("{}:4:23: ones: `nope` is not defined", f.display());
    assert!(err.contains(&want), "{err}");
    assert!(!err.contains("(byte"), "{err}");
    fs::remove_dir_all(d).unwrap();
}

/// A function that runs as written calls the functions of `std/Stack.taut`
/// that extraction writes out at each call, as the proofs' calls are written.
#[test]
fn a_function_run_as_written_calls_the_stack_functions() {
    let d = dir("runtime-stack");
    let stack = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std/Stack.taut");
    let file = d.join("main.taut");
    fs::write(
        &file,
        format!(
            r#"import "{}"
fn count(): Nat {{
  var s: Stack(Nat) := Stack::new()
  eprint("counting\n")
  Stack::push(&mut s, Succ(Succ(Zero)))
  Stack::push(&mut s, 5)
  let top: Option(Nat) := Stack::pop(&mut s)
  let empty: Bool := Stack::is_empty(&s)
  Stack::len(&s)
}}
perform show("n", count())
"#,
            stack.canonicalize().unwrap().display().to_string()
        ),
    )
    .unwrap();
    let (out, err, ok) = tauto(&["run", file.to_str().unwrap()]);
    assert!(ok, "{err}");
    assert_eq!(out, "n = 1\n");
    assert_eq!(err, "counting\n");
    fs::remove_dir_all(d).unwrap();
}

/// `tauto run` writes what the program prints as it prints it: a program
/// that is still running has already shown its earlier lines.
#[test]
fn run_writes_output_before_the_program_ends() {
    use std::io::{BufRead, BufReader};
    let d = dir("live-output");
    let file = d.join("main.taut");
    fs::write(
        &file,
        "perform stderr(\"first\\n\")\nperform sleep(5000)\nperform stderr(\"second\\n\")\n",
    )
    .unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(["run", file.to_str().unwrap()])
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let mut err = BufReader::new(child.stderr.take().unwrap());
    let mut line = String::new();
    err.read_line(&mut line).unwrap();
    assert_eq!(line, "first\n");
    assert!(
        child.try_wait().unwrap().is_none(),
        "the program has already ended"
    );
    let mut rest = String::new();
    std::io::Read::read_to_string(&mut err, &mut rest).unwrap();
    assert_eq!(rest, "second\n");
    assert!(child.wait().unwrap().success());
}
