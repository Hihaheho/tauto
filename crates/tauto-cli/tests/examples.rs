//! The examples run on the evaluator and on the Rust backend and print the
//! same lines; the example with a bridge crate
//! runs on the backend only.

use std::path::PathBuf;
use std::process::Command;

fn example(path: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(path)
}

/// A run of an example in this repository is a run in the project whose `Tauto.eure` trusts
/// commands: the approval is kept in a home of its own, not in the home of whoever runs the
/// tests, so that what the tests approve is not left there and what the user approved earlier
/// does not decide them.
fn isolate(command: &mut Command) {
    let home = std::env::temp_dir().join(format!("tauto-examples-home-{}", std::process::id()));
    command.arg("--approve-trust").env("TAUTO_HOME", home);
}

fn stdout(args: &[&str], path: &PathBuf) -> String {
    stdout_built_in(args, path, None)
}

/// `stdout`, with the generated crates built under `target_dir` when it is
/// given: two runs of one package name in one directory would share a build.
fn stdout_built_in(args: &[&str], path: &PathBuf, target_dir: Option<&PathBuf>) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
    if args.iter().any(|a| *a == "--tote") {
        let args: Vec<&str> = args.iter().copied().filter(|a| *a != "--tote").collect();
        command.current_dir(path).args(&args).arg(".");
    } else {
        command.args(args).arg(path);
    }
    isolate(&mut command);
    if let Some(dir) = target_dir {
        command.env("TAUTO_TARGET_DIR", dir);
    }
    let out = command.output().unwrap();
    assert!(
        out.status.success(),
        "{args:?} {}: {}",
        path.display(),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn handlers_agree_on_both_backends() {
    let path = example("handlers.taut");
    let eval = stdout(&["run"], &path);
    let rust = stdout(&["run", "--backend", "rust"], &path);
    assert!(!eval.is_empty());
    assert_eq!(eval, rust);
}

#[test]
fn effects_agree_on_both_backends() {
    let path = example("effects.taut");
    let eval = stdout(&["run"], &path);
    assert_eq!(eval, "42\n-1\n66\n7\n");
    assert_eq!(eval, stdout(&["run", "--backend", "rust"], &path));
}

#[test]
fn streams_agree_on_both_backends() {
    let path = example("streams.taut");
    let eval = stdout(&["run"], &path);
    assert_eq!(
        eval,
        "30\n10\n9\n60\n5\n"
    );
    assert_eq!(eval, stdout(&["run", "--backend", "rust"], &path));
}

#[test]
fn ownership_agrees_on_both_backends() {
    let path = example("ownership.taut");
    let niri = stdout(&["run", "--check-ownership"], &path);
    assert_eq!(niri, "3\n9\n12\n");
    assert_eq!(niri, stdout(&["run", "--backend", "rust"], &path));
}

#[test]
fn the_files_example_runs_with_its_bridge() {
    let rust = stdout(&["run", "--backend", "rust"], &example("rust/files"));
    assert_eq!(rust, "\"HELLO\"\n5\n");
}

#[test]
fn the_regex_demo_runs_with_its_generated_bindings() {
    let rust = stdout(&["run", "--backend", "rust"], &example("rust/regex_demo"));
    assert_eq!(
        rust,
        "true\nfalse\n\"a+b\"\n\"aaab\"\n1\n1\nSome(5)\nSome(5)\n\"ab\"\n\"aab\"\n\"aaab\"\n1\n1\n\"1\"\n\"2\"\n\"3\"\n\"1\"\n\"2aab3\"\nBuf { .. }\nBuf { .. }\nBuf { .. }\n"
    );
}

#[test]
fn the_json_demo_runs_with_its_generated_bindings() {
    let rust = stdout(&["run", "--backend", "rust"], &example("rust/json_demo"));
    assert_eq!(rust, "false\ntrue\n\"[1,2,3]\"\ntrue\n");
}

#[test]
fn the_tasks_example_runs_on_threads() {
    let rust = stdout(&["run", "--backend", "rust"], &example("rust/tasks"));
    assert_eq!(
        rust,
        "2001\n4000\n2000\n1\n"
    );
}

/// `rust.executor = "tokio"`: the generated `main` builds a tokio runtime and
/// the bodies of tasks run on its blocking pool.
#[test]
fn the_tasks_example_runs_on_tokio() {
    let dir = std::env::temp_dir().join(format!("tauto-tasks-tokio-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("bridge/src")).unwrap();
    std::fs::create_dir_all(dir.join("src")).unwrap();
    let src = example("rust/tasks");
    for f in ["src/main.taut", "bridge/Cargo.toml", "bridge/src/lib.rs"] {
        std::fs::copy(src.join(f), dir.join(f)).unwrap();
    }
    let manifest = std::fs::read_to_string(src.join("Tauto.eure"))
        .unwrap()
        .replace("rust {\n", "rust {\n  executor = \"tokio\"\n");
    std::fs::write(dir.join("Tauto.eure"), manifest).unwrap();
    let rust = stdout_built_in(
        &["run", "--backend", "rust"],
        &dir,
        Some(&dir.join("build")),
    );
    assert_eq!(
        rust,
        "2001\n4000\n2000\n1\n"
    );
}

/// A program that starts tasks may move its values between threads: an extern
/// type that is not `Send + Sync` is refused where it is bound.
#[test]
fn an_extern_type_that_cannot_cross_threads_is_refused() {
    let dir = std::env::temp_dir().join(format!("tauto-tasks-bad-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("bridge/src")).unwrap();
    std::fs::create_dir_all(dir.join("src")).unwrap();
    let src = example("rust/tasks");
    for f in ["Tauto.eure", "src/main.taut", "bridge/Cargo.toml"] {
        std::fs::copy(src.join(f), dir.join(f)).unwrap();
    }
    std::fs::write(
        dir.join("bridge/src/lib.rs"),
        r#"use std::cell::Cell;
use std::rc::Rc;

#[derive(Clone)]
pub struct Counter(Rc<Cell<u64>>);

pub fn counter_new() -> Counter {
    Counter(Rc::new(Cell::new(0)))
}

pub fn counter_add(c: Counter, n: u64) {
    c.0.set(c.0.get() + n);
}

pub fn counter_get(c: Counter) -> u64 {
    c.0.get()
}
"#,
    )
    .unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
    command
        .args(["run", "--backend", "rust"])
        .arg(&dir)
        .env("TAUTO_TARGET_DIR", dir.join("build"));
    isolate(&mut command);
    let out = command.output().unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("the extern type Counter cannot cross threads"),
        "{stderr}"
    );
}

#[test]
fn well_founded_recursion_runs_as_written_on_both_backends() {
    // `decreasing_by` functions run as the recursion they are written as, the proofs of the
    // calls left out; the evaluator and the Rust backend agree.
    let path = example("wf");
    let eval = stdout(&["run", "--tote"], &path);
    let rust = stdout(&["run", "--backend", "rust"], &path);
    assert_eq!(eval, "4\n3 7 5 \n13\n");
    assert_eq!(eval, rust);
}

/// A tote that reads text with an `inductive_syntax!` and whose rules `mode!`
/// turns into a checker runs: `std/mode.taut`'s functions are macro code, run
/// while the program is read, and are not part of what runs.
#[test]
fn typed_lang_reads_checks_and_runs_text() {
    use std::io::Write;
    use std::process::Stdio;

    let typed = example("typed-lang");
    let mut child = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(&typed)
        .args(["run", "--backend", "vm", "."])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(
        b"1 + 2 + 3\nif 1 + 1 == 2 then 10 else 20\n(1 == 1) == true\n1 + true\nif 1 then 2 else 3\nif true then 1 else false\n1 + * 2\n2 + 3\n\n:quit\n99\n"
    ).unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8(out.stdout).unwrap(),
        "typed-lang REPL (:quit to exit)\n\
         > 6 : Nat\n\
         > 10 : Nat\n\
         > rejected by the type checker\n\
         > rejected by the type checker\n\
         > rejected by the type checker\n\
         > rejected by the type checker\n\
         > syntax error: this text is not a token of the syntax\n\
         > 5 : Nat\n\
         > > "
    );
}
