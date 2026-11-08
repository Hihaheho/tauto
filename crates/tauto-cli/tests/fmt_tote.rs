//! `tauto fmt` written in Tauto (`totes/fmtcmd`, run with `TAUTO_FMT=tote`) against the
//! command in Rust: the same files written, the same status, the same output.

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

fn temp() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "tauto-fmt-tote-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    path
}

/// What `tauto fmt ARGS` does to `files` in a fresh directory: its status, its two outputs and the
/// files afterwards.
fn run(
    tote: bool,
    files: &[(&str, &str)],
    args: &[&str],
) -> (Option<i32>, String, String, Vec<String>) {
    let dir = temp();
    for (name, text) in files {
        fs::write(dir.join(name), text).unwrap();
    }
    let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
    command
        .current_dir(&dir)
        .env("TAUTO_LANG", "en")
        .arg("fmt")
        .args(args);
    if tote {
        command.env("TAUTO_FMT", "tote");
    }
    let out = command.output().unwrap();
    let after = files
        .iter()
        .map(|(name, _)| fs::read_to_string(dir.join(name)).unwrap_or_default())
        .collect();
    let _ = fs::remove_dir_all(&dir);
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
        after,
    )
}

fn same(files: &[(&str, &str)], args: &[&str]) {
    assert_eq!(
        run(true, files, args),
        run(false, files, args),
        "args {args:?}"
    );
}

const UGLY: &str = "let x   :=   1\nperform show(\"x\",x)\n";
const NICE: &str = "let x := 1\nperform show(\"x\", x)\n";
const BAD: &str = "let x := (\n";

#[test]
fn lays_files_out() {
    same(&[("a.taut", UGLY), ("b.taut", NICE)], &["a.taut", "b.taut"]);
}

#[test]
fn check_lists_the_files_that_would_change() {
    same(
        &[("a.taut", UGLY), ("b.taut", NICE)],
        &["--check", "a.taut", "b.taut"],
    );
    same(&[("b.taut", NICE)], &["--check", "b.taut"]);
}

#[test]
fn a_file_that_does_not_parse_fails_and_the_rest_are_laid_out() {
    same(
        &[("bad.taut", BAD), ("a.taut", UGLY)],
        &["bad.taut", "a.taut"],
    );
}

#[test]
fn a_missing_file_ends_the_run() {
    same(&[("a.taut", UGLY)], &["missing.taut", "a.taut"]);
}

#[test]
fn wrong_arguments_print_the_usage() {
    same(&[], &[]);
    same(&[("a.taut", UGLY)], &["--bogus", "a.taut"]);
}

#[test]
fn a_declaration_broken_in_its_parameters_keeps_pub_open_whole() {
    // `pub(open)` is one word of the grammar: a long declaration breaks inside its parentheses.
    let long = "pub(open) effect tls_accept(stream: TcpStream, server: TlsServer, deadline: Option(i64)): Result(TlsStream, IoError) resume 1\n";
    same(&[("a.taut", long)], &["a.taut"]);
    same(&[("a.taut", long)], &["--check", "a.taut"]);
}

#[test]
fn a_block_that_only_holds_an_if_is_taken_off_its_arm() {
    let source = "fn repl(): Unit {\n  match read() {\n    Some(line) => {\n      if line == \":quit\" {\n        ()\n      } else {\n        run(line)\n        repl()\n      }\n    }\n    None => ()\n  }\n}\n";
    same(&[("a.taut", source)], &["a.taut"]);
    same(&[("a.taut", source)], &["--check", "a.taut"]);
}

/// The library files: the two commands say the same of each, formatted or not.
#[test]
fn a_short_block_goes_on_one_line() {
    let source = "inductive R: Type {\n  R0: R\n  R1: R\n}\nfn f(r: R): R {\n  match r {\n    R0 => R1\n    R1 => R0\n  }\n}\nfn g(r: R): Nat {\n  match r {\n    R::R0 => 0\n    _ => f(1)\n  }\n}\n";
    let joined = "inductive R: Type { R0: R, R1: R }\nfn f(r: R): R {\n  match r { R0 => R1, R1 => R0 }\n}\n";
    let (_, _, _, after) = run(false, &[("a.taut", source)], &["a.taut"]);
    assert!(after[0].starts_with(joined), "{}", after[0]);
    assert!(
        after[0].contains("    R::R0 => 0\n    _ => f(1)\n"),
        "{}",
        after[0]
    );
    same(&[("a.taut", source)], &["a.taut"]);
}

#[test]
fn the_library_files_get_the_same_answer() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = Vec::new();
    for dir in ["std", "meta"] {
        let mut stack = vec![root.join(dir)];
        while let Some(d) = stack.pop() {
            for entry in fs::read_dir(&d).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    stack.push(path);
                } else if path.extension().is_some_and(|e| e == "taut") {
                    files.push(path);
                }
            }
        }
    }
    files.sort();
    assert!(files.len() > 20);
    for file in files {
        let text = fs::read_to_string(&file).unwrap();
        let name = file.file_name().unwrap().to_str().unwrap();
        // Run beside the file, so that the imports that a syntax literal needs are found.
        let tote = check_in_place(true, &file, &text);
        let rust = check_in_place(false, &file, &text);
        assert_eq!(tote, rust, "{name}");
    }
}

/// `tauto fmt --check FILE` on a file where it is, with its status and what it printed.
fn check_in_place(tote: bool, file: &std::path::Path, _text: &str) -> (Option<i32>, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
    command
        .current_dir(file.parent().unwrap())
        .env("TAUTO_LANG", "en")
        .args(["fmt", "--check"])
        .arg(file.file_name().unwrap());
    if tote {
        command.env("TAUTO_FMT", "tote");
    }
    let out = command.output().unwrap();
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
    )
}
