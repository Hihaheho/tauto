//! `include_text!` read by `totes/elaborator` (`--include`) against the reader of
//! `tauto::program::include`: the program after the calls are replaced, and the
//! spans of the calls that failed.

use std::path::Path;

use selfhost_harness::{assert_same_dump, run_tote_native};
use tauto::program::include::{Included, read_includes};
use tauto::surface::{Program, dump::dump_program};
use tauto_parse::parse_program_unresolved_at;

const STEPS: u64 = 200_000_000_000;

fn expected(file: &Path) -> String {
    let source = std::fs::read_to_string(file).unwrap();
    let mut program = parse_program_unresolved_at(&source, 0).unwrap();
    let mut included = Included::default();
    read_includes(&mut program.stmts, file, &|_| None, &mut included);
    let mut out = format!("== {}\n", file.display());
    out.push_str(&dump_program(&Program {
        stmts: program.stmts,
        errors: Vec::new(),
    }));
    for (_, span) in &included.errors {
        out.push_str(&format!("error {} {}\n", span.start, span.end));
    }
    out
}

#[test]
fn include_text_reads_the_same_files_as_the_host() {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-include-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let tote = dir.join("tote");
    std::fs::create_dir_all(tote.join("sub/deeper")).unwrap();
    std::fs::write(tote.join("Tauto.eure"), "package {\n  name = \"t\"\n  version = \"0.1.0\"\n}\n").unwrap();
    std::fs::write(tote.join("sub/a.txt"), "hello \"x\"\n\tτ").unwrap();
    std::fs::write(tote.join("top.txt"), "top").unwrap();
    std::fs::write(tote.join("sub/deeper/bad.txt"), [0xff, 0xfe, 0x41]).unwrap();
    std::fs::write(dir.join("outside.txt"), "outside").unwrap();
    #[cfg(unix)]
    std::os::unix::fs::symlink(dir.join("outside.txt"), tote.join("sub/link.txt")).unwrap();
    let calls = [
        "a.txt",
        "./a.txt",
        "deeper/../a.txt",
        "../top.txt",
        "../../outside.txt",
        "../../../etc/passwd",
        "/etc/passwd",
        "missing.txt",
        "",
        "deeper/bad.txt",
        "deeper",
        "link.txt",
        "a//a.txt",
    ];
    let mut body = String::new();
    for (i, c) in calls.iter().enumerate() {
        body.push_str(&format!("fn f{i}(): Text {{ include_text!(\"{c}\") }}\n"));
    }
    body.push_str("fn g(x: Text): Text { match x { _ => include_text!(\"a.txt\") } }\n");
    body.push_str("fn h(): Text { include_text!(1) }\n");
    body.push_str("fn k(): Text { other_macro!(\"a.txt\") }\n");
    let file = tote.join("sub/main.taut");
    std::fs::write(&file, body).unwrap();
    let mut args = vec!["--include".to_string()];
    args.push(file.to_string_lossy().into_owned());
    let out = run_tote_native("elaborator", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_same_dump("include", &expected(&file), &out.stdout);
    let _ = std::fs::remove_dir_all(&dir);
}
