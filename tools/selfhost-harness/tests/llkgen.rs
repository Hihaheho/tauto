//! `totes/llkgen` against the tables parol made: the lookahead automata of
//! every table file in the repository (`docs/design/macro.md`
//! 「`tauto.par` との共通性と self-host」).

use std::path::{Path, PathBuf};

use selfhost_harness::{root, run_tote, run_tote_native};

const STEPS: u64 = 200_000_000_000;

fn tables() -> Vec<PathBuf> {
    let mut out = Vec::new();
    for dir in [
        "crates/tauto-syntax/tests/data",
        "crates/tauto/tests/syntax_fixtures/.tauto-syntax",
        "examples/nat/.tauto-syntax",
        "examples/lambda/.tauto-syntax",
    ] {
        let Ok(entries) = std::fs::read_dir(root().join(dir)) else {
            continue;
        };
        for e in entries.flatten() {
            if e.path().extension().is_some_and(|x| x == "tables") {
                out.push(e.path());
            }
        }
    }
    out.sort();
    out
}

fn lines_of(table: &Path, names: &[&str]) -> String {
    let text = std::fs::read_to_string(table).unwrap();
    let mut out = String::new();
    for line in text.lines() {
        if names.iter().any(|n| line.split(' ').next() == Some(n)) {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

#[test]
fn the_lookahead_automata_are_the_ones_parol_made() {
    let files = tables();
    assert!(files.len() >= 3, "{files:?}");
    for file in files {
        let out = run_tote_native("syntaxgen", &[file.display().to_string()], STEPS);
        assert_eq!(out.error, None);
        assert_eq!(out.stderr, "");
        let got: String = out
            .stdout
            .lines()
            .skip(1)
            .map(|l| format!("{l}\n"))
            .collect();
        let want = lines_of(&file, &["max_k", "lookahead"]);
        assert_eq!(got, want, "{}", file.display());
    }
}

/// The same on the evaluator (`tauto run`), so that it and the Rust backend
/// cannot drift apart on the generator.
#[test]
fn the_evaluator_makes_the_same_lookahead_automata() {
    let file = root().join("crates/tauto-syntax/tests/data/math.tables");
    let out = run_tote("syntaxgen", &[file.display().to_string()], STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let got: String = out
        .stdout
        .lines()
        .skip(1)
        .map(|l| format!("{l}\n"))
        .collect();
    assert_eq!(got, lines_of(&file, &["max_k", "lookahead"]));
}

/// Every grammar in the repository with the table parol made of it, found by
/// the hash of the grammar.
fn grammars() -> Vec<(PathBuf, PathBuf)> {
    let all = tables();
    let mut out = Vec::new();
    for dir in [
        "crates/tauto-syntax/tests/data",
        "crates/tauto/tests/syntax_fixtures",
        "crates/tauto-parol",
        "examples/nat",
        "examples/lambda",
        "cases/macro/grammars",
    ] {
        let Ok(entries) = std::fs::read_dir(root().join(dir)) else {
            continue;
        };
        for e in entries.flatten() {
            if e.path().extension().is_none_or(|x| x != "par") {
                continue;
            }
            let hash = tauto_syntax::sha256_hex(&std::fs::read(e.path()).unwrap());
            let want = format!("grammar_sha256 {hash}");
            if let Some(t) = all.iter().find(|t| {
                std::fs::read_to_string(t)
                    .unwrap()
                    .lines()
                    .any(|l| l == want)
            }) {
                out.push((e.path(), t.clone()));
            }
        }
    }
    out.sort();
    out
}

#[test]
fn the_grammars_read_come_to_the_tables_parol_made() {
    let pairs = grammars();
    assert!(pairs.len() >= 3, "{pairs:?}");
    let names = [
        "title",
        "max_k",
        "terminals",
        "non_terminals",
        "nt_kinds",
        "start",
        "productions",
        "symbol_attrs",
        "lookahead",
        "skip",
    ];
    for (par, table) in pairs {
        let out = run_tote_native(
            "syntaxgen",
            &["--par".to_string(), par.display().to_string()],
            STEPS,
        );
        assert_eq!(out.error, None);
        assert_eq!(out.stderr, "");
        let got: String = out
            .stdout
            .lines()
            .skip(1)
            .map(|l| format!("{l}\n"))
            .collect();
        assert_eq!(got, lines_of(&table, &names), "{}", par.display());
    }
}

/// The expression as `totes/llkgen` shows it (`rx_show`).
fn show_hir(h: &regex_syntax::hir::Hir) -> String {
    use regex_syntax::hir::{Class, HirKind};
    let list =
        |hs: &[regex_syntax::hir::Hir]| hs.iter().map(show_hir).collect::<Vec<_>>().join(",");
    match h.kind() {
        HirKind::Empty => "E".into(),
        HirKind::Literal(l) => {
            let chars: Vec<String> = std::str::from_utf8(&l.0)
                .unwrap()
                .chars()
                .map(|c| (c as u32).to_string())
                .collect();
            format!("L[{}]", chars.join(" "))
        }
        HirKind::Class(Class::Unicode(c)) => {
            let rs: Vec<String> = c
                .ranges()
                .iter()
                .map(|r| format!("{}-{}", r.start() as u32, r.end() as u32))
                .collect();
            format!("C[{}]", rs.join(" "))
        }
        HirKind::Class(Class::Bytes(_)) => "BYTES".into(),
        HirKind::Look(_) => "LOOK".into(),
        HirKind::Repetition(r) => {
            assert!(r.greedy);
            format!(
                "R{{{},{}}}({})",
                r.min,
                r.max.map_or("-".to_string(), |m| m.to_string()),
                show_hir(&r.sub)
            )
        }
        HirKind::Capture(c) => format!("P({})", show_hir(&c.sub)),
        HirKind::Concat(hs) => format!("S({})", list(hs)),
        HirKind::Alternation(hs) => format!("A({})", list(hs)),
    }
}

#[test]
fn the_regular_expressions_are_read_as_the_regex_syntax_reads_them() {
    let file = root().join("tools/selfhost-harness/tests/data/regexes.txt");
    let text = std::fs::read_to_string(&file).unwrap();
    let out = run_tote_native(
        "syntaxgen",
        &["--rx".to_string(), file.display().to_string()],
        STEPS,
    );
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let want: String = text
        .lines()
        .filter(|l| !l.is_empty())
        .map(|l| format!("{}\n", show_hir(&regex_syntax::parse(l).unwrap())))
        .collect();
    for (i, (g, w)) in out.stdout.lines().zip(want.lines()).enumerate() {
        assert_eq!(
            g,
            w,
            "{}",
            text.lines().filter(|l| !l.is_empty()).nth(i).unwrap()
        );
    }
    assert_eq!(out.stdout, want);
}

#[test]
fn the_scanners_are_the_ones_scnr2_made() {
    let pairs = grammars();
    assert!(pairs.len() >= 3, "{pairs:?}");
    for (par, table) in pairs {
        let out = run_tote_native(
            "syntaxgen",
            &["--scan".to_string(), par.display().to_string()],
            STEPS,
        );
        assert_eq!(out.error, None);
        assert_eq!(out.stderr, "");
        let got: String = out
            .stdout
            .lines()
            .skip(1)
            .map(|l| format!("{l}\n"))
            .collect();
        assert_eq!(
            got,
            lines_of(&table, &["classes", "modes", "lookahead_dfas"]),
            "{}",
            par.display()
        );
    }
}

#[test]
fn the_table_files_are_written_byte_for_byte_as_the_generator_writes_them() {
    let pairs = grammars();
    assert!(pairs.len() >= 3, "{pairs:?}");
    for (par, table) in pairs {
        let out = run_tote_native(
            "syntaxgen",
            &["--gen".to_string(), par.display().to_string()],
            STEPS,
        );
        assert_eq!(out.error, None);
        assert_eq!(out.stderr, "");
        let want = std::fs::read_to_string(&table).unwrap();
        assert_eq!(out.stdout, want, "{}", par.display());
    }
}

#[test]
fn the_tote_stands_in_for_the_generator_on_standard_input() {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let bin = selfhost_harness::tote_binary("syntaxgen").unwrap();
    for name in ["math", "tauto"] {
        let dir = root().join("crates/tauto-syntax/tests/data");
        let grammar = std::fs::read(dir.join(format!("{name}.par"))).unwrap();
        let mut child = Command::new(&bin)
            .arg("--allow-read")
            .env("TAUTO_STEP_LIMIT", STEPS.to_string())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(&grammar).unwrap();
        let out = child.wait_with_output().unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let want = std::fs::read_to_string(dir.join(format!("{name}.tables"))).unwrap();
        assert_eq!(String::from_utf8(out.stdout).unwrap(), want, "{name}");
    }
}

#[test]
fn ambiguous_grammar_names_the_rule_alternatives_and_lookahead() {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("tauto-llk-conflict-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let grammar = dir.join("conflict.par");
    for (rules, expected) in [
        (
            "Start: Left | Right;\nLeft: 'a';\nRight: 'a';",
            "LL(3) conflict in rule Start\n  alternative #1: Left\n  alternative #2: Right\n  common lookahead: Left EndOfInput",
        ),
        (
            "Start: 'a' 'b' 'c' 'd' | 'a' 'b' 'c' 'e';",
            "LL(3) conflict in rule Start\n  alternative #1: A B C D\n  alternative #2: A B C E\n  common lookahead: A B C",
        ),
        (
            "Start: 'x' Choice;\nChoice: EmptyA | EmptyB;\nEmptyA: ;\nEmptyB: ;",
            "LL(3) conflict in rule Choice\n  alternative #2: EmptyA\n  alternative #3: EmptyB\n  common lookahead: EndOfInput",
        ),
    ] {
        std::fs::write(
            &grammar,
            format!("%start Start\n%title \"conflict\"\n%%\n{rules}\n"),
        )
        .unwrap();
        let out = run_tote_native(
            "syntaxgen",
            &["--par".into(), grammar.display().to_string()],
            STEPS,
        );
        assert_eq!(out.error, None);
        assert_eq!(out.exit, Some(0), "{}", out.stderr);
        assert_eq!(
            out.stdout.lines().skip(1).collect::<Vec<_>>().join("\n"),
            expected
        );
        let out = run_tote_native(
            "syntaxgen",
            &["--gen".into(), grammar.display().to_string()],
            STEPS,
        );
        assert_eq!(out.error, None);
        assert_eq!(out.exit, Some(1));
        assert_eq!(out.stdout, "");
        assert_eq!(out.stderr.trim(), format!("the grammar: {expected}"));
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn lalr_conflict_names_the_state_terminal_and_productions() {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("tauto-lalr-conflict-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let grammar = dir.join("conflict.par");
    for (start, rules, expected) in [
        (
            "E",
            "E: E Plus E | Num;\nNum: /[0-9]+/;\nPlus: '+';",
            "LALR(1) shift/reduce conflict in state 6 on Plus\n  shift to state 4\n  reduce by production #1 of E",
        ),
        (
            "S",
            "S: A | B;\nA: Num;\nB: Num;\nNum: /[0-9]+/;",
            "LALR(1) reduce/reduce conflict in state 4 on EndOfInput\n  reduce by production #3 of A\n  reduce by production #4 of B",
        ),
    ] {
        std::fs::write(
            &grammar,
            format!("%start {start}\n%title \"conflict\"\n%grammar_type 'LALR(1)'\n%%\n{rules}\n"),
        )
        .unwrap();
        let out = run_tote_native(
            "syntaxgen",
            &["--gen".into(), grammar.display().to_string()],
            STEPS,
        );
        assert_eq!(out.error, None);
        assert_eq!(out.exit, Some(1));
        assert_eq!(out.stdout, "");
        assert_eq!(out.stderr.trim(), format!("the grammar: {expected}"));
    }
    std::fs::remove_dir_all(dir).unwrap();
}
