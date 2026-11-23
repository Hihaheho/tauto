//! `totes/macros` against `tauto::macros::scope`: the names an expansion made, tied to their binders.
//!
//! A name's scopes are written after `__m` here, so that the reader of either
//! side takes them as part of an identifier.

use std::collections::HashSet;

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};
use tauto::macros::scope::resolve_with;
use tauto::surface::{Program, Stmt, dump::dump_program};
use tauto_parse::parse_program_unresolved_at;

/// The program as the tote reads it: modules left as written, and the host's
/// `perform budget(n, f)` read as a budget (`surface_program_as_written`).
fn parse_program_at(source: &str, base: u32) -> Result<Program, String> {
    let mut p = parse_program_unresolved_at(source, base)?;
    tauto::resolve::host_budgets_as_written(&mut p.stmts);
    Ok(p)
}

const STEPS: u64 = 200_000_000_000;
const SEP: &str = "__m";

fn ctors(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        match s {
            Stmt::Struct(d) | Stmt::Enum(d) => {
                out.extend(d.constructors.iter().map(|c| c.name.to_string()))
            }
            Stmt::Inductive(d) => out.extend(d.constructors.iter().map(|c| c.name.to_string())),
            Stmt::Mutual { items, .. } => ctors(items, out),
            _ => {}
        }
    }
}

fn expected(source: &str) -> String {
    std::panic::catch_unwind(|| {
        parse_program_at(source, 0).ok().map(|p| {
            let mut set = HashSet::new();
            ctors(&p.stmts, &mut set);
            dump_program(&Program {
                stmts: resolve_with(p.stmts, &set, SEP),
                errors: Vec::new(),
            })
        })
    })
    .ok()
    .flatten()
    .unwrap_or_else(|| "error\n".to_string())
}

/// Words that the grammar reads as more than a name.
const WORDS: &[&str] = &[
    "theorem",
    "def",
    "import",
    "mutual",
    "axiom",
    "inductive",
    "forall",
    "exists",
    "decreasing_by",
    "let",
    "var",
    "fn",
    "return",
    "while",
    "loop",
    "break",
    "continue",
    "if",
    "else",
    "match",
    "struct",
    "enum",
    "effect",
    "handle",
    "with",
    "perform",
    "budget",
    "brand",
    "copy",
    "shared",
    "affine",
    "linear",
    "resume",
    "direct",
    "mut",
    "module",
    "extern",
    "syntax",
    "macro",
    "quote",
    "stmts",
    "steps",
    "true",
    "false",
    "by",
    "in",
    "as",
    "where",
    "type",
    "decreasing",
    "Refl",
    "calc",
    "from",
    "do",
    "then",
    "Never",
    "Type",
    "Prop",
    "Sort",
];

/// `source` with some of its names given scopes: which names, and which
/// scopes, by where they come in the text.
fn marked(source: &str) -> String {
    rewritten(source, false)
}

/// `source` with some of its names written `$name`, as in a `quote`.
fn dollared(source: &str) -> String {
    rewritten(source, true)
}

fn rewritten(source: &str, dollar: bool) -> String {
    let chars: Vec<char> = source.chars().collect();
    let mut out = String::new();
    let (mut i, mut count) = (0, 0usize);
    let start = |c: char| c.is_alphabetic() || c == '_';
    let part = |c: char| c.is_alphanumeric() || c == '_';
    while i < chars.len() {
        let c = chars[i];
        let at = |i: usize, n: usize| chars.get(i + n).copied();
        if c == '/' && at(i, 1) == Some('/') {
            while i < chars.len() && chars[i] != '\n' {
                out.push(chars[i]);
                i += 1;
            }
        } else if c == '/' && at(i, 1) == Some('*') {
            while i < chars.len() && !(chars[i] == '*' && at(i, 1) == Some('/')) {
                out.push(chars[i]);
                i += 1;
            }
        } else if c == '"' || c == '`' {
            out.push(c);
            i += 1;
            while i < chars.len() && chars[i] != c {
                if chars[i] == '\\' && c == '"' {
                    out.push(chars[i]);
                    i += 1;
                }
                if i < chars.len() {
                    out.push(chars[i]);
                    i += 1;
                }
            }
            if i < chars.len() {
                out.push(c);
                i += 1;
            }
        } else if start(c) || (c == '$' && at(i, 1).is_some_and(start)) {
            let from = i;
            i += 1;
            while i < chars.len() && part(chars[i]) {
                i += 1;
            }
            let word: String = chars[from..i].iter().collect();
            let bare = word.trim_start_matches('$');
            let plain = chars.get(from.wrapping_sub(1)).is_none_or(|p| !part(*p))
                && chars.get(i) != Some(&'!');
            if plain && !WORDS.contains(&bare) && dollar {
                count += 1;
                if count % 3 == 0 && !word.starts_with('$') {
                    out.push('$');
                }
                out.push_str(&word);
            } else if plain && !WORDS.contains(&bare) {
                out.push_str(&word);
                count += 1;
                match (count * 7 + word.len()) % 4 {
                    1 => out.push_str("__m1"),
                    2 => out.push_str("__m2"),
                    _ => {}
                }
            } else {
                out.push_str(&word);
            }
        } else {
            out.push(c);
            i += 1;
        }
    }
    out
}

fn compare(label: &str, inputs: Vec<(String, String)>) {
    tauto_test_suite::with_deep_stack(|| {
        let m = materialize(label, &inputs);
        let out = run_tote_native("macros", &m.paths, STEPS);
        assert_eq!(out.error, None);
        assert_eq!(out.stderr, "");
        let mut rust = String::new();
        for (path, (_, source)) in m.paths.iter().zip(&inputs) {
            rust.push_str(&format!("== {path}\n{}", expected(source)));
        }
        assert_same_dump("macros", &rust, &out.stdout);
    })
}

fn part(label: &str, n: usize, of: usize) {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .enumerate()
        .filter(|(i, _)| i % of == n)
        .map(|(_, (name, source))| (name, marked(&source)))
        .collect();
    compare(label, inputs);
}

/// The cases marked `differential = "macros"` in `cases/`.
fn cases() -> Vec<(String, String)> {
    selfhost_harness::differential("macros")
}

#[test]
fn macros_match_the_cases() {
    compare("macros-cases", cases());
}

#[test]
fn macros_match_the_marked_corpus_0() {
    part("macros-0", 0, 3);
}

#[test]
fn macros_match_the_marked_corpus_1() {
    part("macros-1", 1, 3);
}

#[test]
fn macros_match_the_marked_corpus_2() {
    part("macros-2", 2, 3);
}

#[test]
fn the_marked_corpus_is_mostly_programs() {
    let all = corpus();
    let ok = all
        .iter()
        .filter(|(_, s)| expected(&marked(s)) != "error\n")
        .count();
    assert!(ok * 2 > all.len(), "{ok} of {}", all.len());
}

// ---------------------------------------------------------------------------
// Lift

use tauto::macros::syn::{Lift, Lower};

/// Whether a value holds a macro call on a literal (whose start the reader of
/// the tote does not keep).
fn has_literal(n: &tauto::macros::Node) -> bool {
    use tauto::macros::Node;
    match n {
        Node::Ctor(name, fs) => {
            name.ends_with("ExMacroCall")
                || name.ends_with("StMacroCall")
                || fs.iter().any(|(_, f)| has_literal(f))
        }
        Node::List(v) => v.iter().any(has_literal),
        Node::Option(Some(x)) => has_literal(x),
        Node::Pair(p) => has_literal(&p.0) || has_literal(&p.1),
        _ => false,
    }
}

fn expected_lift(source: &str) -> String {
    expected_lift_with(source, None)
}

/// The variables the tote makes atoms of (`mc_atoms`).
fn atoms() -> std::collections::HashMap<tauto::surface::Name, u64> {
    [("x", 11), ("a", 12), ("n", 13), ("f", 14)]
        .into_iter()
        .map(|(k, v)| (k.into(), v))
        .collect()
}

/// Each statement lifted with a table of spans, and the spans it gave out.
fn expected_lift_spans(source: &str) -> String {
    std::panic::catch_unwind(|| {
        let Ok(p) = parse_program_at(source, 0) else {
            return "error\n".to_string();
        };
        let mut out = String::new();
        for s in &p.stmts {
            let table = std::cell::RefCell::new(tauto::macros::syn::SpanTable::default());
            let lift = Lift {
                scopes: &[3, 7],
                quote: false,
                atoms: None,
                spans: Some(&table),
                reflip: None,
            };
            match lift.stmt(s) {
                Err(_) => out.push_str("err\n"),
                Ok(n) if has_literal(&n) => out.push_str("skip\n"),
                Ok(n) => {
                    out.push_str(&format!("ok {}\n", n.show()));
                    out.push_str("spans");
                    for (id, span) in &table.borrow().issued {
                        out.push_str(&format!(" {id}:{}:{}", span.start, span.end));
                    }
                    out.push('\n');
                }
            }
        }
        out
    })
    .unwrap_or_else(|_| "error\n".to_string())
}

fn expected_lift_atoms(source: &str) -> String {
    expected_lift_with(source, Some(atoms()))
}

fn expected_lift_with(
    source: &str,
    atoms: Option<std::collections::HashMap<tauto::surface::Name, u64>>,
) -> String {
    std::panic::catch_unwind(move || {
        let Ok(p) = parse_program_at(source, 0) else {
            return "error\n".to_string();
        };
        let lift = Lift {
            scopes: &[3, 7],
            quote: false,
            atoms: atoms.as_ref(),
            spans: None,
            reflip: None,
        };
        let mut out = String::new();
        for s in &p.stmts {
            match lift.stmt(s) {
                Err(_) => out.push_str("err\n"),
                Ok(n) if has_literal(&n) => out.push_str("skip\n"),
                Ok(n) => out.push_str(&format!("ok {}\n", n.show())),
            }
        }
        out
    })
    .unwrap_or_else(|_| "error\n".to_string())
}

/// Each statement lifted and lowered again with the expansion 5, as a one
/// statement program.
fn expected_lower(source: &str) -> String {
    std::panic::catch_unwind(|| {
        let Ok(p) = parse_program_at(source, 0) else {
            return "error\n".to_string();
        };
        let lift = Lift {
            scopes: &[3, 7],
            quote: false,
            atoms: None,
            spans: None,
            reflip: None,
        };
        let mut out = String::new();
        for s in &p.stmts {
            match lift.stmt(s) {
                Err(_) => out.push_str("err\n"),
                Ok(n) if has_literal(&n) => out.push_str("skip\n"),
                Ok(n) => {
                    let mut fresh = |at: u32| tauto_parol::Span {
                        start: at,
                        end: at + 1,
                    };
                    let atoms = std::collections::HashMap::new();
                    let mut lower = Lower {
                        scope: 5,
                        fresh: &mut fresh,
                        captures: Vec::new(),
                        atoms: &atoms,
                        opened: Vec::new(),
                    };
                    match lower.stmt(&n) {
                        Err(_) => out.push_str("err\n"),
                        Ok(stmt) => out.push_str(&format!(
                            "ok\n{}",
                            dump_program(&Program {
                                stmts: vec![stmt],
                                errors: Vec::new()
                            })
                        )),
                    }
                }
            }
        }
        out
    })
    .unwrap_or_else(|_| "error\n".to_string())
}

fn compare_lift(label: &str, inputs: Vec<(String, String)>) {
    compare_with(label, inputs, "--lift", expected_lift);
}

fn compare_lower(label: &str, inputs: Vec<(String, String)>) {
    compare_with(label, inputs, "--lower", expected_lower);
}

fn compare_with(
    label: &str,
    inputs: Vec<(String, String)>,
    flag: &str,
    expected_lift: fn(&str) -> String,
) {
    // The Rust side reads and lifts the deepest files of the corpus.
    tauto_test_suite::with_deep_stack(|| {
        let m = materialize(label, &inputs);
        let mut args = vec![flag.to_string()];
        args.extend(m.paths.iter().cloned());
        let out = run_tote_native("macros", &args, STEPS);
        assert_eq!(out.error, None);
        assert_eq!(out.stderr, "");
        let mut rust = String::new();
        for (path, (_, source)) in m.paths.iter().zip(&inputs) {
            rust.push_str(&format!("== {path}\n{}", expected_lift(source)));
        }
        assert_same_dump(flag, &rust, &out.stdout);
    })
}

fn lift_part(label: &str, n: usize, of: usize) {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .enumerate()
        .filter(|(i, _)| i % of == n)
        .collect::<Vec<_>>()
        .into_iter()
        .map(|(_, x)| x)
        .collect();
    compare_lift(label, inputs);
}

#[test]
fn lift_matches_the_cases() {
    compare_lift("lift-cases", cases());
}

#[test]
fn lift_matches_the_corpus_0() {
    lift_part("lift-0", 0, 3);
}

#[test]
fn lift_matches_the_corpus_1() {
    lift_part("lift-1", 1, 3);
}

#[test]
fn lift_matches_the_corpus_2() {
    lift_part("lift-2", 2, 3);
}

#[test]
fn lower_matches_the_cases() {
    compare_lower("lower-cases", cases());
}

#[test]
fn lower_matches_the_corpus_0() {
    compare_lower("lower-0", corpus_part(0, 3));
}

#[test]
fn lower_matches_the_corpus_1() {
    compare_lower("lower-1", corpus_part(1, 3));
}

#[test]
fn lower_matches_the_corpus_2() {
    compare_lower("lower-2", corpus_part(2, 3));
}

fn corpus_part(n: usize, of: usize) -> Vec<(String, String)> {
    corpus()
        .into_iter()
        .enumerate()
        .filter(|(i, _)| i % of == n)
        .map(|(_, x)| x)
        .collect()
}

// ---------------------------------------------------------------------------
// Quote

/// The term a `quote` of the program makes, as a one statement program.
fn expected_quote(source: &str, stmts: bool) -> String {
    std::panic::catch_unwind(|| {
        let Ok(p) = parse_program_at(source, 0) else {
            return "error\n".to_string();
        };
        let span = tauto_parol::Span {
            start: 0,
            end: source.len() as u32,
        };
        match tauto::macros::quote::desugar(stmts, &p.stmts, span) {
            Err(_) => "err\n".to_string(),
            Ok(term) => dump_program(&Program {
                stmts: vec![Stmt::Expr(term)],
                errors: Vec::new(),
            }),
        }
    })
    .unwrap_or_else(|_| "error\n".to_string())
}

fn compare_quote(label: &str, inputs: Vec<(String, String)>, stmts: bool) {
    let flag = if stmts { "--quote-stmts" } else { "--quote" };
    tauto_test_suite::with_deep_stack(|| {
        let m = materialize(label, &inputs);
        let mut args = vec![flag.to_string()];
        args.extend(m.paths.iter().cloned());
        let out = run_tote_native("macros", &args, STEPS);
        assert_eq!(out.error, None);
        assert_eq!(out.stderr, "");
        let mut rust = String::new();
        for (path, (_, source)) in m.paths.iter().zip(&inputs) {
            rust.push_str(&format!("== {path}\n{}", expected_quote(source, stmts)));
        }
        assert_same_dump(flag, &rust, &out.stdout);
    })
}

/// Bodies of a `quote`, with the places a value is put in.
fn quote_cases() -> Vec<(String, String)> {
    [
        r#"x"#,
        r#"$x"#,
        r#"$(f(a, b))"#,
        r#"f($x, 1)"#,
        r#"$x + $y"#,
        r#"let $n := $v
$n"#,
        r#"$body"#,
        r#"$a
$b
x"#,
        r#"fn $name($p: Nat): Nat { $p }"#,
        r#"match $e { Some($x) => $x, None => 0 }"#,
        r#"[1, 2, $x]"#,
        r#"-5"#,
        r#""text""#,
        r#"(1, $x)"#,
        r#"quote { x }"#,
        r#"if $c { $a } else { $b }"#,
    ]
    .iter()
    .enumerate()
    .map(|(i, s)| (format!("quote{i}"), s.to_string()))
    .collect()
}

#[test]
fn quote_matches_the_cases() {
    compare_quote("quote-cases", quote_cases(), false);
    compare_quote("quote-stmts-cases", quote_cases(), true);
}

#[test]
fn quote_modules_as_statement_values() {
    compare_quote(
        "quote-module-stmts",
        selfhost_harness::differential("macro-module-quotes"),
        true,
    );
}

#[test]
fn lower_modules_and_remove_the_expansion_scope() {
    compare_with(
        "reflip-module-stmts",
        selfhost_harness::differential("macro-module-quotes"),
        "--reflip-module-stmts",
        expected_reflip,
    );
}

#[test]
fn sealed_effect_cases_expand_with_a_scoped_module_and_public_aliases() {
    let mut cases = std::collections::BTreeMap::<String, Vec<(String, String)>>::new();
    for (path, source) in selfhost_harness::differential("macro-sealed-expansion") {
        let (case, file) = path.rsplit_once('/').unwrap();
        cases.entry(case.to_owned()).or_default().push((file.to_owned(), source));
    }
    assert_eq!(cases.len(), 4);
    for (case, mut files) in cases {
        files.sort_by_key(|(file, _)| match file.as_str() {
            "macro.nib" => 0,
            "lib.nib" => 1,
            "main.nib" => 2,
            _ => panic!("{case}: unexpected source {file}"),
        });
        let scratch = materialize("sealed-macro-expansion", &files);
        let mut args = vec!["--expand-modules".to_owned()];
        args.extend(scratch.paths.iter().cloned());
        let out = run_tote_native("macros", &args, STEPS);
        assert_eq!(out.error, None, "{case}");
        assert_eq!(out.exit, Some(0), "{case}: {}", out.stderr);
        assert!(!out.stdout.lines().any(|line| line.starts_with("error ")), "{case}: {}", out.stdout);
        for expected in [
            "kind #enter sealed#1",
            "name sealed#1::#a_sealed",
            "kind #effect-mode sealed#1::a handle",
            "kind #alias a sealed#1::a",
            "kind #alias perform_a sealed#1::perform_a",
        ] {
            assert!(out.stdout.contains(expected), "{case}: missing {expected}: {}", out.stdout);
        }
        assert!(!out.stdout.contains("kind #alias a_sealed "), "{case}");
    }
}

#[test]
fn quote_matches_the_corpus() {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .map(|(name, source)| (name, dollared(&source)))
        .collect();
    let (a, b): (Vec<_>, Vec<_>) = inputs
        .into_iter()
        .enumerate()
        .partition(|(i, _)| i % 2 == 0);
    let strip = |v: Vec<(usize, (String, String))>| v.into_iter().map(|(_, x)| x).collect();
    compare_quote("quote-corpus-expr", strip(a), false);
    compare_quote("quote-corpus-stmts", strip(b), true);
}

#[test]
fn lift_writes_the_variables_of_the_context_as_atoms() {
    let inputs: Vec<_> = corpus().into_iter().step_by(3).collect();
    compare_with("lift-atoms", inputs, "--lift-atoms", expected_lift_atoms);
    compare_with(
        "lift-atoms-cases",
        cases(),
        "--lift-atoms",
        expected_lift_atoms,
    );
}

#[test]
fn lift_gives_out_the_spans_in_the_order_of_the_rust_walk() {
    let inputs: Vec<_> = corpus().into_iter().step_by(2).collect();
    compare_with("lift-spans", inputs, "--lift-spans", expected_lift_spans);
    compare_with(
        "lift-spans-cases",
        cases(),
        "--lift-spans",
        expected_lift_spans,
    );
}

/// Each statement lifted, lowered with the expansion 5, and read again with
/// that scope flipped back (`syn_expand`).
fn expected_reflip(source: &str) -> String {
    std::panic::catch_unwind(|| {
        let Ok(p) = parse_program_at(source, 0) else {
            return "error\n".to_string();
        };
        let lift = Lift {
            scopes: &[3, 7],
            quote: false,
            atoms: None,
            spans: None,
            reflip: None,
        };
        let back = Lift {
            scopes: &[],
            quote: false,
            atoms: None,
            spans: None,
            reflip: Some(5),
        };
        let mut out = String::new();
        for s in &p.stmts {
            match lift.stmt(s) {
                Err(_) => out.push_str("err\n"),
                Ok(n) if has_literal(&n) => out.push_str("skip\n"),
                Ok(n) => {
                    let mut fresh = |at: u32| tauto_parol::Span {
                        start: at,
                        end: at + 1,
                    };
                    let atoms = std::collections::HashMap::new();
                    let mut lower = Lower {
                        scope: 5,
                        fresh: &mut fresh,
                        captures: Vec::new(),
                        atoms: &atoms,
                        opened: Vec::new(),
                    };
                    match lower.stmt(&n).and_then(|stmt| back.stmt(&stmt)) {
                        Err(_) => out.push_str("err\n"),
                        Ok(n) => out.push_str(&format!("ok {}\n", n.show())),
                    }
                }
            }
        }
        out
    })
    .unwrap_or_else(|_| "error\n".to_string())
}

#[test]
fn a_lowered_expansion_is_read_again_with_its_scope_flipped_back() {
    let inputs: Vec<_> = corpus().into_iter().step_by(2).collect();
    compare_with("reflip", inputs, "--reflip", expected_reflip);
    compare_with("reflip-cases", cases(), "--reflip", expected_reflip);
}
