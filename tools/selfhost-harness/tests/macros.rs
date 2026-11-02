//! `totes/macros` against `tauto::macros::scope`: the names an expansion made, tied to their binders.
//!
//! A name's scopes are written after `__m` here, so that the reader of either
//! side takes them as part of an identifier.

use std::collections::HashSet;

use selfhost_harness::{assert_same_dump, corpus, materialize, run_tote_native};
use tauto::macros::scope::resolve_with;
use tauto::surface::{
    Program, Stmt, dump::dump_program, parse_program_unresolved_at as parse_program_at,
};

const STEPS: u64 = 200_000_000_000;
const SEP: &str = "__m";

fn ctors(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        match s {
            Stmt::Struct(d) | Stmt::Enum(d) => {
                out.extend(d.constructors.iter().map(|c| c.name.clone()))
            }
            Stmt::Inductive(d) => out.extend(d.constructors.iter().map(|c| c.name.clone())),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => ctors(items, out),
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
    "view",
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
    let m = materialize(label, &inputs);
    let out = run_tote_native("macros", &m.paths, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let mut rust = String::new();
    for (path, (_, source)) in m.paths.iter().zip(&inputs) {
        rust.push_str(&format!("== {path}\n{}", expected(source)));
    }
    assert_same_dump("macros", &rust, &out.stdout);
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

/// Programs written to show each rule.
fn cases() -> Vec<(String, String)> {
    [
        // A name of the expansion meets the binder of the same expansion.
        r#"fn f(x__m1: Nat): Nat { let y__m1 := x__m1
 y__m1 }"#,
        // The caller's `x` is not the expansion's.
        r#"fn f(x: Nat): Nat { let t__m1 := x
 t__m1 }"#,
        // A global of the expansion must not be taken by a local of the caller.
        r#"fn g(a: Nat): Nat { a }
fn f(g: Nat): Nat { g__m1(g) }"#,
        // A declaration of the expansion, used by it.
        r#"fn helper__m1(a: Nat): Nat { a }
fn f(a: Nat): Nat { helper__m1(a) }"#,
        r#"struct P__m1 { x: Nat }
fn f(p: P__m1): Nat { p.x }"#,
        r#"enum E__m1 { A__m1, B__m1(Nat) }
fn f(e: E__m1): Nat { match e { A__m1 => 1, B__m1(n__m1) => n__m1 } }"#,
        r#"enum E { A, B(Nat) }
fn f(e: E): Nat { match e { A => 1, B(n) => n } }"#,
        r#"enum E { A__m1, B }
fn f(e: E): Nat { match e { A__m1 => 1, B => 2 } }"#,
        r#"theorem t__m1(a__m1: Nat): a__m1 == a__m1 { Refl }"#,
        r#"fn f(n: Nat): Nat { let r := (x__m1, y__m1) => x__m1
 r(n, n) }"#,
        r#"fn f(n: Nat): Nat { if n == 0 { let a__m1 := 1
 a__m1 } else { let a__m1 := 2
 a__m1 } }"#,
        r#"mutual { fn a__m1(): Nat { b__m1() }
 fn b__m1(): Nat { 1 } }"#,
        r#"module m { fn a__m1(): Nat { 1 }
 fn b(): Nat { a__m1() } }"#,
        r#"effect Ask__m1(): Nat
fn f(): Nat { perform Ask__m1() }"#,
        r#"inductive Nat2__m1: Type { Z__m1: Nat2__m1
 S__m1(n__m1: Nat2__m1): Nat2__m1 }"#,
        r#"fn f(n: Nat): Nat { var a__m1 := n
 a__m1 := a__m1
 a__m1 }"#,
        r#"fn f(n: Nat): Nat { let g__m1 := n
 let g := n
 g__m1 }"#,
        r#"fn f(g: Nat): Nat { let h := g__m2
 g__m1 }"#,
    ]
    .iter()
    .enumerate()
    .map(|(i, s)| (format!("case{i}"), s.to_string()))
    .collect()
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
        Node::Product(members) => members.iter().any(|(_, value)| has_literal(value)),
        _ => false,
    }
}

fn expected_lift(source: &str) -> String {
    expected_lift_with(source, None)
}

/// The variables the tote makes atoms of (`mc_atoms`).
fn atoms() -> std::collections::HashMap<String, u64> {
    [("x", 11), ("a", 12), ("n", 13), ("f", 14)]
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
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
    atoms: Option<std::collections::HashMap<String, u64>>,
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
