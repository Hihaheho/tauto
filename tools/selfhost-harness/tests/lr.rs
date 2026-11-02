//! `totes/lr` against `crates/tauto-syntax`: the same LALR(1) tables
//! (`crates/tauto-syntax/tests/data/*_lr.tables`), the same texts, the same
//! events or the same error.

use selfhost_harness::{root, run_tote};
use tauto_syntax::{Event, Limits, ParseError, Tables, parse};

const STEPS: u64 = 20_000_000_000;

/// What `totes/lr`'s runner prints for a text, from the Rust parse: the root
/// (number `non_terminals`) around the tree, with the skipped tokens at the
/// end inside it.
fn expected(t: &Tables, text: &str) -> String {
    let mut out = String::from("==\n");
    match parse(t, text, 0, &Limits::default()) {
        Ok(events) => {
            let line = |e: &Event| match e {
                Event::Open { non_terminal, .. } => format!("open {non_terminal}\n"),
                Event::Close => "close\n".to_string(),
                Event::Token(tok) => format!("token {} {} {}\n", tok.terminal, tok.start, tok.end),
            };
            out += &format!("open {}\n", t.non_terminals().len());
            events.iter().for_each(|e| out += &line(e));
            out += "close\n";
        }
        Err(ParseError::Syntax(e)) => {
            let at = e.at.map_or(text.len() as u32, |tok| tok.start);
            out += &format!("error {at}");
            e.expected.iter().for_each(|x| out += &format!(" {x}"));
            out += "\n";
        }
        Err(e) => panic!("{text:?}: {e:?}"),
    }
    out
}

fn agree(name: &str, texts: &[&str]) {
    let file = root().join(format!("crates/tauto-syntax/tests/data/{name}.tables"));
    let t = Tables::read(&std::fs::read_to_string(file).unwrap()).unwrap();
    let mut args: Vec<String> = t.scan_texts().into();
    args.extend(t.lr_texts().unwrap());
    args.extend(texts.iter().map(|s| s.to_string()));
    let out = run_tote("lr", &args, STEPS);
    assert_eq!(out.error, None, "{}", out.stderr);
    assert_eq!(out.stderr, "");
    let want: String = texts.iter().map(|text| expected(&t, text)).collect();
    assert_eq!(out.stdout, want);
}

#[test]
fn math_parses_as_the_rust_parser_does() {
    agree(
        "math_lr",
        &[
            "1 = 2",
            " 1+2 + (3+4) = ( 5 ) ",
            "((1)) = 1+1+1+1",
            "1 + = 2",
            "1 = 2 +",
            "= 1",
            "(1 = 2",
            "1 = 2)",
            "",
            "   ",
        ],
    );
}

/// Equations of random sums, each also with a byte dropped.
fn equations() -> Vec<String> {
    let mut seed = 7u64;
    let mut next = move |n: u64| {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (seed >> 33) % n
    };
    fn sum(next: &mut dyn FnMut(u64) -> u64, depth: u32) -> String {
        (0..1 + next(4))
            .map(|_| {
                if depth > 0 && next(3) == 0 {
                    format!("( {})", sum(next, depth - 1))
                } else {
                    next(100).to_string()
                }
            })
            .collect::<Vec<_>>()
            .join(if next(2) == 0 { "+" } else { " + " })
    }
    let mut out = Vec::new();
    for _ in 0..100 {
        let text = format!("{} = {}", sum(&mut next, 3), sum(&mut next, 3));
        let mut broken = text.clone();
        broken.remove(next(text.len() as u64) as usize);
        out.extend([text, broken]);
    }
    out
}

#[test]
fn random_equations_parse_as_the_rust_parser_does() {
    let texts = equations();
    agree(
        "math_lr",
        &texts.iter().map(String::as_str).collect::<Vec<_>>(),
    );
}

#[test]
fn items_parses_as_the_rust_parser_does() {
    agree(
        "items_lr",
        &[
            "1",
            " 1 , 2,3 ;",
            "-",
            "(1, (2;), -) ;",
            "((-))",
            "1,",
            ",1",
            "1 2",
            "(1",
            "- ;",
            "",
        ],
    );
}
