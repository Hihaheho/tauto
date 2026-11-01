//! LALR(1) tables, made by totes/lalrgen, run by this crate: each grammar of
//! tests/data as an LALR(1) grammar (the `_lr` files) against its LL(1)
//! tables. `items` has a start symbol of two productions, which the
//! generator puts under one it adds.

use tauto_syntax::{Ast, Cst, Limits, ParseError, Tables, build_ast, build_cst, parse};

fn tables(name: &str) -> Tables {
    let text = match name {
        "math" => include_str!("data/math.tables"),
        "math_lr" => include_str!("data/math_lr.tables"),
        "items" => include_str!("data/items.tables"),
        "items_lr" => include_str!("data/items_lr.tables"),
        _ => unreachable!(),
    };
    Tables::read(text).expect("tables")
}

/// The tree without its spans (the spans are checked by `spans_are_tight`).
fn shape(a: &Ast) -> String {
    match a {
        Ast::Node {
            ty, ctor, fields, ..
        } => format!(
            "{ty}.{ctor}({})",
            fields.iter().map(shape).collect::<Vec<_>>().join(" ")
        ),
        Ast::Token(t) => format!("{}@{}", t.terminal, t.start),
        Ast::List(l) => format!("[{}]", l.iter().map(shape).collect::<Vec<_>>().join(" ")),
        Ast::Opt(o) => format!("?{}", o.as_deref().map(shape).unwrap_or_default()),
    }
}

/// The lossless tree with the non-terminals by name (the two tables number them differently).
fn cst_shape(t: &Tables, c: &Cst) -> String {
    match c {
        Cst::Node {
            non_terminal,
            children,
            start,
            end,
        } => format!(
            "{}{start}-{end}({})",
            t.non_terminals()[*non_terminal as usize],
            children
                .iter()
                .map(|c| cst_shape(t, c))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        Cst::Token(tok) => format!("{}@{}", tok.terminal, tok.start),
    }
}

/// The first and last byte of the tokens under a tree, if it has any.
fn extent(a: &Ast) -> Option<(u32, u32)> {
    match a {
        Ast::Token(t) => Some((t.start, t.end)),
        Ast::Node { fields, .. } => join(fields.iter().map(extent)),
        Ast::List(l) => join(l.iter().map(extent)),
        Ast::Opt(o) => o.as_deref().and_then(extent),
    }
}

fn join(it: impl Iterator<Item = Option<(u32, u32)>>) -> Option<(u32, u32)> {
    it.flatten().reduce(|(a, b), (c, d)| (a.min(c), b.max(d)))
}

/// Every node spans its own tokens and no more. (The LL(k) parse gives an item of a repetition
/// the span of the rest of the list too.)
fn spans_are_tight(a: &Ast) {
    match a {
        Ast::Node { span, fields, .. } => {
            if let Some(e) = extent(a) {
                assert_eq!(*span, e, "{a:?}");
            }
            fields.iter().for_each(spans_are_tight);
        }
        Ast::List(l) => l.iter().for_each(spans_are_tight),
        Ast::Opt(Some(o)) => spans_are_tight(o),
        _ => {}
    }
}

fn run(t: &Tables, text: &str) -> Result<(Ast, Cst), ParseError> {
    let events = parse(t, text, 0, &Limits::default())?;
    Ok((
        build_ast(t, &events).expect("ast"),
        build_cst(t, &events).expect("cst"),
    ))
}

/// The same trees from both tables, or an error from both.
fn agree(name: &str, texts: &[String]) {
    let (ll, lr) = (tables(name), tables(&format!("{name}_lr")));
    let mut parsed = 0;
    for text in texts {
        match (run(&ll, text), run(&lr, text)) {
            (Ok((a, c)), Ok((b, d))) => {
                assert_eq!(shape(&a), shape(&b), "{text:?}");
                assert_eq!(cst_shape(&ll, &c), cst_shape(&lr, &d), "{text:?}");
                spans_are_tight(&b);
                parsed += 1;
            }
            (Err(_), Err(_)) => {}
            (a, b) => panic!("{text:?}: {:?} and {:?}", a.err(), b.err()),
        }
    }
    assert!(parsed >= 30, "{parsed} texts parse");
}

/// Texts of the tokens `alphabet`, every one up to `len` of them long, spaced out a little.
fn texts(alphabet: &[&str], len: usize) -> Vec<String> {
    let mut out = vec![String::new()];
    let mut last = vec![Vec::<&str>::new()];
    for _ in 0..len {
        let mut next = Vec::new();
        for w in &last {
            for a in alphabet {
                let mut w = w.clone();
                w.push(a);
                next.push(w);
            }
        }
        out.extend(next.iter().enumerate().map(|(i, w)| {
            w.iter()
                .enumerate()
                .map(|(j, a)| {
                    if (i + j) % 3 == 0 {
                        format!(" {a}")
                    } else {
                        a.to_string()
                    }
                })
                .collect()
        }));
        last = next;
    }
    out
}

/// Equations of random sums, each also with a byte dropped.
fn equations() -> Vec<String> {
    let mut seed = 1u64;
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
    for _ in 0..2000 {
        let text = format!("{} = {}", sum(&mut next, 3), sum(&mut next, 3));
        let mut broken = text.clone();
        broken.remove(next(text.len() as u64) as usize);
        out.extend([text, broken]);
    }
    out
}

#[test]
fn math_agrees_with_ll() {
    agree("math", &texts(&["1", "+", "=", "(", ")"], 7));
    agree("math", &equations());
}

#[test]
fn items_agrees_with_ll() {
    agree("items", &texts(&["1", ",", ";", "-", "(", ")"], 7));
}

#[test]
fn reads_the_generator() {
    let t = tables("math_lr");
    assert_eq!(t.title(), Some("math"));
    assert!(t.generator().starts_with("lalrgen "));
}

#[test]
fn a_long_list_stays_shallow() {
    // A left recursive list needs no stack (the LL parse needs a frame per item).
    let t = tables("math_lr");
    let text = format!("1{} = 2", "+1".repeat(200_000));
    let limits = Limits {
        max_input: 1 << 21,
        max_stack: 64,
    };
    let events = parse(&t, &text, 0, &limits).expect("parse");
    let Ast::Node { fields, .. } = build_ast(&t, &events).expect("ast") else {
        panic!("a node")
    };
    let Ast::Node { fields: sum, .. } = &fields[0] else {
        panic!("a sum")
    };
    let Ast::List(items) = &sum[1] else {
        panic!("a list")
    };
    assert_eq!(items.len(), 200_000);
    let Ast::Node { span, .. } = &items[199_999] else {
        panic!("an item")
    };
    assert_eq!(*span, (399_999, 400_001));
}

#[test]
fn reports_what_the_state_expects() {
    let t = tables("math_lr");
    let names = |e: &[u32]| -> Vec<String> {
        e.iter()
            .map(|&i| t.terminals()[i as usize].clone())
            .collect()
    };
    match parse(&t, "1 + = 2", 0, &Limits::default()) {
        Err(ParseError::Syntax(e)) => {
            assert_eq!(e.at.map(|t| t.start), Some(4));
            assert_eq!(names(&e.expected), ["Num", "LParen"]);
        }
        other => panic!("{other:?}"),
    }
    match parse(&t, "1 = 2 +", 0, &Limits::default()) {
        Err(ParseError::Syntax(e)) => {
            assert_eq!(e.at, None);
            assert_eq!(names(&e.expected), ["Num", "LParen"]);
        }
        other => panic!("{other:?}"),
    }
}
