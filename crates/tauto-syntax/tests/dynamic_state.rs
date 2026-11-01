//! The states of the scanner (`%state`, scnr2's dynamic state): Rust's raw
//! strings, whose end has as many `#` as their start. Tables made by
//! totes/llkgen from tests/data/raw.par.

use tauto_syntax::{Limits, Tables, build_ast, parse, tokens};

fn tables() -> Tables {
    Tables::read(include_str!("data/raw.tables")).expect("tables")
}

/// The tokens the parser reads, as (terminal name, text).
fn scan(text: &str) -> Vec<(String, String)> {
    let t = tables();
    tokens(&t, text, 0)
        .expect("scan")
        .into_iter()
        .filter(|tok| !t.is_skipped(tok.terminal))
        .map(|tok| {
            (
                t.terminals()[tok.terminal as usize].clone(),
                text[tok.start as usize..tok.end as usize].to_string(),
            )
        })
        .collect()
}

fn pairs(xs: &[(&str, &str)]) -> Vec<(String, String)> {
    xs.iter()
        .map(|(a, b)| (a.to_string(), b.to_string()))
        .collect()
}

#[test]
fn a_raw_string_ends_with_as_many_hashes_as_it_starts_with() {
    assert_eq!(
        scan(r###"r##"a"#b"## c"###),
        pairs(&[
            ("RawOpen", "r##\""),
            ("RawText", "a"),
            ("RawQuote", "\"#"),
            ("RawText", "b"),
            ("RawClose", "\"##"),
            ("Ident", "c"),
        ])
    );
}

#[test]
fn a_raw_string_without_hashes_ends_at_the_first_quote() {
    assert_eq!(
        scan(r#"r"x" y"#),
        pairs(&[
            ("RawOpen", "r\""),
            ("RawText", "x"),
            ("RawClose", "\""),
            ("Ident", "y"),
        ])
    );
}

#[test]
fn more_hashes_than_the_start_are_not_its_end() {
    // `"##` after `r#"`: the end takes one `#`; the other is after the string.
    assert_eq!(
        scan(r###"r#"a"##"###),
        pairs(&[
            ("RawOpen", "r#\""),
            ("RawText", "a"),
            ("RawClose", "\"#"),
            ("Error", "#"),
        ])
    );
}

#[test]
fn the_parser_reads_the_tokens() {
    let t = tables();
    let text = r###"a r##"x"#y"## b"###;
    let events = parse(&t, text, 0, &Limits::default()).expect("parse");
    build_ast(&t, &events).expect("ast");
}
