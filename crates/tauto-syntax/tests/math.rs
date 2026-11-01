//! The `math` syntax of the macro cases (`cases/macro/syntax.eure`), without
//! `Embed`: tables made by
//! totes/llkgen from tests/data/math.par, run by this crate.

use tauto_syntax::{Ast, Event, Limits, ParseError, Tables, build_ast, parse};

fn tables() -> Tables {
    Tables::read(include_str!("data/math.tables")).expect("tables")
}

fn type_index(t: &Tables, name: &str) -> u32 {
    use tauto_syntax::TypeDef;
    t.schema()
        .types
        .iter()
        .position(|d| match d {
            TypeDef::Struct { name: n, .. } | TypeDef::Enum { name: n, .. } => n == name,
        })
        .unwrap_or_else(|| panic!("no type {name}")) as u32
}

fn ast(t: &Tables, text: &str) -> Ast {
    let events = parse(t, text, 0, &Limits::default()).expect("parse");
    build_ast(t, &events).expect("ast")
}

#[test]
fn reads_the_header() {
    let t = tables();
    assert_eq!(t.title(), Some("math"));
    assert_eq!(t.max_k(), 1);
    assert_eq!(t.grammar_sha256().len(), 64);
}

#[test]
fn builds_the_types_of_the_design() {
    let t = tables();
    use tauto_syntax::{FieldTy, TypeDef};
    let eqn = &t.schema().types[type_index(&t, "Eqn") as usize];
    let TypeDef::Struct { fields, .. } = eqn else {
        panic!("Eqn is a struct")
    };
    let names: Vec<_> = fields.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["sum", "equals", "sum_2"]);
    let sum = &t.schema().types[type_index(&t, "Sum") as usize];
    let TypeDef::Struct { fields, .. } = sum else {
        panic!("Sum is a struct")
    };
    assert_eq!(fields[1].0, "rep");
    assert_eq!(
        fields[1].1,
        FieldTy::List(Box::new(FieldTy::Named("Sum_Rep1".into())))
    );
    let term = &t.schema().types[type_index(&t, "Term") as usize];
    assert!(
        matches!(term, TypeDef::Enum { ctors, .. } if ctors.iter().map(|c| c.name.as_str()).eq(["Num", "Paren"]))
    );
}

#[test]
fn parses_an_equation() {
    let t = tables();
    let Ast::Node {
        ty, span, fields, ..
    } = ast(&t, "1 + 2 = 3")
    else {
        panic!("a node")
    };
    assert_eq!(ty, type_index(&t, "Eqn"));
    assert_eq!(span, (0, 9));
    assert_eq!(fields.len(), 3);
    // sum: term + one Sum_Rep1
    let Ast::Node { fields: sum, .. } = &fields[0] else {
        panic!()
    };
    let Ast::List(rep) = &sum[1] else {
        panic!("the repetition is a list")
    };
    assert_eq!(rep.len(), 1);
    let Ast::Node {
        ty: rep_ty,
        fields: rep_fields,
        ..
    } = &rep[0]
    else {
        panic!()
    };
    assert_eq!(*rep_ty, type_index(&t, "Sum_Rep1"));
    assert!(matches!(rep_fields[0], Ast::Token(tok) if (tok.start, tok.end) == (2, 3)));
    // equals is a token
    assert!(matches!(fields[1], Ast::Token(tok) if (tok.start, tok.end) == (6, 7)));
}

#[test]
fn keeps_the_order_of_a_long_repetition() {
    let t = tables();
    let Ast::Node { fields, .. } = ast(&t, "1+2+3+4=10") else {
        panic!()
    };
    let Ast::Node { fields: sum, .. } = &fields[0] else {
        panic!()
    };
    let Ast::List(rep) = &sum[1] else { panic!() };
    let starts: Vec<u32> = rep
        .iter()
        .map(|r| {
            let Ast::Node { fields, .. } = r else {
                panic!()
            };
            let Ast::Node { span, .. } = &fields[1] else {
                panic!("term node")
            };
            span.0
        })
        .collect();
    assert_eq!(starts, [2, 4, 6]);
}

#[test]
fn nests_parentheses() {
    let t = tables();
    let Ast::Node { fields, .. } = ast(&t, "(1 + 2) = 3") else {
        panic!()
    };
    let Ast::Node { fields: sum, .. } = &fields[0] else {
        panic!()
    };
    let Ast::Node {
        ctor, fields: term, ..
    } = &sum[0]
    else {
        panic!()
    };
    assert_eq!(*ctor, 1, "Term::Paren");
    assert!(matches!(&term[0], Ast::Node { ty, .. } if *ty == type_index(&t, "Paren")));
}

#[test]
fn the_events_keep_white_space() {
    let t = tables();
    let events = parse(&t, "1 = 1", 0, &Limits::default()).unwrap();
    let tokens = events
        .iter()
        .filter(|e| matches!(e, Event::Token(_)))
        .count();
    assert_eq!(tokens, 5, "three tokens and two spaces");
    let opens = events
        .iter()
        .filter(|e| matches!(e, Event::Open { .. }))
        .count();
    let closes = events.iter().filter(|e| matches!(e, Event::Close)).count();
    assert_eq!(opens, closes);
}

#[test]
fn base_moves_the_positions() {
    let t = tables();
    let events = parse(&t, "1=1", 100, &Limits::default()).unwrap();
    let Some(Event::Token(first)) = events.iter().find(|e| matches!(e, Event::Token(_))) else {
        panic!()
    };
    assert_eq!((first.start, first.end), (100, 101));
}

#[test]
fn reports_where_and_what_was_expected() {
    let t = tables();
    let Err(ParseError::Syntax(e)) = parse(&t, "1 + = 3", 0, &Limits::default()) else {
        panic!("a syntax error")
    };
    assert_eq!(e.at.map(|t| (t.start, t.end)), Some((4, 5)));
    let names: Vec<&str> = e
        .expected
        .iter()
        .map(|&n| t.terminals()[n as usize].as_str())
        .collect();
    assert_eq!(names, ["Num", "LParen"]);
}

#[test]
fn reports_the_end_of_input() {
    let t = tables();
    let Err(ParseError::Syntax(e)) = parse(&t, "1 +", 0, &Limits::default()) else {
        panic!()
    };
    assert_eq!(e.at, None);
    let Err(ParseError::Syntax(e)) = parse(&t, "1 = 2 )", 0, &Limits::default()) else {
        panic!()
    };
    assert_eq!(e.at.map(|t| t.start), Some(6));
}

#[test]
fn rejects_what_the_scanner_cannot_read() {
    let t = tables();
    let r = parse(&t, "1 + @", 0, &Limits::default());
    assert!(
        matches!(r, Err(ParseError::Lex(_)) | Err(ParseError::Syntax(_))),
        "{r:?}"
    );
}

#[test]
fn limits_stop_a_deep_input() {
    let t = tables();
    let deep = format!("{}1{} = 1", "(".repeat(5000), ")".repeat(5000));
    let r = parse(
        &t,
        &deep,
        0,
        &Limits {
            max_input: 1 << 20,
            max_stack: 1000,
        },
    );
    assert_eq!(
        r,
        Err(ParseError::Limit(
            "the parse stack is deeper than the limit"
        ))
    );
    let r = parse(
        &t,
        &deep,
        0,
        &Limits {
            max_input: 10,
            max_stack: 1 << 16,
        },
    );
    assert!(matches!(r, Err(ParseError::Limit(_))));
}

#[test]
fn a_hand_broken_table_is_refused() {
    let text = include_str!("data/math.tables").replace("start 0", "start 99");
    assert!(Tables::read(&text).is_err());
    assert!(Tables::read("nonsense").is_err());
}

fn leaves(c: &tauto_syntax::Cst, out: &mut Vec<tauto_syntax::Token>) {
    match c {
        tauto_syntax::Cst::Token(t) => out.push(*t),
        tauto_syntax::Cst::Node { children, .. } => children.iter().for_each(|c| leaves(c, out)),
    }
}

#[test]
fn the_tree_holds_every_token_in_order_and_names_only_the_grammars_nodes() {
    use tauto_syntax::Cst;
    let t = tables();
    let text = "  1 + (2 + 3)  =  6 ";
    let events = parse(&t, text, 0, &Limits::default()).expect("parse");
    let cst = tauto_syntax::build_cst(&t, &events).expect("cst");
    let mut tokens = Vec::new();
    leaves(&cst, &mut tokens);
    let again: String = tokens
        .iter()
        .map(|t| &text[t.start as usize..t.end as usize])
        .collect();
    assert_eq!(again, text);
    let Cst::Node {
        non_terminal,
        children,
        start,
        end,
    } = &cst
    else {
        panic!("a node")
    };
    assert_eq!(t.non_terminals()[*non_terminal as usize], "Eqn");
    // The range leaves out the white space around; the children hold it.
    assert_eq!(&text[*start as usize..*end as usize], "1 + (2 + 3)  =  6");
    assert!(matches!(&children[0], Cst::Token(w) if t.is_skipped(w.terminal)));
    // A repetition's own non-terminal is not a node: `Sum` holds its `Term`s directly.
    let names: Vec<&str> = children
        .iter()
        .filter_map(|c| match c {
            Cst::Node { non_terminal, .. } => {
                Some(t.non_terminals()[*non_terminal as usize].as_str())
            }
            Cst::Token(_) => None,
        })
        .collect();
    assert_eq!(names, ["Sum", "Equals", "Sum"]);
}
