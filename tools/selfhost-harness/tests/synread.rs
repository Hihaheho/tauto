//! `totes/synread` against `tauto_syntax` and the host's reader of a literal: the parser's text
//! a syntax's tables make (`Tables::runtime_text`), and the value a literal is read into
//! (`Builder::node` of `tauto_parse::syntax`, the form of `Node::show`) or why it is not read.
//!
//! The inputs are the cases marked `differential = "synread"`: the first line of a case's source is
//! `NAME SHA256 [FROM [LINE:TAKEN…]]` (or `NAME SHA256.START`, the tables of another start symbol) of the tables in
//! `cases/.tauto-syntax`, the rest is the literal.

use selfhost_harness::{assert_same_dump, differential, materialize, root, run_tote_native};
use tauto::surface::SyntaxLit;
use tauto_surface::span::Span;
use tauto::syntax::Builder;
use tauto_syntax::{Limits, RuntimeIds, Tables, build_ast};

const STEPS: u64 = 200_000_000_000;

/// The number the tote gives the node of the type `ty` and constructor `ctor`: after the five
/// that every parse makes, the schema's in order (`tb_node_id`).
fn node_id(tables: &Tables, ty: u32, ctor: u32) -> u32 {
    use tauto_syntax::TypeDef;
    let before: usize = tables.schema().types[..ty as usize]
        .iter()
        .map(|t| match t {
            TypeDef::Struct { .. } => 1,
            TypeDef::Enum { ctors, .. } => ctors.len(),
        })
        .sum();
    let own = match &tables.schema().types[ty as usize] {
        TypeDef::Struct { .. } => 0,
        TypeDef::Enum { .. } => ctor as usize,
    };
    (5 + before + own) as u32
}

/// What the tote prints for one input, as the Rust side makes it.
fn expected(source: &str) -> String {
    let (header, literal) = source.split_once('\n').unwrap();
    let mut words = header.split(' ');
    let (name, key) = (words.next().unwrap(), words.next().unwrap());
    let start: u32 = words.next().map_or(0, |w| w.parse().unwrap());
    let shifts: Vec<(u32, u32)> = words
        .map(|w| {
            let (a, b) = w.split_once(':').unwrap();
            (a.parse().unwrap(), b.parse().unwrap())
        })
        .collect();
    let sha = key.split('.').next().unwrap();
    let tables = Tables::read(
        &std::fs::read_to_string(root().join(format!("cases/.tauto-syntax/{key}.tables"))).unwrap(),
    )
    .unwrap();
    let _ = sha;
    let mut out = String::new();
    let ids = RuntimeIds {
        span: 0,
        ctx: 1,
        token: 2,
        diag: 3,
        arg: 4,
    };
    let text = tables
        .runtime_text(name, &mut |ty, ctor| Ok(node_id(&tables, ty, ctor)), ids)
        .unwrap();
    out.push_str(&format!("text{text}\n"));
    // The host's own path: the events of the parse with the host's limits, the tree, and the values
    // of the literal's tokens and nodes.
    match tauto_syntax::parse(&tables, literal, 0, &Limits::default()) {
        Err(e) => {
            let d = tauto_syntax::describe(name, &tables, literal, &e);
            let args: Vec<String> = d.args.iter().map(|(n, v)| format!("{n}={v}")).collect();
            out.push_str(&format!(
                "error {} {} [{}] {}\n",
                d.message,
                d.at,
                d.expected.join(","),
                args.join(";")
            ));
        }
        Ok(events) => {
            let ast = build_ast(&tables, &events).unwrap();
            let lit = SyntaxLit {
                name: Some(name.to_string()),
                text: literal.to_string(),
                start,
                shifts,
                error: None,
                span: Span::new(0, 0),
            };
            let builder = Builder {
                name,
                tables: &tables,
                lit: &lit,
                scopes: &[],
            };
            // A hole that does not read or lift is one error here, whatever it is.
            match builder.node(&ast) {
                Ok(node) => {
                    // `totes/macros` writes the constructors of a lifted expression `SynExpr.ExApp`
                    // where the host's value shows `SynExpr::ExApp`: the same constructor.
                    let mut shown = node.show();
                    for ty in ["SynExpr", "SynStmt", "SynPattern", "SynBinder"] {
                        shown = shown.replace(&format!("{ty}::"), &format!("{ty}."));
                    }
                    out.push_str(&format!("node {shown}\n"));
                }
                Err(_) => out.push_str("error embedded\n"),
            }
        }
    }
    out
}

#[test]
fn synread_matches_the_marked_cases() {
    let inputs = differential("synread");
    let m = materialize("synread", &inputs);
    let mut args = vec![root().join("cases/.tauto-syntax").to_string_lossy().into_owned()];
    args.extend(m.paths.iter().cloned());
    let out = run_tote_native("synread", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let mut rust = String::new();
    for (path, (_, source)) in m.paths.iter().zip(&inputs) {
        rust.push_str(&format!("== {path}\n{}", expected(source)));
    }
    assert_same_dump("synread", &rust, &out.stdout);
}
