//! Runtime parsing with the same diagnostics in every execution backend.
//!
//! Derived from parol and scnr2 by Jörg Singer (MIT OR Apache-2.0); see NOTICE.
use crate::{Ast, Limits, ParseError, Tables, build_ast, parse};

/// Why a text is not of a syntax. The message is not written here: `message`
/// is the id of a message of the tools and `args` its arguments, so that each
/// tool writes it in its language (`macro-syntax-*` of the messages). An
/// argument named `expected` comes once for each terminal that would have been
/// taken, in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub message: String,
    pub at: u32,
    pub expected: Vec<String>,
    pub args: Vec<(String, String)>,
}

/// The id of a text that is not a token of the syntax: `syntax`.
pub const NOT_A_TOKEN: &str = "macro-syntax-not-a-token";
/// The id of a terminal that does not fit: `syntax`, each `expected`, `found`.
pub const EXPECTED_FOUND: &str = "macro-syntax-expected-found";
/// The id of a text that ends too soon: `syntax`, each `expected`.
pub const EXPECTED_END: &str = "macro-syntax-expected-end";
/// The id of a limit of the parse that ran out: `syntax`, `detail`.
pub const LIMIT: &str = "macro-syntax-limit";
/// The id of a tree that does not make the syntax's types: `detail`.
pub const SCHEMA: &str = "macro-syntax-schema";
/// The id of tables that do not read: `syntax`, `detail`.
pub const TABLES: &str = "macro-syntax-tables";

fn arg(name: &str, value: &str) -> (String, String) {
    (name.to_string(), value.to_string())
}

/// The diagnostic of an error of the parse of `text`.
pub fn describe(name: &str, tables: &Tables, text: &str, e: &ParseError) -> Diagnostic {
    let syntax = arg("syntax", name);
    match e {
        ParseError::Lex(l) => Diagnostic {
            message: NOT_A_TOKEN.into(),
            at: l.at,
            expected: Vec::new(),
            args: vec![syntax],
        },
        // The scanner's catch-all token (`Error`) is text that is no token
        // of the syntax, not a terminal of it.
        ParseError::Syntax(s)
            if s
                .at
                .is_some_and(|t| tables.terminals()[t.terminal as usize] == "Error") =>
        {
            Diagnostic {
                message: NOT_A_TOKEN.into(),
                at: s.at.map_or(0, |t| t.start),
                expected: Vec::new(),
                args: vec![syntax],
            }
        }
        ParseError::Syntax(s) => {
            let mut args = vec![syntax];
            args.extend(
                s.expected
                    .iter()
                    .map(|&t| arg("expected", tables.terminal_phrase(t))),
            );
            let message = match s.at {
                Some(t) => {
                    args.push(arg("found", tables.terminal_phrase(t.terminal)));
                    EXPECTED_FOUND
                }
                None => EXPECTED_END,
            };
            Diagnostic {
                message: message.into(),
                at: s.at.map_or(text.len() as u32, |t| t.start),
                expected: s
                    .expected
                    .iter()
                    .map(|&t| tables.terminals()[t as usize].clone())
                    .collect(),
                args,
            }
        }
        ParseError::Limit(m) => Diagnostic {
            message: LIMIT.into(),
            at: 0,
            expected: Vec::new(),
            args: vec![syntax, arg("detail", m)],
        },
    }
}

pub fn parse_ast(name: &str, tables: &Tables, text: &str) -> Result<Ast, Diagnostic> {
    let events =
        parse(tables, text, 0, &Limits::default()).map_err(|e| describe(name, tables, text, &e))?;
    build_ast(tables, &events).map_err(|e| Diagnostic {
        message: SCHEMA.into(),
        at: 0,
        expected: Vec::new(),
        args: vec![arg("detail", &e.0)],
    })
}
