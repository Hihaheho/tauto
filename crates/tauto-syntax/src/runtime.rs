//! Runtime parsing with the same diagnostics in every execution backend.
//!
//! Derived from parol and scnr2 by Jörg Singer (MIT OR Apache-2.0); see NOTICE.
use crate::{Ast, Limits, ParseError, Tables, build_ast, parse};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub message: String,
    pub at: u32,
    pub expected: Vec<String>,
}

pub fn parse_ast(name: &str, tables: &Tables, text: &str) -> Result<Ast, Diagnostic> {
    let failed = |message, at, expected| {
        Err(Diagnostic {
            message,
            at,
            expected,
        })
    };
    let events = match parse(tables, text, 0, &Limits::default()) {
        Ok(e) => e,
        Err(ParseError::Lex(l)) => {
            return failed(
                format!("macro.syntax_error: in {name}: this text is not a token of the syntax"),
                l.at,
                Vec::new(),
            );
        }
        Err(ParseError::Syntax(s)) => {
            let expected: Vec<String> = s
                .expected
                .iter()
                .map(|&t| tables.terminals()[t as usize].clone())
                .collect();
            let at = s.at.map_or(text.len() as u32, |t| t.start);
            let found = match s.at {
                Some(t) => format!("found {}", tables.terminals()[t.terminal as usize]),
                None => "found the end of the text".to_string(),
            };
            let list = if expected.is_empty() {
                "something else".to_string()
            } else {
                expected.join(" or ")
            };
            return failed(
                format!("macro.syntax_error: in {name}: expected {list}, {found}"),
                at,
                expected,
            );
        }
        Err(ParseError::Limit(m)) => {
            return failed(format!("macro.syntax_error: in {name}: {m}"), 0, Vec::new());
        }
    };
    match build_ast(tables, &events) {
        Ok(ast) => Ok(ast),
        Err(e) => failed(format!("macro.syntax_error: {}", e.0), 0, Vec::new()),
    }
}
