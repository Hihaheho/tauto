//! Tauto syntax: the parol grammar (`tauto.par`), the generated LL(k)
//! parser, a concrete syntax tree with byte spans, and syntax errors.
//!
//! This crate only reads text. Names, types and meaning belong to
//! `tauto`; nothing parol generates leaves this crate.

use tauto_message::msg;

mod cst;
mod nib_tables;

pub use cst::{Cst, CstNode, NodeId, NodeKind, Span, is_trivia};
pub use node_kind::{NonTerminalKind, TerminalKind};

// Generated from tauto.par by `bash scripts/generate-tauto-parol.sh` and
// committed (src/generated/); rerun it after every change to the grammar.
// The generated parser names these modules by absolute path
// (`crate::grammar`, `crate::grammar_trait`).
#[allow(clippy::all, dead_code, unused_imports, unused_variables)]
mod grammar_trait {
    include!("generated/grammar_trait.rs");
}
#[allow(clippy::all, dead_code, unused_imports)]
mod parser {
    include!("generated/parser.rs");

    /// Semantic actions that keep nothing: the tree is the `CstBuilder`'s.
    /// parol's own typed AST (`GrammarAuto`), which moves large values on
    /// every production, is not built.
    struct NoActions;

    impl<'t> parol_runtime::parser::UserActionsTrait<'t> for NoActions {
        fn call_semantic_action_for_production_number(
            &mut self,
            _prod_num: usize,
            _children: &[parol_runtime::parser::ParseTreeType<'t>],
        ) -> Result<(), parol_runtime::ParolError> {
            Ok(())
        }

        fn on_comment(&mut self, _token: parol_runtime::lexer::Token<'t>) {}
    }

    /// The tables of this parser and of its scanner, as the data of
    /// `totes/syntax` (`docs/design/self-host.md`).
    pub fn syntax_tables() -> Vec<crate::nib_tables::Table> {
        use crate::nib_tables::{Inputs, render};
        let start = NON_TERMINALS
            .iter()
            .position(|n| *n == "Program")
            .expect("the start symbol");
        render(&Inputs {
            terminal_names: TERMINAL_NAMES,
            non_terminals: NON_TERMINALS,
            declared: crate::declared::DECLARED,
            max_k: MAX_K,
            skip: SKIP_TOKENS_BY_SCANNER_STATE,
            lookahead: LOOKAHEAD_AUTOMATA,
            productions: PRODUCTIONS,
            modes: grammar_scanner::MODES,
            class_of: grammar_scanner::GrammarScanner::match_function,
            start,
        })
    }

    /// `parse_into` without the typed AST.
    pub fn parse_tree<'t, T: TreeConstruct<'t>>(
        input: &'t str,
        tree_builder: &mut T,
    ) -> Result<(), ParolError>
    where
        ParolError: From<T::Error>,
    {
        use grammar_scanner::GrammarScanner;
        // The start symbol, found by name so a grammar change cannot shift it.
        let start = NON_TERMINALS
            .iter()
            .position(|n| *n == "Program")
            .expect("the start symbol");
        let mut llk_parser = LLKParser::new(
            start,
            LOOKAHEAD_AUTOMATA,
            PRODUCTIONS,
            TERMINAL_NAMES,
            NON_TERMINALS,
        );
        let scanner = GrammarScanner::new();
        llk_parser.parse_into(
            tree_builder,
            TokenStream::new_with_skip_tokens(
                input,
                "tauto",
                scanner.scanner_impl.clone(),
                &GrammarScanner::match_function,
                MAX_K,
                SKIP_TOKENS_BY_SCANNER_STATE,
            )
            .unwrap(),
            &mut NoActions,
        )
    }
}
#[allow(clippy::all, dead_code)]
mod node_kind {
    include!("generated/node_kind.rs");
}
mod declared {
    include!("generated/declared.rs");
}

mod grammar {
    use crate::grammar_trait::GrammarTrait;

    /// The semantic actions do nothing: the tree is built by `CstBuilder`.
    #[derive(Debug, Default)]
    pub struct Grammar<'t>(std::marker::PhantomData<&'t ()>);

    impl<'t> GrammarTrait<'t> for Grammar<'t> {}
}

/// The parser's and the scanner's tables, as the data of `totes/syntax`
/// (`totes/syntax/src/tables/<name>.txt`, `docs/design/self-host.md`).
pub fn syntax_tables() -> Vec<Table> {
    parser::syntax_tables()
}

pub use nib_tables::Table;

/// A syntax error, located by byte offsets into the source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxError {
    pub message: String,
    /// `None` when parol could not say where (for instance at the end of input).
    pub span: Option<Span>,
    /// Terminal names the parser would have accepted, when known.
    pub expected: Vec<String>,
}

/// The tree of a parse, and the errors met while building it. The tree is
/// always there: on an error it holds everything read up to that point, so
/// highlighting and completion keep working while a line is half typed.
#[derive(Debug, Clone)]
pub struct Parsed {
    pub cst: Cst,
    pub errors: Vec<SyntaxError>,
}

impl Parsed {
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }
}

/// The deepest syntax tree `parse` accepts. A parenthesized expression is
/// about twenty levels, so this allows a few hundred nested parentheses.
pub const MAX_DEPTH: usize = 10_000;

/// The error of a source nested deeper than `MAX_DEPTH`, in English (its
/// id is `parse-too-deep`).
pub const TOO_DEEP: &str = "the source nests too deeply";

pub fn parse(source: &str) -> Parsed {
    let mut builder = cst::CstBuilder::new();
    match parser::parse_tree(source, &mut builder) {
        Ok(()) => {
            let cst = builder.build(source);
            if cst.depth() > MAX_DEPTH {
                // Every later stage walks the tree recursively; an empty one
                // keeps them from running out of stack.
                return Parsed {
                    cst: cst::CstBuilder::new().build(source),
                    errors: vec![SyntaxError {
                        message: msg!("parse-too-deep").to_string(),
                        span: None,
                        expected: Vec::new(),
                    }],
                };
            }
            Parsed {
                cst,
                errors: Vec::new(),
            }
        }
        Err(error) => {
            let mut errors = Vec::new();
            collect_errors(error, source, &mut errors);
            let cst = builder.build(source);
            let terminals = cst.terminals();
            for e in &mut errors {
                if let Some(span) = e.span
                    && let_type_without_assign(&terminals, span.start)
                {
                    e.message = msg!("parse-let-type-eq").to_string();
                }
            }
            if errors.is_empty() {
                errors.push(SyntaxError {
                    message: msg!("parse-syntax-error").to_string(),
                    span: None,
                    expected: Vec::new(),
                });
            }
            Parsed { cst, errors }
        }
    }
}

fn location_span(start: u32, end: u32, source: &str) -> Option<Span> {
    // parol uses 0..0 for the end of input and for tokens it made up while
    // recovering; place those at the end of the text.
    if start == 0 && end == 0 && !source.is_empty() {
        let len = source.len() as u32;
        return Some(Span::new(len, len));
    }
    Some(Span::new(start, end.max(start)))
}

/// The spelling of a keyword token (`Kw…`), so that a reserved word used
/// as a name is reported as such rather than by its token name.
fn keyword_text<'a>(found: &str, span: Option<Span>, source: &'a str) -> Option<&'a str> {
    if !found.starts_with("Kw") {
        return None;
    }
    let span = span?;
    let word = source.get(span.start as usize..span.end as usize)?;
    (!word.is_empty() && word.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'))
        .then_some(word)
}

/// Whether the error at `at` stops a `let` that has a `=` and no `:=`
/// (`let x: T = v`): the `=` was read as the equality of a type, so the
/// binding's `:=` is what the parser then missed.
fn let_type_without_assign(terminals: &[(TerminalKind, Span)], at: u32) -> bool {
    let kinds: Vec<TerminalKind> = terminals
        .iter()
        .filter(|(k, s)| s.start < at && !is_trivia(*k))
        .map(|(k, _)| *k)
        .collect();
    let mut saw_eq = false;
    for (i, kind) in kinds.iter().enumerate().rev() {
        match kind {
            TerminalKind::Eq => saw_eq = true,
            TerminalKind::KwLet => return saw_eq,
            // A line break after `=` continues the type.
            TerminalKind::Nl if i > 0 && kinds[i - 1] == TerminalKind::Eq => {}
            TerminalKind::Assign
            | TerminalKind::Nl
            | TerminalKind::Semi
            | TerminalKind::LBrace
            | TerminalKind::RBrace => return false,
            _ => {}
        }
    }
    false
}

fn collect_errors(error: parol_runtime::ParolError, source: &str, out: &mut Vec<SyntaxError>) {
    use parol_runtime::{ParolError, ParserError};
    match error {
        ParolError::ParserError(ParserError::SyntaxErrors { entries }) => {
            for entry in entries {
                // The lookahead failed as a whole; a keyword in it is what
                // broke it (`fn loop(…)` fails at `loop`, not at `fn`).
                let culprit = entry
                    .unexpected_tokens
                    .iter()
                    .rfind(|t| t.token_type.starts_with("Kw"))
                    .or_else(|| entry.unexpected_tokens.first());
                let span = culprit
                    .map(|t| location_span(t.token.start, t.token.end, source))
                    .unwrap_or_else(|| {
                        location_span(entry.error_location.start, entry.error_location.end, source)
                    });
                let expected = entry
                    .expected_tokens
                    .iter()
                    .map(|t| t.to_string())
                    .collect();
                let found = culprit.map(|t| t.token_type.clone()).unwrap_or_default();
                out.push(SyntaxError {
                    message: if found.is_empty() {
                        msg!("parse-unexpected-input").to_string()
                    } else if let Some(word) = keyword_text(&found, span, source) {
                        msg!("parse-keyword-as-name", word = word).to_string()
                    } else {
                        msg!("parse-unexpected", found = found).to_string()
                    },
                    span,
                    expected,
                });
            }
        }
        ParolError::ParserError(ParserError::UnprocessedInput { last_token, .. }) => {
            out.push(SyntaxError {
                message: msg!("parse-input-after-end").to_string(),
                span: location_span(last_token.start, last_token.end, source),
                expected: Vec::new(),
            });
        }
        ParolError::ParserError(ParserError::TreeError { source: inner }) => {
            out.push(SyntaxError {
                message: inner.to_string(),
                span: None,
                expected: Vec::new(),
            });
        }
        other => out.push(SyntaxError {
            message: other.to_string(),
            span: None,
            expected: Vec::new(),
        }),
    }
}

pub fn check(source: &str) -> Result<(), String> {
    let parsed = parse(source);
    match parsed.errors.first() {
        None => Ok(()),
        Some(e) => Err(e.message.clone()),
    }
}
