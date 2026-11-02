//! The functions a `syntax` registers with `with fmt f, tokens g`
//! (`docs/design/macro.md`「構文に付ける関数（`with`）」): what lays out a literal's text
//! and what an editor colours it as. They run in the program they are written in, with the
//! limits of a macro, answer no host effect, and read the text as tokens or as the lossless tree.

use std::rc::Rc;
use tauto_message::{Message, msg};

use tauto_syntax::{Cst, Event, Limits, ParseError, Tables, build_cst, parse};

use crate::eval::{Host, call_function};
use crate::macros::{Node, Options};
use crate::rows::{RowReport, check_program_rows};
use crate::surface::Program;
use crate::syntax::{Registration, Role};
use crate::types::{Ty, TypeReport, check_program};
use tauto_parol::Span;

/// The colours an editor's legend lists, in order: what a `SynHighlight` names one of.
pub const HIGHLIGHT_KINDS: [&str; 23] = [
    "keyword",
    "number",
    "string",
    "variable",
    "comment",
    "operator",
    "type",
    "function",
    "parameter",
    "property",
    "namespace",
    "enumMember",
    "macro",
    "regexp",
    "struct",
    "enum",
    "class",
    "interface",
    "typeParameter",
    "method",
    "event",
    "decorator",
    "modifier",
];

/// How deep a tree may be before it is not handed to a function.
const DEPTH: usize = 2_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reads {
    /// `List(SynTok)`: the scanner's tokens, skipped ones included. Needs no parse, so it works
    /// on text that is not finished.
    Tokens,
    /// `SynCst`: the lossless tree. Needs a parse.
    Tree,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Highlight {
    pub start: u32,
    pub end: u32,
    pub kind: &'static str,
}

/// A registered function that has been found and whose type has been read.
#[derive(Debug, Clone)]
struct Bound {
    function: String,
    reads: Reads,
}

/// The program the registered functions run in, checked.
pub struct Library<'p> {
    program: std::borrow::Cow<'p, Program>,
    report: TypeReport,
    registrations: Vec<(Registration, Bound)>,
    /// The registrations that could not be bound, and why.
    unbound: Vec<(Registration, String)>,
}

pub fn validate(program: &Program, registrations: &[Registration]) -> Vec<(String, Span)> {
    if registrations.is_empty() {
        return Vec::new();
    }
    if !program.errors.is_empty() {
        // The program's own errors come first; the functions are looked at when it is right.
        return Vec::new();
    }
    let report = check_program(program);
    if !report.errors.is_empty() {
        return Vec::new();
    }
    let report = report.with_prelude();
    let rows = check_program_rows(program);
    let mut errors = Vec::new();
    for r in registrations {
        if let Err(message) = bind(&report, &rows, r) {
            errors.push((message, r.span));
        }
    }
    errors
}

/// The type a registered function must have, for the message.
fn wanted(role: Role) -> &'static str {
    match role {
        Role::Fmt => "(List(SynTok) | SynCst, u64) -> Option(Text)",
        Role::Tokens => "(List(SynTok) | SynCst) -> List(SynHighlight)",
    }
}

fn bind(report: &TypeReport, rows: &RowReport, r: &Registration) -> Result<Bound, String> {
    let head = |problem: Message| {
        msg!(
            "tauto-reg",
            syntax = &r.syntax,
            function = &r.function,
            role = r.role.word(),
            problem = problem
        )
        .to_string()
    };
    let Some(scheme) = report.schemes.get(&r.function) else {
        return Err(head(msg!("tauto-reg-not-defined")));
    };
    let Ty::Fn(params, result, _) = &scheme.ty else {
        return Err(head(msg!("tauto-reg-not-function")));
    };
    let arity = match r.role {
        Role::Fmt => 2,
        Role::Tokens => 1,
    };
    let wrong = |what: Message| {
        head(msg!(
            "tauto-reg-wrong",
            what = what,
            wanted = wanted(r.role)
        ))
    };
    if params.len() != arity {
        return Err(wrong(msg!("tauto-reg-arity", count = params.len())));
    }
    let reads = match params[0].unborrowed() {
        Ty::Named(n, args)
            if n == "List" && matches!(args.as_slice(), [Ty::Named(m, _)] if m == "SynTok") =>
        {
            Reads::Tokens
        }
        Ty::Named(n, _) if n == "SynCst" => Reads::Tree,
        other => return Err(wrong(msg!("tauto-reg-reads", ty = other.to_string()))),
    };
    if r.role == Role::Fmt && params[1].unborrowed().to_string() != "u64" {
        return Err(wrong(msg!("tauto-reg-width", ty = params[1].to_string())));
    }
    let made = match (r.role, &**result) {
        (Role::Fmt, Ty::Named(n, args))
            if n == "Option" && matches!(args.as_slice(), [Ty::Text]) =>
        {
            true
        }
        (Role::Tokens, Ty::Named(n, args))
            if n == "List"
                && matches!(args.as_slice(), [Ty::Named(m, _)] if m == "SynHighlight") =>
        {
            true
        }
        _ => false,
    };
    if !made {
        return Err(wrong(msg!("tauto-reg-makes", ty = result.to_string())));
    }
    if let Some((_, row)) = rows.functions.iter().find(|(n, _)| *n == r.function) {
        for e in row {
            if e.starts_with('?') {
                return Err(head(msg!("tauto-reg-unknown-effect", effect = e.as_str())));
            }
            if crate::host::HOST_EFFECTS.contains(&e.as_str()) {
                return Err(head(msg!("tauto-reg-host-effect", effect = e.as_str())));
            }
            if !matches!(e.as_str(), "Div" | "macro_error") {
                return Err(head(msg!("tauto-reg-effect", effect = e.as_str())));
            }
        }
    }
    Ok(Bound {
        function: r.function.clone(),
        reads,
    })
}

impl<'p> Library<'p> {
    /// The program checked, with the registrations that are right. `Err` when the program does
    /// not check; a registration that is wrong is left out (`validate` says why).
    pub fn open(program: &'p Program, registrations: &[Registration]) -> Result<Self, String> {
        Self::open_with(std::borrow::Cow::Borrowed(program), registrations, true)
    }

    /// As [`Library::open`], but a program that does not check is used as far as it goes: a call
    /// of a function that does not check is the call's own error.
    pub fn open_lenient(
        program: &'p Program,
        registrations: &[Registration],
    ) -> Result<Self, String> {
        Self::open_with(std::borrow::Cow::Borrowed(program), registrations, false)
    }

    /// [`Library::open_lenient`] of a program it keeps.
    pub fn open_lenient_owned(
        program: Program,
        registrations: &[Registration],
    ) -> Result<Library<'static>, String> {
        Library::open_with(std::borrow::Cow::Owned(program), registrations, false)
    }

    fn open_with(
        program: std::borrow::Cow<'p, Program>,
        registrations: &[Registration],
        strict: bool,
    ) -> Result<Self, String> {
        if registrations.is_empty() {
            return Ok(Library {
                program,
                report: TypeReport::default(),
                registrations: Vec::new(),
                unbound: Vec::new(),
            });
        }
        let report = check_program(&program);
        if strict && let Some(e) = report.errors.first() {
            return Err(e.to_string());
        }
        let report = report.with_prelude();
        let rows = check_program_rows(&program);
        let mut bound = Vec::new();
        let mut unbound = Vec::new();
        for r in registrations {
            match bind(&report, &rows, r) {
                Ok(b) => bound.push((r.clone(), b)),
                Err(why) => unbound.push((r.clone(), why)),
            }
        }
        Ok(Library {
            program,
            report,
            registrations: bound,
            unbound,
        })
    }

    /// Why the function registered for `role` of `syntax` cannot be used, when it cannot.
    pub fn unbound(&self, syntax: &str, role: Role) -> Option<&str> {
        self.unbound
            .iter()
            .find(|(r, _)| r.syntax == syntax && r.role == role)
            .map(|(_, why)| why.as_str())
    }

    pub fn has(&self, syntax: &str, role: Role) -> bool {
        self.find(syntax, role).is_some()
    }

    fn find(&self, syntax: &str, role: Role) -> Option<&Bound> {
        self.registrations
            .iter()
            .find(|(r, _)| r.syntax == syntax && r.role == role)
            .map(|(_, b)| b)
    }

    fn call(&self, bound: &Bound, args: &[Node]) -> Result<Node, String> {
        let limits = Options::default();
        let mut host = Host::new(limits.call_steps, limits.allocations);
        match call_function(
            &self.program,
            &self.report,
            &bound.function,
            args,
            &mut host,
        ) {
            Ok((node, _)) => Ok(node),
            Err(e) => Err(msg!(
                "tauto-reg-call-error",
                function = &bound.function,
                error = e.to_string()
            )
            .to_string()),
        }
    }

    /// The text of a literal laid out by the syntax's `fmt` function for lines of `width`
    /// columns, or `None` when there is no such function or it leaves the text as it is.
    /// The text it makes differs from the one given in white space only, and is a fixed point
    /// of the function.
    pub fn format(
        &self,
        syntax: &str,
        tables: &Rc<Tables>,
        text: &str,
        width: u64,
    ) -> Result<Option<String>, String> {
        let Some(bound) = self.find(syntax, Role::Fmt) else {
            return Ok(None);
        };
        let once = |input: &str| -> Result<Option<String>, String> {
            let arg = input_node(bound.reads, tables, input)?;
            let made = self.call(bound, &[arg, Node::Int(width as i64)])?;
            match made.as_option() {
                Some(None) => Ok(None),
                Some(Some(t)) => t.as_text().map(|t| Some(t.to_string())).ok_or_else(|| {
                    msg!("tauto-reg-not-text", function = &bound.function).to_string()
                }),
                None => Err(msg!("tauto-reg-not-option", function = &bound.function).to_string()),
            }
        };
        let Some(laid) = once(text)? else {
            return Ok(None);
        };
        if laid == text {
            return Ok(None);
        }
        same_but_white_space(tables, text, &laid)?;
        match once(&laid)? {
            Some(again) if again != laid => {
                Err(msg!("tauto-reg-not-idempotent", function = &bound.function).to_string())
            }
            _ => Ok(Some(laid)),
        }
    }

    /// What the syntax's `tokens` function says of a literal's text, or `None` when there is
    /// no such function.
    pub fn highlight(
        &self,
        syntax: &str,
        tables: &Rc<Tables>,
        text: &str,
    ) -> Result<Option<Vec<Highlight>>, String> {
        let Some(bound) = self.find(syntax, Role::Tokens) else {
            return Ok(None);
        };
        let arg = input_node(bound.reads, tables, text)?;
        let made = self.call(bound, &[arg])?;
        let items = made
            .as_list()
            .ok_or_else(|| msg!("tauto-reg-not-list", function = &bound.function).to_string())?;
        let mut out = Vec::new();
        for item in items {
            let int = |name: &str| {
                item.named(name)
                    .and_then(Node::as_int)
                    .and_then(|n| u32::try_from(n).ok())
            };
            let (Some(start), Some(end), Some(kind)) = (
                int("start"),
                int("end"),
                item.named("kind").and_then(Node::as_text),
            ) else {
                return Err(msg!("tauto-reg-malformed", function = &bound.function).to_string());
            };
            let Some(kind) = HIGHLIGHT_KINDS.iter().find(|k| **k == kind) else {
                return Err(
                    msg!("tauto-reg-colour", function = &bound.function, kind = kind).to_string(),
                );
            };
            if start > end || end as usize > text.len() {
                return Err(msg!(
                    "tauto-reg-range",
                    function = &bound.function,
                    start = start,
                    end = end
                )
                .to_string());
            }
            out.push(Highlight {
                start,
                end,
                kind: kind,
            });
        }
        Ok(Some(out))
    }
}

fn input_node(reads: Reads, tables: &Tables, text: &str) -> Result<Node, String> {
    let token = |t: &tauto_syntax::Token| {
        Node::Ctor(
            "SynTok".to_string(),
            vec![
                (None, Node::text(&tables.terminals()[t.terminal as usize])),
                (None, Node::text(&text[t.start as usize..t.end as usize])),
                (None, Node::Int(i64::from(t.start))),
                (None, Node::Int(i64::from(t.end))),
                (None, Node::Bool(tables.is_skipped(t.terminal))),
            ],
        )
    };
    match reads {
        Reads::Tokens => {
            let tokens = tauto_syntax::tokens(tables, text, 0)
                .map_err(|e| msg!("tauto-reg-not-token", byte = e.at).to_string())?;
            Ok(Node::List(tokens.iter().map(token).collect()))
        }
        Reads::Tree => {
            let events = match parse(tables, text, 0, &Limits::default()) {
                Ok(e) => e,
                Err(ParseError::Lex(l)) => {
                    return Err(msg!("tauto-reg-not-token", byte = l.at).to_string());
                }
                Err(ParseError::Syntax(s)) => {
                    return Err(msg!(
                        "tauto-reg-not-syntax",
                        byte = s.at.map_or(text.len() as u32, |t| t.start)
                    )
                    .to_string());
                }
                Err(ParseError::Limit(m)) => return Err(m.to_string()),
            };
            let cst = build_cst(tables, &events).map_err(|e| e.0.to_string())?;
            tree(tables, &cst, &token, 0)
        }
    }
}

fn tree(
    tables: &Tables,
    cst: &Cst,
    token: &dyn Fn(&tauto_syntax::Token) -> Node,
    depth: usize,
) -> Result<Node, String> {
    if depth > DEPTH {
        return Err(msg!("tauto-reg-too-deep").to_string());
    }
    Ok(match cst {
        Cst::Token(t) => Node::ctor("SynCst::CstTok", vec![token(t)]),
        Cst::Node {
            non_terminal,
            children,
            start,
            end,
        } => {
            let children = children
                .iter()
                .map(|c| tree(tables, c, token, depth + 1))
                .collect::<Result<Vec<_>, _>>()?;
            Node::ctor(
                "SynCst::CstNode",
                vec![
                    Node::text(&tables.non_terminals()[*non_terminal as usize]),
                    Node::List(children),
                    Node::Int(i64::from(*start)),
                    Node::Int(i64::from(*end)),
                ],
            )
        }
    })
}

/// The tokens of a text that are not white space, with their terminals.
fn solid(tables: &Tables, text: &str) -> Result<Vec<(u32, String)>, String> {
    let tokens = tauto_syntax::tokens(tables, text, 0)
        .map_err(|e| msg!("tauto-reg-laid-not-token", byte = e.at).to_string())?;
    Ok(tokens
        .iter()
        .map(|t| {
            (
                t.terminal,
                text[t.start as usize..t.end as usize].to_string(),
            )
        })
        .filter(|(_, s)| !s.trim().is_empty())
        .collect())
}

/// Checks that `laid` is the text of the syntax `text` is, with only white space moved.
fn same_but_white_space(tables: &Tables, text: &str, laid: &str) -> Result<(), String> {
    let events = parse(tables, laid, 0, &Limits::default());
    if !matches!(events, Ok(ref e) if e.iter().any(|ev| matches!(ev, Event::Open { .. }))) {
        return Err(msg!("tauto-reg-laid-not-syntax").to_string());
    }
    if solid(tables, text)? != solid(tables, laid)? {
        return Err(msg!("tauto-reg-laid-changes").to_string());
    }
    Ok(())
}
