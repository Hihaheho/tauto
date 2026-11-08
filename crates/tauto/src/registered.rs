//! The functions a `syntax` registers with `with fmt f, tokens g`
//! (`docs/design/macro.md`「構文に付ける関数（`with`）」): what lays out a literal's text
//! and what an editor colours it as. They run in the program they are written in, with the
//! limits of a macro, answer no host effect, and read the text as tokens or as the lossless tree.

use crate::surface::{Name, Stmt};
use tauto_message::{Message, msg};

use tauto_syntax::{Cst, Event, Limits, ParseError, Tables, build_cst, parse};

use crate::eval::{Host, call_bound_function};
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
    function: Name,
    reads: Reads,
}

/// The program the registered functions run in, checked.
pub struct Library<'p> {
    program: std::borrow::Cow<'p, Program>,
    report: TypeReport,
    registrations: Vec<(Registration, Bound)>,
    /// The registrations that could not be bound, and why.
    unbound: Vec<(Registration, Message)>,
}

/// The checked executable representation of registered functions that use proof-language types.
pub(crate) fn executable(
    program: &Program,
    registrations: &[Registration],
    standard: &std::collections::HashSet<Name>,
) -> Option<Program> {
    if registrations.is_empty() || standard.is_empty() || !program.errors.is_empty() {
        return None;
    }
    let report = check_program(program).with_prelude_for(program);
    let rows = check_program_rows(program);
    if registrations
        .iter()
        .all(|r| bind(program, &report, &rows, r).is_ok())
    {
        return None;
    }
    let stmts = crate::extract::executable_prefix(&program.stmts, standard).ok()?;
    Some(Program {
        stmts,
        errors: Vec::new(),
    })
}

pub fn validate(program: &Program, registrations: &[Registration]) -> Vec<(Message, Span)> {
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
    let report = report.with_prelude_for(&program);
    let rows = check_program_rows(program);
    let mut errors = Vec::new();
    for r in registrations {
        if let Err(message) = bind(program, &report, &rows, r) {
            errors.push((message.into(), r.span));
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

fn registered_reference<'a>(
    names: impl Iterator<Item = &'a Name>,
    function: &Name,
) -> Option<&'a Name> {
    let mut candidates =
        names.filter(|name| **name == *function || function.spelling() == Some(name.as_str()));
    candidates.next().filter(|_| candidates.next().is_none())
}

fn bind(
    program: &Program,
    report: &TypeReport,
    rows: &RowReport,
    r: &Registration,
) -> Result<Bound, Message> {
    let head = |problem: Message| {
        msg!(
            "tauto-reg",
            syntax = &r.syntax,
            function = r.function.as_str(),
            role = r.role.word(),
            problem = problem
        )
    };
    let reference = registered_reference(
        program
            .stmts
            .iter()
            .filter_map(|statement| match statement {
                Stmt::Fn(function) => Some(&function.name),
                _ => None,
            }),
        &r.function,
    );
    let Some((reference, scheme)) = reference.and_then(|n| report.schemes.get_key_value(n)) else {
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
            if crate::bindings::is_library(n, "List")
                && matches!(args.as_slice(), [Ty::Named(m, _)] if crate::bindings::is_library(m, "SynTok")) =>
        {
            Reads::Tokens
        }
        Ty::Named(n, _) if crate::bindings::is_library(n, "SynCst") => Reads::Tree,
        other => return Err(wrong(msg!("tauto-reg-reads", ty = other.to_string()))),
    };
    if r.role == Role::Fmt && !matches!(params[1].unborrowed(), Ty::Int(crate::types::Width::U64)) {
        return Err(wrong(msg!("tauto-reg-width", ty = params[1].to_string())));
    }
    let made = match (r.role, &**result) {
        (Role::Fmt, Ty::Named(n, args))
            if crate::bindings::is_library(n, "Option")
                && matches!(args.as_slice(), [Ty::Text]) =>
        {
            true
        }
        (Role::Tokens, Ty::Named(n, args))
            if crate::bindings::is_library(n, "List")
                && matches!(args.as_slice(), [Ty::Named(m, _)] if crate::bindings::is_library(m, "SynHighlight")) =>
        {
            true
        }
        _ => false,
    };
    if !made {
        return Err(wrong(msg!("tauto-reg-makes", ty = result.to_string())));
    }
    if let Some((_, row)) = rows.functions.iter().find(|(n, _)| n == reference) {
        for e in row {
            if e.starts_with('?') {
                return Err(head(msg!("tauto-reg-unknown-effect", effect = e.as_str())));
            }
            if crate::host::HOST_EFFECTS.contains(&e.as_str()) {
                return Err(head(msg!("tauto-reg-host-effect", effect = e.as_str())));
            }
            if !["Div", "macro_error"]
                .iter()
                .any(|name| crate::bindings::is_library(e, name))
            {
                return Err(head(msg!("tauto-reg-effect", effect = e.as_str())));
            }
        }
    }
    Ok(Bound {
        function: reference.clone(),
        reads,
    })
}

impl<'p> Library<'p> {
    /// The program checked, with the registrations that are right. `Err` when the program does
    /// not check; a registration that is wrong is left out (`validate` says why).
    pub fn open(program: &'p Program, registrations: &[Registration]) -> Result<Self, Message> {
        Self::open_with(std::borrow::Cow::Borrowed(program), registrations, true)
    }

    /// As [`Library::open`], but a program that does not check is used as far as it goes: a call
    /// of a function that does not check is the call's own error.
    pub fn open_lenient(
        program: &'p Program,
        registrations: &[Registration],
    ) -> Result<Self, Message> {
        Self::open_with(std::borrow::Cow::Borrowed(program), registrations, false)
    }

    /// [`Library::open_lenient`] of a program it keeps.
    pub fn open_lenient_owned(
        program: Program,
        registrations: &[Registration],
    ) -> Result<Library<'static>, Message> {
        Library::open_with(std::borrow::Cow::Owned(program), registrations, false)
    }

    fn open_with(
        program: std::borrow::Cow<'p, Program>,
        registrations: &[Registration],
        strict: bool,
    ) -> Result<Self, Message> {
        if registrations.is_empty() {
            return Ok(Library {
                program,
                report: TypeReport::default(),
                registrations: Vec::new(),
                unbound: Vec::new(),
            });
        }
        let mut program = program;
        tauto_surface::resolve::Resolver::new(crate::bindings::library_bindings())
            .statements(&mut program.to_mut().stmts);
        let report = check_program(&program);
        if strict && let Some(e) = report.errors.first() {
            return Err(Message::text(e.to_string()));
        }
        let report = report.with_prelude_for(&program);
        let rows = check_program_rows(&program);
        let mut bound = Vec::new();
        let mut unbound = Vec::new();
        for r in registrations {
            match bind(&program, &report, &rows, r) {
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
    pub fn unbound(&self, syntax: &str, role: Role) -> Option<&Message> {
        self.unbound
            .iter()
            .find(|(r, _)| r.syntax == syntax && r.role == role)
            .map(|(_, why)| why)
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

    fn call(&self, bound: &Bound, args: &[Node]) -> Result<Node, Message> {
        let limits = Options::default();
        let mut host = Host::new(limits.call_steps, limits.allocations);
        match call_bound_function(
            &self.program,
            &self.report,
            &bound.function,
            args,
            &mut host,
        ) {
            Ok((node, _)) => Ok(node),
            Err(e) => Err(msg!(
                "tauto-reg-call-error",
                function = bound.function.to_string(),
                error = e.to_string()
            )),
        }
    }

    /// The text of a literal laid out by the syntax's `fmt` function for lines of `width`
    /// columns, or `None` when there is no such function or it leaves the text as it is.
    /// The text it makes differs from the one given in white space only, and is a fixed point
    /// of the function.
    pub fn format(
        &self,
        syntax: &str,
        tables: &std::sync::Arc<Tables>,
        text: &str,
        width: u64,
    ) -> Result<Option<String>, Message> {
        let Some(bound) = self.find(syntax, Role::Fmt) else {
            return Ok(None);
        };
        let once = |input: &str| -> Result<Option<String>, Message> {
            let arg = input_node(bound.reads, tables, input)?;
            let made = self.call(bound, &[arg, Node::Int(width as i64)])?;
            match made.as_option() {
                Some(None) => Ok(None),
                Some(Some(t)) => t.as_text().map(|t| Some(t.to_string())).ok_or_else(|| {
                    msg!("tauto-reg-not-text", function = bound.function.to_string())
                }),
                None => Err(msg!(
                    "tauto-reg-not-option",
                    function = bound.function.to_string()
                )),
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
            Some(again) if again != laid => Err(msg!(
                "tauto-reg-not-idempotent",
                function = bound.function.to_string()
            )),
            _ => Ok(Some(laid)),
        }
    }

    /// What the syntax's `tokens` function says of a literal's text, or `None` when there is
    /// no such function.
    pub fn highlight(
        &self,
        syntax: &str,
        tables: &std::sync::Arc<Tables>,
        text: &str,
    ) -> Result<Option<Vec<Highlight>>, Message> {
        let Some(bound) = self.find(syntax, Role::Tokens) else {
            return Ok(None);
        };
        let arg = input_node(bound.reads, tables, text)?;
        let made = self.call(bound, &[arg])?;
        let items = made.as_list().ok_or_else(|| {
            msg!("tauto-reg-not-list", function = bound.function.to_string()).to_string()
        })?;
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
                return Err(msg!(
                    "tauto-reg-malformed",
                    function = bound.function.to_string()
                ));
            };
            let Some(kind) = HIGHLIGHT_KINDS.iter().find(|k| **k == kind) else {
                return Err(msg!(
                    "tauto-reg-colour",
                    function = bound.function.to_string(),
                    kind = kind
                ));
            };
            if start > end || end as usize > text.len() {
                return Err(msg!(
                    "tauto-reg-range",
                    function = bound.function.to_string(),
                    start = start,
                    end = end
                ));
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

fn input_node(reads: Reads, tables: &Tables, text: &str) -> Result<Node, Message> {
    let token = |t: &tauto_syntax::Token| {
        Node::Ctor(
            "SynTok".into(),
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
                .map_err(|e| msg!("tauto-reg-not-token", byte = e.at))?;
            Ok(Node::List(tokens.iter().map(token).collect()))
        }
        Reads::Tree => {
            let events = match parse(tables, text, 0, &Limits::default()) {
                Ok(e) => e,
                Err(ParseError::Lex(l)) => {
                    return Err(msg!("tauto-reg-not-token", byte = l.at));
                }
                Err(ParseError::Syntax(s)) => {
                    return Err(msg!(
                        "tauto-reg-not-syntax",
                        byte = s.at.map_or(text.len() as u32, |t| t.start)
                    ));
                }
                Err(ParseError::Limit(m)) => return Err(Message::text(m.to_string())),
            };
            let cst = build_cst(tables, &events).map_err(|e| Message::text(e.0.to_string()))?;
            tree(tables, &cst, &token, 0)
        }
    }
}

fn tree(
    tables: &Tables,
    cst: &Cst,
    token: &dyn Fn(&tauto_syntax::Token) -> Node,
    depth: usize,
) -> Result<Node, Message> {
    if depth > DEPTH {
        return Err(msg!("tauto-reg-too-deep"));
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
fn solid(tables: &Tables, text: &str) -> Result<Vec<(u32, String)>, Message> {
    let tokens = tauto_syntax::tokens(tables, text, 0)
        .map_err(|e| msg!("tauto-reg-laid-not-token", byte = e.at))?;
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
fn same_but_white_space(tables: &Tables, text: &str, laid: &str) -> Result<(), Message> {
    let events = parse(tables, laid, 0, &Limits::default());
    if !matches!(events, Ok(ref e) if e.iter().any(|ev| matches!(ev, Event::Open { .. }))) {
        return Err(msg!("tauto-reg-laid-not-syntax"));
    }
    if solid(tables, text)? != solid(tables, laid)? {
        return Err(msg!("tauto-reg-laid-changes"));
    }
    Ok(())
}

#[cfg(test)]
mod identity_tests {
    use super::*;

    #[test]
    fn bound_registration_does_not_select_a_same_spelled_function() {
        let registered: Name = crate::identity::DeclRef::fresh("format").into();
        let other: Name = crate::identity::DeclRef::fresh("format").into();
        assert!(registered_reference([&other].into_iter(), &registered).is_none());
        assert_eq!(
            registered_reference([&other, &registered].into_iter(), &registered),
            Some(&registered)
        );
        assert!(
            registered_reference([&other, &registered].into_iter(), &Name::from("format"))
                .is_none()
        );
    }
}
