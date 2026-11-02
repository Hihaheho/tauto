//! `tauto fmt`: lays a file out again without changing a single token, except that an ASCII
//! escape (`\times`, `\forall`, …) is written as its sign (`×`, `∀`, …). The members of a
//! product are in the order they are written, which is part of the type, so they are left as they are.
//!
//! A line is a run of tokens up to a newline that ends a statement (one
//! outside `( )` and `[ ]`). It is indented two spaces for each enclosing
//! `{`, and its tokens are spaced one way: a space after `,`, none inside
//! brackets, otherwise one space wherever the source had whitespace. A line
//! longer than [`WIDTH`] is broken at its outermost bracket that does not
//! fit (a `{ }` closed on the line, such as a record literal, counts), one argument per line, and so on inward. A line that holds a comment
//! inside brackets, or a block whose newlines matter inside brackets, is left
//! as written. The tokens are those of the syntax tree of the source (`tauto_parol::parse`), so a source that does not
//! parse is not laid out. The tokens of the result are checked against the source's.

use tauto_message::msg;
use tauto_parol::{Cst, NodeId, NodeKind, NonTerminalKind, Span, SyntaxError, TerminalKind};

pub const WIDTH: usize = 100;

#[derive(Debug, Clone, PartialEq)]
enum Kind {
    Open,
    Close,
    Comma,
    Comment,
    Other,
}

#[derive(Debug, Clone)]
struct Token {
    text: String,
    kind: Kind,
    /// The terminal of the syntax tree it was read from (a token cut in two, such as `#(`, gives
    /// both halves the terminal of its brackets or of the whole).
    term: TerminalKind,
    spaced: bool,
    newlines: usize,
    start: usize,
    end: usize,
    /// It is an ASCII escape (`\times`), whose text here is the sign.
    escaped: bool,
}

/// The ASCII escapes of signs, `\times` for `×`, and the sign each stands for.
const ESCAPES: [(&str, &str); 13] = [
    ("times", "×"),
    ("land", "∧"),
    ("lor", "∨"),
    ("iff", "↔"),
    ("neg", "¬"),
    ("vdash", "⊢"),
    ("omega", "ω"),
    ("forall", "∀"),
    ("exists", "∃"),
    ("cup", "∪"),
    ("llbracket", "⟦"),
    ("rrbracket", "⟧"),
    ("square", "□"),
];

/// The terminals of the syntax tree in the order they are written, comments among them. A
/// syntax literal (name, opening, pieces and closing) is one, kept as written; the line breaks
/// and white space between the others are left out, for the gaps between the rest tell them.
fn leaves(cst: &Cst) -> Vec<(TerminalKind, Span)> {
    let mut out = Vec::new();
    let mut stack: Vec<(NodeId, Option<Span>)> =
        cst.root().into_iter().map(|r| (r, None)).collect();
    while let Some((id, literal)) = stack.pop() {
        match cst.kind(id) {
            NodeKind::Terminal(kind) => {
                let span = cst.span(id);
                let within = literal.is_some_and(|l| l.start <= span.start && span.end <= l.end);
                if !within
                    && !matches!(
                        kind,
                        TerminalKind::Nl | TerminalKind::NewLine | TerminalKind::Whitespace
                    )
                {
                    out.push((kind, span));
                }
            }
            NodeKind::NonTerminal(kind) => {
                let mut literal = literal;
                if kind == NonTerminalKind::SyntaxLit && literal.is_none() {
                    let span = cst.span(id);
                    out.push((TerminalKind::MacroText, span));
                    literal = Some(span);
                }
                stack.extend(cst.node(id).children.iter().rev().map(|&c| (c, literal)));
            }
        }
    }
    out.sort_by_key(|(_, span)| span.start);
    out
}

fn kind_of(term: TerminalKind) -> Kind {
    match term {
        TerminalKind::LParen | TerminalKind::LBracket | TerminalKind::LBrace => Kind::Open,
        TerminalKind::RParen | TerminalKind::RBracket | TerminalKind::RBrace => Kind::Close,
        TerminalKind::Comma => Kind::Comma,
        TerminalKind::LineComment | TerminalKind::BlockComment | TerminalKind::Comment => {
            Kind::Comment
        }
        _ => Kind::Other,
    }
}

/// The tokens of `source`, read from its syntax tree. A tuple or record opening (`#(`, `#{`) is
/// the `#` and its bracket, and a macro's name (`m!`) is the name and the `!`, as the layout
/// treats them apart. When the source does not parse, the tokens read up to the error, and the
/// error.
fn lex(source: &str) -> Result<Vec<Token>, String> {
    let parsed = tauto_parol::parse(source);
    let mut out: Vec<Token> = Vec::new();
    let mut prev_end = 0usize;
    for (term, span) in leaves(&parsed.cst) {
        let (start, end) = (span.start as usize, span.end as usize);
        let gap = source.get(prev_end..start).unwrap_or_default();
        let (mut spaced, mut newlines) = (!gap.is_empty(), gap.matches('\n').count());
        let text = &source[start..end];
        let escape = text
            .strip_prefix('\\')
            .and_then(|name| ESCAPES.iter().find(|(n, _)| *n == name));
        let pieces: Vec<(&str, TerminalKind, usize)> = match text {
            "#(" => vec![("#", term, start + 1), ("(", TerminalKind::LParen, end)],
            "#{" => vec![("#", term, start + 1), ("{", TerminalKind::LBrace, end)],
            _ if term == TerminalKind::MacroName => {
                let name = text.len() - 1;
                vec![(&text[..name], term, start + name), ("!", term, end)]
            }
            _ => vec![(text, term, end)],
        };
        let mut at = start;
        for (piece, term, to) in pieces {
            out.push(Token {
                escaped: escape.is_some(),
                text: escape.map_or(piece, |e| e.1).to_string(),
                kind: kind_of(term),
                term,
                spaced,
                newlines,
                start: at,
                end: to,
            });
            (spaced, newlines, at) = (false, 0, to);
        }
        prev_end = end;
    }
    // A raw name that is not needed is written without its `r#`: one whose word is not reserved.
    // A reserved word is a name only with `r#`, wherever it stands.
    for t in out.iter_mut() {
        let Some(name) = t.text.strip_prefix("r#") else {
            continue;
        };
        if !tauto_surface::surface::print::RESERVED.contains(&name) {
            t.text = name.to_string();
        }
    }
    match parsed.errors.first() {
        Some(error) => Err(failure(source, &out, error)),
        None => Ok(out),
    }
}

/// Why the source does not parse: an unclosed comment or string where the tree stops, a bracket
/// that closes nothing or is the wrong one, a bracket left open at the end, or else the error
/// of the parser.
fn failure(source: &str, tokens: &[Token], error: &SyntaxError) -> String {
    let at = error.span.map_or(source.len(), |s| s.start as usize);
    let rest = source.get(at..).unwrap_or_default();
    if rest.starts_with("/*") {
        return msg!("tauto-fmt-unclosed-comment").to_string();
    }
    if rest.starts_with(['"', '\'']) || rest.starts_with("plaintext`") {
        return msg!("tauto-fmt-unclosed-string").to_string();
    }
    let mut seen = tokens.to_vec();
    if let Some(closer) = rest.chars().next().filter(|c| matches!(c, ')' | ']' | '}')) {
        seen.push(Token {
            text: closer.to_string(),
            kind: Kind::Close,
            term: TerminalKind::RParen,
            spaced: false,
            newlines: 0,
            start: at,
            end: at + 1,
            escaped: false,
        });
    }
    if (rest.trim().is_empty() || seen.len() > tokens.len())
        && let Err(why) = balanced(&seen)
    {
        return why;
    }
    error.message.clone()
}

/// A line, as a tree: tokens and bracketed groups of comma-separated items.
/// The most brackets open at once that `format` takes.
const MAX_BRACKETS: usize = 1_000;

/// Every bracket closes, and with its own kind; the rest of `format` relies on it.
fn balanced(tokens: &[Token]) -> Result<(), String> {
    let mut stack: Vec<&str> = Vec::new();
    for t in tokens {
        match t.kind {
            Kind::Open if stack.len() >= MAX_BRACKETS => {
                return Err(msg!("tauto-fmt-too-deep").to_string());
            }
            Kind::Open => stack.push(&t.text),
            Kind::Close => {
                let pair = match stack.pop() {
                    Some("(") => ")",
                    Some("[") => "]",
                    Some(_) => "}",
                    None => return Err(msg!("tauto-fmt-unmatched", token = &t.text).to_string()),
                };
                if t.text != pair {
                    return Err(msg!("tauto-fmt-unmatched", token = &t.text).to_string());
                }
            }
            _ => {}
        }
    }
    match stack.last() {
        Some(open) => Err(msg!("tauto-fmt-unclosed", token = *open).to_string()),
        None => Ok(()),
    }
}

#[derive(Debug)]
enum Node {
    Tok(Token),
    Group {
        open: Token,
        items: Vec<Vec<Node>>,
        close: Token,
    },
}

/// Commas split a group's items only outside braces that stay open past the line; a line's own
/// commas (`<A, B>`) are plain tokens. A `{ }` closed on the line is a group, and so is any `{ }`
/// inside a group: there it closes on the line too, so a nested record literal can break in the
/// same pass as its parent rather than only once its parent's break gives it a line of its own.
/// An effect row (`! {Div, stdout}`) is never a group: a newline inside it does not parse.
fn tree(tokens: &[Token], i: &mut usize, in_group: bool) -> Vec<Node> {
    let mut out = Vec::new();
    let mut braces = 0usize;
    while *i < tokens.len() {
        let t = &tokens[*i];
        match t.kind {
            Kind::Close if t.text != "}" => return out,
            Kind::Close if in_group && braces == 0 => return out,
            Kind::Comma if in_group && braces == 0 => return out,
            Kind::Open
                if t.text != "{"
                    || (!after_bang(&out) && (in_group || closes_on_line(tokens, *i))) =>
            {
                let open = t.clone();
                *i += 1;
                let mut items = Vec::new();
                loop {
                    items.push(tree(tokens, i, true));
                    match tokens.get(*i) {
                        Some(t) if t.kind == Kind::Comma => *i += 1,
                        _ => break,
                    }
                }
                let close = tokens[*i].clone();
                *i += 1;
                if items.len() == 1 && items[0].is_empty() {
                    items.clear();
                }
                out.push(Node::Group { open, items, close });
            }
            _ => {
                if t.text == "{" {
                    braces += 1;
                } else if t.text == "}" {
                    braces = braces.saturating_sub(1);
                }
                out.push(Node::Tok(t.clone()));
                *i += 1;
            }
        }
    }
    out
}

/// Whether the last node is a `!`, so that a `{` after it opens an effect row.
fn after_bang(nodes: &[Node]) -> bool {
    matches!(nodes.last(), Some(Node::Tok(t)) if t.text == "!")
}

/// Whether the `{` at `i` closes on the same line, as a record literal does: then, outside other
/// brackets (where a newline would not end a field), it is a group
/// like `( )`, broken at its commas, and not a block.
fn closes_on_line(tokens: &[Token], i: usize) -> bool {
    let mut depth = 0usize;
    for t in &tokens[i..] {
        match t.kind {
            Kind::Open => depth += 1,
            Kind::Close => {
                depth -= 1;
                if depth == 0 {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn gap(prev: Option<&str>, t: &Token) -> &'static str {
    match prev {
        None => "",
        Some("(" | "[") => "",
        Some(",") => " ",
        _ if matches!(t.text.as_str(), ")" | "]" | ",") => "",
        // A macro's `!` is joined to its argument list: `m! (x)` is laid out as `m!(x)`.
        Some("!") if t.text == "(" => "",
        _ if t.spaced => " ",
        _ => "",
    }
}

fn flat(nodes: &[Node], prev: &mut Option<String>, out: &mut String) {
    for n in nodes {
        match n {
            Node::Tok(t) => push(t, prev, out),
            Node::Group { open, items, close } => {
                push(open, prev, out);
                for (k, item) in items.iter().enumerate() {
                    if k > 0 {
                        out.push(',');
                        *prev = Some(",".into());
                    }
                    flat(item, prev, out);
                }
                push(close, prev, out);
            }
        }
    }
}

fn push(t: &Token, prev: &mut Option<String>, out: &mut String) {
    out.push_str(gap(prev.as_deref(), t));
    out.push_str(&t.text);
    *prev = Some(t.text.clone());
}

fn flat_text(nodes: &[Node]) -> String {
    let mut s = String::new();
    flat(nodes, &mut None, &mut s);
    s
}

fn width(s: &str) -> usize {
    s.chars().count()
}

/// The width of what follows a group on the same line, as far as the group must fit. Up to a
/// `=>`, all of it, with `tail`. After a `=>` the rest can break on its own, so only through
/// the next group's opening bracket: `Cons(y, ys) => f(…)` breaks inside `f(`, keeping the
/// pattern whole, and `(z: Nat) => g(…)` likewise keeps the parameter whole.
fn unbroken_width(nodes: &[Node], tail: usize) -> usize {
    let mut prev: Option<String> = None;
    let mut s = String::new();
    let mut arrow = false;
    for n in nodes {
        match n {
            Node::Group { open, items, .. } if arrow && !items.is_empty() => {
                push(open, &mut prev, &mut s);
                return width(&s);
            }
            Node::Tok(t) if t.term == TerminalKind::FatArrow => {
                arrow = true;
            }
            _ => {}
        }
        flat(std::slice::from_ref(n), &mut prev, &mut s);
    }
    width(&s) + tail
}

/// The width of `nodes` with `tail` after them, if the first group among them that can break does:
/// up to its opening bracket.
fn least_width(nodes: &[Node], tail: usize) -> usize {
    match nodes
        .iter()
        .position(|n| matches!(n, Node::Group { items, .. } if !items.is_empty()))
    {
        Some(g) => {
            let Node::Group { open, .. } = &nodes[g] else {
                unreachable!()
            };
            let mut s = String::new();
            let mut prev = None;
            flat(&nodes[..g], &mut prev, &mut s);
            push(open, &mut prev, &mut s);
            width(&s)
        }
        None => width(&flat_text(nodes)) + tail,
    }
}

fn arrow_follows(nodes: &[Node]) -> bool {
    nodes
        .iter()
        .any(|n| matches!(n, Node::Tok(t) if t.term == TerminalKind::FatArrow))
}

/// Lays out `nodes` starting at column `col` of a line indented `indent`,
/// breaking the groups that do not fit. `tail` is the width of what follows
/// on the same line. On an attribute line (`@m!(…) => inductive R`) the `=>` names what the
/// attribute is on, not a pattern's body, so the call before it may break.
fn layout(nodes: &[Node], indent: usize, tail: usize, out: &mut String) {
    let attribute = matches!(nodes.first(), Some(Node::Tok(t)) if t.text == "@");
    let mut prev: Option<String> = None;
    for (k, n) in nodes.iter().enumerate() {
        let col = out.rsplit('\n').next().map_or(0, width);
        let rest = unbroken_width(&nodes[k + 1..], tail);
        match n {
            Node::Tok(t) => push(t, &mut prev, out),
            Node::Group { open, items, close } => {
                let mut here = String::new();
                let mut p = prev.clone();
                flat(std::slice::from_ref(n), &mut p, &mut here);
                // A `{ }` breaks last: only if it does not fit with what follows broken.
                let rest = if open.text == "{" {
                    least_width(&nodes[k + 1..], tail)
                } else {
                    rest
                };
                // A group before a `=>` (an arm's pattern, a parameter) stays on one line.
                if col + width(&here) + rest <= WIDTH
                    || items.is_empty()
                    || (!attribute && arrow_follows(&nodes[k + 1..]))
                {
                    out.push_str(&here);
                    prev = p;
                    continue;
                }
                push(open, &mut prev, out);
                let inner = indent + 2;
                for (j, item) in items.iter().enumerate() {
                    out.push('\n');
                    out.push_str(&" ".repeat(inner));
                    let comma = usize::from(j + 1 < items.len());
                    layout(item, inner, comma, out);
                    if comma == 1 {
                        out.push(',');
                    }
                }
                out.push('\n');
                out.push_str(&" ".repeat(indent));
                out.push_str(&close.text);
                prev = Some(close.text.clone());
            }
        }
    }
}

pub fn escapes(source: &str) -> Vec<(usize, usize)> {
    lex(source)
        .unwrap_or_default()
        .iter()
        .filter(|t| t.escaped)
        .map(|t| (t.start, t.end))
        .collect()
}

/// Lays out the source, returning an error for lexing failures, unmatched
/// brackets detected during layout, or changes to the token sequence.
///
/// # Panics
///
/// An unclosed parenthesis or square bracket can exhaust the tokens while
/// constructing a group, before the final bracket check.
pub fn format(source: &str) -> Result<String, String> {
    let tokens = lex(source)?;
    balanced(&tokens)?;
    let mut out = String::new();
    let mut stack: Vec<String> = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        // A line: up to a newline where only braces are open.
        let start = i;
        let depth = stack.iter().filter(|o| *o == "{").count();
        let mut verbatim = false;
        let mut j = i;
        loop {
            let t = &tokens[j];
            if t.kind == Kind::Open {
                stack.push(t.text.clone());
            } else if t.kind == Kind::Close && stack.pop().is_none() {
                return Err(msg!("tauto-fmt-unmatched", token = &t.text).to_string());
            }
            if t.kind == Kind::Comment && stack.iter().any(|o| o != "{") {
                verbatim = true;
            }
            j += 1;
            match tokens.get(j) {
                None => break,
                Some(next) if next.newlines > 0 => {
                    let only_braces = stack.iter().all(|o| o == "{");
                    if only_braces {
                        if !continues_list(&tokens[start..j], next) {
                            break;
                        }
                        // A list of what a declaration makes is kept as it was broken.
                        verbatim = true;
                        continue;
                    }
                    if stack.last().is_some_and(|o| o == "{") {
                        verbatim = true;
                    }
                }
                _ => {}
            }
        }
        let line = &tokens[start..j];
        if start > 0 {
            out.push_str(if line[0].newlines > 1 { "\n\n" } else { "\n" });
        }
        let indent = 2 * (depth - usize::from(line[0].text == "}").min(depth));
        if verbatim {
            write_verbatim(source, line, indent, &mut out);
        } else {
            out.push_str(&" ".repeat(indent));
            let mut k = 0;
            let nodes = tree(line, &mut k, false);
            if k != line.len() {
                return Err(msg!("tauto-fmt-unmatched", token = &line[k].text).to_string());
            }
            layout(&nodes, indent, 0, &mut out);
        }
        i = j;
    }
    if !stack.is_empty() {
        return Err(msg!("tauto-fmt-unclosed-bracket").to_string());
    }
    out.push('\n');
    let same = |a: &[Token], b: &[Token]| {
        let raw = |t: &str| t.strip_prefix("r#").unwrap_or(t).to_string();
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| raw(&x.text) == raw(&y.text))
    };
    if !same(&tokens, &lex(&out)?) {
        return Err(msg!("tauto-fmt-changes-tokens").to_string());
    }
    Ok(out)
}

/// Whether a list of what a declaration makes (`=> fn a, theorem b`) goes on at `next`, on a new
/// line: after its `=>` or after one of its commas.
fn continues_list(line: &[Token], next: &Token) -> bool {
    let is_kind = |t: &Token| {
        matches!(
            t.term,
            TerminalKind::KwFn
                | TerminalKind::KwTheorem
                | TerminalKind::KwDef
                | TerminalKind::KwInductive
                | TerminalKind::KwStruct
                | TerminalKind::KwEnum
        )
    };
    let arrow = |t: &Token| t.term == TerminalKind::FatArrow;
    match line.last() {
        Some(last) if arrow(last) => is_kind(next),
        Some(last) if last.kind == Kind::Comma => {
            is_kind(next)
                && line
                    .windows(3)
                    .any(|w| arrow(&w[0]) && is_kind(&w[1]) && w[2].term == TerminalKind::Ident)
        }
        _ => false,
    }
}

/// The line as written, its first line indented anew and its other lines
/// as they were, without trailing whitespace.
fn write_verbatim(source: &str, line: &[Token], indent: usize, out: &mut String) {
    let text = &source[line[0].start..line[line.len() - 1].end];
    out.push_str(&" ".repeat(indent));
    let lines: Vec<&str> = text.split('\n').map(str::trim_end).collect();
    out.push_str(&lines.join("\n"));
}

#[cfg(test)]
mod tests {
    use super::format;

    #[test]
    fn a_deep_nesting_is_an_error() {
        tauto_messages::install();
        let deep = format!("let x := {}1{}\n", "(".repeat(50_000), ")".repeat(50_000));
        assert_eq!(format(&deep), Err("the source nests too deeply".into()));
    }
}
