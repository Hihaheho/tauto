//! Syntax literals: ``math`1 + 2` ``, ``math<`a `b` c`>`` and a block of three
//! to six backticks. The scanner reads
//! a literal as an opening, pieces and a closing; here they become one
//! [`SyntaxLit`] holding the text between them, with a block's indentation
//! taken off like Eure's `Text::parse_indented_block`.
//!
//! [`lexical`] reads a source text alone and gives every literal it writes ([`LitSite`], with
//! where its body is and its form) and every comment ([`Comment`], for [`super::fence`]), from
//! the syntax tree. Tools that work on the text of a file (the formatter, the editor's colours)
//! find literals and comments here and nowhere else.

use tauto_message::{Message, msg};
use tauto_parol::{NodeId, NodeKind, NonTerminalKind as Nt, Span, TerminalKind};

use super::fence::Comment;
use super::{Reader, SurfaceTerm, TermKind};

/// What a literal holds, and where each byte of it was written.
#[derive(Debug, Clone, PartialEq)]
pub struct SyntaxLit {
    /// The syntax's name; `None` when it is not written.
    pub name: Option<String>,
    /// The text between the opening and the closing (a block's without its indentation).
    pub text: String,
    /// The span position of `text`'s first byte, as written.
    pub start: u32,
    /// For a block whose lines lost their indentation: for each line, the
    /// offset in `text` where it starts and the bytes taken off it and the
    /// lines before it (so a position in `text` is `start` plus this).
    pub shifts: Vec<(u32, u32)>,
    /// A line of a block that is less indented than its closing: the message
    /// and where. Reported when the literal is read into a value.
    pub error: Option<(Message, Span)>,
    pub span: Span,
}

impl SyntaxLit {
    /// The span position of byte `offset` of `text`, as written in the file.
    pub fn position(&self, offset: u32) -> u32 {
        let removed = match self.shifts.partition_point(|&(line, _)| line <= offset) {
            0 => 0,
            n => self.shifts[n - 1].1,
        };
        self.start + offset + removed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LitForm {
    Text,
    /// `` name<`text`> `` with this many `<` (and `>`).
    Delim(usize),
    Block(usize),
}

/// A literal of the source text, and where its body is written.
#[derive(Debug, Clone, PartialEq)]
pub struct LitSite {
    pub lit: SyntaxLit,
    pub form: LitForm,
    /// The bytes written between the opening and the closing: for a block, from the line after
    /// the opening to the start of the closing fence's indentation (the last newline included).
    /// `lit.text` is this with a block's indentation taken off.
    pub body: Span,
    /// For a block: the white space before the closing fence, which `lit.text` lost from each line.
    pub indent: String,
    /// For a block: the closing fence starts its own line (a block whose last line holds text
    /// before the fence has no indentation to take off).
    pub own_line: bool,
    /// It is the grammar of a `syntax!` declaration.
    pub grammar: bool,
}

/// The literals and comments of a source text, in the order they are written.
#[derive(Debug, Clone, Default)]
pub struct Lexical {
    pub literals: Vec<LitSite>,
    pub comments: Vec<Comment>,
    /// Why the text does not parse. The literals and comments are then those of the tree as far
    /// as it was read.
    pub error: Option<String>,
}

/// Reads `source` and collects its literals and comments from the syntax tree (strings,
/// comments and literals are told apart by the scanner, not here).
pub fn lexical(source: &str) -> Lexical {
    let parsed = tauto_parol::parse(source);
    let reader = Reader::new(&parsed, source);
    let cst = &parsed.cst;
    let mut out = Lexical {
        error: parsed.errors.first().map(|e| {
            e.span.map_or_else(
                || e.message.clone(),
                |s| format!("{} (byte {})", e.message, s.start),
            )
        }),
        ..Lexical::default()
    };
    let mut stack: Vec<(NodeId, bool)> = cst.root().into_iter().map(|r| (r, false)).collect();
    while let Some((id, grammar)) = stack.pop() {
        match cst.kind(id) {
            NodeKind::Terminal(
                kind @ (TerminalKind::Comment
                | TerminalKind::LineComment
                | TerminalKind::BlockComment),
            ) => out.comments.push(Comment {
                span: cst.span(id),
                block: kind == TerminalKind::BlockComment,
            }),
            NodeKind::Terminal(_) => {}
            NodeKind::NonTerminal(Nt::SyntaxLit) => out.literals.push(reader.site(id, grammar)),
            NodeKind::NonTerminal(kind) => {
                let grammar = grammar || kind == Nt::SyntaxDecl;
                stack.extend(cst.node(id).children.iter().rev().map(|&c| (c, grammar)));
            }
        }
    }
    out
}

impl Reader<'_> {
    fn site(&self, id: NodeId, grammar: bool) -> LitSite {
        let lit = self.lit(id);
        let form = self.literal_kind(id);
        let (end, indent, own_line) = match form {
            // The text is the bytes between the opening and the closing.
            LitForm::Text | LitForm::Delim(_) => {
                (lit.start + lit.text.len() as u32, String::new(), true)
            }
            LitForm::Block(n) => {
                let whole = self.cst.span(id).text(self.source);
                let split = split_block(whole, n);
                (
                    lit.start + split.body.len() as u32,
                    split.indent.to_string(),
                    split.own_line,
                )
            }
        };
        LitSite {
            body: Span::new(lit.start, end),
            lit,
            form,
            indent,
            own_line,
            grammar,
        }
    }

    /// A `SyntaxLit` node: `MacroText`, `MacroDelim1…3` or `MacroBlock3…6`.
    pub(super) fn syntax_lit(&self, id: NodeId, span: Span) -> SurfaceTerm {
        SurfaceTerm::new(TermKind::SyntaxLit(Box::new(self.lit(id))), span)
    }

    pub(super) fn lit(&self, id: NodeId) -> SyntaxLit {
        let raw = self.cst.span(id);
        let written = self.span(id);
        let whole = raw.text(self.source);
        let kind = self.literal_kind(id);
        let name_of = |end: usize| {
            let name = &whole[..end];
            (!name.is_empty()).then(|| name.to_string())
        };
        match kind {
            LitForm::Text => {
                let tick = whole.find('`').unwrap_or(0);
                let body = whole
                    .get(tick + 1..whole.len().saturating_sub(1))
                    .unwrap_or("");
                SyntaxLit {
                    name: name_of(tick),
                    text: body.to_string(),
                    start: written.start + tick as u32 + 1,
                    shifts: Vec::new(),
                    error: None,
                    span: written,
                }
            }
            LitForm::Delim(n) => {
                let open = whole.find('<').unwrap_or(0);
                let head = open + n + 1; // name, n of `<`, a backtick
                let close = n + 1; // a backtick, n of `>`
                let body = whole
                    .get(head..whole.len().saturating_sub(close))
                    .unwrap_or("");
                SyntaxLit {
                    name: name_of(open),
                    text: body.to_string(),
                    start: written.start + head as u32,
                    shifts: Vec::new(),
                    error: None,
                    span: written,
                }
            }
            LitForm::Block(n) => self.block_lit(whole, n, written),
        }
    }

    fn literal_kind(&self, id: NodeId) -> LitForm {
        let mut node = id;
        loop {
            match self.nt(node) {
                Some(Nt::MacroText) => return LitForm::Text,
                Some(Nt::MacroDelim1) => return LitForm::Delim(1),
                Some(Nt::MacroDelim2) => return LitForm::Delim(2),
                Some(Nt::MacroDelim3) => return LitForm::Delim(3),
                Some(Nt::MacroBlock3) => return LitForm::Block(3),
                Some(Nt::MacroBlock4) => return LitForm::Block(4),
                Some(Nt::MacroBlock5) => return LitForm::Block(5),
                Some(Nt::MacroBlock6) => return LitForm::Block(6),
                _ => {}
            }
            match self.cst.children_iter(node).next() {
                Some(c) => node = c,
                None => break,
            }
        }
        LitForm::Text
    }

    /// ```` ```name ```` and a line end, the content, the closing fence.
    fn block_lit(&self, whole: &str, n: usize, written: Span) -> SyntaxLit {
        let split = split_block(whole, n);
        let (name, body, indent) = (split.name, split.body, split.indent.len());
        let start = written.start + split.line_end as u32;
        let mut text = String::with_capacity(body.len());
        let mut shifts = Vec::new();
        let mut removed = 0u32;
        let mut error = None;
        let mut offset = 0usize;
        for line in body.split_inclusive('\n') {
            let bare = line.trim_end_matches(['\n', '\r']);
            let ends = &line[bare.len()..];
            let lead = bare.len() - bare.trim_start_matches([' ', '\t']).len();
            let take = if bare.trim().is_empty() {
                // A line of white space only becomes an empty line.
                bare.len()
            } else if lead >= indent {
                indent
            } else {
                error.get_or_insert((
                    msg!("surface-block-indent", lead = lead, indent = indent),
                    Span::new(start + offset as u32, start + (offset + bare.len()) as u32),
                ));
                lead
            };
            removed += take as u32;
            shifts.push((text.len() as u32, removed));
            text.push_str(&bare[take..]);
            text.push_str(ends);
            offset += line.len();
        }
        SyntaxLit {
            name: (!name.is_empty()).then(|| name.to_string()),
            text,
            start,
            shifts: if indent == 0 { Vec::new() } else { shifts },
            error,
            span: written,
        }
    }
}

struct BlockSplit<'a> {
    name: &'a str,
    line_end: usize,
    /// The lines of the content, up to the newline before the closing fence's line.
    body: &'a str,
    indent: &'a str,
    own_line: bool,
}

/// ```` ```name ```` and a line end, the content, the closing fence of `n` backticks, cut apart.
/// The white space before the closing fence is the indentation to take off.
fn split_block(whole: &str, n: usize) -> BlockSplit<'_> {
    let after_ticks = &whole[n.min(whole.len())..];
    let name_len = after_ticks
        .find(|c: char| c.is_whitespace())
        .unwrap_or(after_ticks.len());
    let name = &after_ticks[..name_len];
    let line_end = whole.find('\n').map_or(whole.len(), |i| i + 1);
    let inner_end = whole.len().saturating_sub(n).max(line_end);
    let content = &whole[line_end..inner_end];
    let blank = |s: &str| s.chars().all(|c| c == ' ' || c == '\t');
    let (body, indent, own_line) = match content.rfind('\n') {
        Some(i) if blank(&content[i + 1..]) => (&content[..=i], &content[i + 1..], true),
        None if blank(content) => ("", content, true),
        _ => (content, "", false),
    };
    BlockSplit {
        name,
        line_end,
        body,
        indent,
        own_line,
    }
}
