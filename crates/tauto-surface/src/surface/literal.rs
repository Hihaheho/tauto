//! Syntax literals: ``math`1 + 2` ``, ``math<`a `b` c`>`` and a block of three
//! to six backticks. The scanner reads
//! a literal as an opening, pieces and a closing; here they become one
//! [`SyntaxLit`] holding the text between them, with a block's indentation
//! taken off like Eure's `Text::parse_indented_block`.

use tauto_message::msg;
use tauto_parol::{NodeId, NonTerminalKind as Nt, Span};

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
    pub error: Option<(String, Span)>,
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

impl Reader<'_> {
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
            Kind::Text => {
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
            Kind::Delim(n) => {
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
            Kind::Block(n) => self.block_lit(whole, n, written),
        }
    }

    fn literal_kind(&self, id: NodeId) -> Kind {
        let mut node = id;
        loop {
            match self.nt(node) {
                Some(Nt::MacroText) => return Kind::Text,
                Some(Nt::MacroDelim1) => return Kind::Delim(1),
                Some(Nt::MacroDelim2) => return Kind::Delim(2),
                Some(Nt::MacroDelim3) => return Kind::Delim(3),
                Some(Nt::MacroBlock3) => return Kind::Block(3),
                Some(Nt::MacroBlock4) => return Kind::Block(4),
                Some(Nt::MacroBlock5) => return Kind::Block(5),
                Some(Nt::MacroBlock6) => return Kind::Block(6),
                _ => {}
            }
            match self.cst.children_iter(node).next() {
                Some(c) => node = c,
                None => break,
            }
        }
        Kind::Text
    }

    /// ```` ```name ```` and a line end, the content, the closing fence.
    fn block_lit(&self, whole: &str, n: usize, written: Span) -> SyntaxLit {
        let after_ticks = &whole[n.min(whole.len())..];
        let name_len = after_ticks
            .find(|c: char| c.is_whitespace())
            .unwrap_or(after_ticks.len());
        let name = &after_ticks[..name_len];
        let line_end = whole.find('\n').map_or(whole.len(), |i| i + 1);
        let inner_end = whole.len().saturating_sub(n).max(line_end);
        let content = &whole[line_end..inner_end];
        let start = written.start + line_end as u32;
        // The closing fence's own line: whitespace before it is the indentation to take off.
        let (body, indent) = match content.rfind('\n') {
            Some(i) if content[i + 1..].chars().all(|c| c == ' ' || c == '\t') => {
                (&content[..=i], content.len() - i - 1)
            }
            None if content.chars().all(|c| c == ' ' || c == '\t') => ("", content.len()),
            _ => (content, 0),
        };
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
                    msg!("surface-block-indent", lead = lead, indent = indent).to_string(),
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

enum Kind {
    Text,
    Delim(usize),
    Block(usize),
}
