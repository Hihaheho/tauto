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

use crate::span::Span;
use tauto_message::{Message, msg};

use super::fence::Comment;
use super::{SurfaceTerm, TermKind};

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
