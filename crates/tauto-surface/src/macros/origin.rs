//! Where the nodes of an expansion came from. The checkers key their tables by span, and a macro may fill in one
//! input twice, so every node of an expansion's output gets a span of its
//! own, from [`EXPANSION_BASE`] on, one byte each. The map says which
//! position was written for it and which expansion made it.

use crate::span::Span;

/// Where the spans of expansions start; the prelude's start at `1 << 31`.
pub const EXPANSION_BASE: u32 = 1 << 30;

#[derive(Debug, Clone, Default, PartialEq)]
pub struct SpanMap {
    /// For each span made: the position as written, and the expansion.
    origins: Vec<(u32, u32)>,
    /// Texts a declaration made and read at places of their own (the proof side of
    /// `inductive_syntax!`): the first place, how many bytes, and where the
    /// declaration was written.
    texts: Vec<(u32, u32, u32)>,
}

/// The expansion of a span that a declaration's own text made rather than a macro.
pub const NO_EXPANSION: u32 = u32::MAX;

impl SpanMap {
    /// A span for a node of expansion `expansion`. `written` 0 is no position of the
    /// macro's output (`Syn::call_span()`, a name `Syn::global` makes): the node stands
    /// at `call`, the start of the macro call.
    pub fn fresh(&mut self, written: u32, expansion: u32, call: u32) -> Span {
        let written = if written == 0 { call } else { written };
        let at = EXPANSION_BASE + self.origins.len() as u32;
        self.origins.push((written, expansion));
        Span::new(at, at + 1)
    }

    /// The written position and the expansion of a span made here.
    pub fn origin(&self, at: u32) -> Option<(u32, u32)> {
        if let Some(&(_, _, written)) = self
            .texts
            .iter()
            .find(|&&(start, len, _)| start <= at && at <= start + len)
        {
            return Some((written, NO_EXPANSION));
        }
        let i = at.checked_sub(EXPANSION_BASE)? as usize;
        self.origins.get(i).copied()
    }

    /// The spans made from the `from`-th on, as made for a statement that has since moved by
    /// `by` bytes: the positions written in a file move with it.
    pub fn moved_from(&mut self, from: usize, by: i64) {
        for (written, _) in self.origins.iter_mut().skip(from) {
            *written = crate::surface::shift::position(*written, by);
        }
    }

    /// Says that the `len` bytes from `start` are a text the declaration written at
    /// `written` made, so that a place in it is shown where the declaration is.
    pub fn text(&mut self, start: u32, len: u32, written: u32) {
        self.texts.push((start, len, written));
    }

    pub fn len(&self) -> usize {
        self.origins.len()
    }

    pub fn is_empty(&self) -> bool {
        self.origins.is_empty()
    }
}
