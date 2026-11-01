//! The lossless tree: every token of a parse, the skipped ones (white space,
//! comments) too, under the non-terminals the grammar names. A repetition,
//! an option or a group of the grammar's own making is not a node: its
//! tokens and nodes belong to the node around it.

use crate::ast::SchemaError;
use crate::parse::Event;
use crate::scan::Token;
use crate::tables::{NtKind, Tables};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cst {
    Node {
        non_terminal: u32,
        children: Vec<Cst>,
        /// The bytes from its first to its last token that is not skipped (the white space and
        /// comments around are among its `children`, outside this range); a node of no such
        /// token is empty, where the text before it ends.
        start: u32,
        end: u32,
    },
    Token(Token),
}

impl Cst {
    pub fn range(&self) -> (u32, u32) {
        match self {
            Cst::Node { start, end, .. } => (*start, *end),
            Cst::Token(t) => (t.start, t.end),
        }
    }
}

struct Frame {
    non_terminal: u32,
    /// Each child, paired with whether it holds a token that is not skipped.
    children: Vec<(Cst, bool)>,
}

pub fn build_cst(tables: &Tables, events: &[Event]) -> Result<Cst, SchemaError> {
    let mut stack: Vec<Frame> = Vec::new();
    let mut result = None;
    let mut last_end = 0u32;
    // The start symbol an LR generator adds above the grammar's own is not a node either.
    let added = |n: u32| {
        tables.lr.is_some() && n == tables.start && tables.nt_kinds[n as usize] == NtKind::Group
    };
    let mut in_added = false;
    for ev in events {
        match *ev {
            Event::Open { non_terminal, .. } if stack.is_empty() && added(non_terminal) => {
                in_added = true
            }
            Event::Open { non_terminal, .. } => stack.push(Frame {
                non_terminal,
                children: Vec::new(),
            }),
            Event::Token(tok) => match stack.last_mut() {
                Some(f) => f
                    .children
                    .push((Cst::Token(tok), !tables.is_skipped(tok.terminal))),
                // What follows the last token of the text belongs to the root.
                None => match &mut result {
                    Some(Cst::Node { children, .. }) if tables.is_skipped(tok.terminal) => {
                        children.push(Cst::Token(tok))
                    }
                    _ => return Err(SchemaError("a token outside a node")),
                },
            },
            Event::Close if stack.is_empty() && in_added => in_added = false,
            Event::Close => {
                let f = stack.pop().ok_or(SchemaError("a close without an open"))?;
                let own = matches!(
                    tables.nt_kinds[f.non_terminal as usize],
                    NtKind::Declared | NtKind::Token
                );
                match stack.last_mut() {
                    Some(parent) if !own => parent.children.extend(f.children),
                    Some(parent) => {
                        let (lead, node, solid) = node(f, &mut last_end, true);
                        parent.children.extend(lead.into_iter().map(|t| (t, false)));
                        parent.children.push((node, solid));
                    }
                    None => result = Some(node(f, &mut last_end, false).1),
                }
            }
        }
    }
    if !stack.is_empty() {
        return Err(SchemaError("an open without a close"));
    }
    result.ok_or(SchemaError("no events"))
}

/// The node of a frame. White space and comments before its first solid child are not its
/// own when `hoist`: they come back first, to go before the node in its parent.
fn node(f: Frame, last_end: &mut u32, hoist: bool) -> (Vec<Cst>, Cst, bool) {
    let mut children = f.children;
    let first = children.iter().position(|(_, solid)| *solid);
    let last = children.iter().rposition(|(_, solid)| *solid);
    let (start, end, solid) = match (first, last) {
        (Some(a), Some(b)) => (children[a].0.range().0, children[b].0.range().1, true),
        _ => (*last_end, *last_end, false),
    };
    *last_end = end;
    let lead = if hoist {
        children
            .iter()
            .take_while(|(c, solid)| matches!(c, Cst::Token(_)) && !solid)
            .count()
    } else {
        0
    };
    let lead: Vec<Cst> = children.drain(..lead).map(|(c, _)| c).collect();
    let node = Cst::Node {
        non_terminal: f.non_terminal,
        children: children.into_iter().map(|(c, _)| c).collect(),
        start,
        end,
    };
    (lead, node, solid)
}
