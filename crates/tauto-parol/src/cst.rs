//! The concrete syntax tree: every non-terminal and token the parser met,
//! with byte spans. Parser callbacks maintain a stack of open non-terminals;
//! each completed node collects its children in input order.

use parol_runtime::{ParolError, Token, parser::parse_tree_type::TreeConstruct};
use std::collections::HashSet;
use std::sync::OnceLock;

use crate::declared::DECLARED;
use crate::node_kind::{NonTerminalKind, TerminalKind};

/// A byte range of the source, end exclusive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    pub fn merge(self, other: Span) -> Span {
        if self.is_empty() && self.start == 0 {
            return other;
        }
        if other.is_empty() && other.start == 0 {
            return self;
        }
        Span::new(self.start.min(other.start), self.end.max(other.end))
    }

    pub fn is_empty(self) -> bool {
        self.start >= self.end
    }

    pub fn contains(self, offset: u32) -> bool {
        self.start <= offset && offset <= self.end
    }

    pub fn text(self, source: &str) -> &str {
        source
            .get(self.start as usize..self.end as usize)
            .unwrap_or_default()
    }
}

pub type NodeId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NodeKind {
    NonTerminal(NonTerminalKind),
    Terminal(TerminalKind),
}

#[derive(Debug, Clone)]
pub struct CstNode {
    pub kind: NodeKind,
    pub span: Span,
    pub children: Vec<NodeId>,
}

#[derive(Debug, Clone)]
pub struct Cst {
    nodes: Vec<CstNode>,
    root: Option<NodeId>,
}

impl Cst {
    pub fn root(&self) -> Option<NodeId> {
        self.root
    }

    pub fn node(&self, id: NodeId) -> &CstNode {
        &self.nodes[id]
    }

    pub fn kind(&self, id: NodeId) -> NodeKind {
        self.nodes[id].kind
    }

    pub fn span(&self, id: NodeId) -> Span {
        self.nodes[id].span
    }

    pub fn non_terminal(&self, id: NodeId) -> Option<NonTerminalKind> {
        match self.nodes[id].kind {
            NodeKind::NonTerminal(k) => Some(k),
            NodeKind::Terminal(_) => None,
        }
    }

    pub fn terminal(&self, id: NodeId) -> Option<TerminalKind> {
        match self.nodes[id].kind {
            NodeKind::Terminal(k) => Some(k),
            NodeKind::NonTerminal(_) => None,
        }
    }

    /// How deep the tree nests, counted without recursing.
    pub fn depth(&self) -> usize {
        let mut deepest = 0;
        let mut stack: Vec<(NodeId, usize)> = self.root.into_iter().map(|r| (r, 1)).collect();
        while let Some((id, depth)) = stack.pop() {
            deepest = deepest.max(depth);
            stack.extend(self.nodes[id].children.iter().map(|&c| (c, depth + 1)));
        }
        deepest
    }

    /// The children of a node with parol's EBNF helper nodes (`…List`,
    /// `…Opt`, `…Group`) inlined, so `Additive: Multiplicative { AddOp
    /// Multiplicative }` reads as `[Multiplicative, AddOp, Multiplicative, …]`.
    pub fn children(&self, id: NodeId) -> Vec<NodeId> {
        self.children_iter(id).collect()
    }

    /// Flattened children in source order, without collecting the result.
    pub fn children_iter(&self, id: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        let mut current = self.nodes[id].children.iter();
        let mut parents = Vec::new();
        std::iter::from_fn(move || {
            loop {
                let Some(&child) = current.next() else {
                    current = parents.pop()?;
                    continue;
                };
                match self.nodes[child].kind {
                    NodeKind::NonTerminal(kind) if !is_declared(kind) => {
                        if !current.as_slice().is_empty() {
                            parents.push(current.clone());
                        }
                        current = self.nodes[child].children.iter();
                    }
                    NodeKind::Terminal(kind) if is_trivia(kind) => {}
                    _ => return Some(child),
                }
            }
        })
    }

    /// The one token a single-token non-terminal such as `Ident` or `Plus`
    /// holds, ignoring whitespace and comments.
    pub fn token(&self, id: NodeId) -> Option<(TerminalKind, Span)> {
        match self.nodes[id].kind {
            NodeKind::Terminal(kind) if !is_trivia(kind) => Some((kind, self.nodes[id].span)),
            NodeKind::Terminal(_) => None,
            NodeKind::NonTerminal(_) => self.nodes[id]
                .children
                .iter()
                .find_map(|&child| self.token(child)),
        }
    }

    /// Every terminal in source order.
    pub fn terminals(&self) -> Vec<(TerminalKind, Span)> {
        let mut out = Vec::new();
        if let Some(root) = self.root {
            self.collect_terminals(root, &mut out);
        }
        out.sort_by_key(|(_, span)| span.start);
        out
    }

    fn collect_terminals(&self, id: NodeId, out: &mut Vec<(TerminalKind, Span)>) {
        match self.nodes[id].kind {
            NodeKind::Terminal(kind) => out.push((kind, self.nodes[id].span)),
            NodeKind::NonTerminal(_) => {
                for &child in &self.nodes[id].children {
                    self.collect_terminals(child, out);
                }
            }
        }
    }

    /// The tree as text, a line for each node and token in the order of the
    /// source, trivia too, none flattened: the depth, the kind, the start and
    /// the end of the span. `totes/syntax` prints the same
    /// (`docs/design/self-host.md`). The depth is a number, not an indent, so
    /// the dump of a deep tree stays small.
    pub fn dump(&self) -> String {
        use std::fmt::Write;
        let mut out = String::new();
        let mut stack: Vec<(NodeId, usize)> = self.root.into_iter().map(|r| (r, 0)).collect();
        while let Some((id, depth)) = stack.pop() {
            let node = &self.nodes[id];
            let _ = match node.kind {
                NodeKind::NonTerminal(k) => write!(out, "{depth} {k}"),
                NodeKind::Terminal(k) => write!(out, "{depth} {k}"),
            };
            let _ = writeln!(out, " {} {}", node.span.start, node.span.end);
            stack.extend(node.children.iter().rev().map(|&c| (c, depth + 1)));
        }
        out
    }

    /// The innermost node of `kind` whose span holds `offset`.
    pub fn innermost(&self, offset: u32, kind: NonTerminalKind) -> Option<NodeId> {
        let mut found = None;
        let mut stack: Vec<NodeId> = self.root.into_iter().collect();
        while let Some(id) = stack.pop() {
            let node = &self.nodes[id];
            if !node.span.contains(offset) {
                continue;
            }
            if node.kind == NodeKind::NonTerminal(kind) {
                found = Some(id);
            }
            stack.extend(node.children.iter().copied());
        }
        found
    }
}

/// Whitespace, the newlines parol skips inside brackets, and comments.
pub fn is_trivia(kind: TerminalKind) -> bool {
    matches!(
        kind,
        TerminalKind::Whitespace
            | TerminalKind::NewLine
            | TerminalKind::LineComment
            | TerminalKind::BlockComment
            | TerminalKind::Comment
    )
}

fn is_declared(kind: NonTerminalKind) -> bool {
    static KINDS: OnceLock<HashSet<NonTerminalKind>> = OnceLock::new();
    KINDS
        .get_or_init(|| {
            DECLARED
                .iter()
                .map(|name| NonTerminalKind::from_non_terminal_name(name))
                .collect()
        })
        .contains(&kind)
}

struct Open {
    node: NodeId,
    span: Span,
    children: Vec<NodeId>,
}

pub(crate) struct CstBuilder {
    nodes: Vec<CstNode>,
    stack: Vec<Open>,
    root: Option<NodeId>,
}

impl CstBuilder {
    pub(crate) fn new() -> Self {
        Self {
            nodes: Vec::new(),
            stack: Vec::new(),
            root: None,
        }
    }

    fn close(&mut self) {
        if let Some(open) = self.stack.pop() {
            let node = &mut self.nodes[open.node];
            node.children = open.children;
            node.span = open.span;
            if let Some(parent) = self.stack.last_mut() {
                parent.span = parent.span.merge(open.span);
            }
        }
    }

    pub(crate) fn build(mut self, _source: &str) -> Cst {
        while !self.stack.is_empty() {
            self.close();
        }
        Cst {
            nodes: self.nodes,
            root: self.root,
        }
    }
}

impl<'t> TreeConstruct<'t> for CstBuilder {
    type Error = ParolError;
    type Tree = ();

    fn open_non_terminal(
        &mut self,
        name: &'static str,
        _size_hint: Option<usize>,
    ) -> Result<(), Self::Error> {
        let kind = NonTerminalKind::from_non_terminal_name(name);
        let id = self.nodes.len();
        self.nodes.push(CstNode {
            kind: NodeKind::NonTerminal(kind),
            span: Span::default(),
            children: Vec::new(),
        });
        match self.stack.last_mut() {
            Some(parent) => parent.children.push(id),
            None => self.root = Some(id),
        }
        self.stack.push(Open {
            node: id,
            span: Span::default(),
            children: Vec::new(),
        });
        Ok(())
    }

    fn close_non_terminal(&mut self) -> Result<(), Self::Error> {
        self.close();
        Ok(())
    }

    fn add_token(&mut self, token: &Token<'t>) -> Result<(), Self::Error> {
        let kind = TerminalKind::from_terminal_index(token.token_type);
        let span = Span::new(token.location.start, token.location.end);
        let id = self.nodes.len();
        self.nodes.push(CstNode {
            kind: NodeKind::Terminal(kind),
            span,
            children: Vec::new(),
        });
        if let Some(parent) = self.stack.last_mut() {
            parent.children.push(id);
            // Whitespace and comments the parser reads ahead belong to no
            // node's extent: a type's span is `Table`, not ` Table`.
            if !is_trivia(kind) {
                parent.span = parent.span.merge(span);
            }
        }
        Ok(())
    }

    fn build(self) -> Result<Self::Tree, Self::Error> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flattened_parameters_keep_order_and_skip_trivia() {
        // CST layout is the parser's own business, so the source is here.
        let source = "fn f(a /* comment */ : i64, b: Text): i64 { 1 }";
        let parsed = crate::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.errors);
        let cst = parsed.cst;
        let params: Vec<Vec<_>> = cst
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| node.kind == NodeKind::NonTerminal(NonTerminalKind::Param))
            .map(|(id, _)| {
                cst.children_iter(id)
                    .map(|child| cst.span(child).text(source))
                    .collect()
            })
            .collect();
        assert_eq!(params, [vec!["a", ":", "i64"], vec!["b", ":", "Text"]]);
    }

    #[test]
    fn first_child_does_not_traverse_later_siblings() {
        let cst = Cst {
            nodes: vec![
                CstNode {
                    kind: NodeKind::NonTerminal(NonTerminalKind::Program),
                    span: Span::default(),
                    children: vec![1, usize::MAX],
                },
                CstNode {
                    kind: NodeKind::Terminal(TerminalKind::Comma),
                    span: Span::default(),
                    children: vec![],
                },
            ],
            root: Some(0),
        };
        assert_eq!(cst.children_iter(0).next(), Some(1));
    }
}
