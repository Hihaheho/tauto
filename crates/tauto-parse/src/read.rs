//! The concrete syntax tree of `tauto-parol` read as the surface syntax:
//! types and expressions here, statements and the program in `program`,
//! literals in `literal`.

#![allow(unused_imports)]
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use tauto_message::{Message, msg};
use tauto_parol::{Cst, NodeId, NodeKind, NonTerminalKind as Nt, Parsed, TerminalKind, parse};
use tauto_surface::span::Span;
use tauto_surface::surface::fence::Comment;
use tauto_surface::surface::qualify::SEPARATOR;
use tauto_surface::surface::*;

mod literal;
pub mod program;
#[cfg(test)]
mod tests;

pub use literal::lexical;
pub use program::{
    parse_builtin_as_written_at, parse_builtin_at, parse_expr_at, parse_program_as_written,
    parse_program_as_written_at, parse_program_located_at, parse_program_unresolved_at,
};

/// For tests and tools: parses `source` and returns, in the order of the
/// source, the terms of every `Type` and `Expr` that is a direct child of a
/// node of `kind` (such as the type written in a parameter, a result or a
/// `let`).
pub fn terms_in(source: &str, kind: Nt) -> Result<Vec<SurfaceTerm>, String> {
    crate::install();
    let parsed = parse(source);
    if let Some(e) = parsed.errors.first() {
        return Err(e.message.clone());
    }
    let reader = Reader::new(&parsed, source);
    let mut out = Vec::new();
    if let Some(root) = parsed.cst.root() {
        reader.collect(root, kind, &mut out);
    }
    Ok(out)
}

struct Reader<'a> {
    cst: &'a Cst,
    source: &'a str,
    /// Added to every span: the prelude's spans start at `PRELUDE_BASE`, so
    /// they never meet a program's.
    base: u32,
}

impl<'a> Reader<'a> {
    pub(super) fn new(parsed: &'a Parsed, source: &'a str) -> Self {
        Self {
            cst: &parsed.cst,
            source,
            base: 0,
        }
    }

    fn span(&self, id: NodeId) -> Span {
        let s = self.cst.span(id);
        Span::new(s.start + self.base, s.end + self.base)
    }

    fn collect(&self, id: NodeId, kind: Nt, out: &mut Vec<SurfaceTerm>) {
        for child in self.cst.children(id) {
            match self.cst.non_terminal(child) {
                Some(k) if k == kind => {
                    for term_node in self.cst.children(child) {
                        if matches!(
                            self.cst.non_terminal(term_node),
                            Some(Nt::Type | Nt::BodyType | Nt::Expr)
                        ) {
                            out.push(self.term(term_node));
                        }
                    }
                }
                _ => self.collect(child, kind, out),
            }
        }
    }

    /// The text of a node. A name written `r#name` is `name`: the `r#` is not part of it. A
    /// quotation hole `$r#name` or `${name}` is `$name`, the hole as it is written plainly.
    fn text(&self, id: NodeId) -> std::borrow::Cow<'_, str> {
        let text = self.cst.span(id).text(self.source);
        if matches!(
            self.nt(id),
            Some(Nt::Ident | Nt::FnName | Nt::CondPath | Nt::OperationName)
        ) {
            unhole(text).map_or_else(|| unraw(text), std::borrow::Cow::Owned)
        } else {
            std::borrow::Cow::Borrowed(text)
        }
    }

    fn nt(&self, id: NodeId) -> Option<Nt> {
        self.cst.non_terminal(id)
    }

    fn first(&self, id: NodeId, kind: Nt) -> Option<NodeId> {
        self.cst
            .children_iter(id)
            .find(|c| self.nt(*c) == Some(kind))
    }

    /// The name of a field written under `id`: a name (`t.r#type`, `#{ r#match: v }`).
    fn label_of(&self, id: NodeId) -> Option<NodeId> {
        self.cst
            .children_iter(id)
            .find(|c| self.nt(*c) == Some(Nt::Ident))
    }

    /// The type written under `id`: a `Type`, or a `BodyType` where a `{` or `=>` follows it.
    /// The `⊢ G from e` an arm's body is, `C => ⊢ G from e`.
    pub(super) fn goal_expr(&self, arm_body: NodeId) -> Option<NodeId> {
        let expr = self.first(arm_body, Nt::Expr)?;
        self.first(expr, Nt::GoalExpr)
    }

    /// The `e` of `⊢ G from e`. A `match` written without a result type takes `G` as its
    /// result type: `⊢ G from match l { … }` is `match l: G { … }`.
    pub(super) fn goal_body(&self, goal: NodeId) -> SurfaceTerm {
        let Some(e) = self.first(goal, Nt::Expr) else {
            return self.other(goal);
        };
        let mut body = self.term(e);
        if matches!(&*body.kind, TermKind::Match { result: None, .. })
            && let Some(ty) = self.ty(goal)
            && let TermKind::Match { result, .. } = Arc::make_mut(&mut body.kind)
        {
            *result = Some(Box::new(self.term(ty)));
        }
        body
    }

    pub(super) fn ty(&self, id: NodeId) -> Option<NodeId> {
        self.cst
            .children_iter(id)
            .find(|c| matches!(self.nt(*c), Some(Nt::Type | Nt::BodyType)))
    }

    pub(super) fn tys(&self, id: NodeId) -> Vec<NodeId> {
        self.cst
            .children_iter(id)
            .filter(|c| matches!(self.nt(*c), Some(Nt::Type | Nt::BodyType)))
            .collect()
    }

    fn all(&self, id: NodeId, kind: Nt) -> Vec<NodeId> {
        self.cst
            .children_iter(id)
            .filter(|c| self.nt(*c) == Some(kind))
            .collect()
    }

    fn other(&self, id: NodeId) -> SurfaceTerm {
        let kind = self
            .nt(id)
            .map(|k| k.to_string())
            .unwrap_or_else(|| "token".into());
        SurfaceTerm::new(TermKind::Other(kind), self.span(id))
    }

    fn term(&self, id: NodeId) -> SurfaceTerm {
        let id = self.through_levels(id);
        let span = self.span(id);
        let kids = self.cst.children(id);
        let Some(kind) = self.nt(id) else {
            // A type/term atom `_` (Wild): Nib partial applications such as
            // `Two(_, i64)`. Not a binding Ident; binders refuse Wild via BindName.
            if self.cst.terminal(id) == Some(TerminalKind::Wild) {
                return SurfaceTerm::var("_", span);
            }
            return self.other(id);
        };
        match kind {
            // A flat sequence of operands and operators, and an operand with its prefixes.
            Nt::Type
            | Nt::BodyType
            | Nt::Seq
            | Nt::Cond
            | Nt::Operand
            | Nt::CondOperand
            | Nt::ArmType => self.sequence(id).0,
            Nt::AngleType | Nt::GenericKind => self.angle_type(id),
            Nt::EffectRow => SurfaceTerm::new(TermKind::Row(self.row_names(id)), span),
            // `⊢ G from e`: `e` checked against `G`.
            Nt::GoalExpr => {
                let body = self.goal_body(id);
                if matches!(&*body.kind, TermKind::Match { .. }) {
                    return body;
                }
                match self.ty(id) {
                    Some(ty) => SurfaceTerm::new(
                        TermKind::Ascribe {
                            term: Box::new(body),
                            ty: Box::new(self.term(ty)),
                        },
                        span,
                    ),
                    None => body,
                }
            }
            Nt::Expr | Nt::AngleExpr => self.expr(&kids, span),
            Nt::Postfix | Nt::CondPostfix => self.postfix(&kids, span),
            Nt::Primary | Nt::CondPrimary => match kids.as_slice() {
                [only] => self.term(*only),
                _ => self.other(id),
            },
            Nt::PathExpr | Nt::CondPath => self.path(id, &kids, span),
            Nt::Number => self.number(id, &kids, span),
            Nt::HoleExpr => SurfaceTerm::new(
                TermKind::Hole(self.text(id).trim_start_matches('?').to_string()),
                span,
            ),
            Nt::Text => SurfaceTerm::new(TermKind::Text(unquote_text(&self.text(id))), span),
            Nt::SyntaxLit => self.syntax_lit(id, span),
            Nt::MacroCall => self.macro_call(id, span),
            Nt::QuoteExpr => self.quote_expr(id, span),
            Nt::SpliceExpr => match self.first(id, Nt::Expr) {
                Some(e) => SurfaceTerm::new(TermKind::Splice(Box::new(self.term(e))), span),
                None => self.other(id),
            },
            Nt::True => SurfaceTerm::new(TermKind::Bool(true), span),
            Nt::False => SurfaceTerm::new(TermKind::Bool(false), span),
            Nt::Paren => self.paren(&kids, span),
            Nt::ListLit => self.list_lit(&kids, span),
            Nt::CongrExpr => self.congr_expr(id, span),
            Nt::BoxHole => SurfaceTerm::new(TermKind::Other(BOX_OUTSIDE.into()), span),
            Nt::ProductLit => self.product_lit(id, span),
            Nt::Brace => match kids.as_slice() {
                [only] => self.term(*only),
                _ => match self.first(id, Nt::BraceBody) {
                    Some(mut body) => {
                        // `BraceBody: Nl BraceBody | …`: the newlines after the `{`.
                        while let Some(inner) = self.first(body, Nt::BraceBody) {
                            body = inner;
                        }
                        match self.first(body, Nt::RecordType) {
                            Some(record) => self.record_type(record, span),
                            None => self.brace_block(body, span),
                        }
                    }
                    None => self.other(id),
                },
            },
            Nt::AnonRecord => self.anon_record(id, span),
            Nt::Block => self.block(id, span),
            Nt::IfExpr => self.if_expr(&kids, span),
            Nt::LoopExpr => match kids.iter().find(|k| self.nt(**k) == Some(Nt::Block)) {
                Some(b) => SurfaceTerm::new(
                    TermKind::Block(vec![Stmt::Loop {
                        body: self.term(*b),
                    }]),
                    span,
                ),
                None => self.other(id),
            },
            Nt::PerformExpr => self.perform(id, span),
            Nt::HandleExpr => self.handle(id, span),
            Nt::MatchExpr => self.match_expr(id, span),
            Nt::StepExpr => self.step_expr(id, span),
            Nt::Item => {
                // `^x` on an Item is a lambda binder mark; as a call argument it
                // is not a term.
                if self.first(id, Nt::Caret).is_some() {
                    return SurfaceTerm::new(
                        TermKind::Other("an unused marker belongs on a binder".into()),
                        span,
                    );
                }
                match kids.first() {
                    Some(e) => self.term(*e),
                    None => self.other(id),
                }
            }
            _ => self.other(id),
        }
    }

    /// The kind of a generic, `Linear` or `(Type) -> Copy`: an operand and, after `->`, a kind.
    fn angle_type(&self, id: NodeId) -> SurfaceTerm {
        let span = self.span(id);
        let id = if self.nt(id) == Some(Nt::GenericKind) {
            match self.first(id, Nt::AngleType) {
                Some(inner) => inner,
                None => return self.other(id),
            }
        } else {
            id
        };
        let Some(head) = self.first(id, Nt::Postfix) else {
            return self.other(id);
        };
        // `A × B × C`: the members in the order written.
        let mut members: Vec<SurfaceTerm> = self.all(id, Nt::Postfix)[1..]
            .iter()
            .map(|p| self.term(*p))
            .collect();
        let mut list = self.first(id, Nt::AngleTypeList);
        while let Some(l) = list {
            members.extend(self.all(l, Nt::Postfix).into_iter().map(|p| self.term(p)));
            list = self.first(l, Nt::AngleTypeList);
        }
        let lhs = if members.is_empty() {
            self.term(head)
        } else {
            members.insert(0, self.term(head));
            let end = members.last().map_or(span.end, |m| m.span.end);
            SurfaceTerm::product_type(members, Span::new(self.span(head).start, end))
        };
        let Some(rest) = self.first(id, Nt::AngleType) else {
            return lhs;
        };
        let product = lhs.as_pair_type().is_some();
        let (params, unused) = match self.sole_paren(head).filter(|_| !product) {
            Some(paren) => {
                let items: Vec<_> = self
                    .all(paren, Nt::Item)
                    .into_iter()
                    .map(|item| self.fn_type_item(item))
                    .collect();
                let unused: Vec<_> = items.iter().map(|(_, _, u)| *u).collect();
                let params: Vec<_> = items.into_iter().map(|(n, t, _)| (n, t)).collect();
                (params, unused)
            }
            None => (vec![(None, lhs)], Vec::new()),
        };
        let unused = if unused.iter().all(Option::is_none) {
            Vec::new()
        } else {
            unused
        };
        SurfaceTerm::new(
            TermKind::Pi {
                params,
                result: Box::new(self.angle_type(rest)),
                effects: None,
                unused,
            },
            span,
        )
    }

    /// An operand with the prefixes that bind to it alone applied (`-x`, `&x`, `@tag x`), and
    /// the ones that stand before a whole sequence left for the caller: `¬` and a binder, which
    /// take the operators tighter than `¬`, and `affine`/`linear`, which stand before an arrow.
    fn piece(&self, operand: NodeId) -> Piece {
        let kids = self.cst.children(operand);
        let Some((&postfix, prefixes)) = kids.split_last() else {
            return Piece::of(self.other(operand));
        };
        let mut acc = self.term(postfix);
        // `affine` and `linear` take the whole arrow, so `affine () -> A` still has a
        // parameter list: no parameter, not one `Unit`.
        let only_kinds = prefixes.iter().all(|p| {
            self.cst
                .children(*p)
                .first()
                .is_some_and(|head| self.nt(*head) == Some(Nt::FnKind))
        });
        let paren = if only_kinds {
            self.sole_paren(postfix)
        } else {
            None
        };
        let mut loose = Vec::new();
        let mut kind = None;
        for &p in prefixes.iter().rev() {
            let Some(head) = self.cst.children(p).first().copied() else {
                continue;
            };
            let span = Span::new(self.span(p).start, acc.span.end);
            match self.nt(head) {
                Some(Nt::NotSign | Nt::Binder) => loose.push(head),
                Some(Nt::FnKind) => kind = Some(head),
                Some(Nt::TagPrefix) => acc = self.tagged(head, acc, span),
                Some(Nt::Borrow) => acc = self.borrowed(head, acc, span),
                _ => acc = SurfaceTerm::app(self.text(p).trim(), vec![acc], span),
            }
        }
        // The prefixes were walked from the last, so the first written is last in `loose`.
        loose.reverse();
        Piece {
            term: acc,
            paren,
            loose,
            kind,
        }
    }

    /// A flat sequence of operands and operators (`Seq`, `BodyType`, `Cond`, or one operand) as the
    /// term the precedences build, and the effect row written after it when no arrow takes it:
    /// `fn f(): A × B ! {e}`. A row binds to the last arrow, `(A) -> B ! {e}`.
    pub(super) fn sequence(
        &self,
        id: NodeId,
    ) -> (
        SurfaceTerm,
        Option<Vec<tauto_surface::surface::WrittenRowEffect>>,
    ) {
        let span = self.span(id);
        let mut pieces = Vec::new();
        let mut ops = Vec::new();
        let mut row = None;
        if matches!(self.nt(id), Some(Nt::Operand | Nt::CondOperand)) {
            pieces.push(self.piece(id));
        } else {
            for k in self.cst.children(id) {
                match self.nt(k) {
                    Some(Nt::Operand | Nt::CondOperand) => pieces.push(self.piece(k)),
                    Some(Nt::Op | Nt::CondOp | Nt::ArmTypeOp) => {
                        ops.push((sign(self.text(k).trim()).to_string(), self.span(k)))
                    }
                    Some(Nt::EffectRow) => row = Some(self.row_entries(k)),
                    _ => {}
                }
            }
        }
        if pieces.is_empty() || ops.len() + 1 != pieces.len() {
            return (self.other(id), None);
        }
        let arrow = ops.iter().rposition(|(o, _)| o == "->");
        let mut climb = Climb {
            reader: self,
            taken: vec![0; pieces.len()],
            pieces,
            ops,
            arrow,
            row: if arrow.is_some() {
                row.clone()
                    .map(|entries| entries.into_iter().map(|e| e.name).collect())
            } else {
                None
            },
        };
        let (parsed, _) = climb.climb(0, 0);
        let term = self.finish(parsed);
        let _ = span;
        (term, if arrow.is_some() { None } else { row })
    }

    /// An operand with `affine` or `linear` written before it, kept as the kind of its type.
    fn finish(&self, parsed: Part) -> SurfaceTerm {
        match parsed.kind {
            Some(kind) => {
                let span = parsed.term.span;
                self.fn_kind(kind, parsed.term, span)
            }
            None => parsed.term,
        }
    }

    fn fn_kind(&self, kind: NodeId, ty: SurfaceTerm, span: Span) -> SurfaceTerm {
        SurfaceTerm::new(
            TermKind::FnKind {
                kind: self.text(kind).trim().to_string(),
                ty: Box::new(ty),
            },
            span,
        )
    }

    fn borrowed(&self, borrow: NodeId, term: SurfaceTerm, span: Span) -> SurfaceTerm {
        SurfaceTerm::new(
            TermKind::Borrow {
                // `&`, `&mut` or `&orig`: the borrow's own words.
                mutable: self.text(borrow).split_whitespace().any(|w| w.ends_with("mut")),
                orig: self.text(borrow).contains("orig"),
                rc: self.text(borrow).starts_with("&rc"),
                term: Box::new(term),
            },
            span,
        )
    }

    fn tagged(&self, prefix: NodeId, term: SurfaceTerm, span: Span) -> SurfaceTerm {
        let tag = self
            .first(prefix, Nt::Ident)
            .map(|i| self.text(i).to_string())
            .unwrap_or_default();
        SurfaceTerm::new(
            TermKind::Tagged {
                tag,
                term: Box::new(term),
            },
            span,
        )
    }

    /// The names in an effect row; a row variable `| e` is `|e`. An entry
    /// with type arguments (`res(Pos)`, `∀ A. res(A)`) is a written effect:
    /// its name and its argument terms, which resolution binds.
    pub(super) fn row_names(&self, row: NodeId) -> Vec<Name> {
        self.row_entries(row).into_iter().map(|e| e.name).collect()
    }

    /// Row members as written, including an unused assertion `^` when present.
    pub(super) fn row_entries(&self, row: NodeId) -> Vec<tauto_surface::surface::WrittenRowEffect> {
        let mut literals = Vec::new();
        let mut variables = Vec::new();
        for set in self.all(row, Nt::EffectSet) {
            for term in self.all(set, Nt::EffectTerm) {
                match self.first(term, Nt::EffectLit) {
                    Some(lit) => literals.push(lit),
                    None => variables.extend(self.first(term, Nt::Ident)),
                }
            }
        }
        // `EffectName` sits under the named `EffectNames` list (members may
        // span lines); EBNF helpers of a one-line literal are inlined so a name
        // can also sit directly under `EffectLit`.
        let mut names: Vec<tauto_surface::surface::WrittenRowEffect> = literals
            .into_iter()
            .flat_map(|lit| {
                let mut found = Vec::new();
                self.collect_effect_names(lit, &mut found);
                found
            })
            .filter_map(|n| self.effect_entry(n))
            .collect();
        if let Some(var) = variables.first() {
            let span = self.span(*var);
            names.push(tauto_surface::surface::WrittenRowEffect {
                name: Name::from(format!("|{}", self.text(*var))),
                unused: None,
                span,
                members: None,
            });
        }
        names
    }

    /// Effect names under a row literal, including those under `EffectNames`.
    pub(super) fn collect_effect_names(&self, lit: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children_iter(lit) {
            match self.nt(c) {
                Some(Nt::EffectName) => out.push(c),
                Some(_) => self.collect_effect_names(c, out),
                None => {}
            }
        }
    }

    /// An effect name of a row or of a set's members: the name alone, or
    /// the name applied to its argument terms under the row's `∀`.
    pub(super) fn effect_entry(
        &self,
        n: NodeId,
    ) -> Option<tauto_surface::surface::WrittenRowEffect> {
        let unused = self.first(n, Nt::Caret).map(|c| self.span(c));
        let ident = self.first(n, Nt::Ident)?;
        let name = self.text(ident).into_owned();
        let span = self.span(n);
        let forall = self.first(n, Nt::EffectForall).map(|f| {
            self.all(f, Nt::Ident)
                .into_iter()
                .map(|i| self.text(i).into_owned())
                .collect::<Vec<_>>()
        });
        let arguments = self.first(n, Nt::TypeCall).map(|args| {
            self.all(args, Nt::TypeCallArg)
                .into_iter()
                .filter_map(|a| self.cst.children_iter(a).find(|c| self.nt(*c).is_some()))
                .map(|a| self.term(a))
                .collect::<Vec<_>>()
        });
        let name = if arguments.is_none() && forall.is_none() {
            Name::from(name)
        } else {
            Name::Written(std::sync::Arc::new(
                tauto_surface::identity::WrittenEffect::new(
                    name,
                    arguments.unwrap_or_default(),
                    forall.clone().unwrap_or_default(),
                    forall.is_some(),
                ),
            ))
        };
        Some(tauto_surface::surface::WrittenRowEffect {
            name,
            unused,
            span,
            members: None,
        })
    }

    /// `∀ x: A. B` and `∃ x: A. B`: the binder, with the body it takes.
    /// `∀ x: A, y: B. P` is `∀ x: A. ∀ y: B. P`, one binder per name, the first outermost.
    fn quantified(&self, binder: NodeId, body: SurfaceTerm) -> SurfaceTerm {
        let kids = self.cst.children(binder);
        let quantifier = kids.first().map(|k| self.text(*k));
        let quantifier = quantifier.as_deref().map_or("", str::trim);
        let binds: Vec<(Name, Option<Span>)> = kids
            .iter()
            .filter(|k| self.nt(**k) == Some(Nt::BindName))
            .map(|k| self.bind_name(*k))
            .collect();
        let binds = if binds.is_empty() {
            kids.iter()
                .filter(|k| self.nt(**k) == Some(Nt::Ident))
                .map(|k| (Name::Spelled(self.text(*k).to_string()), None))
                .collect()
        } else {
            binds
        };
        let domains: Vec<NodeId> = kids
            .iter()
            .copied()
            .filter(|k| self.nt(*k) == Some(Nt::Type))
            .collect();
        let start = self.span(binder).start;
        let span = Span::new(start, body.span.end);
        if binds.is_empty() || binds.len() != domains.len() {
            return SurfaceTerm::new(TermKind::Other("Binder".into()), span);
        }
        let mut body = body;
        for ((name, unused), domain) in binds.into_iter().zip(domains).rev() {
            body = self.quantified_one(quantifier, name, unused, self.term(domain), body, span);
        }
        body
    }

    fn quantified_one(
        &self,
        quantifier: &str,
        binder: Name,
        unused: Option<Span>,
        domain: SurfaceTerm,
        body: SurfaceTerm,
        span: Span,
    ) -> SurfaceTerm {
        if matches!(quantifier, "∃" | "\\exists") {
            SurfaceTerm::new(
                TermKind::Exists {
                    binder,
                    unused,
                    domain: Box::new(domain),
                    body: Box::new(body),
                },
                span,
            )
        } else {
            SurfaceTerm::new(
                TermKind::Pi {
                    params: vec![(Some(binder), domain)],
                    unused: vec![unused],
                    result: Box::new(body),
                    effects: None,
                },
                span,
            )
        }
    }

    fn expr(&self, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let parts: Vec<NodeId> = kids
            .iter()
            .copied()
            .filter(|k| {
                matches!(self.nt(*k), Some(nt) if !matches!(nt, Nt::Gap | Nt::FatArrow | Nt::ThinArrow))
            })
            .collect();
        if parts.iter().any(|k| self.nt(*k) == Some(Nt::Generated)) {
            // `=> fn a, theorem b` is read where a macro call statement or `decreasing_by` is.
            return SurfaceTerm::new(
                TermKind::Other("a list of generated declarations".into()),
                span,
            );
        }
        let [lhs, rhs] = parts.as_slice() else {
            return match parts.as_slice() {
                [only] => self.term(*only),
                _ => SurfaceTerm::new(TermKind::Other("Expr".into()), span),
            };
        };
        // The binder form `(&x) => e` is gone: a borrow is written in the
        // type, `(x: &T) => e`, or comes from the type the closure is
        // expected to have.
        let old_binder = std::cell::Cell::new(None);
        let param = |a: &SurfaceTerm| match &*a.kind {
            // Wild / placeholder `_` is not a binding Ident.
            TermKind::Var(name) if name.as_str() != "_" => Some((name.clone(), None)),
            TermKind::Borrow { mutable, term, .. } => match &*term.kind {
                TermKind::Var(name) if name.as_str() != "_" => {
                    old_binder.set(Some(*mutable));
                    Some((name.clone(), None))
                }
                _ => None,
            },
            _ => None,
        };
        // A lambda `Item`: `^x`, `^x: T`, or an ordinary `Expr [ : Type ]`.
        let item_param = |item: NodeId| -> Option<(Name, Option<bool>, Option<Span>)> {
            if let Some(caret) = self.first(item, Nt::Caret) {
                let ident = self.first(item, Nt::Ident)?;
                let name = Name::Spelled(self.text(ident).to_string());
                return Some((name, None, Some(self.span(caret))));
            }
            param(&self.term(item)).map(|(n, b)| (n, b, None))
        };
        let types: Vec<Option<SurfaceTerm>> = match self.sole_paren(*lhs) {
            Some(paren) => self
                .all(paren, Nt::Item)
                .into_iter()
                .map(|item| self.first(item, Nt::Type).map(|ty| self.term(ty)))
                .collect(),
            None => Vec::new(),
        };
        let types = if types.iter().any(Option::is_some) {
            types
        } else {
            Vec::new()
        };
        // `x: &T` borrows: the parameter is read with `T`, as a borrow.
        // `x: &rc T` takes the counted box as a value.
        let typed_borrows: Vec<Option<bool>> = types
            .iter()
            .map(|t| match t.as_ref().map(|t| &*t.kind) {
                Some(TermKind::Borrow { rc: false, mutable, .. }) => Some(*mutable),
                _ => None,
            })
            .collect();
        let types: Vec<Option<SurfaceTerm>> = types
            .into_iter()
            .map(|t| {
                t.map(|t| match &*t.kind {
                    TermKind::Borrow { rc: false, term, .. } => (**term).clone(),
                    _ => t,
                })
            })
            .collect();
        // `() => e` takes no parameter; `()` is nothing else, the unit being `#()`.
        let empty = self
            .sole_paren(*lhs)
            .is_some_and(|paren| self.all(paren, Nt::Item).is_empty());
        // `(x: A) => …` names its one parameter: the item is read without the type.
        // `(x, y) => …` names each item, a parenthesized list being no term of its own.
        let items = self
            .sole_paren(*lhs)
            .filter(|paren| {
                self.first(*paren, Nt::Comma).is_some()
                    || self
                        .all(*paren, Nt::Item)
                        .iter()
                        .any(|i| self.first(*i, Nt::Caret).is_some())
            })
            .map(|paren| self.all(paren, Nt::Item));
        let single_items = self.sole_paren(*lhs).map(|paren| self.all(paren, Nt::Item));
        let lhs_term = match &single_items {
            Some(items) if items.len() == 1 && !types.is_empty() => {
                if self.first(items[0], Nt::Caret).is_some() {
                    None
                } else {
                    Some(self.term(items[0]))
                }
            }
            _ => Some(self.term(*lhs)),
        };
        let params: Option<Vec<(Name, Option<bool>, Option<Span>)>> = match &items {
            _ if empty => Some(Vec::new()),
            Some(items) => items.iter().copied().map(item_param).collect(),
            None => match &single_items {
                Some(items) if items.len() == 1 && self.first(items[0], Nt::Caret).is_some() => {
                    item_param(items[0]).map(|p| vec![p])
                }
                _ => lhs_term
                    .as_ref()
                    .and_then(|t| param(t).map(|(n, b)| vec![(n, b, None)])),
            },
        };
        if let (Some(mutable), Some(_)) = (old_binder.get(), &params) {
            let message = if mutable {
                "`(&mut x) => e` is not a closure parameter: write `(x: &mut T) => e`, or `(x) => e` where the type says it borrows"
            } else {
                "`(&x) => e` is not a closure parameter: write `(x: &T) => e`, or `(x) => e` where the type says it borrows"
            };
            return SurfaceTerm::new(TermKind::Other(message.into()), span);
        }
        match params {
            Some(params) => {
                let borrows: Vec<Option<bool>> = params
                    .iter()
                    .enumerate()
                    .map(|(i, (_, b, _))| b.or(typed_borrows.get(i).copied().flatten()))
                    .collect();
                let unused_params: Vec<Option<Span>> = params.iter().map(|(_, _, u)| *u).collect();
                let lam = SurfaceTerm::new(
                    TermKind::Lam {
                        params: params.into_iter().map(|(n, _, _)| n).collect(),
                        body: Box::new(self.term(*rhs)),
                        types,
                        unused_params,
                    },
                    span,
                );
                if borrows.iter().all(Option::is_none) {
                    lam
                } else {
                    SurfaceTerm::new(
                        TermKind::BorrowLam {
                            borrows,
                            lam: Box::new(lam),
                        },
                        span,
                    )
                }
            }
            None => SurfaceTerm::new(TermKind::Other("Expr".into()), span),
        }
    }

    /// The node under the precedence levels that hold only it. An operand
    /// sits under every level of the grammar, and reading each level by
    /// recursion makes the depth of the reader grow with the levels times
    /// the nesting of the source, enough to overflow a thread's stack on a
    /// large program.
    fn through_levels(&self, id: NodeId) -> NodeId {
        let mut at = id;
        while let Some(
            Nt::Type
            | Nt::BodyType
            | Nt::Seq
            | Nt::Cond
            | Nt::Operand
            | Nt::CondOperand
            | Nt::Postfix
            | Nt::CondPostfix
            | Nt::Primary
            | Nt::CondPrimary
            | Nt::Brace
            | Nt::ArmBody
            | Nt::OperationType,
        ) = self.nt(at)
        {
            match self.cst.children(at).as_slice() {
                [only] => at = *only,
                _ => break,
            }
        }
        at
    }

    /// The parenthesized list `id` is, when it is nothing else.
    fn sole_paren(&self, id: NodeId) -> Option<NodeId> {
        let mut at = id;
        loop {
            if self.nt(at) == Some(Nt::Paren) {
                return Some(at);
            }
            match self.cst.children(at).as_slice() {
                [only] => at = *only,
                _ => return None,
            }
        }
    }

    /// A function-type parameter: `A`, `x: A`, or `^x: A`.
    fn fn_type_item(&self, item: NodeId) -> (Option<Name>, SurfaceTerm, Option<Span>) {
        if let Some(caret) = self.first(item, Nt::Caret) {
            let Some(ident) = self.first(item, Nt::Ident) else {
                return (None, self.term(item), None);
            };
            let name = Name::Spelled(unraw(self.text(ident).trim()).to_string());
            let ty = match self.first(item, Nt::Type) {
                Some(ty) => self.term(ty),
                None => SurfaceTerm::new(TermKind::Other("Type".into()), self.span(item)),
            };
            return (Some(name), ty, Some(self.span(caret)));
        }
        let (Some(name), Some(ty)) = (self.first(item, Nt::Expr), self.first(item, Nt::Type))
        else {
            return (None, self.term(item), None);
        };
        let ty = self.term(ty);
        match self.term(name).into_kind() {
            TermKind::Borrow { mutable, .. } => (
                None,
                SurfaceTerm::new(
                    TermKind::Borrow { orig: false, rc: false,
                        mutable,
                        term: Box::new(ty.clone()),
                    },
                    ty.span,
                ),
                None,
            ),
            TermKind::Var(name) => (Some(name), ty, None),
            _ => (None, ty, None),
        }
    }

    fn postfix(&self, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let Some((&primary, ops)) = kids.split_first() else {
            return SurfaceTerm::new(TermKind::Other("Postfix".into()), span);
        };
        let acc = self.term(primary);
        self.apply_post(acc, ops, span)
    }

    /// `f(<x: v>, h)`: the implicit arguments named, carried first as a record
    /// the elaborator places by the generics' names, as a pattern's
    /// `C<n: m>(…)` is. A `perform`'s are carried the same way.
    pub(super) fn call_implicits(&self, call: NodeId) -> Option<SurfaceTerm> {
        self.first(call, Nt::CallImplicits).map(|list| {
            let fields = self
                .all(list, Nt::CallImplicit)
                .into_iter()
                .filter_map(|i| {
                    let n = self.first(i, Nt::Ident)?;
                    let v = self.first(i, Nt::AngleExpr)?;
                    Some((unraw(self.text(n).trim()).to_string(), self.term(v)))
                })
                .collect();
            SurfaceTerm::new(
                TermKind::Record {
                    name: tauto_surface::IMPLICITS.into(),
                    fields,
                    base: None,
                },
                self.span(list),
            )
        })
    }

    fn apply_post(&self, mut acc: SurfaceTerm, ops: &[NodeId], _span: Span) -> SurfaceTerm {
        // `C(T)::m`, waiting for the call that gives the method's arguments:
        // the class's arguments, as the implicit record's leading fields.
        let mut member: Option<Vec<(String, SurfaceTerm)>> = None;
        for &op in ops {
            let Some(inner) = self.cst.children(op).into_iter().next() else {
                continue;
            };
            let end = self.span(op).end;
            let span = Span::new(acc.span.start, end);
            if member.is_some() && !matches!(self.nt(inner), Some(Nt::Call)) {
                return SurfaceTerm::new(
                    TermKind::Other(tauto_surface::CLASS_MEMBER_NOT_CALLED.into()),
                    span,
                );
            }
            acc = match self.nt(inner) {
                Some(Nt::Member) => {
                    let text = self.text(inner);
                    let text = text.trim();
                    let method = text.strip_prefix("::").unwrap_or(text);
                    match acc.into_kind() {
                        TermKind::App {
                            function,
                            arguments,
                        } if matches!(&*function.kind, TermKind::Var(_))
                            && !arguments.first().is_some_and(|a| {
                                matches!(&*a.kind, TermKind::Record { name, .. }
                                    if name.spelling() == Some(tauto_surface::IMPLICITS))
                            }) =>
                        {
                            let TermKind::Var(class) = &*function.kind else {
                                unreachable!()
                            };
                            member = Some(
                                arguments
                                    .into_iter()
                                    .enumerate()
                                    .map(|(i, a)| (tauto_surface::class_argument(i), a))
                                    .collect(),
                            );
                            SurfaceTerm::var(&format!("{class}::{method}"), span)
                        }
                        _ => {
                            return SurfaceTerm::new(
                                TermKind::Other(tauto_surface::CLASS_MEMBER_NOT_CLASS.into()),
                                span,
                            );
                        }
                    }
                }
                Some(Nt::Call) => {
                    let implicits = self.call_implicits(inner);
                    let implicits = match member.take() {
                        None => implicits,
                        Some(mut fields) => {
                            let at = implicits.as_ref().map_or(span, |i| i.span);
                            if let Some(TermKind::Record { fields: more, .. }) =
                                implicits.map(|i| i.into_kind())
                            {
                                fields.extend(more);
                            }
                            Some(SurfaceTerm::new(
                                TermKind::Record {
                                    name: tauto_surface::IMPLICITS.into(),
                                    fields,
                                    base: None,
                                },
                                at,
                            ))
                        }
                    };
                    let arguments = implicits
                        .into_iter()
                        .chain(self.all(inner, Nt::Item).into_iter().map(|i| self.term(i)))
                        .collect();
                    SurfaceTerm::new(
                        TermKind::App {
                            function: Box::new(acc),
                            arguments,
                        },
                        span,
                    )
                    .written_call()
                }
                Some(Nt::Field) => {
                    let name = self
                        .label_of(inner)
                        .map(|i| self.text(i).trim().to_string())
                        .unwrap_or_default();
                    SurfaceTerm::new(
                        TermKind::Field {
                            base: Box::new(acc),
                            name,
                        },
                        span,
                    )
                }
                _ => SurfaceTerm::new(TermKind::Other(inner_name(self, inner)), span),
            };
        }
        if member.is_some() {
            return SurfaceTerm::new(
                TermKind::Other(tauto_surface::CLASS_MEMBER_NOT_CALLED.into()),
                acc.span,
            );
        }
        acc
    }

    fn path(&self, id: NodeId, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let only_names = kids.iter().all(|k| matches!(self.nt(*k), Some(Nt::Ident)));
        if only_names {
            let name: String = kids
                .iter()
                .map(|k| self.text(*k).trim().to_owned())
                .collect();
            return SurfaceTerm::var(&name, span);
        }
        let name: String = kids
            .iter()
            .filter(|k| matches!(self.nt(**k), Some(Nt::Ident)))
            .map(|k| self.text(*k).trim().to_owned())
            .collect();
        // `F { }` is a struct without fields.
        let Some(body) = self.first(id, Nt::RecordBody) else {
            return self.other(id);
        };
        let mut inits = Vec::new();
        let mut base = None;
        self.push_field_inits(body, &mut inits, &mut base);
        let fields = inits
            .into_iter()
            .map(|f| {
                let field = self
                    .label_of(f)
                    .map(|i| self.text(i).trim().to_string())
                    .unwrap_or_default();
                let value = match self.first(f, Nt::Expr) {
                    Some(e) => self.term(e),
                    None => self.other(f),
                };
                (field, value)
            })
            .collect();
        let base = base
            .and_then(|b| self.first(b, Nt::Expr))
            .map(|e| Box::new(self.term(e)));
        SurfaceTerm::new(
            TermKind::Record {
                name: tauto_surface::identity::Name::Spelled(name),
                fields,
                base,
            },
            span,
        )
    }

    /// `{ a: A, b: B }`: the record type, the struct `@record.a.b` that
    /// `tauto_surface::records` declares, applied to the fields' types in the order of
    /// their names.
    fn record_type(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let mut decls = Vec::new();
        self.push_field_decls(id, &mut decls);
        let mut fields: Vec<(String, SurfaceTerm)> = decls
            .into_iter()
            .map(|f| {
                let name = self
                    .label_of(f)
                    .map(|i| self.text(i).trim().to_string())
                    .unwrap_or_default();
                let ty = match self.ty(f) {
                    Some(t) => self.term(t),
                    None => self.other(f),
                };
                (name, ty)
            })
            .collect();
        fields.sort_by(|a, b| a.0.cmp(&b.0));
        let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        if let Some(twice) = tauto_surface::records::repeated(&names) {
            return SurfaceTerm::new(
                TermKind::Other(tauto_surface::records::repeated_message(twice)),
                span,
            );
        }
        SurfaceTerm::app(
            &*tauto_surface::records::struct_name(&names),
            fields.into_iter().map(|(_, t)| t).collect(),
            span,
        )
    }

    fn push_field_decls(&self, node: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::FieldDecl) => out.push(c),
                Some(Nt::RecordTypeTail) => self.push_field_decls(c, out),
                _ => {}
            }
        }
    }

    /// `#{ a: 1, b: 2 }`: the literal of the struct `@record.a.b`, its fields
    /// evaluated in the order they are written.
    fn anon_record(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let mut inits = Vec::new();
        let mut base = None;
        self.push_field_inits(id, &mut inits, &mut base);
        if base.is_some() {
            return SurfaceTerm::new(
                TermKind::Other(tauto_surface::records::BASE_MESSAGE.into()),
                span,
            );
        }
        let fields: Vec<(String, SurfaceTerm)> = inits
            .into_iter()
            .map(|f| {
                let field = self
                    .label_of(f)
                    .map(|i| self.text(i).trim().to_string())
                    .unwrap_or_default();
                let value = match self.first(f, Nt::Expr) {
                    Some(e) => self.term(e),
                    None => self.other(f),
                };
                (field, value)
            })
            .collect();
        let mut names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
        names.sort();
        if let Some(twice) = tauto_surface::records::repeated(&names) {
            return SurfaceTerm::new(
                TermKind::Other(tauto_surface::records::repeated_message(twice)),
                span,
            );
        }
        let name = tauto_surface::records::struct_name(&names);
        SurfaceTerm::new(
            TermKind::Record {
                name: tauto_surface::identity::Name::Spelled(name),
                fields,
                base: None,
            },
            span,
        )
    }

    /// The fields of a record's body, and its `..b` when written.
    fn push_field_inits(&self, node: NodeId, out: &mut Vec<NodeId>, base: &mut Option<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::FieldInit) => out.push(c),
                Some(Nt::RecordBase) => *base = Some(c),
                Some(_) => self.push_field_inits(c, out, base),
                _ => {}
            }
        }
    }

    fn number(&self, id: NodeId, kids: &[NodeId], span: Span) -> SurfaceTerm {
        match kids
            .iter()
            .map(|k| self.nt(*k))
            .collect::<Vec<_>>()
            .as_slice()
        {
            [Some(Nt::Integer)] => {
                SurfaceTerm::new(TermKind::Nat(self.text(id).replace('_', "").into()), span)
            }
            [Some(Nt::Float | Nt::Decimal)] => {
                SurfaceTerm::new(TermKind::Float(self.text(id).into()), span)
            }
            _ => self.other(id),
        }
    }

    fn paren(&self, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let items: Vec<SurfaceTerm> = kids
            .iter()
            .filter(|k| self.nt(**k) == Some(Nt::Item))
            .map(|k| self.term(*k))
            .collect();
        let has_comma = kids.iter().any(|k| self.nt(*k) == Some(Nt::Comma));
        let written = kids
            .iter()
            .find(|k| self.nt(**k) == Some(Nt::Item))
            .and_then(|item| self.first(*item, Nt::Type));
        match (items.as_slice(), has_comma) {
            ([only], false) => match written {
                Some(ty) => SurfaceTerm::new(
                    TermKind::Ascribe {
                        term: Box::new(only.clone()),
                        ty: Box::new(self.term(ty)),
                    },
                    span,
                ),
                None => only.clone(),
            },
            // `()` is read as the unit `#()`.
            ([], false) => SurfaceTerm::unit(span),
            // `(a, b)` is not a term: a product is written `#(a, b)`, and a closure's
            // parameters are read from the list where they stand.
            _ => SurfaceTerm::new(TermKind::Other(PAREN_LIST.into()), span),
        }
    }

    /// `⟦and(or(x1, □), y)⟧`: the function `z => and(or(x1, z), y)`. The `□` is not under a
    /// binder written inside the brackets; written more than once, each stands for the same
    /// `z` (`⟦f(□, □)⟧` is `z => f(z, z)`). The parameter's name is one no program can write,
    /// so it captures nothing. Its type is the one the context expects.
    fn congr_expr(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let Some(inner) = self.first(id, Nt::Expr) else {
            return self.other(id);
        };
        let mut body = self.term(inner);
        let name = "congr@hole";
        let (mut found, mut bound) = (0usize, false);
        fill_box(&mut body, name, false, &mut found, &mut bound);
        let message = match (found, bound) {
            (0, _) => Some("`⟦ ⟧` without a `□`"),
            (_, false) => None,
            (_, true) => Some("`□` under a binder inside `⟦ ⟧`"),
        };
        if let Some(message) = message {
            return SurfaceTerm::new(TermKind::Other(message.into()), span);
        }
        SurfaceTerm::new(
            TermKind::Lam {
                params: vec![tauto_surface::identity::Name::Spelled(name.to_string())],
                body: Box::new(body),
                types: Vec::new(),
                unused_params: Vec::new(),
            },
            span,
        )
    }

    /// `[a, b]`: `Cons(a, Cons(b, Nil))`, the terms the constructors make,
    /// as a product is `Pair::Mk(…)`; `[a, ..r]` is `Cons(a, r)`, the rest in the
    /// place of `Nil`. Each cell spans from its item to the `]`.
    fn list_lit(&self, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let mut items: Vec<SurfaceTerm> = Vec::new();
        let mut tail = None;
        let mut next = kids
            .iter()
            .copied()
            .find(|k| self.nt(*k) == Some(Nt::ListItems));
        while let Some(at) = next {
            next = None;
            for c in self.cst.children(at) {
                match self.nt(c) {
                    Some(Nt::Expr) => items.push(self.term(c)),
                    Some(Nt::ListRest) => {
                        tail = self.first(c, Nt::Expr).map(|e| self.term(e));
                    }
                    Some(Nt::ListItems) => next = Some(c),
                    _ => {}
                }
            }
        }
        let tail = tail.unwrap_or_else(|| SurfaceTerm::var("Nil", span));
        items.into_iter().rev().fold(tail, |rest, item| {
            let cell = Span::new(item.span.start, span.end);
            SurfaceTerm::app("Cons", vec![item, rest], cell)
        })
    }

    /// `#(a, b)`: `Pair { fst: a, snd: b }`, and `#(a, b, c)` nests to the
    /// right as `A × B × C` does. `#()` is the unit.
    /// `#(a, b, …)` as written: the members are not spliced here, so that the
    /// program prints back as it is written.
    fn product_lit(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let items: Vec<SurfaceTerm> = self
            .all(id, Nt::Item)
            .into_iter()
            .map(|item| {
                // `#(a: A, b)`: a member at a written type, as `(a: A)` is.
                let term = self.term(item);
                match self.first(item, Nt::Type) {
                    Some(ty) => SurfaceTerm::new(
                        TermKind::Ascribe {
                            term: Box::new(term),
                            ty: Box::new(self.term(ty)),
                        },
                        self.span(item),
                    ),
                    None => term,
                }
            })
            .collect();
        match items.len() {
            0 => SurfaceTerm::unit(span),
            1 => self.other(id),
            _ => SurfaceTerm::product_value(items, span),
        }
    }

    fn macro_call(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let name = self
            .first(id, Nt::MacroName)
            .map(|b| self.text(b).trim().trim_end_matches('!').to_string())
            .unwrap_or_default();
        // `name!()` passes the unit.
        // `name!`x`` passes the syntax literal itself, as `name!(`x`)` does.
        let args = self.first(id, Nt::MacroCallGroup).unwrap_or(id);
        let arg = match (self.first(args, Nt::Expr), self.first(args, Nt::SyntaxLit)) {
            (Some(e), _) => self.term(e),
            (None, Some(lit)) => self.term(lit),
            (None, None) => SurfaceTerm::unit(span),
        };
        SurfaceTerm::new(
            TermKind::MacroCall {
                name,
                arg: Box::new(arg),
            },
            span,
        )
    }

    fn quote_expr(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let stmts = self
            .first(id, Nt::Ident)
            .is_some_and(|i| self.text(i) == "stmts");
        let body = self
            .first(id, Nt::Block)
            .and_then(|b| self.first(b, Nt::Stmts))
            .map(|s| self.collect_stmts(s))
            .unwrap_or_default()
            .into_iter()
            .map(|s| self.stmt(s))
            .collect();
        SurfaceTerm::new(TermKind::Quote { stmts, body }, span)
    }

    /// The block of a `BraceBody`: its statements are under `Stmts` after a `;`,
    /// else its own `Stmt` and `StmtsTail`.
    fn brace_block(&self, body: NodeId, span: Span) -> SurfaceTerm {
        if self.first(body, Nt::Stmts).is_some() {
            return self.block(body, span);
        }
        let mut stmts = Vec::new();
        self.push_stmts(body, &mut stmts);
        let read: Vec<Stmt> = self.stmts_of(&stmts);
        match read.as_slice() {
            [Stmt::Expr(only)] => only.clone(),
            _ => SurfaceTerm::new(TermKind::Block(read), span),
        }
    }

    /// A block holding one expression is that expression.
    fn block(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let stmts: Vec<NodeId> = self
            .first(id, Nt::Stmts)
            .map(|s| self.collect_stmts(s))
            .unwrap_or_default();
        let read: Vec<Stmt> = self.stmts_of(&stmts);
        match read.as_slice() {
            [Stmt::Expr(only)] => only.clone(),
            _ => SurfaceTerm::new(TermKind::Block(read), span),
        }
    }

    /// The `Stmt`s of `Stmts: … [ Stmt StmtsTail ]`, through the tails.
    fn collect_stmts(&self, stmts: NodeId) -> Vec<NodeId> {
        let mut out = Vec::new();
        self.push_stmts(stmts, &mut out);
        out
    }

    fn push_stmts(&self, node: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::Stmt) => out.push(c),
                Some(Nt::StmtsTail) => self.push_stmts(c, out),
                _ => {}
            }
        }
    }

    fn if_expr(&self, kids: &[NodeId], span: Span) -> SurfaceTerm {
        let cond = kids.iter().find(|k| self.nt(**k) == Some(Nt::Cond));
        let then = kids.iter().find(|k| self.nt(**k) == Some(Nt::Block));
        let otherwise = kids.iter().find(|k| self.nt(**k) == Some(Nt::ElseBranch));
        let (Some(cond), Some(then)) = (cond, then) else {
            return SurfaceTerm::new(TermKind::Other("IfExpr".into()), span);
        };
        let otherwise = otherwise.and_then(|e| self.cst.children(*e).into_iter().next());
        SurfaceTerm::new(
            TermKind::If {
                condition: Box::new(self.term(*cond)),
                then: Box::new(self.term(*then)),
                otherwise: otherwise.map(|o| Box::new(self.term(o))),
            },
            span,
        )
    }
}

fn inner_name(reader: &Reader<'_>, id: NodeId) -> String {
    reader
        .nt(id)
        .map(|k| k.to_string())
        .unwrap_or_else(|| "token".into())
}

/// The sign an ASCII escape stands for, `\times` for `×`.
fn sign(op: &str) -> &str {
    match op {
        "\\times" => "×",
        "\\land" => "∧",
        "\\lor" => "∨",
        "\\iff" => "↔",
        op => op,
    }
}

/// One operand of a sequence: its term with the prefixes that bind to it alone applied, the
/// parenthesized list it is when it is nothing else (a candidate for the parameters of `->`),
/// and the prefixes that stand before a whole sequence.
struct Piece {
    term: SurfaceTerm,
    paren: Option<NodeId>,
    /// `¬` and binders, the first written first.
    loose: Vec<NodeId>,
    kind: Option<NodeId>,
}

impl Piece {
    fn of(term: SurfaceTerm) -> Self {
        Piece {
            term,
            paren: None,
            loose: Vec::new(),
            kind: None,
        }
    }
}

/// How a run of one operator was built: `A | B | C` is one union.
#[derive(Clone, Copy, PartialEq)]
enum Flat {
    No,
    Union,
}

/// A term read from a part of a sequence, with what a later operator needs to know of it.
#[derive(Clone)]
struct Part {
    term: SurfaceTerm,
    paren: Option<NodeId>,
    kind: Option<NodeId>,
    flat: Flat,
}

#[derive(Clone, Copy, PartialEq)]
enum Assoc {
    Left,
    Right,
    /// `a = b = c` and `a ↔ b ↔ c` are refused.
    None,
}

/// The level of a binary operator and how it chains. From the loosest: `↔`, `->`, `∨ |`, `∧ ×`,
/// `=`, `||`, `&&`, the comparisons `== != < <= > >=`, `+ -`, `* /`.
fn level(op: &str) -> (u8, Assoc) {
    match op {
        "↔" => (0, Assoc::None),
        "->" => (1, Assoc::Right),
        "∨" | "|" => (2, Assoc::Right),
        "∧" | "×" => (3, Assoc::Right),
        "=" => (EQUAL, Assoc::None),
        "||" => (5, Assoc::Left),
        "&&" => (6, Assoc::Left),
        "==" | "!=" | "<" | "<=" | ">" | ">=" => (7, Assoc::None),
        "+" | "-" => (8, Assoc::Left),
        _ => (9, Assoc::Left),
    }
}

/// The level of `=`: the operand of `¬` is read at this level and above.
const EQUAL: u8 = 4;

struct Climb<'r, 'a> {
    reader: &'r Reader<'a>,
    pieces: Vec<Piece>,
    /// `ops[k]` stands between `pieces[k]` and `pieces[k + 1]`.
    ops: Vec<(String, Span)>,
    /// How many of each piece's `loose` prefixes are applied.
    taken: Vec<usize>,
    /// The index of the last `->`, which takes the effect row written after the sequence.
    arrow: Option<usize>,
    row: Option<Vec<Name>>,
}

impl Climb<'_, '_> {
    /// The operand at `k` and the operators of at least `min` after it. Returns the term and the
    /// index of the last operand it holds.
    fn climb(&mut self, k: usize, min: u8) -> (Part, usize) {
        let (mut lhs, mut k) = self.operand(k);
        while k < self.ops.len() {
            let (level_of, assoc) = level(&self.ops[k].0);
            if level_of < min {
                break;
            }
            let next = if assoc == Assoc::Right {
                level_of
            } else {
                level_of + 1
            };
            let (rhs, end) = self.climb(k + 1, next);
            lhs = self.combine(lhs, k, rhs);
            if assoc == Assoc::None && end < self.ops.len() && level(&self.ops[end].0).0 == level_of
            {
                let (op, at) = self.ops[end].clone();
                let span = Span::new(lhs.term.span.start, at.end);
                // `f<T>(x)` reads as `f < T > (x)`: say how a type is passed instead.
                let message = if self.ops[k].0 == "<" && op == ">" {
                    "`f<T>(x)` reads as the comparisons `f < T > (x)`: a call does not take type \
                     arguments, as `<…>` declares implicit arguments, which are inferred from the \
                     explicit ones; write the call without them (`f(x)`)"
                        .to_string()
                } else {
                    format!("`{op}` after a chain")
                };
                lhs = Part {
                    term: SurfaceTerm::new(TermKind::Other(message), span),
                    paren: None,
                    kind: None,
                    flat: Flat::No,
                };
                return (lhs, self.pieces.len() - 1);
            }
            k = end;
        }
        (lhs, k)
    }

    /// The operand at `k`, with the prefixes written before it that take a sequence.
    fn operand(&mut self, k: usize) -> (Part, usize) {
        let at = self.taken[k];
        if let Some(&prefix) = self.pieces[k].loose.get(at) {
            self.taken[k] += 1;
            // `¬` takes `=` and what binds tighter; a binder takes all that follows.
            let (inner, end) = self.climb(
                k,
                if self.reader.nt(prefix) == Some(Nt::Binder) {
                    0
                } else {
                    EQUAL
                },
            );
            let body = self.reader.finish(inner);
            let term = match self.reader.nt(prefix) {
                Some(Nt::Binder) => self.reader.quantified(prefix, body),
                _ => {
                    let span = Span::new(self.reader.span(prefix).start, body.span.end);
                    // `¬P` is `(P) -> False`: the kernel receives the function type.
                    SurfaceTerm::new(
                        TermKind::Pi {
                            params: vec![(None, body)],
                            result: Box::new(SurfaceTerm::var("False", span)),
                            effects: None,
                            unused: Vec::new(),
                        },
                        span,
                    )
                }
            };
            return (
                Part {
                    term,
                    paren: None,
                    kind: None,
                    flat: Flat::No,
                },
                end,
            );
        }
        let piece = &self.pieces[k];
        (
            Part {
                term: piece.term.clone(),
                paren: piece.paren,
                kind: piece.kind,
                flat: Flat::No,
            },
            k,
        )
    }

    fn combine(&mut self, lhs: Part, k: usize, rhs: Part) -> Part {
        let op = self.ops[k].0.clone();
        if op == "->" {
            return self.arrow(lhs, k, rhs);
        }
        let lhs = self.reader.finish(lhs);
        let flat_rhs = rhs.flat;
        let rhs = self.reader.finish(rhs);
        let span = Span::new(lhs.span.start, rhs.span.end);
        let chained = |lhs: SurfaceTerm, rhs: SurfaceTerm| {
            let mut members = vec![lhs];
            match (&*rhs.kind, flat_rhs == Flat::Union) {
                (TermKind::Union(rest), true) => members.extend(rest.iter().cloned()),
                _ => members.push(rhs),
            }
            TermKind::Union(members)
        };
        let (term, flat) = match op.as_str() {
            "|" => (SurfaceTerm::new(chained(lhs, rhs), span), Flat::Union),
            // `A × B × C` is `A × (B × C)`: `×` binds to the right.
            "×" => (SurfaceTerm::pair_type(lhs, rhs, span), Flat::No),
            "∧" => (SurfaceTerm::app("And", vec![lhs, rhs], span), Flat::No),
            "∨" => (SurfaceTerm::app("Or", vec![lhs, rhs], span), Flat::No),
            "↔" => (SurfaceTerm::app("Iff", vec![lhs, rhs], span), Flat::No),
            op => (SurfaceTerm::app(op, vec![lhs, rhs], span), Flat::No),
        };
        Part {
            term,
            paren: None,
            kind: None,
            flat,
        }
    }

    /// `(x: A, y: &B) -> C`: the parenthesized left is read as a parameter list. A parameter
    /// `x: A` is of type `A` and binds `x` in the later parameters and the result; `&x: A` is `A`
    /// borrowed. An operand that is not a parenthesized list is the one parameter, unnamed.
    fn arrow(&mut self, lhs: Part, k: usize, rhs: Part) -> Part {
        let kind = lhs.kind;
        let (params, unused) = match lhs.paren {
            Some(paren) => {
                let items: Vec<_> = self
                    .reader
                    .all(paren, Nt::Item)
                    .into_iter()
                    .map(|item| self.reader.fn_type_item(item))
                    .collect();
                let unused: Vec<_> = items.iter().map(|(_, _, u)| *u).collect();
                let params: Vec<_> = items.into_iter().map(|(n, t, _)| (n, t)).collect();
                (params, unused)
            }
            None => (vec![(None, lhs.term.clone())], Vec::new()),
        };
        let unused = if unused.iter().all(Option::is_none) {
            Vec::new()
        } else {
            unused
        };
        let result = self.reader.finish(rhs);
        let span = Span::new(lhs.term.span.start, result.span.end);
        let effects = if self.arrow == Some(k) {
            self.row.take()
        } else {
            None
        };
        let term = SurfaceTerm::new(
            TermKind::Pi {
                params,
                result: Box::new(result),
                effects,
                unused,
            },
            span,
        );
        let term = match kind {
            Some(kind) => self.reader.fn_kind(kind, term, span),
            None => term,
        };
        Part {
            term,
            paren: None,
            kind: None,
            flat: Flat::No,
        }
    }
}
