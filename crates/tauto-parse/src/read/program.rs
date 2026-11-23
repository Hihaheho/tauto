#![allow(unused_imports)]
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use super::*;
use tauto_message::{Message, msg};
use tauto_parol::{Cst, NodeId, NodeKind, NonTerminalKind as Nt, Parsed, TerminalKind, parse};
use tauto_surface::span::Span;
use tauto_surface::surface::fence::Comment;
use tauto_surface::surface::qualify::SEPARATOR;
use tauto_surface::surface::*;

/// The program as written, without running macros, its
/// modules resolved. This is what `totes/surface` reads, so what the
/// self-hosted checkers are compared on.
pub fn parse_program_as_written(source: &str) -> Result<Program, String> {
    crate::install();
    parse_program_as_written_at(source, 0)
}

pub fn parse_program_as_written_at(source: &str, base: u32) -> Result<Program, String> {
    crate::install();
    as_written(parse_program_unresolved_at(source, base)?)
}

/// [`parse_program_as_written_at`] of a text built into the binary, read once
/// per process ([`parse_builtin_at`]).
pub fn parse_builtin_as_written_at(source: &'static str, base: u32) -> Result<Program, String> {
    as_written(parse_builtin_at(source, base)?)
}

fn as_written(mut program: Program) -> Result<Program, String> {
    // Resolving reads the standard library through the reader: a caller
    // that reads a program need not have installed it first.
    crate::install();
    let (stmts, mut errors) = super::modules::resolve(std::mem::take(&mut program.stmts));
    errors.extend(std::mem::take(&mut program.errors));
    program.stmts = stmts;
    program.errors = errors;
    tauto_surface::resolve::host_budgets_as_written(&mut program.stmts);
    Ok(program)
}

/// An expression written alone, with spans from `base`: what a syntax's
/// `${ … }` holds.
pub fn parse_expr_at(source: &str, base: u32) -> Result<SurfaceTerm, String> {
    crate::install();
    let program = parse_program_unresolved_at(source, base)?;
    match program.stmts.as_slice() {
        [Stmt::Expr(t)] => Ok(t.clone()),
        _ => Err(msg!("surface-expected-one-expression").to_string()),
    }
}

/// A program with the modules left as written: a program of
/// several files resolves them once all its files are read.
pub fn parse_program_unresolved_at(source: &str, base: u32) -> Result<Program, String> {
    crate::install();
    parse_program_located_at(source, base).map_err(|e| e.to_string())
}

/// [`parse_program_unresolved_at`] of a text built into the binary (the
/// prelude, the kernel's prelude, the standard library): it is read once per
/// process, and each caller gets its own copy, its terms distinct occurrences
/// as if read again. A run reads the same prelude texts in many places and on
/// several threads; each of them parsed the whole text anew.
pub fn parse_builtin_at(source: &'static str, base: u32) -> Result<Program, String> {
    type Read = std::sync::Arc<Result<Program, String>>;
    // Keyed by the text, not where it is: a `const` text may be at a
    // different address in each crate that names it.
    static READ: Mutex<Option<HashMap<(&'static str, u32), Read>>> = Mutex::new(None);
    let key = (source, base);
    let found = READ
        .lock()
        .unwrap()
        .as_ref()
        .and_then(|read| read.get(&key).cloned());
    let read = match found {
        Some(read) => read,
        None => {
            // The lock is not held while reading: reading may read a builtin text.
            let read: Read =
                std::sync::Arc::new(read_program_at(source, base).map_err(|e| e.to_string()));
            READ.lock()
                .unwrap()
                .get_or_insert_default()
                .entry(key)
                .or_insert(read)
                .clone()
        }
    };
    let mut program = (*read).clone()?;
    for stmt in &mut program.stmts {
        super::walk::stmt(stmt, &mut SurfaceTerm::freshen);
    }
    Ok(program)
}

/// [`parse_program_unresolved_at`] with the place of a failure as data.
pub fn parse_program_located_at(source: &str, base: u32) -> Result<Program, ParseError> {
    crate::install();
    if !tauto_surface::surface::parsed::kept() {
        return read_program_at(source, base);
    }
    tauto_surface::surface::parsed::get_or_read(source, base, || read_program_at(source, base))
}

fn read_program_at(source: &str, base: u32) -> Result<Program, ParseError> {
    let failed = |message: String, at: Option<u32>| ParseError {
        message,
        at: at.map(|a| (base as u64 + a as u64) as u32),
    };
    let parsed = parse(source);
    if let Some(e) = parsed.errors.first() {
        let at = e.span.map(|s| s.start as u32);
        // `extern "rust" { … }`: the rust path is not written in the source.
        let after_extern = e.span.is_some_and(|s| {
            source[..(s.start as usize).min(source.len())]
                .trim_end()
                .ends_with("extern")
        });
        if after_extern {
            return Err(failed(msg!("surface-extern-rust-path").to_string(), at));
        }
        return Err(failed(e.message.to_string(), at));
    }
    let mut reader = Reader::new(&parsed, source);
    reader.base = base;
    let root = parsed
        .cst
        .root()
        .ok_or_else(|| failed("empty parse".to_string(), None))?;
    if let Some(at) = reader.bare_kind(root) {
        return Err(failed(
            msg!(
                "surface-bare-kind",
                kind = source[at.0 as usize..at.1 as usize].trim(),
                written = match source[at.0 as usize..at.1 as usize].trim() {
                    "copy" => "Copy",
                    "shared" => "Shared",
                    "linear" => "Linear",
                    _ => "Type",
                }
            )
            .to_string(),
            Some(at.0 as u32),
        ));
    }
    if let Some((at, message)) = reader.refused_form(root) {
        return Err(failed(message.to_string(), Some(at as u32)));
    }
    let mut stmts = Vec::new();
    if let Some(program) = reader.find(root, Nt::Program)
        && let Some(list) = reader.first(program, Nt::Stmts)
    {
        for s in reader.collect_stmts(list) {
            reader.read_into(&mut stmts, s);
        }
    }
    Ok(Program {
        stmts,
        errors: Vec::new(),
    })
}

/// Pushes `stmt`, and before an `extern` block the structs of its opaque
/// types and the `struct`/`enum` of a replaceable block.
fn push_stmt(stmts: &mut Vec<Stmt>, stmt: Stmt) {
    if let Stmt::Extern {
        types,
        structs,
        enums,
        ..
    } = &stmt
    {
        stmts.extend(types.iter().cloned().map(Stmt::Struct));
        stmts.extend(structs.iter().cloned().map(Stmt::Struct));
        stmts.extend(enums.iter().cloned().map(Stmt::Enum));
    }
    stmts.push(stmt);
}

impl Reader<'_> {
    pub(super) fn find(&self, id: NodeId, kind: Nt) -> Option<NodeId> {
        for c in self.cst.children(id) {
            if self.nt(c) == Some(kind) {
                return Some(c);
            }
            if let Some(f) = self.find(c, kind) {
                return Some(f);
            }
        }
        None
    }

    /// Every node of `kind` below `id`, not looking inside one found.
    /// [`Reader::descend`] for several kinds in one walk: `out[i]` gets the nodes of
    /// `kinds[i]`, the outermost of each kind, in order.
    fn descend_kinds<const N: usize>(&self, id: NodeId, kinds: [Nt; N]) -> [Vec<NodeId>; N] {
        fn walk<const N: usize>(
            r: &Reader<'_>,
            id: NodeId,
            kinds: &[Nt; N],
            below: [bool; N],
            out: &mut [Vec<NodeId>; N],
        ) {
            for c in r.cst.children_iter(id) {
                let Some(k) = r.nt(c) else { continue };
                let mut inner = below;
                for (i, kind) in kinds.iter().enumerate() {
                    if *kind == k && !below[i] {
                        out[i].push(c);
                        inner[i] = true;
                    }
                }
                if inner.iter().any(|b| !b) {
                    walk(r, c, kinds, inner, out);
                }
            }
        }
        let mut out = std::array::from_fn(|_| Vec::new());
        walk(self, id, &kinds, [false; N], &mut out);
        out
    }

    fn descend(&self, id: NodeId, kind: Nt, out: &mut Vec<NodeId>) {
        for c in self.cst.children_iter(id) {
            match self.nt(c) {
                Some(k) if k == kind => out.push(c),
                Some(_) => self.descend(c, kind, out),
                None => {}
            }
        }
    }

    /// The statements of a block. A `let` with a pattern is the `match` of its
    /// value with that one arm, whose body is the statements after it, so the
    /// elaborator sees the `match` written by hand.
    pub(super) fn stmts_of(&self, nodes: &[NodeId]) -> Vec<Stmt> {
        let mut out = Vec::new();
        for (at, node) in nodes.iter().enumerate() {
            let Some(decl) = self.pattern_let(*node) else {
                out.push(self.stmt(*node));
                continue;
            };
            let rest = self.stmts_of(&nodes[at + 1..]);
            let span = Span::new(
                self.span(*node).start,
                rest.last().map_or(self.span(*node).end, |_| {
                    self.span(*nodes.last().unwrap_or(node)).end
                }),
            );
            let body = match rest.as_slice() {
                [Stmt::Expr(only)] => only.clone(),
                _ => SurfaceTerm::new(TermKind::Block(rest), span),
            };
            let value = self
                .first(decl, Nt::Expr)
                .map(|e| self.term(e))
                .unwrap_or_else(|| self.other(decl));
            // `let #(a, b): T := e`: the scrutinee's type, as `match e: T` writes it.
            let scrutinee = match self.ty(decl) {
                Some(ty) => SurfaceTerm::new(
                    TermKind::Ascribe {
                        term: Box::new(value),
                        ty: Box::new(self.term(ty)),
                    },
                    self.span(decl),
                ),
                None => value,
            };
            let pattern = self.let_pattern(decl);
            out.push(Stmt::Expr(SurfaceTerm::new(
                TermKind::Match {
                    scrutinee: Box::new(scrutinee),
                    result: None,
                    binder: None,
                    binder_unused: None,
                    arms: vec![MatchArm {
                        pattern,
                        guard: None,
                        goal: None,
                        body,
                    }],
                },
                span,
            )));
            break;
        }
        out
    }

    /// The `LetPatDecl` a statement is, when it has no attribute or visibility.
    fn pattern_let(&self, stmt: NodeId) -> Option<NodeId> {
        if self.first(stmt, Nt::Attribute).is_some() || self.first(stmt, Nt::Visibility).is_some() {
            return None;
        }
        let other = self.first(stmt, Nt::OtherStmt)?;
        let inner = self.cst.children(other).into_iter().next()?;
        (self.nt(inner) == Some(Nt::LetDecl)
            && self.first(inner, Nt::LetProps).is_none()
            && self.has_let_pattern(inner))
        .then_some(inner)
    }

    /// A `let` that is written with a pattern, not a name alone.
    fn has_let_pattern(&self, decl: NodeId) -> bool {
        self.first(decl, Nt::LetPattern).is_some()
            || self.first(decl, Nt::PatternArgs).is_some()
            || self.first(decl, Nt::PatternImplicits).is_some()
    }

    fn let_pattern(&self, decl: NodeId) -> Pattern {
        match self.first(decl, Nt::LetPattern) {
            Some(p) => self.pattern_alt(p),
            None => self.path_pattern(decl),
        }
    }

    fn name_of(&self, id: NodeId) -> String {
        self.text(id).to_string()
    }

    /// A binding name `[Caret] Ident`: the spelled name and where `^` is written.
    /// Rejects a name that is only `_` (the Wild token is not an Ident here).
    pub(super) fn bind_name(&self, id: NodeId) -> (Name, Option<Span>) {
        let bind = if self.nt(id) == Some(Nt::BindName) {
            id
        } else {
            self.first(id, Nt::BindName).unwrap_or(id)
        };
        let unused = self
            .first(bind, Nt::Caret)
            .or_else(|| self.first(id, Nt::Caret))
            .map(|c| self.span(c));
        let ident = self
            .first(bind, Nt::Ident)
            .or_else(|| self.first(id, Nt::Ident));
        let spelling = ident
            .map(|i| {
                let t = self.text(i);
                super::unraw(t.trim()).to_string()
            })
            .unwrap_or_default();
        (Name::Spelled(spelling), unused)
    }

    /// `BindName` under `parent`, or none when absent.
    fn bind_name_of(&self, parent: NodeId) -> Option<(Name, Option<Span>)> {
        self.first(parent, Nt::BindName)
            .or_else(|| self.first(parent, Nt::FnName))
            .map(|b| self.bind_name(b))
    }

    fn infer_condition(&self, node: NodeId) -> InferCondition {
        match self.nt(node) {
            Some(Nt::InferOr | Nt::InferAnd) => {
                let part = if self.nt(node) == Some(Nt::InferOr) {
                    Nt::InferAnd
                } else {
                    Nt::InferAtom
                };
                let mut children = Vec::new();
                self.descend(node, part, &mut children);
                let mut terms = children.into_iter();
                let mut result =
                    self.infer_condition(terms.next().expect("infer condition operand"));
                for term in terms {
                    let next = Box::new(self.infer_condition(term));
                    result = if part == Nt::InferAnd {
                        InferCondition::Or(Box::new(result), next)
                    } else {
                        InferCondition::And(Box::new(result), next)
                    };
                }
                result
            }
            Some(Nt::InferAtom) => {
                if let Some(name) = self.first(node, Nt::Ident) {
                    InferCondition::Parameter(Name::from(self.name_of(name)))
                } else {
                    self.infer_condition(
                        self.first(node, Nt::InferOr)
                            .expect("parenthesized infer condition"),
                    )
                }
            }
            _ => unreachable!("infer condition node"),
        }
    }

    pub(super) fn stmt(&self, id: NodeId) -> Stmt {
        let attrs: Vec<NodeId> = self
            .cst
            .children_iter(id)
            .filter(|c| self.nt(*c) == Some(Nt::Attribute))
            .collect();
        // Attributes written one after another each take the declaration as written; they nest,
        // the first written outermost.
        let mut stmt = self.visible_stmt(id);
        for attr in attrs.into_iter().rev() {
            stmt = self.attributed(id, attr, stmt);
        }
        stmt
    }

    fn attributed(&self, id: NodeId, attr: NodeId, stmt: Stmt) -> Stmt {
        let span = self.span(id);
        let (name, arg) = match self
            .first(attr, Nt::MacroCall)
            .map(|c| self.term(c).kind.clone())
        {
            Some(kind) => match &*kind {
                TermKind::MacroCall { name, arg } => (name.clone(), (**arg).clone()),
                _ => return Stmt::Other("Attribute".into(), span),
            },
            _ => return Stmt::Other("Attribute".into(), span),
        };
        let list = self.first(attr, Nt::AttrGenerates);
        let mut generates = self.generates_clause(
            list,
            self.first(attr, Nt::MacroCall)
                .map_or(span.end, |c| self.span(c).end),
        );
        let replace = list.and_then(|l| self.replace_of(l, &mut generates));
        Stmt::Attributed {
            name,
            arg,
            generates,
            replace,
            stmt: Box::new(stmt),
            span: self.span(attr),
        }
    }

    /// Pushes the statements `id` is: a `macro fn m(…) … { … }` is the function `m` and the registration
    /// of `m` as a macro, in that order.
    pub(super) fn read_into(&self, out: &mut Vec<Stmt>, id: NodeId) {
        let macro_fn = if self.first(id, Nt::Attribute).is_none() {
            self.first(id, Nt::OtherStmt)
                .and_then(|o| self.cst.children(o).into_iter().next())
                .filter(|inner| self.nt(*inner) == Some(Nt::MacroFnDecl))
        } else {
            None
        };
        let Some(inner) = macro_fn else {
            push_stmt(out, self.stmt(id));
            return;
        };
        let span = self.span(id);
        let Some(decl) = self.first(inner, Nt::FnDecl) else {
            out.push(Stmt::Other("macro fn".into(), span));
            return;
        };
        let function = self.fn_decl(decl);
        let name = match &function {
            Stmt::Fn(f) => f.name.clone(),
            _ => tauto_surface::identity::Name::Spelled(String::new()),
        };
        let visibility = self.first(id, Nt::Visibility);
        let function = match visibility {
            Some(v) => with_vis(function, self.vis(v), self.span(v)),
            None => function,
        };
        out.push(function);
        out.push(Stmt::Macro {
            function: name.to_string(),
            name: name.to_string(),
            public: visibility.is_some(),
            span,
        });
    }

    /// `syntax!(name, ```par … ```, with(fmt: f, tokens: g)) => struct a, …` and `inductive_syntax!(…)`.
    fn syntax_decl(&self, inner: NodeId, span: Span) -> Stmt {
        let exprs = self.all(inner, Nt::Expr);
        let [name_expr, grammar_expr] = exprs.as_slice() else {
            return Stmt::Other("SyntaxDecl".into(), span);
        };
        let name = self
            .find(*name_expr, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        let Some(lit) = self.find(*grammar_expr, Nt::SyntaxLit) else {
            return Stmt::Other("SyntaxDecl".into(), span);
        };
        let uses = self
            .first(inner, Nt::SyntaxWith)
            .map(|with| self.all(with, Nt::Item))
            .unwrap_or_default()
            .into_iter()
            .map(|u| {
                let mut names = Vec::new();
                self.descend(u, Nt::Ident, &mut names);
                SyntaxUse {
                    role: names.first().map(|n| self.name_of(*n)).unwrap_or_default(),
                    function: tauto_surface::identity::Name::Spelled(
                        names.get(1).map(|n| self.name_of(*n)).unwrap_or_default(),
                    ),
                    span: self.span(u),
                }
            })
            .collect();
        Stmt::Syntax {
            inductive: self.descend_first(inner, Nt::KwInductiveSyntaxMacro),
            name,
            generates: self.generates_clause(
                self.first(inner, Nt::Generates),
                self.first(inner, Nt::RParen)
                    .map_or(span.end, |p| self.span(p).end),
            ),
            uses,
            grammar: self.lit(lit),
            span,
        }
    }

    /// The word written before the first item of an attribute's list (`=> replace fn f, …`): that item is the
    /// declaration the macro changes, and is taken out of `generates`.
    fn replace_of(&self, list: NodeId, generates: &mut Generates) -> Option<Replace> {
        let word = self.all(list, Nt::Ident).into_iter().next()?;
        let first = self.all(list, Nt::Generated).into_iter().next()?;
        if self.span(word).start >= self.span(first).start {
            return None;
        }
        if generates.items.is_empty() {
            return None;
        }
        let (kind, name) = generates.items.remove(0);
        Some(Replace {
            word: self.name_of(word),
            kind,
            name: tauto_surface::identity::Name::Spelled(name),
            at: Span::new(self.span(word).start, self.span(first).end),
        })
    }

    fn visible_stmt(&self, id: NodeId) -> Stmt {
        let stmt = self.plain_stmt(id);
        match self.first(id, Nt::Visibility) {
            Some(v) => with_vis(stmt, self.vis(v), self.span(v)),
            None => stmt,
        }
    }

    fn vis(&self, v: NodeId) -> Vis {
        if self.descend_first(v, Nt::KwPubOpen) {
            Vis::Open
        } else if self.descend_first(v, Nt::KwPubHandle) {
            Vis::Handle
        } else {
            Vis::Pub
        }
    }

    fn descend_first(&self, id: NodeId, kind: Nt) -> bool {
        let mut found = Vec::new();
        self.descend(id, kind, &mut found);
        !found.is_empty()
    }

    fn plain_stmt(&self, id: NodeId) -> Stmt {
        let span = self.span(id);
        let Some(other) = self.first(id, Nt::OtherStmt) else {
            return Stmt::Other("Stmt".into(), span);
        };
        let Some(inner) = self.cst.children(other).into_iter().next() else {
            return Stmt::Other("OtherStmt".into(), span);
        };
        let kind = self.nt(inner);
        let ident = |s: &Self| {
            s.first(inner, Nt::Ident)
                .map(|i| s.name_of(i))
                .unwrap_or_default()
        };
        let expr = |s: &Self| {
            s.first(inner, Nt::Expr)
                .map(|e| s.term(e))
                .unwrap_or_else(|| s.other(inner))
        };
        match kind {
            // A pattern is read by `stmts_of`, in a block; anywhere else it is no statement.
            Some(Nt::LetDecl) if self.has_let_pattern(inner) => {
                Stmt::Other("let pattern".into(), span)
            }
            Some(Nt::LetDecl) => {
                let (name, unused) = self
                    .bind_name_of(inner)
                    .unwrap_or_else(|| (Name::Spelled(ident(self)), None));
                Stmt::Let {
                    name,
                    ty: self.ty(inner).map(|t| self.term(t)),
                    value: expr(self),
                    borrow: false,
                    borrow_mut: false,
                    stack: self.let_props(inner),
                    unused,
                }
            }
            Some(Nt::VarDecl) => {
                let (name, unused) = self
                    .bind_name_of(inner)
                    .unwrap_or_else(|| (Name::Spelled(ident(self)), None));
                Stmt::Var {
                    name,
                    // A `&mut` binding writes through to what it borrows and is
                    // never rebound, so it cannot be a `var`.
                    ty: self.ty(inner).map(|t| self.term(t)).map(|t| {
                        if matches!(&*t.kind, TermKind::Borrow { mutable: true, .. }) {
                            SurfaceTerm::new(
                                TermKind::Other(
                                    "`var x: &mut T`: a `&mut` binding cannot be `var`".into(),
                                ),
                                t.span,
                            )
                        } else {
                            t
                        }
                    }),
                    value: expr(self),
                    borrow: false,
                    stack: self.let_props(inner),
                    unused,
                }
            }
            Some(Nt::FnDecl) => self.fn_decl(inner),
            Some(Nt::TheoremDecl | Nt::AxiomDecl) => self.theorem_decl(inner, span),
            Some(Nt::DefDecl) => self.def_decl(inner, span),
            Some(Nt::MutualDecl) => {
                let mut nodes = Vec::new();
                self.push_mutual(inner, &mut nodes);
                let items = nodes
                    .into_iter()
                    .filter_map(|item| {
                        let member = self.first(item, Nt::MutualMember)?;
                        let decl = self.cst.children(member).into_iter().next()?;
                        let sp = self.span(decl);
                        let stmt = match self.nt(decl) {
                            Some(Nt::InductiveDecl) => self.inductive_decl(decl, sp),
                            Some(Nt::FnDecl) => self.fn_decl(decl),
                            Some(Nt::TheoremDecl) => self.theorem_decl(decl, sp),
                            _ => return None,
                        };
                        Some(match self.first(item, Nt::Visibility) {
                            Some(v) => with_vis(stmt, self.vis(v), self.span(v)),
                            None => stmt,
                        })
                    })
                    .collect();
                Stmt::Mutual { items, span }
            }
            Some(Nt::ModuleDecl) => {
                let items = self
                    .first(inner, Nt::Block)
                    .and_then(|b| self.first(b, Nt::Stmts))
                    .map(|list| {
                        let mut items = Vec::new();
                        for s in self.collect_stmts(list) {
                            self.read_into(&mut items, s);
                        }
                        items
                    })
                    .unwrap_or_default();
                Stmt::Module {
                    name: ident(self),
                    vis: Vis::Private,
                    items,
                    span,
                }
            }
            Some(Nt::ImportDecl) => {
                // `{ Text, concat }`: the names the import brings.
                let names = self.first(inner, Nt::ImportList).map(|list| {
                    let mut idents = Vec::new();
                    self.descend(list, Nt::Ident, &mut idents);
                    idents
                        .into_iter()
                        .map(|i| (self.name_of(i), self.span(i)))
                        .collect::<Vec<_>>()
                });
                match self.first(inner, Nt::Text) {
                    Some(t) => Stmt::Import {
                        path: super::unquote_text(&self.text(t)),
                        module: false,
                        names,
                        span,
                    },
                    // `import std::list` is kept as the path `std::list`.
                    None => Stmt::Import {
                        path: self
                            .all(inner, Nt::Ident)
                            .into_iter()
                            .map(|i| self.text(i).to_string())
                            .collect::<Vec<_>>()
                            .join(SEPARATOR),
                        module: true,
                        names,
                        span,
                    },
                }
            }
            Some(Nt::SyntaxDecl) => self.syntax_decl(inner, span),
            // Read as the function and its registration by `read_into`.
            Some(Nt::MacroFnDecl) => Stmt::Other("macro fn".into(), span),
            Some(Nt::InductiveDecl) => self.inductive_decl(inner, span),
            Some(Nt::EffectDecl) => self.effect_decl(inner),
            Some(Nt::StructDecl) => Stmt::Struct(self.struct_decl(inner)),
            Some(Nt::EnumDecl) => Stmt::Enum(self.enum_decl(inner)),
            Some(Nt::ClassDecl) => {
                let (generics, bounds) = self.generic_bounds(inner);
                let mut methods = Vec::new();
                self.descend(inner, Nt::ExternFn, &mut methods);
                Stmt::Class(ClassDecl {
                    parents: self.where_clause(inner),
                    parameters: self.generics(inner),
                    unused_parameters: self.unused_generics_of(inner),
                    vis: Vis::Private,
                    name: tauto_surface::identity::Name::Spelled(ident(self)),
                    arity: generics.len(),
                    param: tauto_surface::identity::Name::Spelled(
                        generics.first().cloned().unwrap_or_default(),
                    ),
                    bound: bounds.into_iter().next().flatten(),
                    methods: methods
                        .into_iter()
                        .map(|m| {
                            let mut f = self.method(m);
                            // Class methods stay signatures even though
                            // `ExternFn` may carry a block for replaceable externs.
                            f.body = SurfaceTerm::new(TermKind::Other("ExternFn".into()), f.span);
                            f
                        })
                        .collect(),
                    laws: self.laws(inner),
                    inductive: self.first(inner, Nt::KwInductive).is_some(),
                    span,
                })
            }
            Some(Nt::InstanceDecl) => {
                let (generics, bounds) = self.generic_bounds(inner);
                let mut methods = Vec::new();
                self.descend(inner, Nt::FnDecl, &mut methods);
                Stmt::Instance(InstanceDecl {
                    generic_types: self.generics(inner).into_iter().map(|(_, t)| t).collect(),
                    arguments: self
                        .all(inner, Nt::Type)
                        .into_iter()
                        .skip(1)
                        .map(|t| self.term(t))
                        .collect(),
                    generics: generics.into_iter().map(Name::from).collect(),
                    unused_generics: self.unused_generics_of(inner),
                    bounds: bounds.into_iter().map(|b| b.map(Into::into)).collect(),
                    class: tauto_surface::identity::Name::Spelled(ident(self)),
                    head: self
                        .ty(inner)
                        .map(|t| self.term(t))
                        .unwrap_or_else(|| self.other(inner)),
                    infer_from: self
                        .first(inner, Nt::InferFrom)
                        .and_then(|n| self.first(n, Nt::InferOr).map(|e| self.infer_condition(e))),
                    where_: self.where_clause(inner),
                    methods: methods.into_iter().map(|m| self.method(m)).collect(),
                    laws: self.laws(inner),
                    span,
                })
            }
            Some(Nt::ExternDecl) => {
                let mut nodes = Vec::new();
                self.descend(inner, Nt::ExternFnItem, &mut nodes);
                let mut instances = Vec::new();
                self.descend(inner, Nt::ExternInstance, &mut instances);
                let instances = instances
                    .into_iter()
                    .map(|i| ExternInstance {
                        class: tauto_surface::identity::Name::Spelled(
                            self.first(i, Nt::Ident)
                                .map(|n| self.name_of(n))
                                .unwrap_or_default(),
                        ),
                        ty: self
                            .ty(i)
                            .map(|t| self.term(t))
                            .unwrap_or_else(|| self.other(i)),
                        span: self.span(i),
                    })
                    .collect();
                let mut types = Vec::new();
                self.descend(inner, Nt::ExternType, &mut types);
                let types = types
                    .into_iter()
                    .map(|t| {
                        let name = self
                            .first(t, Nt::Ident)
                            .map(|n| self.name_of(n))
                            .unwrap_or_default();
                        DataDecl {
                            vis: self
                                .first(t, Nt::Visibility)
                                .map_or(Vis::Private, |v| self.vis(v)),
                            kind: self.data_kind(t),
                            name: tauto_surface::identity::Name::Spelled(name.clone()),
                            generics: self.generics(t).into_iter().map(|(g, _)| g).collect(),
                            unused_generics: self.unused_generics_of(t),
                            unused_fields: Vec::new(),
                            rows: self.generic_rows(t),
                            constructors: vec![DataConstructor {
                                name: tauto_surface::identity::Name::Spelled(name),
                                fields: Vec::new(),
                            }],
                            host: true,
                            borrowed: false,
                            coerce: None,
                            span: self.span(t),
                        }
                    })
                    .collect();
                let mut struct_items = Vec::new();
                self.descend(inner, Nt::ExternStructItem, &mut struct_items);
                let structs = struct_items
                    .into_iter()
                    .map(|item| {
                        let vis = self
                            .first(item, Nt::Visibility)
                            .map_or(Vis::Private, |v| self.vis(v));
                        let mut d = self.struct_decl(item);
                        d.vis = vis;
                        d
                    })
                    .collect();
                let mut enum_items = Vec::new();
                self.descend(inner, Nt::ExternEnumItem, &mut enum_items);
                let enums = enum_items
                    .into_iter()
                    .map(|item| {
                        let vis = self
                            .first(item, Nt::Visibility)
                            .map_or(Vis::Private, |v| self.vis(v));
                        let mut d = self.enum_decl(item);
                        d.vis = vis;
                        d
                    })
                    .collect();
                Stmt::Extern {
                    instances,
                    types,
                    structs,
                    enums,
                    fns: nodes
                        .into_iter()
                        .filter_map(|item| {
                            let vis = self
                                .first(item, Nt::Visibility)
                                .map_or(Vis::Private, |v| self.vis(v));
                            let f = self.first(item, Nt::ExternFn)?;
                            match self.fn_decl(f) {
                                Stmt::Fn(mut f) => {
                                    f.vis = vis;
                                    Some(f)
                                }
                                _ => unreachable!(),
                            }
                        })
                        .collect(),
                    span,
                }
            }
            Some(Nt::WhileStmt) => {
                let condition = self
                    .first(inner, Nt::Cond)
                    .map(|e| self.term(e))
                    .unwrap_or_else(|| self.other(inner));
                let body = self
                    .first(inner, Nt::Block)
                    .map(|b| self.term(b))
                    .unwrap_or_else(|| self.other(inner));
                Stmt::While { condition, body }
            }
            Some(Nt::ForStmt) => {
                let pattern = self
                    .first(inner, Nt::PatternAlt)
                    .map(|p| self.pattern_alt(p))
                    .unwrap_or_else(|| Pattern::Other("for".into()));
                let source = self
                    .first(inner, Nt::Cond)
                    .map(|e| self.term(e))
                    .unwrap_or_else(|| self.other(inner));
                let body = self
                    .first(inner, Nt::Block)
                    .map(|b| self.term(b))
                    .unwrap_or_else(|| self.other(inner));
                Stmt::For {
                    pattern,
                    source,
                    body,
                }
            }
            Some(Nt::BreakStmt) => Stmt::Break(self.first(inner, Nt::Expr).map(|e| self.term(e))),
            Some(Nt::ContinueStmt) => Stmt::Continue,
            Some(Nt::ReturnStmt) => Stmt::Return(self.first(inner, Nt::Expr).map(|e| self.term(e))),
            Some(Nt::ExprStmt) => {
                let exprs = self.all(inner, Nt::Expr);
                match exprs.as_slice() {
                    [only] => match self.expr_generates(*only) {
                        Some((call, _)) => Stmt::Called {
                            call: self.term(call),
                            generates: self.generated_items(*only),
                            span,
                        },
                        None => Stmt::Expr(self.term(*only)),
                    },
                    [target, value] => {
                        let target = self.term(*target);
                        let (deref, target) = match super::deref_of(&target) {
                            Some(inner) => (Some(target.span), inner.clone()),
                            None => (None, target),
                        };
                        match &*target.kind {
                            TermKind::Var(name) => Stmt::Assign {
                                name: name.clone(),
                                place: None,
                                value: self.term(*value),
                                deref,
                            },
                            _ => match place_root(&target) {
                                Some(name) => Stmt::Assign {
                                    name,
                                    place: Some(target),
                                    value: self.term(*value),
                                    deref,
                                },
                                None => Stmt::Other("assignment target".into(), span),
                            },
                        }
                    }
                    _ => Stmt::Other("ExprStmt".into(), span),
                }
            }
            Some(k) => Stmt::Other(k.to_string(), span),
            None => Stmt::Other("token".into(), span),
        }
    }

    fn fn_decl(&self, decl: NodeId) -> Stmt {
        let (name, unused) = self
            .bind_name_of(decl)
            .or_else(|| {
                self.first(decl, Nt::FnName).map(|n| {
                    let (name, unused) = self.bind_name(n);
                    (name, unused)
                })
            })
            .unwrap_or_else(|| (Name::Spelled(String::new()), None));
        let (params, unused_params): (Vec<Name>, Vec<Option<Span>>) = self
            .all(decl, Nt::Param)
            .into_iter()
            .map(|p| {
                self.bind_name_of(p).unwrap_or_else(|| {
                    (
                        self.first(p, Nt::Ident)
                            .map(|i| Name::Spelled(self.name_of(i)))
                            .unwrap_or_default(),
                        None,
                    )
                })
            })
            .unzip();
        // An `extern` function has no block: its body is an `Other` term,
        // never run.
        let body = self
            .first(decl, Nt::Block)
            .map(|b| self.term(b))
            .unwrap_or_else(|| self.other(decl));
        let (borrows, param_types) = self
            .all(decl, Nt::Param)
            .into_iter()
            .map(|p| self.param_borrow(p))
            .unzip();
        // The row after the result type, `: &A ! {out_of_bounds}`; a row after a function type
        // is that arrow's.
        let written = self
            .first(decl, Nt::FnResult)
            .and_then(|r| self.first(r, Nt::BodyType));
        let (result, unattached) = match written {
            Some(r) => {
                let (term, row) = self.sequence(r);
                (Some(term), row)
            }
            None => (None, None),
        };
        let row = self
            .first(decl, Nt::FnResult)
            .and_then(|r| self.first(r, Nt::EffectRow));
        // `!?`: the row is not written yet; the declaration takes the one its body performs.
        let row_hole = self.row_hole_of(decl);
        let (effects, written_effects) = if row_hole.is_some() {
            (None, None)
        } else if let Some(row) = row {
            let entries = self.row_entries(row);
            let names = entries.iter().map(|e| e.name.clone()).collect();
            (Some(names), Some(entries))
        } else if let Some(entries) = unattached {
            let names = entries.iter().map(|e| e.name.clone()).collect();
            (Some(names), Some(entries))
        } else {
            (None, None)
        };
        let where_ = self.where_clause(decl);
        // `borrows(m, x.f)`: each path its names joined by `.`.
        let lends = self.first(decl, Nt::FnBorrows).map(|b| {
            self.all(b, Nt::BorrowPath)
                .into_iter()
                .map(|p| {
                    let path = self
                        .all(p, Nt::Ident)
                        .into_iter()
                        .map(|i| self.name_of(i))
                        .collect::<Vec<_>>()
                        .join(".");
                    // `borrows(place(Tree))`: an operation's instance, as
                    // the row writes it.
                    match self.first(p, Nt::TypeCall) {
                        Some(args) => format!("{path}{}", self.text(args)),
                        None => path,
                    }
                })
                .collect()
        });
        let (generics, bounds) = self.generic_bounds(decl);
        let rows = self.generic_rows(decl);
        let phase = self.first(decl, Nt::FnPhase);
        let opaque = phase.is_some_and(|p| self.first(p, Nt::KwOpaque).is_some());
        let ghost = phase.is_some_and(|p| self.first(p, Nt::KwGhost).is_some());
        let decreasing_by = self
            .first(decl, Nt::DecreasingBy)
            .and_then(|d| self.first(d, Nt::Cond))
            .map(|c| self.term(c));
        // The list after `=>`; when it is missing, an empty one where it goes,
        // so that the kernel reports what is missing.
        let generates = match self.first(decl, Nt::Generates) {
            Some(g) => Some(self.generated_items(g)),
            None if decreasing_by.is_some() || opaque => {
                let end = match &decreasing_by {
                    Some(term) => term.span.end,
                    None => [Nt::WhereClause, Nt::FnResult, Nt::RParen]
                        .into_iter()
                        .find_map(|k| self.first(decl, k))
                        .map_or(self.span(decl).start, |n| self.span(n).end),
                };
                Some(tauto_surface::generated::unwritten(end))
            }
            None => None,
        };
        Stmt::Fn(FnDecl {
            vis: Vis::Private,
            name,
            unused,
            generic_types: self.generics(decl).into_iter().map(|(_, ty)| ty).collect(),
            generics: generics.into_iter().map(Name::from).collect(),
            rows,
            bounds: bounds.into_iter().map(|b| b.map(Into::into)).collect(),
            bound_spans: self.generic_spans(decl),
            params,
            unused_generics: self.unused_generics_of(decl),
            unused_params,
            borrows,
            param_types,
            result,
            lends,
            effects,
            written_effects,
            row_hole,
            where_,
            span: self.span(decl),
            opaque,
            ghost,
            decreasing_by,
            generates,
            budget: self.decl_budget(decl),
            body,
        })
    }

    fn where_clause(&self, decl: NodeId) -> Vec<Constraint> {
        self.first(decl, Nt::WhereClause)
            .map(|w| {
                self.all(w, Nt::Constraint)
                    .into_iter()
                    .map(|c| Constraint {
                        arguments: self
                            .all(c, Nt::Type)
                            .into_iter()
                            .skip(1)
                            .map(|t| self.term(t))
                            .collect(),
                        class: tauto_surface::identity::Name::Spelled(
                            self.first(c, Nt::Ident)
                                .map(|i| self.name_of(i))
                                .unwrap_or_default(),
                        ),
                        ty: self
                            .ty(c)
                            .map(|t| self.term(t))
                            .unwrap_or_else(|| self.other(c)),
                        span: self.span(c),
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn method(&self, decl: NodeId) -> FnDecl {
        match self.fn_decl(decl) {
            Stmt::Fn(f) => f,
            _ => unreachable!(),
        }
    }

    fn laws(&self, decl: NodeId) -> Vec<LawDecl> {
        let mut nodes = Vec::new();
        self.descend(decl, Nt::LawDecl, &mut nodes);
        nodes
            .into_iter()
            .map(|l| {
                let span = self.span(l);
                let Stmt::Theorem(theorem) = self.theorem_decl(l, span) else {
                    unreachable!()
                };
                LawDecl {
                    name: theorem.name.clone(),
                    span,
                    theorem,
                }
            })
            .collect()
    }

    fn effect_decl(&self, decl: NodeId) -> Stmt {
        let name = self
            .first(decl, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        let signature = self
            .first(decl, Nt::EffectBody)
            .and_then(|b| self.first(b, Nt::EffectSignature));
        let alias = self
            .first(decl, Nt::EffectBody)
            .and_then(|b| self.first(b, Nt::EffectAlias));
        // `effect ask(question: Text): i64` has the operation's parameters
        // in the parentheses; `effect State(T: Type) {…}` has the set's
        // type parameters.
        let written: Vec<NodeId> = self
            .first(decl, Nt::EffectParams)
            .map(|p| self.all(p, Nt::Param))
            .unwrap_or_default();
        let param_name = |p: NodeId| {
            self.bind_name_of(p)
                .map(|(n, _)| n.to_string())
                .or_else(|| self.first(p, Nt::Ident).map(|i| self.name_of(i)))
                .unwrap_or_default()
        };
        let (param_names, params): (Vec<Name>, Vec<Option<SurfaceTerm>>) = if signature.is_some() {
            written
                .iter()
                .map(|&p| (param_name(p).into(), self.ty(p).map(|t| self.term(t))))
                .unzip()
        } else {
            Default::default()
        };
        let generics: Vec<Name> = if alias.is_some() {
            written.iter().map(|&p| param_name(p).into()).collect()
        } else {
            self.generics(decl).into_iter().map(|(g, _)| g).collect()
        };
        let bounds = if alias.is_some() {
            Vec::new()
        } else {
            self.generic_bounds(decl).1
        };
        let rows = if alias.is_some() {
            vec![false; generics.len()]
        } else {
            self.generic_rows(decl)
        };
        let result = signature.and_then(|sig| self.ty(sig)).map(|t| self.term(t));
        let resume = signature
            .and_then(|sig| self.first(sig, Nt::EffectMode))
            .map(|mode| match self.first(mode, Nt::Quant) {
                Some(q) => self.text(q).replace(char::is_whitespace, ""),
                None => "direct".to_string(),
            });
        let unused_generics = if alias.is_some() {
            vec![None; generics.len()]
        } else {
            self.unused_generics_of(decl)
        };
        Stmt::Effect(EffectDecl {
            module_scope: None,
            vis: Vis::Private,
            name: tauto_surface::identity::Name::Spelled(name),
            generics: generics.into_iter().map(Name::from).collect(),
            bounds: bounds.into_iter().map(|b| b.map(Into::into)).collect(),
            unused_generics,
            rows,
            params,
            param_names,
            result,
            resume,
            // `{div, stdout}` lists names, not a row's set expression.
            set: alias.map(|a| {
                self.all(a, Nt::EffectName)
                    .into_iter()
                    .filter_map(|n| self.effect_entry(n).map(|e| e.name))
                    .collect()
            }),
            span: self.span(decl),
        })
    }

    /// The node of a declaration's generics: `<A>` of a function, theorem or
    /// operation, or `(A: Type)` of a type declaration.
    fn generic_node(&self, node: NodeId) -> Option<NodeId> {
        self.first(node, Nt::Generics)
            .or_else(|| self.first(node, Nt::TypeParams))
    }

    /// The effect row that becomes the function's `written_effects`: the
    /// `FnResult`'s own row, or the row after a result type with no `->` (a
    /// row after `->` binds to that arrow's function type instead).
    fn fn_written_effect_row(&self, decl: NodeId) -> Option<NodeId> {
        let result = self.first(decl, Nt::FnResult)?;
        if let Some(row) = self.first(result, Nt::EffectRow) {
            return Some(row);
        }
        let body = self.first(result, Nt::BodyType)?;
        let row = self.first(body, Nt::EffectRow)?;
        let steals = self.cst.children(body).iter().any(|&k| {
            matches!(self.nt(k), Some(Nt::Op | Nt::CondOp)) && self.text(k).trim() == "->"
        });
        if steals { None } else { Some(row) }
    }

    /// The `!?` the result of `decl` ends with, as the row of the declaration: after the result type
    /// (`fn f(): T !?`) or alone (`fn f() !?`), never one that binds to an arrow of the result type.
    fn row_hole_of(&self, decl: NodeId) -> Option<Span> {
        let result = self.first(decl, Nt::FnResult)?;
        let mut rows = vec![self.first(result, Nt::EffectRow)];
        if let Some(ty) = self.first(result, Nt::BodyType) {
            let arrow = self
                .cst
                .children(ty)
                .iter()
                .any(|k| self.nt(*k) == Some(Nt::Op) && sign(self.text(*k).trim()) == "->");
            if !arrow {
                rows.push(self.first(ty, Nt::EffectRow));
            }
        }
        rows.into_iter()
            .flatten()
            .find(|r| self.first(*r, Nt::Question).is_some())
            .map(|r| self.span(r))
    }

    /// A form the grammar reads but the language does not have: an effect operation written as
    /// `effect ask: (q: T) -> R` (it is `effect ask(q: T): R`), and an effect row with two row
    /// variables or a set literal that writes an effect twice.
    fn refused_form(&self, root: NodeId) -> Option<(u32, Message)> {
        for (kind, span) in self.cst.terminals() {
            let text = span.text(self.source);
            if kind == tauto_parol::TerminalKind::Ident && text == "r#_" {
                return Some((span.start, msg!("surface-raw-underscore")));
            }
            // Lone `_` is the Wild token; an Ident that is only `_` must not remain.
            if kind == tauto_parol::TerminalKind::Ident && text == "_" {
                return Some((span.start, msg!("surface-underscore-not-name")));
            }
        }
        // `^_` is Caret then Wild: not a BindName.
        let terminals = self.cst.terminals();
        for w in terminals.windows(2) {
            if w[0].0 == TerminalKind::Circumflex && w[1].0 == TerminalKind::Wild {
                return Some((w[0].1.start, msg!("surface-unused-marker-wild")));
            }
        }
        // `^` on a `pub` / `pub(open)` / `pub(handle)` declaration name only.
        // Bindings inside the body (and parameters) may still use `^`.
        let [stmts] = self.descend_kinds(root, [Nt::Stmt]);
        for stmt in stmts {
            if self.first(stmt, Nt::Visibility).is_none() {
                continue;
            }
            let Some(other) = self.first(stmt, Nt::OtherStmt) else {
                continue;
            };
            let head = self
                .first(other, Nt::FnDecl)
                .and_then(|d| self.first(d, Nt::FnName))
                .or_else(|| {
                    self.first(other, Nt::MacroFnDecl).and_then(|m| {
                        self.first(m, Nt::FnDecl)
                            .and_then(|d| self.first(d, Nt::FnName))
                    })
                })
                .or_else(|| {
                    [
                        Nt::TheoremDecl,
                        Nt::DefDecl,
                        Nt::AxiomDecl,
                        Nt::LetDecl,
                        Nt::VarDecl,
                    ]
                    .into_iter()
                    .find_map(|nt| {
                        self.first(other, nt)
                            .and_then(|d| self.first(d, Nt::BindName))
                    })
                });
            if let Some(name) = head {
                let mut carets = Vec::new();
                self.descend(name, Nt::Caret, &mut carets);
                if let Some(c) = carets.first() {
                    return Some((self.span(*c).start, msg!("surface-unused-marker-pub")));
                }
            }
            // A field of a struct others can see may be read in their files.
            if let Some(body) = self
                .first(other, Nt::StructDecl)
                .and_then(|d| self.first(d, Nt::StructBody))
            {
                let mut fields = Vec::new();
                self.descend(body, Nt::FieldDecl, &mut fields);
                if let Some(c) = fields.iter().find_map(|f| self.first(*f, Nt::Caret)) {
                    return Some((self.span(c).start, msg!("surface-unused-marker-pub")));
                }
            }
        }
        // `coerce` stands before a field of a struct, once in it, at a level
        // that is `mut` or `owned` when written.
        // One walk of the tree for the four kinds the rules below look at.
        let [structs, fields, effects, rows] = self.descend_kinds(
            root,
            [Nt::StructDecl, Nt::FieldDecl, Nt::EffectDecl, Nt::EffectSet],
        );
        let mut in_structs = Vec::new();
        let mut struct_fields = std::collections::HashSet::new();
        for decl in structs {
            let mut fields = Vec::new();
            if let Some(body) = self.first(decl, Nt::StructBody) {
                self.descend(body, Nt::FieldDecl, &mut fields);
            }
            struct_fields.extend(fields.iter().copied());
            let mut written = fields
                .into_iter()
                .filter(|f| self.first(*f, Nt::FieldCoerce).is_some());
            if let Some(first) = written.next() {
                in_structs.push(first);
                if let Some(second) = written.next() {
                    return Some((self.span(second).start, msg!("surface-coerce-twice")));
                }
            }
        }
        // `^` on a field is for a struct's own fields: a record type's
        // members are not declared here.
        for field in &fields {
            if !struct_fields.contains(field)
                && let Some(c) = self.first(*field, Nt::Caret)
            {
                return Some((self.span(c).start, msg!("surface-unused-marker-record-type")));
            }
        }
        for field in fields {
            let Some(level) = self.coerce_level(field) else {
                continue;
            };
            if !in_structs.contains(&field) {
                return Some((self.span(field).start, msg!("surface-coerce-not-in-struct")));
            }
            if let Err(word) = level {
                return Some((
                    self.span(field).start,
                    msg!("surface-coerce-level", word = word),
                ));
            }
        }
        for e in effects {
            let old = self.first(e, Nt::EffectParams).is_none()
                && self
                    .first(e, Nt::EffectBody)
                    .and_then(|b| self.first(b, Nt::EffectSignature))
                    .and_then(|s| self.ty(s))
                    .is_some_and(|t| {
                        self.descend_first(t, Nt::ThinArrow)
                            && self.text(t).trim_start().starts_with('(')
                    });
            if old {
                return Some((self.span(e).start, msg!("surface-old-effect-operation")));
            }
        }
        // `!?` only ends the result of a `fn` with a body.
        let [fns, extern_fns, hole_rows, effect_names] = self.descend_kinds(
            root,
            [Nt::FnDecl, Nt::ExternFn, Nt::EffectRow, Nt::EffectName],
        );
        // An `extern fn` has a body to infer a row from only when it is replaceable (written
        // with a block); a bare signature in an `extern` or a class has none.
        let allowed_holes: Vec<Span> = fns
            .iter()
            .chain(
                extern_fns
                    .iter()
                    .filter(|decl| self.first(**decl, Nt::Block).is_some()),
            )
            .filter_map(|decl| self.row_hole_of(*decl))
            .collect();
        for row in hole_rows {
            if self.first(row, Nt::Question).is_some() && !allowed_holes.contains(&self.span(row)) {
                return Some((self.span(row).start, msg!("surface-row-hole-place")));
            }
        }
        // A row variable joins a row with `∪`; inside a literal's braces a name is an
        // effect, so a declared row variable written there is refused.
        for decl in fns.iter().chain(extern_fns.iter()) {
            let Some(generics) = self.generic_node(*decl) else {
                continue;
            };
            let variables: Vec<String> = self
                .generic_items(generics)
                .into_iter()
                .filter(|g| self.first(*g, Nt::Bang).is_some())
                .filter_map(|g| self.first(g, Nt::Ident))
                .map(|ident| self.text(ident).trim().to_string())
                .collect();
            if variables.is_empty() {
                continue;
            }
            let mut names = Vec::new();
            self.descend(*decl, Nt::EffectName, &mut names);
            for name in names {
                let written = self.first(name, Nt::Ident).map(|i| self.text(i).trim().to_string());
                if let Some(written) = written
                    && variables.contains(&written)
                    && self.first(name, Nt::TypeCall).is_none()
                    && self.first(name, Nt::EffectForall).is_none()
                {
                    return Some((
                        self.span(name).start,
                        msg!("surface-row-variable-in-literal", name = written),
                    ));
                }
            }
        }
        // `^` unused assertions are only on a function's written row; a
        // function-type row, a row argument, or an effect-set member drops the
        // marker, so those sites refuse it.
        let mut allowed_markers = std::collections::HashSet::new();
        for decl in fns.iter().chain(extern_fns.iter()) {
            if let Some(row) = self.fn_written_effect_row(*decl) {
                let mut names = Vec::new();
                self.descend(row, Nt::EffectName, &mut names);
                allowed_markers.extend(names);
            }
        }
        for name in effect_names {
            if self.first(name, Nt::Caret).is_some() && !allowed_markers.contains(&name) {
                return Some((
                    self.span(name).start,
                    msg!("surface-unused-effect-marker-place"),
                ));
            }
        }
        for row in rows {
            let mut variables = 0;
            for term in self.all(row, Nt::EffectTerm) {
                if self.first(term, Nt::Ident).is_some()
                    && self.first(term, Nt::EffectLit).is_none()
                {
                    variables += 1;
                }
                if let Some(lit) = self.first(term, Nt::EffectLit) {
                    let mut names = Vec::new();
                    self.collect_effect_names(lit, &mut names);
                    let mut seen: Vec<String> = Vec::new();
                    for name in names {
                        let written = self.text(name).trim().to_string();
                        if seen.contains(&written) {
                            return Some((
                                self.span(name).start,
                                msg!("surface-row-repeats-effect", name = written),
                            ));
                        }
                        seen.push(written);
                    }
                }
            }
            if variables > 1 {
                return Some((self.span(row).start, msg!("surface-row-variables")));
            }
        }
        // Class methods share `ExternFn` with replaceable externs, but a
        // class method is only a signature: a body is refused here.
        let [classes] = self.descend_kinds(root, [Nt::ClassDecl]);
        for class in classes {
            let mut methods = Vec::new();
            self.descend(class, Nt::ExternFn, &mut methods);
            for method in methods {
                if self.first(method, Nt::Block).is_some() {
                    return Some((self.span(method).start, msg!("surface-class-method-body")));
                }
            }
        }
        // `^` asserts a binding is unused. Constructor names (`^Some(x)`) and
        // field labels (`Point { ^x: y }`) are not bindings; refuse them. The
        // binding sites are the arguments and field values (`Some(^x)`,
        // `Point { x: ^y }`, and shorthand `Point { ^x }`).
        let [paths, fields] = self.descend_kinds(root, [Nt::PathPattern, Nt::FieldPattern]);
        for path in paths {
            let Some((_, Some(mark))) = self.bind_name_of(path) else {
                continue;
            };
            if self.first(path, Nt::PatternArgs).is_some()
                || self.first(path, Nt::PatternImplicits).is_some()
            {
                return Some((mark.start, msg!("surface-unused-marker-not-binding")));
            }
        }
        for field in fields {
            let Some((_, Some(mark))) = self.bind_name_of(field) else {
                continue;
            };
            if self.first(field, Nt::Pattern).is_some() {
                return Some((mark.start, msg!("surface-unused-marker-not-binding")));
            }
        }
        None
    }

    /// Where a kind is written as a lowercase word, as in `<A: shared>`: it is
    /// written `Shared`.
    fn bare_kind(&self, id: NodeId) -> Option<(u32, u32)> {
        if matches!(self.nt(id), Some(Nt::Generic | Nt::TypeParam))
            && let Some(kind) = self.first(id, Nt::GenericKind)
        {
            let mut names = Vec::new();
            self.descend(kind, Nt::Ident, &mut names);
            for n in names {
                if matches!(self.text(n).trim(), "copy" | "shared" | "affine" | "linear") {
                    let at = self.cst.span(n);
                    return Some((at.start, at.end));
                }
            }
        }
        self.cst.children_iter(id).find_map(|c| self.bare_kind(c))
    }

    fn generic_items(&self, generics: NodeId) -> Vec<NodeId> {
        self.cst
            .children_iter(generics)
            .filter(|c| matches!(self.nt(*c), Some(Nt::Generic | Nt::TypeParam)))
            .collect()
    }

    fn generic_spans(&self, node: NodeId) -> Vec<Span> {
        let Some(generics) = self.generic_node(node) else {
            return Vec::new();
        };
        self.generic_items(generics)
            .into_iter()
            .map(|g| self.span(g))
            .collect()
    }

    /// For each generic of a declaration: whether it is written with `!`, a row variable.
    fn generic_rows(&self, node: NodeId) -> Vec<bool> {
        let Some(generics) = self.generic_node(node) else {
            return Vec::new();
        };
        self.generic_items(generics)
            .into_iter()
            .map(|g| self.first(g, Nt::Bang).is_some())
            .collect()
    }

    /// Where `^` is written before each type parameter of `node`.
    fn unused_generics_of(&self, node: NodeId) -> Vec<Option<Span>> {
        let Some(generics) = self.generic_node(node) else {
            return Vec::new();
        };
        self.generic_items(generics)
            .into_iter()
            .map(|g| self.bind_name_of(g).and_then(|(_, unused)| unused))
            .collect()
    }

    /// The generics' names, and each one's bound as the checker reads it:
    /// `Shared` is `shared`, `(Shared) -> Shared` is
    /// `(shared)->shared`, and a row variable's `!e: <=1` is `<=1`. A bare
    /// `Type` has none.
    fn generic_bounds(&self, node: NodeId) -> (Vec<String>, Vec<Option<String>>) {
        let Some(generics) = self.generic_node(node) else {
            return (Vec::new(), Vec::new());
        };
        self.generic_items(generics)
            .into_iter()
            .map(|g| {
                let (name, _) = self.bind_name_of(g).unwrap_or_else(|| {
                    (
                        self.first(g, Nt::Ident)
                            .map(|i| Name::Spelled(self.name_of(i)))
                            .unwrap_or_default(),
                        None,
                    )
                });
                let bound = match (self.first(g, Nt::RowBound), self.first(g, Nt::GenericKind)) {
                    (Some(b), _) => Some(self.text(b).replace(char::is_whitespace, "")),
                    (None, Some(k)) => self.kind_bound(k),
                    (None, None) => None,
                };
                (name.to_string(), bound)
            })
            .unzip()
    }

    /// A kind as the checker's bound string: the universe names `Copy`,
    /// `Shared` and `Linear` are `copy`, `shared` and `linear`, `Type` is
    /// `affine`, the whitespace is dropped, and `Type` alone is none.
    fn kind_bound(&self, kind: NodeId) -> Option<String> {
        let out: String = self.text(kind).split_whitespace().collect();
        if out == "Type" || out.starts_with("Type(") {
            return None;
        }
        let is_kind = |w: &str| matches!(w, "Copy" | "Shared" | "Type" | "Linear" | "NoBorrow");
        let words = || out.split(|c: char| !(c.is_alphanumeric() || c == '_'));
        if !words().filter(|w| !w.is_empty()).all(is_kind) {
            return Some(out);
        }
        let mut written = String::new();
        let mut word = String::new();
        for c in out.chars().chain(std::iter::once(' ')) {
            if c.is_alphanumeric() || c == '_' {
                word.push(c);
                continue;
            }
            written.push_str(match word.as_str() {
                "Copy" => "copy",
                "Shared" => "shared",
                "Linear" => "linear",
                "Type" => "affine",
                "NoBorrow" => "noborrow",
                w => w,
            });
            word.clear();
            if c != ' ' {
                written.push(c);
            }
        }
        Some(written)
    }

    /// The kernel's reading of a kind: every universe name is `Type`.
    fn kind_term(&self, t: &SurfaceTerm) -> SurfaceTerm {
        match &*t.kind {
            TermKind::Var(n)
                if matches!(n.as_str(), "Copy" | "Shared" | "Linear" | "NoBorrow") =>
            {
                SurfaceTerm::var("Type", t.span)
            }
            TermKind::Pi {
                params,
                result,
                effects,
                unused,
            } => SurfaceTerm::new(
                TermKind::Pi {
                    params: params
                        .iter()
                        .map(|(n, p)| (n.clone(), self.kind_term(p)))
                        .collect(),
                    result: Box::new(self.kind_term(result)),
                    effects: effects.clone(),
                    unused: unused.clone(),
                },
                t.span,
            ),
            _ => t.clone(),
        }
    }

    /// The kind in `struct(affine)` or `enum(linear)`, or `inductive` for
    /// `inductive struct` and `inductive enum`. The kind of an extern `type` is
    /// not read here.
    /// The words written in a declaration's parentheses: `struct(affine)` is
    /// `affine`; an extern type's are joined by `, `, so `type(affine, borrow)`
    /// is `affine, borrow`. The checker reads each word.
    /// The word written in `let(…)` or `var(…)`.
    fn let_props(&self, decl: NodeId) -> Option<String> {
        let props = self.first(decl, Nt::LetProps)?;
        let word = self.first(props, Nt::Ident)?;
        Some(self.text(word).trim().to_string())
    }

    fn data_kind(&self, decl: NodeId) -> Option<String> {
        let Some(head) = self
            .first(decl, Nt::StructHead)
            .or_else(|| self.first(decl, Nt::EnumHead))
        else {
            // `struct(affine)` / `enum(affine)` inside a replaceable `extern`.
            if let Some(props) = self.first(decl, Nt::DeclProps) {
                return self
                    .first(props, Nt::Kind)
                    .map(|k| self.text(k).trim().to_string());
            }
            // An extern `type` writes its words right after `type`.
            let props = self.first(decl, Nt::ExternProps)?;
            let prop = self.first(props, Nt::ExternProp)?;
            let words: Vec<String> = self
                .cst
                .children_iter(prop)
                .filter(|k| matches!(self.nt(*k), Some(Nt::Kind | Nt::KwBorrowKind)))
                .map(|k| self.text(k).trim().to_string())
                .collect();
            return (!words.is_empty()).then(|| words.join(", "));
        };
        // `inductive struct(affine)` is `inductive, affine`: each word is read
        // on its own, as an extern type's are.
        let inductive = self
            .first(head, Nt::KwInductive)
            .map(|k| self.text(k).trim().to_string());
        let kind = self
            .first(head, Nt::DeclProps)
            .and_then(|props| self.first(props, Nt::Kind))
            .map(|k| self.text(k).trim().to_string());
        match (inductive, kind) {
            (Some(i), Some(k)) => Some(format!("{i}, {k}")),
            (i, k) => i.or(k),
        }
    }

    fn data_fields(&self, fields: NodeId) -> Vec<(Option<String>, SurfaceTerm)> {
        let mut nodes = Vec::new();
        self.descend(fields, Nt::FieldDecl, &mut nodes);
        nodes
            .into_iter()
            .map(|f| {
                let name = self.first(f, Nt::Ident).map(|i| self.name_of(i));
                let ty = match self.ty(f) {
                    Some(t) => self.term(t),
                    None => self.other(f),
                };
                (name.into(), ty)
            })
            .collect()
    }

    fn struct_decl(&self, decl: NodeId) -> DataDecl {
        let name = self
            .first(decl, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        // `struct &T` is declared under `&T`, beside `T`.
        let borrowed = self.first(decl, Nt::Amp).is_some()
            || self
                .first(decl, Nt::StructDeclOpt)
                .is_some_and(|o| self.first(o, Nt::Amp).is_some());
        let name = if borrowed { format!("&{name}") } else { name };
        let field_list = self
            .first(decl, Nt::StructBody)
            .and_then(|b| self.first(b, Nt::Fields));
        let fields = field_list.map(|f| self.data_fields(f)).unwrap_or_default();
        let unused_fields: Vec<Option<Span>> = field_list
            .map(|f| {
                let mut nodes = Vec::new();
                self.descend(f, Nt::FieldDecl, &mut nodes);
                nodes
                    .into_iter()
                    .map(|n| self.first(n, Nt::Caret).map(|c| self.span(c)))
                    .collect()
            })
            .filter(|u: &Vec<Option<Span>>| u.iter().any(Option::is_some))
            .unwrap_or_default();
        let coerce = field_list.and_then(|f| {
            let mut nodes = Vec::new();
            self.descend(f, Nt::FieldDecl, &mut nodes);
            nodes.into_iter().enumerate().find_map(|(field, node)| {
                Some(DataCoerce {
                    field,
                    level: self.coerce_level(node)?.ok()?,
                })
            })
        });
        DataDecl {
            vis: Vis::Private,
            kind: self.data_kind(decl),
            name: tauto_surface::identity::Name::Spelled(name.clone()),
            generics: self.generics(decl).into_iter().map(|(g, _)| g).collect(),
            unused_generics: self.unused_generics_of(decl),
            unused_fields,
            rows: self.generic_rows(decl),
            constructors: vec![DataConstructor {
                name: tauto_surface::identity::Name::Spelled(name),
                fields,
            }],
            host: false,
            borrowed,
            coerce,
            span: self.span(decl),
        }
    }

    /// The level of the `coerce` written before a field, if one is: `Err` with
    /// the word when it is not `mut` or `owned`.
    fn coerce_level(&self, field: NodeId) -> Option<Result<CoerceLevel, String>> {
        let coerce = self.first(field, Nt::FieldCoerce)?;
        let Some(level) = self.first(coerce, Nt::CoerceLevel) else {
            return Some(Ok(CoerceLevel::Ref));
        };
        Some(match self.text(level).trim() {
            "mut" => Ok(CoerceLevel::Mut),
            "owned" => Ok(CoerceLevel::Owned),
            other => Err(other.to_string()),
        })
    }

    fn enum_decl(&self, decl: NodeId) -> DataDecl {
        let name = self
            .first(decl, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        let mut variants = Vec::new();
        self.descend(decl, Nt::Variant, &mut variants);
        let constructors = variants
            .into_iter()
            .map(|v| {
                let name = self
                    .first(v, Nt::Ident)
                    .map(|i| self.name_of(i))
                    .unwrap_or_default();
                let fields = match self.first(v, Nt::VariantBody) {
                    None => Vec::new(),
                    Some(body) => match self.first(body, Nt::Fields) {
                        Some(f) => self.data_fields(f),
                        None => self
                            .tys(body)
                            .into_iter()
                            .map(|t| (None, self.term(t)))
                            .collect(),
                    },
                };
                DataConstructor {
                    name: tauto_surface::identity::Name::Spelled(name),
                    fields,
                }
            })
            .collect();
        DataDecl {
            vis: Vis::Private,
            kind: self.data_kind(decl),
            name: tauto_surface::identity::Name::Spelled(name),
            generics: self.generics(decl).into_iter().map(|(g, _)| g).collect(),
            unused_generics: self.unused_generics_of(decl),
            unused_fields: Vec::new(),
            rows: self.generic_rows(decl),
            constructors,
            host: false,
            borrowed: false,
            coerce: None,
            span: self.span(decl),
        }
    }

    /// `<A, n: Nat>` or `(A: Type, n: Nat)`: the generics, typed `Type`
    /// unless a kind is written; `Shared` is read as `Type`.
    fn generics(&self, node: NodeId) -> Vec<(Name, SurfaceTerm)> {
        let Some(generics) = self.generic_node(node) else {
            return Vec::new();
        };
        self.generic_items(generics)
            .into_iter()
            .map(|g| {
                let (name, _) = self.bind_name_of(g).unwrap_or_else(|| {
                    (
                        self.first(g, Nt::Ident)
                            .map(|i| Name::Spelled(self.name_of(i)))
                            .unwrap_or_default(),
                        None,
                    )
                });
                let kind = match (self.first(g, Nt::RowBound), self.first(g, Nt::GenericKind)) {
                    (Some(b), _) => SurfaceTerm::var(
                        &self.text(b).replace(char::is_whitespace, ""),
                        self.span(b),
                    ),
                    (None, Some(k)) => self.kind_term(&self.term(k)),
                    (None, None) => SurfaceTerm::var("Type", self.span(g)),
                };
                (name, kind)
            })
            .collect()
    }

    /// A parameter's borrow and type. A borrow is written in the type:
    /// `x: &T` borrows, `x: &mut T` borrows mutably, and the type the
    /// parameter is read with is `T`, as the binder form once gave it. The
    /// binder form `&x: T` is an error that says where the `&` now goes.
    pub(super) fn param_borrow(&self, p: NodeId) -> (Option<bool>, Option<SurfaceTerm>) {
        if let Some(b) = self.first(p, Nt::Borrow) {
            let mutable = self.text(b).contains("mut");
            let message = if self.text(b).starts_with("&rc") {
                "`&rc x: T` is not a parameter: write `x: &rc T`"
            } else if mutable {
                "`&mut x: T` is not a parameter: write `x: &mut T`"
            } else {
                "`&x: T` is not a parameter: write `x: &T`"
            };
            return (
                Some(mutable),
                Some(SurfaceTerm::new(
                    TermKind::Other(message.into()),
                    self.span(p),
                )),
            );
        }
        match self.ty(p).map(|t| self.term(t)) {
            Some(ty) => match &*ty.kind {
                // `x: &orig T` keeps its type whole: the mark says it borrows.
                TermKind::Borrow { orig: true, .. } => (Some(false), Some(ty)),
                // `x: &rc T` takes a value, the counted box.
                TermKind::Borrow { rc: true, .. } => (None, Some(ty)),
                TermKind::Borrow { mutable, term, .. } => (Some(*mutable), Some((**term).clone())),
                _ => (None, Some(ty)),
            },
            None => (None, None),
        }
    }

    fn typed_params(&self, node: NodeId) -> Vec<(Name, SurfaceTerm)> {
        self.all(node, Nt::Param)
            .into_iter()
            .map(|p| {
                let (name, _) = self.bind_name_of(p).unwrap_or_else(|| {
                    (
                        self.first(p, Nt::Ident)
                            .map(|i| Name::Spelled(self.name_of(i)))
                            .unwrap_or_default(),
                        None,
                    )
                });
                let ty = match self.ty(p) {
                    Some(t) => self.term(t),
                    None => self.other(p),
                };
                (name, ty)
            })
            .collect()
    }

    /// The names of a `Generates` node, or an unwritten clause at `at`.
    fn generates_clause(&self, node: Option<NodeId>, at: u32) -> Generates {
        let clause = match node {
            Some(n) => self.generated_items(n),
            None => Generates {
                at: Span::new(at, at),
                ..Generates::default()
            },
        };
        Generates {
            breaks: true,
            ..clause
        }
    }

    /// The `Generated` children of `node` (a `Generates`, or an `Expr` that ends in the list), as a
    /// clause that starts at its first `=>`.
    fn generated_items(&self, node: NodeId) -> Generates {
        let items: Vec<(String, String)> = self
            .all(node, Nt::Generated)
            .into_iter()
            .filter_map(|g| {
                let kind = self.first(g, Nt::GeneratedKind).map(|k| self.name_of(k))?;
                let parts: Vec<String> = self
                    .all(g, Nt::Ident)
                    .into_iter()
                    .map(|i| self.name_of(i))
                    .collect();
                if parts.is_empty() {
                    return None;
                }
                Some((kind, parts.join(SEPARATOR)))
            })
            .collect();
        let arrow = self.first(node, Nt::FatArrow);
        let last = self.all(node, Nt::Generated).last().copied();
        let at = match (arrow, last) {
            (Some(a), Some(l)) => Span::new(self.span(a).start, self.span(l).end),
            _ => Span::default(),
        };
        Generates {
            items,
            written: true,
            at,
            breaks: false,
        }
    }

    /// For an `Expr` that is `call => fn a, theorem b`: the call and the list.
    pub(super) fn expr_generates(&self, expr: NodeId) -> Option<(NodeId, Vec<(String, String)>)> {
        self.first(expr, Nt::Generated)?;
        let call = self
            .cst
            .children(expr)
            .into_iter()
            .find(|c| matches!(self.nt(*c), Some(nt) if nt != Nt::Gap && nt != Nt::FatArrow))?;
        Some((call, self.generated_items(expr).items))
    }

    fn inductive_decl(&self, decl: NodeId, span: Span) -> Stmt {
        let name = self
            .first(decl, Nt::Ident)
            .map(|i| self.name_of(i))
            .unwrap_or_default();
        let sort = match self.ty(decl) {
            Some(t) => self.term(t),
            None => self.other(decl),
        };
        let mut ctors = Vec::new();
        if let Some(list) = self.first(decl, Nt::Constructors) {
            self.push_constructors(list, &mut ctors);
        }
        let constructors = ctors
            .into_iter()
            .map(|c| {
                let mut params = self.generics(c);
                let implicit = params.len();
                params.extend(self.typed_params(c));
                // `false` and `true`, the constructors of `Bool`, are words.
                let name = if let Some(i) = self.first(c, Nt::Ident) {
                    self.name_of(i)
                } else if self.first(c, Nt::True).is_some() {
                    "true".to_string()
                } else if self.first(c, Nt::False).is_some() {
                    "false".to_string()
                } else {
                    String::new()
                };
                Constructor {
                    name: tauto_surface::identity::Name::Spelled(name),
                    implicit,
                    params,
                    result: match self.ty(c) {
                        Some(t) => self.term(t),
                        None => self.other(c),
                    },
                }
            })
            .collect();
        let generates = self.generates_clause(
            self.first(decl, Nt::Generates),
            self.ty(decl).map_or(span.end, |t| self.span(t).end),
        );
        Stmt::Inductive(InductiveDecl {
            vis: Vis::Private,
            name: tauto_surface::identity::Name::Spelled(name),
            params: self.typed_params(decl),
            sort,
            constructors,
            generates,
            span,
        })
    }

    fn push_mutual(&self, node: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::MutualItem) => out.push(c),
                Some(Nt::MutualItems | Nt::MutualTail) => self.push_mutual(c, out),
                _ => {}
            }
        }
    }

    fn push_constructors(&self, node: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::Constructor) => out.push(c),
                Some(Nt::ConstructorsTail) => self.push_constructors(c, out),
                _ => {}
            }
        }
    }

    fn def_decl(&self, decl: NodeId, span: Span) -> Stmt {
        let Stmt::Theorem(mut t) = self.theorem_decl(decl, span) else {
            unreachable!()
        };
        // `Colon Type Assign Gap Type`: the first `Type` is the result, the
        // second the body.
        let types = self.tys(decl);
        if let [result, body] = types.as_slice() {
            t.ty = self.term(*result);
            t.body = Some(self.term(*body));
        }
        Stmt::Def(t)
    }

    fn theorem_decl(&self, decl: NodeId, span: Span) -> Stmt {
        let (name, unused) = self.bind_name_of(decl).unwrap_or_else(|| {
            (
                self.first(decl, Nt::Ident)
                    .map(|i| Name::Spelled(self.name_of(i)))
                    .unwrap_or_default(),
                None,
            )
        });
        let mut params = self.generics(decl);
        let mut unused_params = self.unused_generics_of(decl);
        unused_params.resize(params.len(), None);
        let n_generics = params.len();
        // `where C(T)` is a parameter after the generics, the record of the
        // class (`crates/tauto-kernel/src/check/classes.rs`).
        for (i, c) in self.where_clause(decl).into_iter().enumerate() {
            let span = c.span;
            let class = SurfaceTerm::var(&c.class, span);
            params.push((
                tauto_surface::identity::Name::Spelled(dictionary_name(&c.class, i)),
                SurfaceTerm::new(
                    TermKind::App {
                        function: Box::new(class),
                        arguments: std::iter::once(c.ty).chain(c.arguments).collect(),
                    },
                    span,
                ),
            ));
            unused_params.push(None);
        }
        for p in self.all(decl, Nt::Param) {
            let (pname, punused) = self.bind_name_of(p).unwrap_or_else(|| {
                (
                    self.first(p, Nt::Ident)
                        .map(|i| Name::Spelled(self.name_of(i)))
                        .unwrap_or_default(),
                    None,
                )
            });
            let ty = match self.ty(p) {
                Some(t) => self.term(t),
                None => self.other(p),
            };
            params.push((pname, ty));
            unused_params.push(punused);
        }
        let ty = match self.ty(decl) {
            Some(t) => self.term(t),
            None => self.other(decl),
        };
        let body = self.first(decl, Nt::Block).map(|b| self.term(b));
        let implicit = n_generics;
        let decreasing_by = self
            .first(decl, Nt::DecreasingBy)
            .and_then(|d| self.first(d, Nt::Cond))
            .map(|c| self.term(c));
        Stmt::Theorem(TheoremDecl {
            vis: Vis::Private,
            name,
            unused,
            implicit,
            params,
            unused_params,
            ty,
            body,
            decreasing_by,
            budget: self.decl_budget(decl),
            span,
        })
    }

    fn decl_budget(&self, decl: NodeId) -> Option<u64> {
        self.first(decl, Nt::DeclBudget)
            .and_then(|b| self.first(b, Nt::Integer))
            .and_then(|i| self.text(i).replace('_', "").parse().ok())
    }

    pub(super) fn perform(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let effect = self
            .first(id, Nt::OperationName)
            .map(|n| self.name_of(n))
            .unwrap_or_default();
        // `perform budget(n, f)` is the host's budget only when `budget`
        // names the library's operation, which name resolution decides
        // (`tauto_surface::resolve`); here it is read as any `perform`. An
        // argument written at a type (`n: T`) is kept as one, so that the
        // resolver can refuse it for the host's budget.
        let budget_spelling = BudgetLimit::of_operation(&effect).is_some();
        // `perform e(<T: A>, x)`: the named type arguments first, as a call's.
        let args = self
            .first(id, Nt::Call)
            .map(|c| {
                self.call_implicits(c)
                    .into_iter()
                    .chain(self.all(c, Nt::Item).into_iter().map(|i| {
                        let term = self.term(i);
                        match self.first(i, Nt::Type).filter(|_| budget_spelling) {
                            Some(ty) => SurfaceTerm::new(
                                TermKind::Ascribe {
                                    term: Box::new(term),
                                    ty: Box::new(self.term(ty)),
                                },
                                self.span(i),
                            ),
                            None => term,
                        }
                    }))
                    .collect()
            })
            .unwrap_or_default();
        SurfaceTerm::new(
            TermKind::Perform {
                effect: tauto_surface::identity::Name::Spelled(effect),
                args,
            },
            span,
        )
    }

    pub(super) fn match_expr(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let Some(scrutinee) = self.first(id, Nt::Cond) else {
            return self.other(id);
        };
        let mut arms = Vec::new();
        let mut nodes = Vec::new();
        // Only under `Arms`: a `match` in the scrutinee has arms of its own.
        if let Some(body) = self.first(id, Nt::Arms) {
            self.descend(body, Nt::Arm, &mut nodes);
        }
        for arm in nodes {
            // `A | B => e` is the arms `A => e` and `B => e`: the sugar is the
            // arms side by side, so exhaustiveness and the kernel see only those.
            let mut patterns = self
                .first(arm, Nt::Pattern)
                .map(|p| self.pattern_alternatives(p))
                .unwrap_or_else(|| vec![Pattern::Other("Arm".into())]);
            // `y: T =>`: only a name takes a type.
            if let Some(ty) = self.first(arm, Nt::ArmType) {
                patterns = match patterns.as_slice() {
                    [Pattern::Bind { name, unused }] => vec![Pattern::Typed {
                        name: name.clone(),
                        ty: Box::new(self.term(ty)),
                        unused: *unused,
                    }],
                    _ => vec![Pattern::Other(
                        "a type after a pattern that is not a name".into(),
                    )],
                };
            }
            let guard = self.first(arm, Nt::Cond).map(|g| self.term(g));
            // `C => ⊢ G from p`: the goal and the proof are under the arm's body.
            let goal = self
                .first(arm, Nt::ArmBody)
                .and_then(|b| self.goal_expr(b))
                .and_then(|g| self.ty(g))
                .map(|g| self.term(g));
            // The arm's goal is checked by the arm itself; its body is the `p` under it.
            let body = match self.first(arm, Nt::ArmBody) {
                Some(b) => match self.goal_expr(b) {
                    Some(g) => self.goal_body(g),
                    None => self.term(b),
                },
                None => self.other(arm),
            };
            for pattern in patterns {
                arms.push(MatchArm {
                    pattern,
                    guard: guard.clone(),
                    goal: goal.clone(),
                    body: body.clone(),
                });
            }
        }
        SurfaceTerm::new(
            TermKind::Match {
                // `match x: T`: the scrutinee's type, as `(x: T)`.
                scrutinee: Box::new(match self.ty(id) {
                    Some(ty) => SurfaceTerm::new(
                        TermKind::Ascribe {
                            term: Box::new(self.term(scrutinee)),
                            ty: Box::new(self.term(ty)),
                        },
                        self.span(scrutinee),
                    ),
                    None => self.term(scrutinee),
                }),
                result: None,
                binder: self
                    .bind_name_of(id)
                    .map(|(n, _)| n)
                    .or_else(|| self.first(id, Nt::Ident).map(|i| self.name_of(i).into())),
                binder_unused: self.bind_name_of(id).and_then(|(_, u)| u),
                arms,
            },
            span,
        )
    }

    /// `by t!(arg): G0 { Δ ⊢ G from p … }`.
    pub(super) fn step_expr(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let Some(call) = self.first(id, Nt::MacroCall) else {
            return self.other(id);
        };
        let TermKind::MacroCall { name, arg } = (*self.term(call).kind).clone() else {
            return self.other(id);
        };
        let mut arms = Vec::new();
        let mut nodes = Vec::new();
        if let Some(body) = self.first(id, Nt::StepBody) {
            self.descend(body, Nt::StepArm, &mut nodes);
        }
        for arm in nodes {
            let mut unused_binders = Vec::new();
            let binders = self
                .all(arm, Nt::StepBinder)
                .into_iter()
                .map(|b| {
                    let (name, unused) = self.bind_name_of(b).unwrap_or_else(|| {
                        (
                            self.first(b, Nt::Ident)
                                .map(|i| Name::Spelled(self.name_of(i)))
                                .unwrap_or_default(),
                            None,
                        )
                    });
                    unused_binders.push(unused);
                    let ty = self
                        .ty(b)
                        .map(|t| self.term(t))
                        .unwrap_or_else(|| self.other(b));
                    (name, ty)
                })
                .collect();
            let goal = self
                .ty(arm)
                .map(|t| self.term(t))
                .unwrap_or_else(|| self.other(arm));
            let body = self
                .first(arm, Nt::Expr)
                .map(|e| self.term(e))
                .unwrap_or_else(|| self.other(arm));
            arms.push(StepArm {
                binders,
                unused_binders,
                goal,
                body,
                span: self.span(arm),
            });
        }
        SurfaceTerm::new(
            TermKind::Step(Box::new(Step {
                tactic: name,
                arg: *arg,
                call: self.span(call),
                before: self.ty(id).map(|t| self.term(t)),
                arms,
            })),
            span,
        )
    }

    fn field_patterns(&self, node: NodeId, out: &mut Vec<NodeId>) {
        for c in self.cst.children(node) {
            match self.nt(c) {
                Some(Nt::FieldPattern) => out.push(c),
                Some(Nt::FieldPatternsTail) => self.field_patterns(c, out),
                _ => {}
            }
        }
    }

    /// The patterns of `p | q | …` as the arms' patterns, one each. Every
    /// alternative names a constructor (or a literal) and binds the same names;
    /// an alternative that is `_` is not allowed, since it would stand for every
    /// constructor without naming it. A pattern without `|` is itself.
    pub(super) fn pattern_alternatives(&self, id: NodeId) -> Vec<Pattern> {
        let alts: Vec<Pattern> = self
            .all(id, Nt::PatternAlt)
            .into_iter()
            .map(|a| self.pattern_alt(a))
            .collect();
        if alts.len() < 2 {
            return alts;
        }
        if alts.iter().any(|p| matches!(p, Pattern::Wild)) {
            return vec![Pattern::Other("`_` in alternatives".into())];
        }
        let first = alt_binders(&alts[0]);
        if alts[1..].iter().any(|p| alt_binders(p) != first) {
            return vec![Pattern::Other(
                "alternatives binding different names".into(),
            )];
        }
        alts
    }

    pub(super) fn pattern(&self, id: NodeId) -> Pattern {
        let alts = self.all(id, Nt::PatternAlt);
        let [alt] = alts.as_slice() else {
            return Pattern::Other("alternatives".into());
        };
        self.pattern_alt(*alt)
    }

    fn pattern_alt(&self, alt: NodeId) -> Pattern {
        let alt = &alt;
        // `@a p`: `p` on the member labelled `a`.
        if let Some(label) = self.first(*alt, Nt::LabelPattern) {
            let tag = self
                .first(label, Nt::TagPrefix)
                .and_then(|t| self.first(t, Nt::Ident))
                .map(|i| self.text(i).trim().to_string())
                .unwrap_or_default();
            return match self.first(label, Nt::PatternAlt) {
                Some(inner) => Pattern::labelled(&tag, self.pattern_alt(inner)),
                None => Pattern::Other("LabelPattern".into()),
            };
        }
        if let Some(path) = self.first(*alt, Nt::PathPattern) {
            return self.path_pattern(path);
        }
        if let Some(lent) = self.first(*alt, Nt::LentPattern) {
            return self.lent_pattern(lent);
        }
        self.pattern_alt_rest(alt)
    }

    /// The fields of `C { f, g: p }`: `f` alone binds `f`.
    fn record_field_patterns(&self, list: NodeId) -> Vec<(String, Pattern)> {
        let mut fields = Vec::new();
        let mut found = Vec::new();
        self.field_patterns(list, &mut found);
        for f in found {
            let (fname, funused) = match self.bind_name_of(f) {
                Some(b) => b,
                None => {
                    let Some(field) = self.label_of(f) else {
                        continue;
                    };
                    (Name::Spelled(self.text(field).to_string()), None)
                }
            };
            let field = fname.to_string();
            let p = match self.first(f, Nt::Pattern) {
                Some(p) => self.pattern(p),
                None => Pattern::Bind {
                    name: Name::Spelled(field.clone()),
                    unused: funused,
                },
            };
            fields.push((field, p));
        }
        fields
    }

    /// `&T { f, … }`: the record of the `struct &T` of `T`, which is declared
    /// under `&T`, as `&T { f: e }` builds it.
    fn lent_pattern(&self, lent: NodeId) -> Pattern {
        let name = self
            .first(lent, Nt::Ident)
            .map(|i| format!("&{}", super::unraw(self.text(i).trim())))
            .unwrap_or_default();
        let fields = self
            .first(lent, Nt::FieldPatterns)
            .map(|list| self.record_field_patterns(list))
            .unwrap_or_default();
        Pattern::Record {
            name: tauto_surface::identity::Name::Spelled(name),
            fields,
        }
    }

    /// `x`, `_`, `^x`, `C(p, …)`, `C { f, … }`, `C<n: p>(…)`: a `PathPattern`,
    /// or the `LetPathPattern` of a `let`, which is never a bare name.
    fn path_pattern(&self, path: NodeId) -> Pattern {
        // Lone `_` is the Wild token, not an Ident.
        if self.first(path, Nt::Wild).is_some()
            && self.first(path, Nt::BindName).is_none()
            && self.first(path, Nt::PatternArgs).is_none()
            && self.first(path, Nt::PatternImplicits).is_none()
        {
            return Pattern::Wild;
        }
        let simple = self.first(path, Nt::PatternArgs).is_none()
            && self.first(path, Nt::PatternImplicits).is_none()
            && self.first(path, Nt::BindName).is_some()
            && self.all(path, Nt::Dot).is_empty();
        if simple {
            let (name, unused) = self.bind_name_of(path).unwrap_or_else(|| {
                (
                    Name::Spelled(
                        self.first(path, Nt::Ident)
                            .map(|i| super::unraw(self.text(i).trim()).to_string())
                            .unwrap_or_default(),
                    ),
                    None,
                )
            });
            // A lone Ident `_` must not remain after the Wild token split.
            if name.as_str() == "_" {
                return Pattern::Wild;
            }
            return Pattern::Bind { name, unused };
        }
        // `BindName` wraps the Ident; direct `Ident` children are gone.
        let name = self
            .bind_name_of(path)
            .map(|(n, _)| n.to_string())
            .unwrap_or_else(|| {
                self.all(path, Nt::Ident)
                    .iter()
                    .map(|id| self.text(*id).trim().to_owned())
                    .collect::<Vec<_>>()
                    .join(SEPARATOR)
            });
        // `C<n: m>(…)`: the implicit arguments named, carried first as a
        // record the elaborator places by the generics' names.
        let implicits: Vec<Pattern> = self
            .first(path, Nt::PatternImplicits)
            .map(|list| {
                let fields = self
                    .all(list, Nt::PatternImplicit)
                    .into_iter()
                    .filter_map(|i| {
                        let n = self.first(i, Nt::Ident)?;
                        let p = self.first(i, Nt::Pattern)?;
                        Some((
                            super::unraw(self.text(n).trim()).to_string(),
                            self.pattern(p),
                        ))
                    })
                    .collect();
                vec![Pattern::Record {
                    name: tauto_surface::IMPLICITS.into(),
                    fields,
                }]
            })
            .unwrap_or_default();
        let Some(args) = self.first(path, Nt::PatternArgs) else {
            return Pattern::Ctor {
                name: tauto_surface::identity::Name::Spelled(name),
                args: implicits,
            };
        };
        if let Some(list) = self.first(args, Nt::FieldPatterns) {
            return Pattern::Record {
                name: tauto_surface::identity::Name::Spelled(name),
                fields: self.record_field_patterns(list),
            };
        }
        let mut all = implicits;
        all.extend(
            self.all(args, Nt::Pattern)
                .into_iter()
                .map(|p| self.pattern(p)),
        );
        Pattern::Ctor {
            name: tauto_surface::identity::Name::Spelled(name),
            args: all,
        }
    }

    fn pattern_alt_rest(&self, alt: &NodeId) -> Pattern {
        // `#(a, b)`: a product's pattern; `#()` is the constructor `Star` of the
        // unit, written with the prelude's full name, so a file's own `Star` is
        // not meant.
        if let Some(tuple) = self.first(*alt, Nt::ProductPattern) {
            let items: Vec<Pattern> = self
                .all(tuple, Nt::Pattern)
                .into_iter()
                .map(|p| self.pattern(p))
                .collect();
            return match items.len() {
                0 => Pattern::Ctor {
                    name: tauto_surface::identity::Name::Spelled(prelude_name("Star")),
                    args: Vec::new(),
                },
                1 => Pattern::Other("one-member product".into()),
                _ => Pattern::product(items),
            };
        }
        // `[x, ..rest]`: `Cons(x, rest)`, and `[]` is `Nil`, the patterns the
        // constructors make, as `[x, ..rest]` the term does.
        if let Some(list) = self.first(*alt, Nt::ListPattern) {
            let mut items: Vec<Pattern> = Vec::new();
            let mut tail = None;
            let mut next = self.first(list, Nt::ListPatternItems);
            while let Some(at) = next {
                next = None;
                for c in self.cst.children(at) {
                    match self.nt(c) {
                        Some(Nt::Pattern) => items.push(self.pattern(c)),
                        Some(Nt::ListPatternRest) => {
                            tail = if self.first(c, Nt::Wild).is_some() {
                                Some(Pattern::Wild)
                            } else {
                                self.bind_name_of(c).map(|(name, unused)| {
                                    if name.as_str() == "_" {
                                        Pattern::Wild
                                    } else {
                                        Pattern::Bind { name, unused }
                                    }
                                })
                            };
                        }
                        Some(Nt::ListPatternItems) => next = Some(c),
                        _ => {}
                    }
                }
            }
            let nil = Pattern::Ctor {
                name: tauto_surface::identity::Name::Spelled("Nil".into()),
                args: Vec::new(),
            };
            return items
                .into_iter()
                .rev()
                .fold(tail.unwrap_or(nil), |rest, item| Pattern::Ctor {
                    name: tauto_surface::identity::Name::Spelled("Cons".into()),
                    args: vec![item, rest],
                });
        }
        let Some(lit) = self.first(*alt, Nt::LiteralPattern) else {
            return Pattern::Other("PatternAlt".into());
        };
        let text = self.text(lit);
        let text = text.trim();
        if self.first(lit, Nt::True).is_some() {
            Pattern::Bool(true)
        } else if self.first(lit, Nt::False).is_some() {
            Pattern::Bool(false)
        } else if self.first(lit, Nt::Text).is_some() {
            Pattern::Text(super::unquote_text(text))
        } else {
            match text.replace([' ', '_'], "").parse::<i64>() {
                Ok(n) => Pattern::Int(n),
                Err(_) => Pattern::Other("number pattern".into()),
            }
        }
    }

    pub(super) fn handle(&self, id: NodeId, span: Span) -> SurfaceTerm {
        let Some(subject) = self.first(id, Nt::HandleSubject) else {
            return self.other(id);
        };
        let Some(body) = self.first(subject, Nt::Block) else {
            return self.other(id);
        };
        let mut handlers = Vec::new();
        let mut withs = Vec::new();
        // Only the tail: the body block can hold `handle`s of its own, whose
        // `with`s are not this one's.
        if let Some(tail) = self.first(subject, Nt::HandleTail) {
            self.descend(tail, Nt::HandleWith, &mut withs);
        }
        // Each `with` wraps the ones before it; the evaluator reads the list as
        // written, so the nesting is kept as nested `Handle` terms.
        let mut term = self.term(body);
        for with in withs {
            handlers.clear();
            let mut hs = Vec::new();
            self.descend(with, Nt::Handler, &mut hs);
            for h in hs {
                handlers.push(self.handler(h));
            }
            term = SurfaceTerm::new(
                TermKind::Handle {
                    body: Box::new(term),
                    handlers: std::mem::take(&mut handlers),
                },
                span,
            );
        }
        term
    }

    fn handler(&self, id: NodeId) -> Handler {
        let body = |s: &Self| {
            s.first(id, Nt::Expr)
                .map(|e| s.term(e))
                .unwrap_or_else(|| s.other(id))
        };
        if let Some(r) = self.first(id, Nt::ReturnHandler) {
            let pattern = self
                .first(r, Nt::Pattern)
                .map(|p| self.pattern(p))
                .unwrap_or(Pattern::Other("return".into()));
            let body = self
                .first(r, Nt::Expr)
                .map(|e| self.term(e))
                .unwrap_or_else(|| self.other(r));
            return Handler::Return { pattern, body };
        }
        let Some(op) = self.first(id, Nt::OperationHandler) else {
            return Handler::Return {
                pattern: Pattern::Wild,
                body: body(self),
            };
        };
        let effect = self
            .first(op, Nt::OperationName)
            .map(|n| self.name_of(n))
            .unwrap_or_default();
        let instance = Instance {
            forall: self
                .first(op, Nt::EffectForall)
                .map(|f| {
                    self.all(f, Nt::Ident)
                        .into_iter()
                        .map(|i| self.name_of(i).into())
                        .collect()
                })
                .unwrap_or_default(),
            args: self
                .first(op, Nt::OperationTypes)
                .map(|t| {
                    self.all(t, Nt::OperationType)
                        .into_iter()
                        .map(|a| self.term(a))
                        .collect()
                })
                .unwrap_or_default(),
        };
        let patterns = self
            .all(op, Nt::Pattern)
            .into_iter()
            .map(|p| self.pattern(p))
            .collect();
        // `, k` / `, ^k` is the BindName after the closing parenthesis.
        let cont_bind = self
            .cst
            .children(op)
            .into_iter()
            .rfind(|c| self.nt(*c) == Some(Nt::BindName))
            .map(|b| self.bind_name(b));
        let (cont, cont_unused) = match cont_bind {
            Some((name, unused)) => (Some(name), unused),
            None => (
                self.cst
                    .children(op)
                    .into_iter()
                    .rfind(|c| self.nt(*c) == Some(Nt::Ident))
                    .map(|i| Name::from(self.name_of(i))),
                None,
            ),
        };
        let guard = self.first(op, Nt::Cond).map(|g| self.term(g));
        let body = self
            .first(op, Nt::Expr)
            .map(|e| self.term(e))
            .unwrap_or_else(|| self.other(op));
        Handler::Operation {
            effect: tauto_surface::identity::Name::Spelled(effect),
            instance,
            patterns,
            cont,
            cont_unused,
            guard,
            body,
        }
    }
}

/// The full name of a declaration of the prelude (`std::prelude::Pair`).
fn prelude_name(n: &str) -> String {
    format!(
        "{}{}{n}",
        super::qualify::PRELUDE_MODULE,
        super::qualify::SEPARATOR
    )
}
