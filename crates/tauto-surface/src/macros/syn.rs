//! The surface syntax as a macro's values and back: [`Lift`] reads a term, a statement or a pattern as the `Syn…` values
//! of `std/prelude/Macro.taut` (what `quote` and `${…}` make), [`Lower`] writes
//! the values a macro returns as the surface syntax again.

use tauto_message::msg;
use tauto_parol::Span;

use super::node::Node;
use super::scope::{self, flip, mark};
use crate::surface::{
    BudgetLimit, Constructor, DataConstructor, DataDecl, EffectDecl, FnDecl, Handler,
    InductiveDecl, Instance, MatchArm, Pattern, Stmt, SurfaceTerm, SyntaxLit, TermKind,
    TheoremDecl,
};

type R<T> = Result<T, String>;

fn st(name: &str, fields: Vec<(&str, Node)>) -> Node {
    Node::Ctor(
        name.to_string(),
        fields
            .into_iter()
            .map(|(n, f)| (Some(n.to_string()), f))
            .collect(),
    )
}

fn ex(ctor: &str, fields: Vec<Node>) -> Node {
    Node::ctor(&format!("SynExpr::{ctor}"), fields)
}

fn stm(ctor: &str, fields: Vec<Node>) -> Node {
    Node::ctor(&format!("SynStmt::{ctor}"), fields)
}

fn pt(ctor: &str, fields: Vec<Node>) -> Node {
    Node::ctor(&format!("SynPattern::{ctor}"), fields)
}

fn param(name: Node, ty: Node) -> Node {
    Node::product(vec![(None, "SynExpr", ty), (None, "SynIdent", name)])
}

fn members<'n>(p: &'n Node, a: &str, b: &str) -> Result<(&'n Node, &'n Node), String> {
    match (p.member(None, a), p.member(None, b)) {
        (Some(x), Some(y)) => Ok((x, y)),
        _ => Err(format!("expected {a} × {b}")),
    }
}

fn list(items: Vec<Node>) -> Node {
    Node::List(items)
}

/// The generics as a macro sees them: a row variable keeps its `!`, `!e`.
fn generic_texts(names: &[String], rows: &[bool]) -> Node {
    let written: Vec<String> = names
        .iter()
        .enumerate()
        .map(|(i, n)| {
            if rows.get(i).copied().unwrap_or(false) {
                format!("!{n}")
            } else {
                n.clone()
            }
        })
        .collect();
    texts(&written)
}

/// The names and the row flags of generics read back from `generic_texts`.
fn split_generics(items: Vec<String>) -> (Vec<String>, Vec<bool>) {
    items
        .into_iter()
        .map(|g| match g.strip_prefix('!') {
            Some(name) => (name.to_string(), true),
            None => (g, false),
        })
        .unzip()
}

fn texts(items: &[String]) -> Node {
    list(items.iter().map(|t| Node::text(t)).collect())
}

fn span_node(at: u32) -> Node {
    st("SynSpan", vec![("id", Node::Int(i64::from(at)))])
}

/// `f(x)` in the surface syntax, at `span`.
/// `xs` of a `$xs...`: a list whose values a `quote` puts in where a list goes.
fn spread(name: &str) -> Option<&str> {
    name.strip_prefix('$')?.strip_suffix("...")
}

fn call(f: &str, args: Vec<SurfaceTerm>, span: Span) -> SurfaceTerm {
    SurfaceTerm::new(
        TermKind::App {
            function: Box::new(SurfaceTerm::var(f, span)),
            arguments: args,
        },
        span,
    )
}

/// Reads the surface syntax as values. With `quote`, a name that starts
/// with `$` and `$(e)` are filled in with what they name.
pub struct Lift<'a> {
    /// The scopes every name carries: none for a `quote` (its own tote's, which
    /// the names do not need), the call's for the text of a macro's input.
    pub scopes: &'a [u64],
    pub quote: bool,
    /// Variables of a typed macro's context, by name: written as their atom.
    pub atoms: Option<&'a std::collections::HashMap<String, u64>>,
    /// When given, every node gets a span of its own, found again by the
    /// number: the position, and in the high bits which of the nodes that start there.
    pub spans: Option<&'a std::cell::RefCell<SpanTable>>,
    /// Names already carry the scopes of a `Lower` that flipped this expansion's
    /// scope; flip it back (`syn_expand`).
    pub reflip: Option<u64>,
}

#[derive(Default)]
pub struct SpanTable {
    seen: std::collections::HashMap<u32, u32>,
    pub issued: Vec<(u64, Span)>,
    pub terms: Vec<(u64, crate::surface::TermId)>,
}

impl Lift<'_> {
    fn ctx(&self) -> Node {
        self.ctx_of(self.scopes)
    }

    fn ctx_of(&self, scopes: &[u64]) -> Node {
        st(
            "SynCtx",
            vec![(
                "scopes",
                list(scopes.iter().map(|s| Node::Int(*s as i64)).collect()),
            )],
        )
    }

    fn span(&self, span: Span) -> Node {
        self.span_for(span, None)
    }

    fn span_for(&self, span: Span, occurrence: Option<crate::surface::TermId>) -> Node {
        match self.spans {
            None => span_node(span.start),
            Some(table) => {
                let mut table = table.borrow_mut();
                let k = table.seen.entry(span.start).or_insert(0);
                let id = u64::from(span.start) | (u64::from(*k) << 32);
                *k += 1;
                table.issued.push((id, span));
                if let Some(occurrence) = occurrence {
                    table.terms.push((id, occurrence));
                }
                st("SynSpan", vec![("id", Node::Int(id as i64))])
            }
        }
    }

    /// A name: the value of the name after `$`, when it is one.
    fn ident(&self, name: &str, span: Span) -> Node {
        self.ident_at(name, span, self.span(span))
    }

    fn ident_at(&self, name: &str, span: Span, syntax_span: Node) -> Node {
        if self.quote
            && let Some(var) = name.strip_prefix('$')
        {
            return Node::Splice(Box::new(SurfaceTerm::var(var, span)));
        }
        let (name, ctx) = match self.reflip {
            Some(scope) => {
                let (base, _) = scope::split(name);
                (base, self.ctx_of(&flip(&scope::scopes_of(name), scope)))
            }
            None => (name, self.ctx()),
        };
        st(
            "SynIdent",
            vec![
                ("name", Node::text(name)),
                ("ctx", ctx),
                ("span", syntax_span),
            ],
        )
    }

    fn ident_text(&self, name: &str) -> Node {
        // A name written as text (a field, a tag): no scopes.
        Node::text(name)
    }

    fn opt_expr(&self, t: &Option<SurfaceTerm>) -> R<Node> {
        Ok(Node::opt(match t {
            Some(t) => Some(self.expr(t)?),
            None => None,
        }))
    }

    fn exprs(&self, items: &[SurfaceTerm]) -> R<Node> {
        let mut out = Vec::new();
        for i in items {
            match self.spread_of(i) {
                Some(xs) => out.push(xs),
                None => out.push(self.expr(i)?),
            }
        }
        Ok(list(out))
    }

    /// A `$xs...` of a `quote`, as the list it puts in.
    fn spread_of(&self, t: &SurfaceTerm) -> Option<Node> {
        let TermKind::Var(n) = &*t.kind else {
            return None;
        };
        self.spread_name(n, t.span)
    }

    fn spread_name(&self, n: &str, span: Span) -> Option<Node> {
        let xs = spread(n).filter(|_| self.quote)?;
        Some(Node::SpliceList(Box::new(SurfaceTerm::var(xs, span))))
    }

    fn binder(&self, name: &str, ty: Option<Node>, span: Span) -> Node {
        Node::ctor(
            "SynBinder::BName",
            vec![self.ident(name, span), Node::opt(ty)],
        )
    }

    pub fn expr(&self, t: &SurfaceTerm) -> R<Node> {
        let span = self.span_for(t.span, Some(t.id()));
        Ok(match &*t.kind {
            TermKind::Var(n) => {
                if self.quote && spread(n).is_some() {
                    return Err(msg!("surface-quote-spread-expr", name = n).to_string());
                } else if self.quote && n.starts_with('$') {
                    // A name or an expression: `syn_expr_of` takes either.
                    let inner = SurfaceTerm::var(&n[1..], t.span);
                    Node::Splice(Box::new(call("Syn::expr_of", vec![inner], t.span)))
                } else if let Some(atom) = self.atoms.and_then(|a| a.get(n)) {
                    ex("ExAtom", vec![Node::Int(*atom as i64), span])
                } else {
                    ex("ExVar", vec![self.ident_at(n, t.span, span)])
                }
            }
            TermKind::Splice(inner) => {
                if !self.quote {
                    return Err(msg!("surface-quote-splice-outside").to_string());
                }
                Node::Splice(Box::new(call(
                    "Syn::expr_of",
                    vec![(**inner).clone()],
                    t.span,
                )))
            }
            TermKind::Nat(s) => ex("ExNat", vec![Node::text(s), span]),
            TermKind::Float(s) => {
                return Err(msg!("surface-quote-float", literal = s).to_string());
            }
            TermKind::Text(s) => ex("ExText", vec![Node::text(s), span]),
            TermKind::Bool(b) => ex("ExBool", vec![Node::Bool(*b), span]),
            // `#()`, the unit, is a node of its own.
            TermKind::App {
                function,
                arguments,
            } if arguments.is_empty()
                && matches!(&*function.kind, TermKind::Var(f) if f == "Tuple") =>
            {
                ex("ExUnit", vec![span])
            }
            TermKind::App {
                function,
                arguments,
            } => ex(
                "ExApp",
                vec![self.expr(function)?, self.exprs(arguments)?, span],
            ),
            TermKind::Pi {
                params,
                result,
                effects,
            } => {
                let mut ps = Vec::new();
                for (name, ty) in params {
                    ps.push(st(
                        "SynParam",
                        vec![
                            (
                                "name",
                                Node::opt(name.as_ref().map(|n| self.ident(n, t.span))),
                            ),
                            ("ty", self.expr(ty)?),
                        ],
                    ));
                }
                ex(
                    "ExPi",
                    vec![
                        list(ps),
                        self.expr(result)?,
                        Node::opt(effects.as_ref().map(|e| texts(e))),
                        span,
                    ],
                )
            }
            TermKind::Exists {
                binder,
                domain,
                body,
            } => ex(
                "ExExists",
                vec![
                    self.binder(binder, None, t.span),
                    self.expr(domain)?,
                    self.expr(body)?,
                    span,
                ],
            ),
            TermKind::Lam {
                params,
                body,
                types,
            } => ex(
                "ExLam",
                vec![
                    list(
                        params
                            .iter()
                            .enumerate()
                            .map(|(i, p)| {
                                let ty = match types.get(i) {
                                    Some(Some(ty)) => Some(self.expr(ty)?),
                                    _ => None,
                                };
                                Ok(self
                                    .spread_name(p, t.span)
                                    .unwrap_or_else(|| self.binder(p, ty, t.span)))
                            })
                            .collect::<R<Vec<_>>>()?,
                    ),
                    self.expr(body)?,
                    span,
                ],
            ),
            TermKind::Union(items) => ex("ExUnion", vec![self.exprs(items)?, span]),
            TermKind::Tagged { tag, term } => ex(
                "ExTagged",
                vec![self.ident_text(tag), self.expr(term)?, span],
            ),
            TermKind::If {
                condition,
                then,
                otherwise,
            } => ex(
                "ExIf",
                vec![
                    self.expr(condition)?,
                    self.expr(then)?,
                    Node::opt(match otherwise {
                        Some(o) => Some(self.expr(o)?),
                        None => None,
                    }),
                    span,
                ],
            ),
            TermKind::Field { base, name } => ex(
                "ExField",
                vec![self.expr(base)?, self.ident_text(name), span],
            ),
            TermKind::Block(stmts) => ex("ExBlock", vec![self.stmts(stmts)?, span]),
            TermKind::Perform { effect, args } => ex(
                "ExPerform",
                vec![self.ident(effect, t.span), self.exprs(args)?, span],
            ),
            TermKind::Handle { body, handlers } => {
                let mut hs = Vec::new();
                for h in handlers {
                    hs.push(self.handler(h, t.span)?);
                }
                ex("ExHandle", vec![self.expr(body)?, list(hs), span])
            }
            TermKind::Budget { limit, steps, body } => {
                let ctor = match limit {
                    BudgetLimit::Steps => "ExBudget",
                    BudgetLimit::Memory => "ExBudgetMemory",
                };
                ex(ctor, vec![self.expr(steps)?, self.expr(body)?, span])
            }
            TermKind::Match {
                scrutinee,
                result,
                binder,
                arms,
            } => {
                let mut as_ = Vec::new();
                for a in arms {
                    as_.push(self.arm(a, t.span)?);
                }
                ex(
                    "ExMatch",
                    vec![
                        self.expr(scrutinee)?,
                        Node::opt(match result {
                            Some(r) => Some(self.expr(r)?),
                            None => None,
                        }),
                        list(as_),
                        Node::opt(binder.as_ref().map(|h| self.ident(h, t.span))),
                        span,
                    ],
                )
            }
            TermKind::Record { base: Some(_), .. } => {
                return Err(
                    "a struct literal with `..` is written out before macros see it".into(),
                );
            }
            // `#(a, b)` is quoted as the record of the prelude's `Pair` it is read as
            // where it is elaborated.
            TermKind::Tuple(_) => {
                let pair = format!(
                    "{}{}Pair",
                    crate::surface::qualify::PRELUDE_MODULE,
                    crate::surface::qualify::SEPARATOR
                );
                return self.expr(&crate::surface::qualify::tuple_as_pairs(t, &pair));
            }
            TermKind::Record { name, fields, .. } => {
                let mut fs = Vec::new();
                for (n, v) in fields {
                    fs.push(Node::product(vec![
                        (None, "SynExpr", self.expr(v)?),
                        (None, "Text", self.ident_text(n)),
                    ]));
                }
                ex("ExRecord", vec![self.ident(name, t.span), list(fs), span])
            }
            TermKind::Borrow { mutable, term } => ex(
                "ExBorrow",
                vec![Node::Bool(*mutable), self.expr(term)?, span],
            ),
            TermKind::FnKind { kind, ty } => ex(
                "ExFnKind",
                vec![self.ident_text(kind), self.expr(ty)?, span],
            ),
            TermKind::BorrowLam { borrows, lam } => ex(
                "ExBorrowLam",
                vec![
                    list(
                        borrows
                            .iter()
                            .map(|b| Node::opt(b.map(Node::Bool)))
                            .collect(),
                    ),
                    self.expr(lam)?,
                    span,
                ],
            ),
            // A literal stays text; an expression is the argument of an untyped or a
            // typed macro, and is passed on as syntax.
            TermKind::MacroCall { name, arg } => match &*arg.kind {
                TermKind::SyntaxLit(lit) => ex(
                    "ExMacroCall",
                    vec![
                        self.ident(name, t.span),
                        Node::text(&lit.text),
                        span_node(lit.start),
                    ],
                ),
                _ => ex(
                    "ExMacroExpr",
                    vec![self.ident(name, t.span), self.expr(arg)?, span],
                ),
            },
            TermKind::Quote { .. } => return Err(msg!("surface-quote-in-quote").to_string()),
            TermKind::SyntaxLit(_) => {
                return Err(msg!("surface-quote-syntax-literal").to_string());
            }
            TermKind::Hole(name) => ex("ExHole", vec![Node::text(name), span]),
            TermKind::Step(_) => return Err(msg!("surface-quote-step").to_string()),
            TermKind::Row(_) => {
                return Err(msg!("surface-quote-row").to_string());
            }
            TermKind::Product(_) | TermKind::Ascribe { .. } => {
                return Err(msg!("surface-quote-product").to_string());
            }
            TermKind::Other(n) => return Err(msg!("surface-quote-other", what = n).to_string()),
        })
    }

    pub fn stmts(&self, stmts: &[Stmt]) -> R<Node> {
        Ok(list(self.stmt_list(stmts)?))
    }

    /// The statements of a `quote stmts { … }`: a lone `$name` is a list of
    /// statements to put in, and `$(e)` an expression to run.
    pub fn stmt_list(&self, stmts: &[Stmt]) -> R<Vec<Node>> {
        let mut out = Vec::new();
        for s in stmts {
            if self.quote
                && let Stmt::Expr(t) = s
                && let TermKind::Var(n) = &*t.kind
                && let Some(var) = n.strip_prefix('$')
            {
                let var = var.strip_suffix("...").unwrap_or(var);
                out.push(Node::SpliceList(Box::new(SurfaceTerm::var(var, t.span))));
                continue;
            }
            out.push(self.stmt(s)?);
        }
        Ok(out)
    }

    pub fn stmt(&self, s: &Stmt) -> R<Node> {
        Ok(match s {
            Stmt::Let {
                name,
                ty,
                value,
                borrow,
                borrow_mut,
            } => stm(
                "StLet",
                vec![
                    self.ident(name, value.span),
                    self.opt_expr(ty)?,
                    self.expr(value)?,
                    Node::Bool(*borrow),
                    Node::Bool(*borrow_mut),
                    self.span(value.span),
                ],
            ),
            Stmt::Var {
                name,
                ty,
                value,
                borrow,
            } => stm(
                "StVar",
                vec![
                    self.ident(name, value.span),
                    self.opt_expr(ty)?,
                    self.expr(value)?,
                    Node::Bool(*borrow),
                    self.span(value.span),
                ],
            ),
            Stmt::Assign { place: Some(_), .. } => {
                return Err(msg!("surface-quote-field-assign").to_string());
            }
            Stmt::Assign { name, value, .. } => stm(
                "StAssign",
                vec![
                    self.ident(name, value.span),
                    self.expr(value)?,
                    self.span(value.span),
                ],
            ),
            Stmt::Fn(f) => stm("StFn", vec![self.fn_decl(f)?]),
            Stmt::Expr(t) => match &*t.kind {
                TermKind::MacroCall { name, arg }
                    if matches!(&*arg.kind, TermKind::SyntaxLit(_)) =>
                {
                    let TermKind::SyntaxLit(lit) = &*arg.kind else {
                        unreachable!("matched above")
                    };
                    stm(
                        "StMacroCall",
                        vec![
                            self.ident(name, t.span),
                            Node::text(&lit.text),
                            span_node(lit.start),
                        ],
                    )
                }
                _ => stm("StExpr", vec![self.expr(t)?]),
            },
            Stmt::While { condition, body } => {
                stm("StWhile", vec![self.expr(condition)?, self.expr(body)?])
            }
            Stmt::Return(e) => stm("StReturn", vec![self.opt_expr(&e.clone())?]),
            Stmt::Theorem(d) => stm("StTheorem", vec![self.theorem(d)?]),
            Stmt::Def(d) => stm("StDef", vec![self.theorem(d)?]),
            Stmt::Struct(d) => stm("StStruct", vec![self.data(d)?]),
            Stmt::Enum(d) => stm("StEnum", vec![self.data(d)?]),
            Stmt::Inductive(d) => stm("StInductive", vec![self.inductive(d)?]),
            Stmt::Effect(e) => stm("StEffect", vec![self.effect(e)?]),
            Stmt::Mutual { items, span } => {
                stm("StMutual", vec![self.stmts(items)?, self.span(*span)])
            }
            Stmt::Import { .. }
            | Stmt::Extern { .. }
            | Stmt::Class(_)
            | Stmt::Instance(_)
            | Stmt::Syntax { .. }
            | Stmt::Macro { .. }
            | Stmt::Module { .. }
            | Stmt::Attributed { .. }
            | Stmt::Called { .. }
            | Stmt::Other(..) => return Err(msg!("surface-quote-statement").to_string()),
        })
    }

    fn fn_decl(&self, f: &FnDecl) -> R<Node> {
        let mut types = Vec::new();
        for t in &f.param_types {
            types.push(self.opt_expr(t)?);
        }
        Ok(st(
            "SynFn",
            vec![
                ("name", self.ident(&f.name, f.span)),
                ("generics", generic_texts(&f.generics, &f.rows)),
                (
                    "bounds",
                    list(
                        f.bounds
                            .iter()
                            .map(|b| Node::opt(b.as_ref().map(|b| Node::text(b))))
                            .collect(),
                    ),
                ),
                (
                    "params",
                    list(f.params.iter().map(|p| self.ident(p, f.span)).collect()),
                ),
                (
                    "borrows",
                    list(
                        f.borrows
                            .iter()
                            .map(|b| Node::opt(b.map(Node::Bool)))
                            .collect(),
                    ),
                ),
                ("param_types", list(types)),
                ("result", self.opt_expr(&f.result)?),
                ("effects", Node::opt(f.effects.as_ref().map(|e| texts(e)))),
                ("body", self.expr(&f.body)?),
                ("span", self.span(f.span)),
            ],
        ))
    }

    fn theorem(&self, d: &TheoremDecl) -> R<Node> {
        let mut params = Vec::new();
        for (n, t) in &d.params {
            params.push(param(self.ident(n, d.span), self.expr(t)?));
        }
        Ok(st(
            "SynTheorem",
            vec![
                ("name", self.ident(&d.name, d.span)),
                ("implicit", Node::Int(d.implicit as i64)),
                ("params", list(params)),
                ("ty", self.expr(&d.ty)?),
                ("body", self.opt_expr(&d.body)?),
                ("span", self.span(d.span)),
            ],
        ))
    }

    fn data(&self, d: &DataDecl) -> R<Node> {
        let mut ctors = Vec::new();
        for c in &d.constructors {
            ctors.push(self.ctor(c, d.span)?);
        }
        Ok(st(
            "SynData",
            vec![
                ("kind", Node::opt(d.kind.as_ref().map(|k| Node::text(k)))),
                ("name", self.ident(&d.name, d.span)),
                ("generics", generic_texts(&d.generics, &d.rows)),
                ("ctors", list(ctors)),
                ("span", self.span(d.span)),
            ],
        ))
    }

    fn params(&self, params: &[(String, SurfaceTerm)], span: Span) -> R<Node> {
        let mut out = Vec::new();
        for (n, t) in params {
            out.push(param(self.ident(n, span), self.expr(t)?));
        }
        Ok(list(out))
    }

    fn inductive(&self, d: &InductiveDecl) -> R<Node> {
        let mut ctors = Vec::new();
        for c in &d.constructors {
            ctors.push(st(
                "SynIndCtor",
                vec![
                    ("name", self.ident(&c.name, d.span)),
                    ("implicit", Node::Int(c.implicit as i64)),
                    ("params", self.params(&c.params, d.span)?),
                    ("result", self.expr(&c.result)?),
                ],
            ));
        }
        Ok(st(
            "SynInductive",
            vec![
                ("name", self.ident(&d.name, d.span)),
                ("params", self.params(&d.params, d.span)?),
                ("sort", self.expr(&d.sort)?),
                ("ctors", list(ctors)),
                ("span", self.span(d.span)),
            ],
        ))
    }

    fn ctor(&self, c: &DataConstructor, span: Span) -> R<Node> {
        let mut fields = Vec::new();
        for (n, t) in &c.fields {
            fields.push(Node::product(vec![
                (
                    None,
                    "Option(SynIdent)",
                    Node::opt(n.as_ref().map(|n| self.ident(n, span))),
                ),
                (None, "SynExpr", self.expr(t)?),
            ]));
        }
        Ok(st(
            "SynCtor",
            vec![
                ("name", self.ident(&c.name, span)),
                ("fields", list(fields)),
            ],
        ))
    }

    fn effect(&self, e: &EffectDecl) -> R<Node> {
        let mut params = Vec::new();
        for p in &e.params {
            params.push(self.opt_expr(p)?);
        }
        Ok(st(
            "SynEffect",
            vec![
                ("name", self.ident(&e.name, e.span)),
                ("generics", texts(&e.generics)),
                ("params", list(params)),
                ("result", self.opt_expr(&e.result)?),
                (
                    "resume",
                    Node::opt(e.resume.as_ref().map(|r| Node::text(r))),
                ),
                ("span", self.span(e.span)),
            ],
        ))
    }

    fn pattern(&self, p: &Pattern, span: Span) -> R<Node> {
        Ok(match p {
            Pattern::Wild => pt("PtWild", vec![]),
            Pattern::Bind(n) if self.quote && spread(n).is_some() => {
                return Err(msg!("surface-quote-spread-pattern", name = n).to_string());
            }
            Pattern::Bind(n) => pt("PtBind", vec![self.ident(n, span)]),
            Pattern::Int(i) => pt("PtInt", vec![Node::Int(*i)]),
            Pattern::Bool(b) => pt("PtBool", vec![Node::Bool(*b)]),
            Pattern::Text(t) => pt("PtText", vec![Node::text(t)]),
            Pattern::Ctor { name, args } => {
                let mut a = Vec::new();
                for x in args {
                    match x {
                        Pattern::Bind(n) if let Some(xs) = self.spread_name(n, span) => a.push(xs),
                        _ => a.push(self.pattern(x, span)?),
                    }
                }
                pt("PtCtor", vec![self.ident(name, span), list(a)])
            }
            Pattern::Record { name, fields } => {
                let mut a = Vec::new();
                for (n, x) in fields {
                    a.push(Node::product(vec![
                        (None, "SynPattern", self.pattern(x, span)?),
                        (None, "Text", Node::text(n)),
                    ]));
                }
                pt("PtRecord", vec![self.ident(name, span), list(a)])
            }
            // `#(p, q)` is quoted as the record of the prelude's `Pair` it is read as
            // where it is elaborated.
            Pattern::Tuple(_) => {
                let pair = format!(
                    "{}{}Pair",
                    crate::surface::qualify::PRELUDE_MODULE,
                    crate::surface::qualify::SEPARATOR
                );
                return self.pattern(
                    &crate::surface::qualify::tuple_pattern_as_pairs(p, &pair),
                    span,
                );
            }
            Pattern::Other(n) => return Err(msg!("surface-quote-pattern", what = n).to_string()),
        })
    }

    fn arm(&self, a: &MatchArm, span: Span) -> R<Node> {
        Ok(st(
            "SynArm",
            vec![
                ("pattern", self.pattern(&a.pattern, span)?),
                (
                    "guard",
                    Node::opt(match &a.guard {
                        Some(g) => Some(self.expr(g)?),
                        None => None,
                    }),
                ),
                (
                    "goal",
                    Node::opt(match &a.goal {
                        Some(g) => Some(self.expr(g)?),
                        None => None,
                    }),
                ),
                ("body", self.expr(&a.body)?),
            ],
        ))
    }

    fn handler(&self, h: &Handler, span: Span) -> R<Node> {
        Ok(match h {
            Handler::Return { pattern, body } => Node::ctor(
                "SynHandler::HReturn",
                vec![self.pattern(pattern, span)?, self.expr(body)?],
            ),
            Handler::Operation {
                effect,
                instance,
                patterns,
                cont,
                guard,
                body,
            } => {
                let mut types = Vec::new();
                for t in &instance.args {
                    types.push(self.expr(t)?);
                }
                let mut ps = Vec::new();
                for p in patterns {
                    ps.push(self.pattern(p, span)?);
                }
                Node::ctor(
                    "SynHandler::HOp",
                    vec![
                        self.ident(effect, span),
                        list(ps),
                        Node::opt(cont.as_ref().map(|c| self.ident(c, span))),
                        Node::opt(match guard {
                            Some(g) => Some(self.expr(g)?),
                            None => None,
                        }),
                        self.expr(body)?,
                        texts(&instance.forall),
                        list(types),
                    ],
                )
            }
        })
    }
}

/// Writes the values of a macro's output as the surface syntax. Every node
/// gets a span of its own (`origin.rs`), and a name the scopes of the
/// expansion `scope` flipped (`docs/design/macro.md`「衛生（スコープ集合）」, 5).
pub struct Lower<'a> {
    pub scope: u64,
    pub fresh: &'a mut dyn FnMut(u32) -> Span,
    /// The names made with `syn_ident_like`, for the trace.
    pub captures: Vec<String>,
    /// The atoms of the call's `Judgement`, and the names they stand for.
    pub atoms: &'a std::collections::HashMap<u64, String>,
    /// The atoms of binders `Judgement::open` opened, bound by the binder of the output
    /// that uses them, innermost last.
    pub opened: Vec<(u64, String)>,
}

/// An atom `Judgement::open` makes for the binder it opens is at least this; the
/// atoms of a call's context are below it.
pub const OPEN_ATOM: u64 = 1_000_000_000;

impl Lower<'_> {
    fn span_of(&mut self, n: &Node) -> R<Span> {
        let id = n
            .named("id")
            .and_then(Node::as_int)
            .ok_or("a SynSpan has an id")?;
        Ok((self.fresh)(id as u32))
    }

    fn ctor<'n>(&self, n: &'n Node, ty: &str) -> R<(&'n str, &'n Node)> {
        let name = n
            .ctor_name()
            .ok_or_else(|| format!("expected a {ty}, found something else"))?;
        Ok((name, n))
    }

    fn field<'n>(&self, n: &'n Node, i: usize) -> R<&'n Node> {
        n.field(i)
            .ok_or_else(|| format!("{} has no field {i}", n.ctor_name().unwrap_or("a value")))
    }

    fn list<'n>(&self, n: &'n Node) -> R<&'n [Node]> {
        n.as_list().ok_or_else(|| "expected a List".to_string())
    }

    fn text(&self, n: &Node) -> R<String> {
        n.as_text()
            .map(str::to_string)
            .ok_or_else(|| "expected a Text".to_string())
    }

    fn boolean(&self, n: &Node) -> R<bool> {
        n.as_bool().ok_or_else(|| "expected a Bool".to_string())
    }

    /// A name, marked with the scopes after the flip.
    fn ident(&mut self, n: &Node) -> R<String> {
        let name = self.text(n.named("name").ok_or("a SynIdent has a name")?)?;
        let ctx = n.named("ctx").ok_or("a SynIdent has a ctx")?;
        let scopes = ctx
            .named("scopes")
            .and_then(Node::as_list)
            .ok_or("a SynCtx has scopes")?;
        let scopes: Vec<u64> = scopes
            .iter()
            .filter_map(Node::as_int)
            .map(|i| i as u64)
            .collect();
        Ok(mark(&name, &flip(&scopes, self.scope)))
    }

    fn ident_span(&mut self, n: &Node) -> R<Span> {
        self.span_of(n.named("span").ok_or("a SynIdent has a span")?)
    }

    fn opt<T>(&mut self, n: &Node, f: &mut dyn FnMut(&mut Self, &Node) -> R<T>) -> R<Option<T>> {
        match n.as_option().ok_or("expected an Option")? {
            Some(inner) => Ok(Some(f(self, inner)?)),
            None => Ok(None),
        }
    }

    fn exprs(&mut self, n: &Node) -> R<Vec<SurfaceTerm>> {
        let items = self.list(n)?.to_vec();
        items.iter().map(|i| self.expr(i)).collect()
    }

    pub fn expr(&mut self, n: &Node) -> R<SurfaceTerm> {
        let (ctor, _) = self.ctor(n, "SynExpr")?;
        let term = |kind, span| SurfaceTerm::new(kind, span);
        let sp = |this: &mut Self, i: usize| -> R<Span> {
            let f = this.field(n, i)?;
            this.span_of(f)
        };
        Ok(match ctor {
            "ExVar" => {
                let id = self.field(n, 0)?;
                let name = self.ident(id)?;
                let span = self.ident_span(id)?;
                term(TermKind::Var(name), span)
            }
            "ExAtom" => {
                let atom = self.field(n, 0)?.as_int().ok_or("an atom is a number")?;
                let atom = atom as u64;
                let name = match self.opened.iter().rev().find(|(a, _)| *a == atom) {
                    Some((_, name)) => name.clone(),
                    None if atom >= OPEN_ATOM => {
                        return Err(msg!("surface-scope-extrusion", atom = atom).to_string());
                    }
                    None => self
                        .atoms
                        .get(&atom)
                        .ok_or("macro.unknown_atom: an atom is not one of the input's")?
                        .clone(),
                };
                term(TermKind::Var(name), sp(self, 1)?)
            }
            "ExNat" => term(TermKind::Nat(self.text(self.field(n, 0)?)?), sp(self, 1)?),
            "ExText" => term(TermKind::Text(self.text(self.field(n, 0)?)?), sp(self, 1)?),
            "ExBool" => term(
                TermKind::Bool(self.boolean(self.field(n, 0)?)?),
                sp(self, 1)?,
            ),
            "ExUnit" => {
                let span = sp(self, 0)?;
                SurfaceTerm::app("Tuple", Vec::new(), span)
            }
            "ExApp" => {
                let function = self.expr(self.field(n, 0)?)?;
                let arguments = self.exprs(self.field(n, 1)?)?;
                term(
                    TermKind::App {
                        function: Box::new(function),
                        arguments,
                    },
                    sp(self, 2)?,
                )
            }
            "ExPi" => {
                let mut params = Vec::new();
                for p in self.list(self.field(n, 0)?)?.to_vec() {
                    let name = match p.named("name").ok_or("a SynParam has a name")?.as_option() {
                        Some(Some(id)) => Some(self.ident(id)?),
                        _ => None,
                    };
                    params.push((
                        name,
                        self.expr(p.named("ty").ok_or("a SynParam has a ty")?)?,
                    ));
                }
                let result = self.expr(self.field(n, 1)?)?;
                let effects = self.opt(self.field(n, 2)?, &mut |this, e| {
                    this.list(e)?.iter().map(|t| this.text(t)).collect()
                })?;
                term(
                    TermKind::Pi {
                        params,
                        result: Box::new(result),
                        effects,
                    },
                    sp(self, 3)?,
                )
            }
            "ExLam" => {
                let mut params = Vec::new();
                let mut types = Vec::new();
                let depth = self.opened.len();
                for b in self.list(self.field(n, 0)?)?.to_vec() {
                    // The written type is read outside the parameters.
                    types.push(match b.ctor_name() {
                        Some("BName") => {
                            self.opt(self.field(&b, 1)?, &mut |this, e| this.expr(e))?
                        }
                        _ => None,
                    });
                    params.push(self.binder(&b)?);
                }
                if types.iter().all(Option::is_none) {
                    types.clear();
                }
                let body = self.expr(self.field(n, 1)?)?;
                self.opened.truncate(depth);
                term(
                    TermKind::Lam {
                        params,
                        body: Box::new(body),
                        types,
                    },
                    sp(self, 2)?,
                )
            }
            "ExIf" => {
                let condition = self.expr(self.field(n, 0)?)?;
                let then = self.expr(self.field(n, 1)?)?;
                let otherwise = self.opt(self.field(n, 2)?, &mut |this, e| this.expr(e))?;
                term(
                    TermKind::If {
                        condition: Box::new(condition),
                        then: Box::new(then),
                        otherwise: otherwise.map(Box::new),
                    },
                    sp(self, 3)?,
                )
            }
            "ExField" => {
                let base = self.expr(self.field(n, 0)?)?;
                let name = self.text(self.field(n, 1)?)?;
                term(
                    TermKind::Field {
                        base: Box::new(base),
                        name,
                    },
                    sp(self, 2)?,
                )
            }
            "ExBlock" => {
                let stmts = self.stmts(self.field(n, 0)?)?;
                term(TermKind::Block(stmts), sp(self, 1)?)
            }
            "ExPerform" => {
                let id = self.field(n, 0)?;
                let effect = self.ident(id)?;
                let args = self.exprs(self.field(n, 1)?)?;
                term(TermKind::Perform { effect, args }, sp(self, 2)?)
            }
            "ExHandle" => {
                let body = self.expr(self.field(n, 0)?)?;
                let mut handlers = Vec::new();
                for h in self.list(self.field(n, 1)?)?.to_vec() {
                    handlers.push(self.handler(&h)?);
                }
                term(
                    TermKind::Handle {
                        body: Box::new(body),
                        handlers,
                    },
                    sp(self, 2)?,
                )
            }
            "ExBudget" | "ExBudgetMemory" => {
                let steps = self.expr(self.field(n, 0)?)?;
                let body = self.expr(self.field(n, 1)?)?;
                let limit = if ctor == "ExBudget" {
                    BudgetLimit::Steps
                } else {
                    BudgetLimit::Memory
                };
                term(
                    TermKind::Budget {
                        limit,
                        steps: Box::new(steps),
                        body: Box::new(body),
                    },
                    sp(self, 2)?,
                )
            }
            "ExMatch" => {
                let scrutinee = self.expr(self.field(n, 0)?)?;
                let result = self.opt(self.field(n, 1)?, &mut |this, e| this.expr(e))?;
                let mut arms = Vec::new();
                for a in self.list(self.field(n, 2)?)?.to_vec() {
                    arms.push(self.arm(&a)?);
                }
                let binder = self.opt(self.field(n, 3)?, &mut |this, x| this.ident(x))?;
                term(
                    TermKind::Match {
                        binder,
                        scrutinee: Box::new(scrutinee),
                        result: result.map(Box::new),
                        arms,
                    },
                    sp(self, 4)?,
                )
            }
            "ExRecord" => {
                let id = self.field(n, 0)?;
                let name = self.ident(id)?;
                let mut fields = Vec::new();
                for p in self.list(self.field(n, 1)?)?.to_vec() {
                    let (k, v) = members(&p, "Text", "SynExpr")?;
                    fields.push((self.text(k)?, self.expr(v)?));
                }
                term(
                    TermKind::Record {
                        name,
                        fields,
                        base: None,
                    },
                    sp(self, 2)?,
                )
            }
            "ExBorrow" => {
                let mutable = self.boolean(self.field(n, 0)?)?;
                let inner = self.expr(self.field(n, 1)?)?;
                term(
                    TermKind::Borrow {
                        mutable,
                        term: Box::new(inner),
                    },
                    sp(self, 2)?,
                )
            }
            "ExUnion" => {
                let items = self.exprs(self.field(n, 0)?)?;
                term(TermKind::Union(items), sp(self, 1)?)
            }
            "ExTagged" => {
                let tag = self.text(self.field(n, 0)?)?;
                let inner = self.expr(self.field(n, 1)?)?;
                term(
                    TermKind::Tagged {
                        tag,
                        term: Box::new(inner),
                    },
                    sp(self, 2)?,
                )
            }
            "ExExists" => {
                let binder = self.binder(self.field(n, 0)?)?;
                let domain = self.expr(self.field(n, 1)?)?;
                let body = self.expr(self.field(n, 2)?)?;
                term(
                    TermKind::Exists {
                        binder,
                        domain: Box::new(domain),
                        body: Box::new(body),
                    },
                    sp(self, 3)?,
                )
            }
            "ExFnKind" => {
                let kind = self.text(self.field(n, 0)?)?;
                let ty = self.expr(self.field(n, 1)?)?;
                term(
                    TermKind::FnKind {
                        kind,
                        ty: Box::new(ty),
                    },
                    sp(self, 2)?,
                )
            }
            "ExBorrowLam" => {
                let mut borrows = Vec::new();
                for b in self.list(self.field(n, 0)?)?.to_vec() {
                    borrows.push(self.opt(&b, &mut |this, x| this.boolean(x))?);
                }
                let lam = self.expr(self.field(n, 1)?)?;
                term(
                    TermKind::BorrowLam {
                        borrows,
                        lam: Box::new(lam),
                    },
                    sp(self, 2)?,
                )
            }
            "ExMacroCall" => {
                let id = self.field(n, 0)?;
                let name = self.ident(id)?;
                let span = self.ident_span(id)?;
                let text = self.text(self.field(n, 1)?)?;
                let at = self
                    .field(n, 2)?
                    .named("id")
                    .and_then(Node::as_int)
                    .unwrap_or(0) as u32;
                term(
                    TermKind::MacroCall {
                        name,
                        arg: Box::new(term(
                            TermKind::SyntaxLit(Box::new(SyntaxLit {
                                name: None,
                                text,
                                start: at,
                                shifts: Vec::new(),
                                error: None,
                                span,
                            })),
                            span,
                        )),
                    },
                    span,
                )
            }
            "ExMacroExpr" => {
                let id = self.field(n, 0)?;
                let name = self.ident(id)?;
                let span = self.ident_span(id)?;
                let arg = self.expr(self.field(n, 1)?)?;
                term(
                    TermKind::MacroCall {
                        name,
                        arg: Box::new(arg),
                    },
                    span,
                )
            }
            "ExHole" => term(TermKind::Hole(self.text(self.field(n, 0)?)?), sp(self, 1)?),
            other => return Err(format!("{other} is not a SynExpr")),
        })
    }

    fn binder(&mut self, n: &Node) -> R<String> {
        match n.ctor_name() {
            Some("BName") => self.ident(self.field(n, 0)?),
            Some("BAtom") => {
                let atom = self.field(n, 0)?.as_int().ok_or("an atom is a number")? as u64;
                if atom >= OPEN_ATOM {
                    let name = format!("_a{atom}");
                    self.opened.push((atom, name.clone()));
                    return Ok(name);
                }
                self.atoms
                    .get(&atom)
                    .cloned()
                    .ok_or_else(|| "macro.unknown_atom: an atom is not one of the input's".into())
            }
            _ => Err("expected a SynBinder".into()),
        }
    }

    pub fn stmts(&mut self, n: &Node) -> R<Vec<Stmt>> {
        let items = self.list(n)?.to_vec();
        items.iter().map(|s| self.stmt(s)).collect()
    }

    pub fn stmt(&mut self, n: &Node) -> R<Stmt> {
        let (ctor, _) = self.ctor(n, "SynStmt")?;
        let opt_expr = |this: &mut Self, i: usize| -> R<Option<SurfaceTerm>> {
            let f = this.field(n, i)?;
            this.opt(f, &mut |t, e| t.expr(e))
        };
        Ok(match ctor {
            "StLet" => Stmt::Let {
                name: self.ident(self.field(n, 0)?)?,
                ty: opt_expr(self, 1)?,
                value: self.expr(self.field(n, 2)?)?,
                borrow: self.boolean(self.field(n, 3)?)?,
                borrow_mut: self.boolean(self.field(n, 4)?)?,
            },
            "StVar" => Stmt::Var {
                name: self.ident(self.field(n, 0)?)?,
                ty: opt_expr(self, 1)?,
                value: self.expr(self.field(n, 2)?)?,
                borrow: self.boolean(self.field(n, 3)?)?,
            },
            "StAssign" => Stmt::Assign {
                name: self.ident(self.field(n, 0)?)?,
                place: None,
                value: self.expr(self.field(n, 1)?)?,
            },
            "StFn" => Stmt::Fn(self.fn_decl(self.field(n, 0)?)?),
            "StExpr" => Stmt::Expr(self.expr(self.field(n, 0)?)?),
            "StWhile" => Stmt::While {
                condition: self.expr(self.field(n, 0)?)?,
                body: self.expr(self.field(n, 1)?)?,
            },
            "StReturn" => Stmt::Return(opt_expr(self, 0)?),
            "StTheorem" => Stmt::Theorem(self.theorem(self.field(n, 0)?)?),
            "StDef" => Stmt::Def(self.theorem(self.field(n, 0)?)?),
            "StStruct" => Stmt::Struct(self.data(self.field(n, 0)?)?),
            "StEnum" => Stmt::Enum(self.data(self.field(n, 0)?)?),
            "StInductive" => Stmt::Inductive(self.inductive(self.field(n, 0)?)?),
            "StEffect" => Stmt::Effect(self.effect(self.field(n, 0)?)?),
            "StMutual" => Stmt::Mutual {
                items: self.stmts(self.field(n, 0)?)?,
                span: self.span_of(self.field(n, 1)?)?,
            },
            "StMacroCall" => {
                let expr = self.expr(&Node::ctor(
                    "SynExpr::ExMacroCall",
                    vec![
                        self.field(n, 0)?.clone(),
                        self.field(n, 1)?.clone(),
                        self.field(n, 2)?.clone(),
                    ],
                ))?;
                Stmt::Expr(expr)
            }
            other => return Err(format!("{other} is not a SynStmt")),
        })
    }

    fn fn_decl(&mut self, n: &Node) -> R<FnDecl> {
        let get = |k: &str| n.named(k).ok_or_else(|| format!("a SynFn has {k}"));
        let name_node = get("name")?;
        let name = self.ident(name_node)?;
        let span = self.span_of(get("span")?)?;
        let (generics, rows) = split_generics(
            self.list(get("generics")?)?
                .iter()
                .map(|t| self.text(t))
                .collect::<R<Vec<_>>>()?,
        );
        let mut bounds = Vec::new();
        for b in self.list(get("bounds")?)?.to_vec() {
            bounds.push(self.opt(&b, &mut |this, x| this.text(x))?);
        }
        let mut params = Vec::new();
        for p in self.list(get("params")?)?.to_vec() {
            params.push(self.ident(&p)?);
        }
        let mut borrows = Vec::new();
        for b in self.list(get("borrows")?)?.to_vec() {
            borrows.push(self.opt(&b, &mut |this, x| this.boolean(x))?);
        }
        let mut param_types = Vec::new();
        for t in self.list(get("param_types")?)?.to_vec() {
            param_types.push(self.opt(&t, &mut |this, x| this.expr(x))?);
        }
        let result = self.opt(get("result")?, &mut |this, x| this.expr(x))?;
        let effects = self.opt(get("effects")?, &mut |this, x| {
            this.list(x)?.iter().map(|t| this.text(t)).collect()
        })?;
        let body = self.expr(get("body")?)?;
        Ok(FnDecl {
            budget: None,
            vis: crate::surface::Vis::Open,
            opaque: false,
            decreasing_by: None,
            generates: None,
            name,
            generics,
            rows,
            bounds,
            bound_spans: Vec::new(),
            params,
            borrows,
            param_types,
            result,
            effects,
            where_: Vec::new(),
            span,
            body,
        })
    }

    fn theorem(&mut self, n: &Node) -> R<TheoremDecl> {
        let get = |k: &str| n.named(k).ok_or_else(|| format!("a SynTheorem has {k}"));
        let name = self.ident(get("name")?)?;
        let span = self.span_of(get("span")?)?;
        let implicit = get("implicit")?.as_int().unwrap_or(0) as usize;
        let mut params = Vec::new();
        for p in self.list(get("params")?)?.to_vec() {
            let (k, v) = members(&p, "SynIdent", "SynExpr")?;
            params.push((self.ident(k)?, self.expr(v)?));
        }
        let ty = self.expr(get("ty")?)?;
        let body = self.opt(get("body")?, &mut |this, x| this.expr(x))?;
        Ok(TheoremDecl {
            budget: None,
            vis: crate::surface::Vis::Open,
            decreasing_by: None,
            name,
            implicit,
            params,
            ty,
            body,
            span,
        })
    }

    fn params(&mut self, n: &Node) -> R<Vec<(String, SurfaceTerm)>> {
        let mut params = Vec::new();
        for p in self.list(n)?.to_vec() {
            let (k, v) = members(&p, "SynIdent", "SynExpr")?;
            params.push((self.ident(k)?, self.expr(v)?));
        }
        Ok(params)
    }

    fn inductive(&mut self, n: &Node) -> R<InductiveDecl> {
        let get = |k: &str| n.named(k).ok_or_else(|| format!("a SynInductive has {k}"));
        let name = self.ident(get("name")?)?;
        let params = self.params(get("params")?)?;
        let sort = self.expr(get("sort")?)?;
        let span = self.span_of(get("span")?)?;
        let mut constructors = Vec::new();
        for c in self.list(get("ctors")?)?.to_vec() {
            let field = |k: &str| c.named(k).ok_or_else(|| format!("a SynIndCtor has {k}"));
            constructors.push(Constructor {
                name: self.ident(field("name")?)?,
                implicit: field("implicit")?.as_int().unwrap_or(0) as usize,
                params: self.params(field("params")?)?,
                result: self.expr(field("result")?)?,
            });
        }
        Ok(InductiveDecl {
            vis: crate::surface::Vis::Open,
            generates: Default::default(),
            name,
            params,
            sort,
            constructors,
            span,
        })
    }

    fn data(&mut self, n: &Node) -> R<DataDecl> {
        let get = |k: &str| n.named(k).ok_or_else(|| format!("a SynData has {k}"));
        let kind = self.opt(get("kind")?, &mut |this, x| this.text(x))?;
        let name = self.ident(get("name")?)?;
        let (generics, rows) = split_generics(
            self.list(get("generics")?)?
                .iter()
                .map(|t| self.text(t))
                .collect::<R<Vec<_>>>()?,
        );
        let span = self.span_of(get("span")?)?;
        let mut constructors = Vec::new();
        for c in self.list(get("ctors")?)?.to_vec() {
            let cname = self.ident(c.named("name").ok_or("a SynCtor has a name")?)?;
            let mut fields = Vec::new();
            for f in self
                .list(c.named("fields").ok_or("a SynCtor has fields")?)?
                .to_vec()
            {
                let (k, v) = members(&f, "Option(SynIdent)", "SynExpr")?;
                let key = self.opt(k, &mut |this, x| this.ident(x))?;
                fields.push((key, self.expr(v)?));
            }
            constructors.push(DataConstructor {
                name: cname,
                fields,
            });
        }
        Ok(DataDecl {
            vis: crate::surface::Vis::Open,
            kind,
            name,
            generics,
            rows,
            constructors,
            host: false,
            span,
        })
    }

    fn effect(&mut self, n: &Node) -> R<EffectDecl> {
        let get = |k: &str| n.named(k).ok_or_else(|| format!("a SynEffect has {k}"));
        let name = self.ident(get("name")?)?;
        let (generics, rows) = split_generics(
            self.list(get("generics")?)?
                .iter()
                .map(|t| self.text(t))
                .collect::<R<Vec<_>>>()?,
        );
        let mut params = Vec::new();
        for p in self.list(get("params")?)?.to_vec() {
            params.push(self.opt(&p, &mut |this, x| this.expr(x))?);
        }
        let result = self.opt(get("result")?, &mut |this, x| this.expr(x))?;
        let resume = self.opt(get("resume")?, &mut |this, x| this.text(x))?;
        let span = self.span_of(get("span")?)?;
        Ok(EffectDecl {
            vis: crate::surface::Vis::Open,
            name,
            generics,
            rows,
            params,
            param_names: Vec::new(),
            result,
            resume,
            set: None,
            span,
        })
    }

    fn pattern(&mut self, n: &Node) -> R<Pattern> {
        let (ctor, _) = self.ctor(n, "SynPattern")?;
        Ok(match ctor {
            "PtWild" => Pattern::Wild,
            "PtBind" => Pattern::Bind(self.ident(self.field(n, 0)?)?),
            "PtInt" => Pattern::Int(self.field(n, 0)?.as_int().ok_or("expected an i64")?),
            "PtBool" => Pattern::Bool(self.boolean(self.field(n, 0)?)?),
            "PtText" => Pattern::Text(self.text(self.field(n, 0)?)?),
            "PtCtor" => {
                let name = self.ident(self.field(n, 0)?)?;
                let mut args = Vec::new();
                for a in self.list(self.field(n, 1)?)?.to_vec() {
                    args.push(self.pattern(&a)?);
                }
                Pattern::Ctor { name, args }
            }
            "PtRecord" => {
                let name = self.ident(self.field(n, 0)?)?;
                let mut fields = Vec::new();
                for p in self.list(self.field(n, 1)?)?.to_vec() {
                    let (k, v) = members(&p, "Text", "SynPattern")?;
                    fields.push((self.text(k)?, self.pattern(v)?));
                }
                Pattern::Record { name, fields }
            }
            other => return Err(format!("{other} is not a SynPattern")),
        })
    }

    fn arm(&mut self, n: &Node) -> R<MatchArm> {
        let get = |k: &str| n.named(k).ok_or_else(|| format!("a SynArm has {k}"));
        Ok(MatchArm {
            goal: self.opt(get("goal")?, &mut |this, x| this.expr(x))?,
            pattern: self.pattern(get("pattern")?)?,
            guard: self.opt(get("guard")?, &mut |this, x| this.expr(x))?,
            body: self.expr(get("body")?)?,
        })
    }

    fn handler(&mut self, n: &Node) -> R<Handler> {
        let (ctor, _) = self.ctor(n, "SynHandler")?;
        Ok(match ctor {
            "HReturn" => Handler::Return {
                pattern: self.pattern(self.field(n, 0)?)?,
                body: self.expr(self.field(n, 1)?)?,
            },
            "HOp" => {
                let effect = self.ident(self.field(n, 0)?)?;
                let mut patterns = Vec::new();
                for p in self.list(self.field(n, 1)?)?.to_vec() {
                    patterns.push(self.pattern(&p)?);
                }
                let cont = self.opt(self.field(n, 2)?, &mut |this, x| this.ident(x))?;
                let guard = self.opt(self.field(n, 3)?, &mut |this, x| this.expr(x))?;
                let body = self.expr(self.field(n, 4)?)?;
                let mut forall = Vec::new();
                for t in self.list(self.field(n, 5)?)?.to_vec() {
                    forall.push(self.text(&t)?);
                }
                let mut args = Vec::new();
                for t in self.list(self.field(n, 6)?)?.to_vec() {
                    args.push(self.expr(&t)?);
                }
                let instance = Instance { forall, args };
                Handler::Operation {
                    effect,
                    instance,
                    patterns,
                    cont,
                    guard,
                    body,
                }
            }
            other => return Err(format!("{other} is not a SynHandler")),
        })
    }
}

pub fn is_marked(name: &str) -> bool {
    !scope::split(name).1.is_empty()
}
