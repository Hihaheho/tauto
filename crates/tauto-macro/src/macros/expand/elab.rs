//! The `elab_*` operations of a typed macro: ask the kernel, read-only, about terms in the context of a `Judgement`.
//! They are for the kernel's fragment; in the executable one a type is equal
//! to another when it is written the same way, and nothing else is offered.

use std::collections::{HashMap, HashSet};

use tauto_message::msg;
use tauto_parol::Span;

use crate::macros::checker::TypedChecker;
use crate::macros::node::Node;
use crate::macros::scope;
use crate::macros::syn::{Lift, Lower, OPEN_ATOM};
use crate::surface::{Stmt, SurfaceTerm, print};
use std::sync::Arc;

type R<T> = Result<T, String>;

pub struct ElabEnv {
    pub checker: Arc<dyn TypedChecker>,
    /// The declarations before the one the macro is in.
    pub prefix: Vec<Stmt>,
    /// The scope of the expansion the macro runs in, which lowering flips.
    pub scope: u64,
    pub ctors: HashSet<String>,
    /// Each constructor with the constructors of its type.
    pub families: HashMap<String, Vec<String>>,
    pub arities: HashMap<String, usize>,
}

/// A `Judgement` as the pieces `elab_*` needs.
struct Parts<'n> {
    term: &'n Node,
    ty: &'n Node,
    ctx: Vec<(u64, String, &'n Node)>,
    fragment: String,
}

fn parts(n: &Node) -> R<Parts<'_>> {
    let field = |name: &str| n.named(name).ok_or_else(|| format!("a Judgement has a {name}"));
    let mut ctx = Vec::new();
    for b in field("ctx")?.as_list().ok_or("a Judgement has a ctx list")? {
        let atom = b
            .named("atom")
            .and_then(Node::as_int)
            .ok_or("a Judgement::Binder has an atom")? as u64;
        let name = b
            .named("name")
            .and_then(Node::as_text)
            .ok_or("a Judgement::Binder has a name")?;
        let ty = b.named("ty").ok_or("a Judgement::Binder has a ty")?;
        let name = if atom >= OPEN_ATOM {
            format!("_a{atom}")
        } else {
            name.to_string()
        };
        ctx.push((atom, name, ty));
    }
    Ok(Parts {
        term: field("term")?,
        ty: field("ty")?,
        ctx,
        fragment: field("fragment")?
            .as_text()
            .ok_or("a Judgement has a fragment")?
            .to_string(),
    })
}

impl ElabEnv {
    fn lower(&self, n: &Node, atoms: &HashMap<u64, String>) -> R<SurfaceTerm> {
        let mut fresh = |at: u32| Span::new(at, at + 1);
        let mut lower = Lower {
            scope: self.scope,
            fresh: &mut fresh,
            captures: Vec::new(),
            atoms,
            opened: Vec::new(),
        };
        let term = lower.expr(n)?;
        let mut resolved = scope::resolve(vec![Stmt::Expr(term)], &self.ctors);
        match resolved.pop() {
            Some(Stmt::Expr(t)) => Ok(t),
            _ => Err("a term".into()),
        }
    }

    fn lift(&self, t: &SurfaceTerm, names: &HashMap<String, u64>) -> R<Node> {
        Lift {
            scopes: &[],
            quote: false,
            atoms: Some(names),
            spans: None,
            reflip: None,
        }
        .expr(t)
    }

    fn atoms(p: &Parts) -> (HashMap<u64, String>, HashMap<String, u64>) {
        let by_atom = p.ctx.iter().map(|(a, n, _)| (*a, n.clone())).collect();
        let by_name = p.ctx.iter().map(|(a, n, _)| (n.clone(), *a)).collect();
        (by_atom, by_name)
    }

    fn context(&self, p: &Parts, atoms: &HashMap<u64, String>) -> R<Vec<(String, SurfaceTerm)>> {
        p.ctx
            .iter()
            .map(|(_, name, ty)| Ok((name.clone(), self.lower(ty, atoms)?)))
            .collect()
    }

    fn code(
        &self,
        term: &SurfaceTerm,
        ty: &SurfaceTerm,
        names: &HashMap<String, u64>,
        ctx_node: &Node,
    ) -> R<Node> {
        Ok(Node::Ctor(
            "Judgement".into(),
            vec![
                (Some("term".into()), self.lift(term, names)?),
                (Some("ty".into()), self.lift(ty, names)?),
                (Some("row".into()), Node::List(Vec::new())),
                (Some("ctx".into()), ctx_node.clone()),
                (Some("fragment".into()), Node::text("Kernel")),
                (Some("tys".into()), Node::List(Vec::new())),
                (Some("usage".into()), Node::List(Vec::new())),
                (
                    Some("span".into()),
                    Node::Ctor("SynSpan".into(), vec![(Some("id".into()), Node::Int(0))]),
                ),
            ],
        ))
    }

    fn diag(message: String) -> Node {
        Node::ctor(
            "Err",
            vec![Node::Ctor(
                "SynDiag".into(),
                vec![
                    (Some("message".into()), Node::Text(message)),
                    (Some("at".into()), Node::Int(0)),
                    (Some("expected".into()), Node::List(Vec::new())),
                    (Some("code".into()), Node::text("macro.elab_check")),
                ],
            )],
        )
    }

    pub fn call(&self, op: &str, args: &[Node]) -> R<Node> {
        let arg = |i: usize| {
            args.get(i)
                .ok_or_else(|| msg!("macro-elab-more-arguments", op = op).to_string())
        };
        match op {
            "Elab::defeq" => {
                let (a, b) = (parts(arg(0)?)?, parts(arg(1)?)?);
                let (atoms_a, _) = Self::atoms(&a);
                let (atoms_b, _) = Self::atoms(&b);
                let ta = self.lower(a.term, &atoms_a)?;
                let tb = self.lower(b.term, &atoms_b)?;
                if a.fragment != "Kernel" || b.fragment != "Kernel" {
                    return Ok(Node::Bool(print::print_term(&ta) == print::print_term(&tb)));
                }
                let context = self.context(&a, &atoms_a)?;
                let mut k = self.checker.elaborator(&self.prefix, &context)?;
                Ok(Node::Bool(k.defeq(&ta, &tb)?))
            }
            "Elab::whnf" => {
                let c = parts(arg(0)?)?;
                let (atoms, names) = Self::atoms(&c);
                let t = self.lower(c.term, &atoms)?;
                if c.fragment != "Kernel" {
                    return Ok(arg(0)?.clone());
                }
                let mut k = self
                    .checker
                    .elaborator(&self.prefix, &self.context(&c, &atoms)?)?;
                let w = k.whnf(&t)?;
                let ty = self.lower(c.ty, &atoms)?;
                self.code(&w, &ty, &names, arg(0)?.named("ctx").ok_or("ctx")?)
            }
            "Elab::check" => {
                let ctx = parts(arg(1)?)?;
                let (atoms, names) = Self::atoms(&ctx);
                let e = self.lower(arg(0)?, &atoms)?;
                if ctx.fragment != "Kernel" {
                    return Ok(Self::diag(msg!("macro-elab-check-kernel").to_string()));
                }
                let mut k = self
                    .checker
                    .elaborator(&self.prefix, &self.context(&ctx, &atoms)?)?;
                let wanted = match arg(2)?.as_option() {
                    Some(Some(t)) => Some(self.lower(parts(t)?.term, &atoms)?),
                    _ => None,
                };
                let done = match &wanted {
                    Some(ty) => k.check(&e, ty).map(|e| (e, ty.clone())),
                    None => k.infer(&e),
                };
                let ctx_node = arg(1)?.named("ctx").ok_or("ctx")?;
                match done {
                    Ok((term, ty)) => Ok(Node::ctor(
                        "Ok",
                        vec![self.code(&term, &ty, &names, ctx_node)?],
                    )),
                    Err(m) => Ok(Self::diag(m)),
                }
            }
            "Elab::global" => {
                let name = arg(0)?.as_text().ok_or("a Text")?;
                let k = self.checker.elaborator(&self.prefix, &[])?;
                Ok(match k.type_of(name) {
                    Some(ty) => {
                        let none = HashMap::new();
                        let term = SurfaceTerm::var(name, Span::new(0, 1));
                        Node::some(self.code(&term, &ty, &none, &Node::List(Vec::new()))?)
                    }
                    None => Node::none(),
                })
            }
            "Elab::resolve" => {
                let id = arg(0)?;
                let name = id
                    .named("name")
                    .and_then(Node::as_text)
                    .ok_or("a SynIdent has a name")?;
                let ctx = parts(arg(1)?)?;
                let (atoms, names) = Self::atoms(&ctx);
                let k = self
                    .checker
                    .elaborator(&self.prefix, &self.context(&ctx, &atoms)?)?;
                Ok(match k.type_of(name) {
                    Some(ty) => {
                        let term = SurfaceTerm::var(name, Span::new(0, 1));
                        let ctx_node = arg(1)?.named("ctx").ok_or("ctx")?;
                        Node::some(self.code(&term, &ty, &names, ctx_node)?)
                    }
                    None => Node::none(),
                })
            }
            "Elab::constructor_arity" => {
                let name = arg(0)?.as_text().ok_or("a Text")?;
                Ok(match self.arities.get(name) {
                    Some(n) => Node::some(Node::Int(*n as i64)),
                    None => Node::none(),
                })
            }
            "Elab::siblings" => {
                let name = arg(0)?.as_text().ok_or("a Text")?;
                Ok(match self.families.get(name) {
                    Some(all) => {
                        Node::some(Node::List(all.iter().map(|n| Node::text(n)).collect()))
                    }
                    None => Node::none(),
                })
            }
            other => Err(msg!("macro-elab-unknown-op", op = other).to_string()),
        }
    }
}
