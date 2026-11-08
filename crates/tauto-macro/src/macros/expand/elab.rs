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
use crate::surface::{Stmt, SurfaceTerm};
use std::sync::Arc;

type R<T> = Result<T, String>;

pub struct ElabEnv {
    pub checker: Arc<dyn TypedChecker>,
    pub atoms: std::cell::RefCell<HashMap<u64, crate::surface::Name>>,
    /// The declarations before the one the macro is in.
    pub prefix: Vec<Stmt>,
    /// The declarations of the enclosing modules by their names there, inner
    /// modules winning.
    pub module_names: HashMap<String, tauto_surface::identity::DeclRef>,
    /// The scope of the expansion the macro runs in, which lowering flips.
    pub scope: u64,
    pub ctors: HashSet<String>,
    pub bindings: tauto_surface::resolve::Resolver,
    pub families: HashMap<crate::surface::Name, Vec<crate::surface::Name>>,
    pub arities: HashMap<crate::surface::Name, usize>,
}

struct Parts<'n> {
    term: &'n Node,
    ty: &'n Node,
    ctx: Vec<(u64, String, &'n Node)>,
    fragment: String,
}

fn parts(n: &Node) -> R<Parts<'_>> {
    let field = |name: &str| {
        n.named(name)
            .ok_or_else(|| format!("a Judgement has a {name}"))
    };
    let mut ctx = Vec::new();
    for b in field("ctx")?
        .as_list()
        .ok_or("a Judgement has a ctx list")?
    {
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

/// Gives a name the macro read in an enclosing module, spelled as that
/// module's own items spell it, its declaration there.
pub(super) fn module_resolved(
    t: &mut SurfaceTerm,
    names: &HashMap<String, tauto_surface::identity::DeclRef>,
) {
    if names.is_empty() {
        return;
    }
    crate::surface::walk::term(t, &mut |t| {
        // A name the file did not know was set aside as a declaration of its
        // own spelling; the module gives it the declaration it names there.
        let spelling = match &*t.kind {
            crate::surface::TermKind::Var(crate::surface::Name::Spelled(s)) => s.clone(),
            crate::surface::TermKind::Var(crate::surface::Name::Global(r)) => {
                r.display().to_string()
            }
            _ => return,
        };
        if let Some(reference) = names.get(spelling.as_str())
            && !matches!(&*t.kind, crate::surface::TermKind::Var(crate::surface::Name::Global(r)) if r == reference)
        {
            t.kind = std::sync::Arc::new(crate::surface::TermKind::Var(
                crate::surface::Name::Global(reference.clone()),
            ));
        }
    });
}

impl ElabEnv {
    fn constructor_reference(&self, ident: &Node) -> R<Option<crate::surface::Name>> {
        match ident.named("declaration").and_then(Node::as_option) {
            Some(Some(Node::Declaration(reference))) => Ok(Some(reference.clone().into())),
            Some(None) => {
                let spelling = ident
                    .named("name")
                    .and_then(Node::as_text)
                    .ok_or("a SynIdent name")?;
                Ok(self.bindings.source_reference(spelling))
            }
            _ => Err("a SynIdent declaration reference".into()),
        }
    }

    fn lower(&self, n: &Node, atoms: &HashMap<u64, crate::surface::Name>) -> R<SurfaceTerm> {
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
            Some(Stmt::Expr(mut t)) => {
                module_resolved(&mut t, &self.module_names);
                Ok(t)
            }
            _ => Err("a term".into()),
        }
    }

    fn lift(&self, t: &SurfaceTerm, names: &HashMap<crate::surface::Name, u64>) -> R<Node> {
        Lift {
            scopes: &[],
            quote: false,
            atoms: Some(names),
            spans: None,
            reflip: None,
        }
        .expr(t)
    }

    fn atoms(
        &self,
        p: &Parts,
    ) -> R<(
        HashMap<u64, crate::surface::Name>,
        HashMap<crate::surface::Name, u64>,
    )> {
        let mut known = self.atoms.borrow_mut();
        let mut by_atom = HashMap::new();
        let mut by_name = HashMap::new();
        for (atom, display, _) in &p.ctx {
            let reference = match known.get(atom) {
                Some(reference) => reference.clone(),
                None if *atom >= OPEN_ATOM => {
                    let reference = crate::surface::Name::Local(
                        tauto_surface::identity::LocalRef::fresh(display),
                    );
                    known.insert(*atom, reference.clone());
                    reference
                }
                None => return Err("macro.unknown_atom: an atom is not one of the input's".into()),
            };
            if by_atom.insert(*atom, reference.clone()).is_some() {
                return Err("macro.duplicate_atom: a context binds an atom once".into());
            }
            by_name.insert(reference, *atom);
        }
        Ok((by_atom, by_name))
    }

    fn context(
        &self,
        p: &Parts,
        atoms: &HashMap<u64, crate::surface::Name>,
    ) -> R<Vec<(crate::surface::Name, SurfaceTerm)>> {
        p.ctx
            .iter()
            .map(|(atom, _, ty)| {
                Ok((
                    atoms.get(atom).ok_or("unknown context atom")?.clone(),
                    self.lower(ty, atoms)?,
                ))
            })
            .collect()
    }

    fn code(
        &self,
        term: &SurfaceTerm,
        ty: &SurfaceTerm,
        names: &HashMap<crate::surface::Name, u64>,
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

    fn result(name: &str, fields: Vec<Node>) -> Node {
        Node::Ctor(
            crate::macros::node::ConstructorRef::resolved(
                tauto_surface::bindings::library_name(&format!("Result::{name}")),
                name.into(),
            ),
            fields.into_iter().map(|field| (None, field)).collect(),
        )
    }

    fn diag(message: String) -> Node {
        Self::result(
            "Err",
            vec![Node::Ctor(
                "SynDiag".into(),
                vec![
                    (Some("message".into()), Node::Text(message)),
                    (Some("at".into()), Node::Int(0)),
                    (Some("expected".into()), Node::List(Vec::new())),
                    (Some("code".into()), Node::text("macro.elab_check")),
                    (Some("args".into()), Node::List(Vec::new())),
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
                let (atoms_a, _) = self.atoms(&a)?;
                let (atoms_b, _) = self.atoms(&b)?;
                let ta = self.lower(a.term, &atoms_a)?;
                let tb = self.lower(b.term, &atoms_b)?;
                if a.fragment != "Kernel" || b.fragment != "Kernel" {
                    return Ok(Node::Bool(crate::surface::same_term_structure(&ta, &tb)));
                }
                let context = self.context(&a, &atoms_a)?;
                let mut k = self.checker.elaborator(&self.prefix, &context)?;
                Ok(Node::Bool(k.defeq(&ta, &tb)?))
            }
            "Elab::whnf" => {
                let c = parts(arg(0)?)?;
                let (atoms, names) = self.atoms(&c)?;
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
                let (atoms, names) = self.atoms(&ctx)?;
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
                    Ok((term, ty)) => Ok(Self::result(
                        "Ok",
                        vec![self.code(&term, &ty, &names, ctx_node)?],
                    )),
                    Err(m) => Ok(Self::diag(m)),
                }
            }
            "Elab::global" => {
                let name = arg(0)?.as_text().ok_or("a Text")?;
                let mut k = self.checker.elaborator(&self.prefix, &[])?;
                let mut term = SurfaceTerm::var(name, Span::new(0, 1));
                module_resolved(&mut term, &self.module_names);
                Ok(match k.infer(&term) {
                    Ok((term, ty)) => {
                        let none = HashMap::new();
                        Node::some(self.code(&term, &ty, &none, &Node::List(Vec::new()))?)
                    }
                    Err(_) => Node::none(),
                })
            }
            "Elab::resolve" => {
                let id = arg(0)?;

                let ctx = parts(arg(1)?)?;
                let (atoms, names) = self.atoms(&ctx)?;
                let mut k = self
                    .checker
                    .elaborator(&self.prefix, &self.context(&ctx, &atoms)?)?;
                let term = self.lower(&Node::ctor("SynExpr::ExVar", vec![id.clone()]), &atoms)?;
                Ok(match k.infer(&term) {
                    Ok((term, ty)) => {
                        let ctx_node = arg(1)?.named("ctx").ok_or("ctx")?;
                        Node::some(self.code(&term, &ty, &names, ctx_node)?)
                    }
                    Err(_) => Node::none(),
                })
            }
            "Elab::constructor_arity" => Ok(
                match self
                    .constructor_reference(arg(0)?)?
                    .and_then(|reference| self.arities.get(&reference))
                {
                    Some(n) => Node::some(Node::Int(*n as i64)),
                    None => Node::none(),
                },
            ),
            "Elab::siblings" => Ok(
                match self
                    .constructor_reference(arg(0)?)?
                    .and_then(|reference| self.families.get(&reference))
                {
                    Some(all) => {
                        let mut identifiers = Vec::new();
                        for reference in all {
                            let expression = self.lift(
                                &SurfaceTerm::var(reference, Span::new(0, 1)),
                                &HashMap::new(),
                            )?;
                            let Node::Ctor(_, fields) = expression else {
                                return Err("a lifted identifier".into());
                            };
                            identifiers.push(
                                fields
                                    .into_iter()
                                    .next()
                                    .ok_or("a lifted identifier field")?
                                    .1,
                            );
                        }
                        Node::some(Node::List(identifiers))
                    }
                    None => Node::none(),
                },
            ),
            other => Err(msg!("macro-elab-unknown-op", op = other).to_string()),
        }
    }
}
