//! Source spellings for structurally identical terms in the same proof context.
use crate::check::Kernel;
use crate::program::Loaded;
use crate::surface::{SurfaceTerm as T, TermKind, TheoremDecl, walk};
use std::collections::HashMap;

type Context = Vec<(String, T)>;

#[derive(Default)]
pub(super) struct Notation {
    entries: Vec<Entry>,
}
struct Entry {
    term: T,
    context: Context,
    occurrence: crate::surface::TermId,
    text: String,
}

// Position and sharing are not part of structural equality. Type arguments
// and binding names remain part of the structure.
fn structure(t: &T) -> T {
    let mut t = t.clone();
    walk::term(&mut t, &mut |t| t.span = Default::default());
    t
}
fn context(ctx: &[(String, T)]) -> Context {
    ctx.iter().map(|(n, t)| (n.clone(), structure(t))).collect()
}

impl Notation {
    pub(super) fn new(loaded: &Loaded, kernel: &Kernel, decl: &TheoremDecl) -> Self {
        let mut out = Self::default();
        let roots: HashMap<_, _> = loaded
            .expansions
            .iter()
            .filter_map(|e| {
                if e.root == 0 || e.parent.is_some() {
                    return None;
                }
                let file = loaded.files.iter().rev().find(|f| f.base <= e.call.start)?;
                let text = file
                    .text
                    .get((e.call.start - file.base) as usize..(e.call.end - file.base) as usize)?;
                Some((e.root, text.to_string()))
            })
            .collect();
        if roots.is_empty() {
            return out;
        }
        // The source statement and the elaborated statement cover both written
        // syntax and explicit kernel arguments without guessing an expansion.
        let mut ctx = Vec::new();
        for (n, ty) in &decl.params {
            out.collect(ty, &ctx, &roots);
            ctx.push((n.clone(), ty.clone()));
        }
        out.collect(&decl.ty, &ctx, &roots);
        if let Some(body) = &decl.body {
            out.collect(body, &ctx, &roots);
        }
        let library = kernel.library();
        if let Some(g) = library.iter().find(|g| g.name == decl.name) {
            let mut ty = &g.ty;
            let mut ctx = Vec::new();
            while ctx.len() < decl.params.len() {
                let TermKind::Pi { params, result, .. } = &*ty.kind else {
                    break;
                };
                for (n, domain) in params {
                    out.collect(domain, &ctx, &roots);
                    let Some(n) = n else {
                        return out;
                    };
                    ctx.push((n.clone(), domain.clone()));
                }
                ty = result;
            }
            if ctx.len() == decl.params.len() {
                out.collect(ty, &ctx, &roots);
                if let Some((_, body)) = kernel
                    .elaborated()
                    .iter()
                    .rev()
                    .find(|(n, _)| n == &decl.name)
                {
                    let mut body = body;
                    let mut count = 0;
                    while count < ctx.len() {
                        let TermKind::Lam {
                            params,
                            body: inner,
                            ..
                        } = &*body.kind
                        else {
                            break;
                        };
                        if params
                            .iter()
                            .zip(&ctx[count..])
                            .any(|(n, (expected, _))| n != expected)
                        {
                            break;
                        }
                        count += params.len();
                        body = inner;
                    }
                    if count == ctx.len() {
                        out.collect(body, &ctx, &roots);
                    }
                }
            }
        }
        out
    }

    fn collect(&mut self, t: &T, ctx: &[(String, T)], roots: &HashMap<u32, String>) {
        if let Some(text) = roots.get(&t.span.start) {
            self.entries.push(Entry {
                term: structure(t),
                context: context(ctx),
                occurrence: t.id(),
                text: text.clone(),
            });
            // Elaboration may give generated children the root's span too.
            // Only the outermost node at that position denotes the expansion.
            return;
        }
        // Inner bindings have no stable source identity in a written-back
        // derivation. Keep their expanded form rather than infer a provenance.
        if matches!(&*t.kind, TermKind::Pi { .. } | TermKind::Lam { .. }) {
            return;
        }
        Self::children(t, ctx, &mut |child, ctx| self.collect(child, ctx, roots));
    }

    // A lambda without parameter types cannot establish the identities of its
    // bindings. Its judgments are printed separately with their typed context.
    fn children(t: &T, ctx: &[(String, T)], f: &mut impl FnMut(&T, &[(String, T)])) {
        match &*t.kind {
            TermKind::Pi { params, result, .. } => {
                let mut ctx = ctx.to_vec();
                for (n, ty) in params {
                    f(ty, &ctx);
                    if let Some(n) = n {
                        ctx.push((n.clone(), ty.clone()));
                    }
                }
                f(result, &ctx);
            }
            TermKind::Lam {
                params,
                types,
                body,
            } => {
                let mut ctx = ctx.to_vec();
                for (i, n) in params.iter().enumerate() {
                    let Some(Some(ty)) = types.get(i) else {
                        return;
                    };
                    f(ty, &ctx);
                    ctx.push((n.clone(), ty.clone()));
                }
                f(body, &ctx);
            }
            // These source binders are lowered before the recorded judgments.
            TermKind::Exists { .. }
            | TermKind::Match { .. }
            | TermKind::Block(..)
            | TermKind::Handle { .. }
            | TermKind::Quote { .. }
            | TermKind::Step(..) => {}
            _ => walk::children(&mut t.clone(), &mut |child| f(child, ctx)),
        }
    }

    fn spelling(&self, t: &T, ctx: &[(String, T)]) -> Option<String> {
        let ctx = context(ctx);
        let term = structure(t);
        let matches: Vec<_> = self
            .entries
            .iter()
            .filter(|e| {
                e.term == term
                    && ctx.starts_with(&e.context)
                    && e.context
                        .iter()
                        .enumerate()
                        .all(|(i, (n, _))| !ctx[i + 1..].iter().any(|(other, _)| other == n))
            })
            .collect();
        let own: Vec<_> = matches
            .iter()
            .copied()
            .filter(|e| e.occurrence == t.id())
            .collect();
        let choices = if own.is_empty() { &matches } else { &own };
        let first = choices.first()?;
        choices
            .iter()
            .all(|e| e.text == first.text)
            .then(|| first.text.clone())
    }

    pub(super) fn show(&self, t: &T, ctx: &[(String, T)], equations: bool) -> String {
        if self.entries.is_empty() {
            return crate::surface::print::print_term(&if equations {
                Kernel::eqs_written(t)
            } else {
                t.clone()
            });
        }
        let mut selected = HashMap::new();
        fn select(
            n: &Notation,
            t: &T,
            ctx: &[(String, T)],
            selected: &mut HashMap<crate::surface::TermId, String>,
        ) {
            if let Some(text) = n.spelling(t, ctx) {
                selected.insert(t.id(), text);
                return;
            }
            Notation::children(t, ctx, &mut |c, ctx| select(n, c, ctx, selected));
        }
        select(self, t, ctx, &mut selected);
        let t = if equations {
            Kernel::eqs_written(t)
        } else {
            t.clone()
        };
        crate::surface::print::print_term_with(&t, &|t| selected.get(&t.id()).cloned())
    }
}
