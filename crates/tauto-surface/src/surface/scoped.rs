//! `import` at the head of a declaration's body: `fn`, `macro fn`, `theorem`
//! and `def` written at the top of a file. Its names are seen in that body
//! only, closures, nested functions and quotes included, and not in the
//! declaration's signature (`docs/design/visibility.md`「Scope」). An `import`
//! anywhere else inside a file is an error.

use super::program::Stmt;
use super::walk;
use super::{SurfaceTerm, TermKind};
use crate::span::Span;

/// The body of a declaration that may begin with imports.
pub fn body(s: &Stmt) -> Option<&SurfaceTerm> {
    match s {
        Stmt::Fn(f) => Some(&f.body),
        Stmt::Theorem(d) | Stmt::Def(d) => d.body.as_ref(),
        Stmt::Attributed { stmt, .. } => body(stmt),
        _ => None,
    }
}

/// [`body`], to change.
pub fn body_mut(s: &mut Stmt) -> Option<&mut SurfaceTerm> {
    match s {
        Stmt::Fn(f) => Some(&mut f.body),
        Stmt::Theorem(d) | Stmt::Def(d) => d.body.as_mut(),
        Stmt::Attributed { stmt, .. } => body_mut(stmt),
        _ => None,
    }
}

/// The imports at the head of the body of the top-level statement `s`, before
/// its other statements, in the order written.
pub fn head_imports(s: &Stmt) -> Vec<&Stmt> {
    match body(s).map(|b| &*b.kind) {
        Some(TermKind::Block(stmts)) => stmts
            .iter()
            .take_while(|s| matches!(s, Stmt::Import { .. }))
            .collect(),
        _ => Vec::new(),
    }
}

/// Whether the top-level statement `s` imports anything at the head of its body.
pub fn has_head_imports(s: &Stmt) -> bool {
    !head_imports(s).is_empty()
}

/// Every `import` written inside the top-level statement `s`, at any depth
/// outside a quote, in the order written: what the file depends on.
pub fn nested_imports(s: &Stmt) -> Vec<&Stmt> {
    let mut out = Vec::new();
    in_stmt(s, &mut out);
    out
}

fn in_stmt<'a>(s: &'a Stmt, out: &mut Vec<&'a Stmt>) {
    match s {
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            for item in items {
                if matches!(item, Stmt::Import { .. }) {
                    out.push(item);
                } else {
                    in_stmt(item, out);
                }
            }
        }
        _ => walk::visit_roots(s, &mut |t| in_term(t, out)),
    }
}

fn in_term<'a>(t: &'a SurfaceTerm, out: &mut Vec<&'a Stmt>) {
    match &*t.kind {
        // What a quote holds is syntax a macro makes, which never imports.
        TermKind::Quote { .. } => {}
        TermKind::Block(stmts) => {
            for s in stmts {
                if matches!(s, Stmt::Import { .. }) {
                    out.push(s);
                } else {
                    walk::visit_roots(s, &mut |t| in_term(t, out));
                }
            }
        }
        _ => walk::visit_children(t, &mut |c| in_term(c, out)),
    }
}

/// The span of each `import` inside `stmts` that is not at the head of the
/// body of a top-level declaration.
pub fn misplaced(stmts: &[Stmt]) -> Vec<Span> {
    let mut out = Vec::new();
    for s in stmts {
        let allowed: Vec<Span> = head_imports(s).iter().map(|i| import_span(i)).collect();
        for i in nested_imports(s) {
            let at = import_span(i);
            if !allowed.contains(&at) {
                out.push(at);
            }
        }
    }
    out
}

/// Where an `import` is written.
pub fn import_span(s: &Stmt) -> Span {
    match s {
        Stmt::Import { span, .. } => *span,
        _ => Span::default(),
    }
}

/// The span of the body of the top-level statement `s`, when it has one.
pub fn body_span(s: &Stmt) -> Option<Span> {
    body(s).map(|b| b.span)
}

/// Takes the imports at the head of the bodies of `stmts` away, once the names of the
/// bodies are read: the checkers see each body as if they were not written.
pub fn strip(stmts: &mut [Stmt]) {
    for s in stmts {
        if !has_head_imports(s) {
            continue;
        }
        let Some(body) = body_mut(s) else {
            continue;
        };
        let TermKind::Block(items) = &*body.kind else {
            continue;
        };
        let rest: Vec<Stmt> = items
            .iter()
            .skip_while(|s| matches!(s, Stmt::Import { .. }))
            .cloned()
            .collect();
        *body = match rest.as_slice() {
            // A block of one expression is that expression, as the reader reads it.
            [Stmt::Expr(only)] => only.clone(),
            _ => SurfaceTerm::new(TermKind::Block(rest), body.span),
        };
    }
}
