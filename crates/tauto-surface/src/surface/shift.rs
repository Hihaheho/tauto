//! A statement moved in its file: every place it holds that was written in a file (not one an
//! expansion made, nor the prelude's) moves by the same number of bytes. An editor's server
//! uses it to take what it made of a statement for the same statement written further on.
//!
//! Not every place a statement can hold is reached ([`moved`] does not move a `where` of a
//! function, say); [`moved_to`] says whether moving one statement makes it the other, place
//! for place, and a caller takes what it kept only then.

use std::sync::Arc;

use tauto_parol::Span;

use super::{Stmt, SurfaceTerm, TermKind, walk};
use crate::macros::EXPANSION_BASE;

/// `at` moved by `by`, when it was written in a file; `0..0` is no place and stays.
pub fn place(at: Span, by: i64) -> Span {
    if (at.start == 0 && at.end == 0) || at.start >= EXPANSION_BASE {
        return at;
    }
    Span::new(offset(at.start, by), offset(at.end, by))
}

/// A position written in a file, moved by `by`.
pub fn position(at: u32, by: i64) -> u32 {
    if at == 0 || at >= EXPANSION_BASE {
        at
    } else {
        offset(at, by)
    }
}

fn offset(at: u32, by: i64) -> u32 {
    (at as i64 + by).clamp(0, u32::MAX as i64) as u32
}

/// `s` with its places moved by `by` bytes.
pub fn moved(s: &mut Stmt, by: i64) {
    if by == 0 {
        return;
    }
    own_places(s, by);
    walk::stmt(s, &mut |t| term_places(t, by));
}

/// Whether `from`, moved by `by`, is `to` with every place the same.
pub fn moved_to(from: &Stmt, to: &Stmt, by: i64) -> bool {
    let mut m = from.clone();
    moved(&mut m, by);
    m == *to
}

fn term_places(t: &mut SurfaceTerm, by: i64) {
    t.span = place(t.span, by);
    match &*t.kind {
        TermKind::Step(_)
        | TermKind::SyntaxLit(_)
        | TermKind::Block(_)
        | TermKind::Quote { .. } => {}
        _ => return,
    }
    match Arc::make_mut(&mut t.kind) {
        TermKind::Step(step) => {
            step.call = place(step.call, by);
            for arm in &mut step.arms {
                arm.span = place(arm.span, by);
            }
        }
        TermKind::SyntaxLit(lit) => {
            lit.start = position(lit.start, by);
            lit.span = place(lit.span, by);
            if let Some((_, at)) = &mut lit.error {
                *at = place(*at, by);
            }
        }
        // The terms of these statements are walked with the term; their own places are not.
        TermKind::Block(stmts) | TermKind::Quote { body: stmts, .. } => {
            for s in stmts {
                own_places(s, by);
            }
        }
        _ => {}
    }
}

/// The places a statement holds outside its terms, and those of the statements in it.
fn own_places(s: &mut Stmt, by: i64) {
    match s {
        Stmt::Fn(d) => fn_places(d, by),
        Stmt::Theorem(d) | Stmt::Def(d) => d.span = place(d.span, by),
        Stmt::Attributed {
            generates,
            replace,
            stmt,
            span,
            ..
        } => {
            generates.at = place(generates.at, by);
            if let Some(r) = replace {
                r.at = place(r.at, by);
            }
            own_places(stmt, by);
            *span = place(*span, by);
        }
        Stmt::Mutual { items, span } | Stmt::Module { items, span, .. } => {
            for i in items {
                own_places(i, by);
            }
            *span = place(*span, by);
        }
        Stmt::Import { names, span, .. } => {
            for (_, at) in names.iter_mut().flatten() {
                *at = place(*at, by);
            }
            *span = place(*span, by);
        }
        Stmt::Inductive(d) => {
            d.generates.at = place(d.generates.at, by);
            d.span = place(d.span, by);
        }
        Stmt::Effect(d) => d.span = place(d.span, by),
        Stmt::Struct(d) | Stmt::Enum(d) => d.span = place(d.span, by),
        Stmt::Extern {
            fns,
            instances,
            types,
            span,
        } => {
            for d in fns {
                fn_places(d, by);
            }
            for i in instances {
                i.span = place(i.span, by);
            }
            for d in types {
                d.span = place(d.span, by);
            }
            *span = place(*span, by);
        }
        Stmt::Class(c) => {
            for d in &mut c.methods {
                fn_places(d, by);
            }
            for l in &mut c.laws {
                l.span = place(l.span, by);
                l.theorem.span = place(l.theorem.span, by);
            }
            c.span = place(c.span, by);
        }
        Stmt::Instance(i) => {
            for c in &mut i.where_ {
                c.span = place(c.span, by);
            }
            for d in &mut i.methods {
                fn_places(d, by);
            }
            for l in &mut i.laws {
                l.span = place(l.span, by);
                l.theorem.span = place(l.theorem.span, by);
            }
            i.span = place(i.span, by);
        }
        Stmt::Called {
            generates, span, ..
        } => {
            generates.at = place(generates.at, by);
            *span = place(*span, by);
        }
        Stmt::Syntax {
            grammar,
            generates,
            uses,
            span,
            ..
        } => {
            grammar.start = position(grammar.start, by);
            grammar.span = place(grammar.span, by);
            if let Some((_, at)) = &mut grammar.error {
                *at = place(*at, by);
            }
            generates.at = place(generates.at, by);
            for u in uses {
                u.span = place(u.span, by);
            }
            *span = place(*span, by);
        }
        Stmt::Macro { span, .. } | Stmt::Other(_, span) => *span = place(*span, by),
        Stmt::Let { .. }
        | Stmt::Var { .. }
        | Stmt::Assign { .. }
        | Stmt::While { .. }
        | Stmt::Return(_)
        | Stmt::Expr(_) => {}
    }
}

fn fn_places(d: &mut super::FnDecl, by: i64) {
    for at in &mut d.bound_spans {
        *at = place(*at, by);
    }
    for c in &mut d.where_ {
        c.span = place(c.span, by);
    }
    if let Some(g) = &mut d.generates {
        g.at = place(g.at, by);
    }
    d.span = place(d.span, by);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::parse_program_unresolved_at;

    #[test]
    fn a_statement_read_further_on_is_the_statement_moved() {
        let text = "theorem t(c: Nat): Eq(Nat, c, c) {\n  by norm!(): Eq(Nat, c, c) {}\n}\n\
                    fn f(x: Nat): Nat { match x { Zero => x, Succ(m) => m } }\n";
        let here = parse_program_unresolved_at(text, 10).expect("reads");
        let further = parse_program_unresolved_at(text, 25).expect("reads");
        assert!(!here.stmts.is_empty());
        for (a, b) in here.stmts.iter().zip(&further.stmts) {
            assert_ne!(a, b);
            assert!(moved_to(a, b, 15), "{a:#?}\n{b:#?}");
            assert!(!moved_to(a, b, 14));
        }
    }
}
