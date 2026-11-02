//! The syntax of a `direct` operation's arm:
//! every path of the arm ends in one call `k(e)`, and `k` is nowhere else.
//!
//! ```text
//! T ::= k(e)                                  k is not in e
//!     | { s1; …; sn; T }                      k is not in s1 … sn
//!     | if c { T } else { T }                 k is not in c; else is required
//!     | match x { p1 => T, …, pm => T }       k is not in x or a guard
//! ```
//!
//! This is a check of the form alone; it uses no types.

use crate::surface::walk::{Node, values, values_stmt};
use crate::surface::{Stmt, SurfaceTerm, TermKind};

/// Whether `body` is a tail form for the continuation `k`.
pub fn is_tail_form(body: &SurfaceTerm, k: &str) -> bool {
    match &*body.kind {
        TermKind::App {
            function,
            arguments,
        } => {
            matches!(&*function.kind, TermKind::Var(n) if n == k)
                && arguments.len() == 1
                && !mentions(&arguments[0], k)
        }
        TermKind::Block(stmts) => match stmts.split_last() {
            Some((Stmt::Expr(last), init)) => {
                !init.iter().any(|s| stmt_mentions(s, k)) && is_tail_form(last, k)
            }
            _ => false,
        },
        TermKind::If {
            condition,
            then,
            otherwise,
        } => match otherwise {
            Some(o) => !mentions(condition, k) && is_tail_form(then, k) && is_tail_form(o, k),
            None => false,
        },
        TermKind::Match {
            scrutinee, arms, ..
        } => {
            !mentions(scrutinee, k)
                && !arms.is_empty()
                && arms.iter().all(|a| {
                    a.guard.as_ref().is_none_or(|g| !mentions(g, k)) && is_tail_form(&a.body, k)
                })
        }
        _ => false,
    }
}

pub fn mentions(t: &SurfaceTerm, name: &str) -> bool {
    let mut found = false;
    values(t, &mut |n| {
        if let Node::Term(t) = n
            && let TermKind::Var(v) = &*t.kind
            && v == name
        {
            found = true;
        }
        if let Node::Stmt(Stmt::Assign { name: v, .. }) = n
            && v == name
        {
            found = true;
        }
    });
    found
}

fn stmt_mentions(s: &Stmt, name: &str) -> bool {
    let mut found = false;
    values_stmt(s, &mut |n| {
        if let Node::Term(t) = n
            && let TermKind::Var(v) = &*t.kind
            && v == name
        {
            found = true;
        }
        if let Node::Stmt(Stmt::Assign { name: v, .. }) = n
            && v == name
        {
            found = true;
        }
    });
    found
}

/// Whether `t` lends `name` mutably (`&mut name…`) or assigns it.
pub fn lends_mutably(t: &SurfaceTerm, name: &str) -> bool {
    let mut found = false;
    values(t, &mut |n| match n {
        Node::Term(t) if matches!(&*t.kind, TermKind::Borrow { mutable: true, .. }) => {
            let TermKind::Borrow { term, .. } = &*t.kind else {
                unreachable!()
            };
            if root_of(term) == Some(name) {
                found = true;
            }
        }
        Node::Stmt(Stmt::Assign { name: v, .. }) if v == name => found = true,
        _ => {}
    });
    found
}

fn root_of(t: &SurfaceTerm) -> Option<&str> {
    match &*t.kind {
        TermKind::Var(n) => Some(n),
        TermKind::Field { base, .. } => root_of(base),
        _ => None,
    }
}
