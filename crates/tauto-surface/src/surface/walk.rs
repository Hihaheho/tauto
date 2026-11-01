//! Every term of a statement, for the passes that rewrite terms where they
//! stand (`syntax::expand`, `macros`), and the parts of a program that run, for
//! the checks of executable code (`rows`, `lin`, `direct`).

use super::program::{Handler, Stmt};
use super::{SurfaceTerm, TermKind};
use std::sync::Arc;

/// `f` on each term the statement holds, outermost first, and then on each term
/// inside one that `f` left in place.
pub fn stmt(s: &mut Stmt, f: &mut dyn FnMut(&mut SurfaceTerm)) {
    roots(s, &mut |t| term(t, f));
}

/// `f` on each term the statement holds itself (the terms of the statements in
/// a `mutual` or a `module` too), not on the terms inside those.
pub fn roots(s: &mut Stmt, f: &mut dyn FnMut(&mut SurfaceTerm)) {
    match s {
        Stmt::Let { ty, value, .. } | Stmt::Var { ty, value, .. } => {
            if let Some(t) = ty {
                f(t);
            }
            f(value);
        }
        Stmt::Assign { value, .. } => f(value),
        Stmt::Fn(d) => {
            for t in d.param_types.iter_mut().flatten() {
                f(t);
            }
            if let Some(r) = &mut d.result {
                f(r);
            }
            f(&mut d.body);
        }
        Stmt::Theorem(d) | Stmt::Def(d) => {
            for (_, t) in &mut d.params {
                f(t);
            }
            f(&mut d.ty);
            if let Some(b) = &mut d.body {
                f(b);
            }
        }
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            items.iter_mut().for_each(|i| roots(i, f))
        }
        // As for a call, an attribute's literal argument is the macro's to read.
        Stmt::Attributed { arg, stmt, .. } => {
            if !matches!(&*arg.kind, TermKind::SyntaxLit(_)) {
                f(arg);
            }
            roots(stmt, f);
        }
        Stmt::While { condition, body } => {
            f(condition);
            f(body);
        }
        Stmt::Return(Some(e)) | Stmt::Expr(e) => f(e),
        Stmt::Called { call, .. } => f(call),
        Stmt::Struct(d) | Stmt::Enum(d) => {
            for c in &mut d.constructors {
                for (_, t) in &mut c.fields {
                    f(t);
                }
            }
        }
        Stmt::Effect(e) => {
            for t in e.params.iter_mut().flatten() {
                f(t);
            }
            if let Some(r) = &mut e.result {
                f(r);
            }
        }
        Stmt::Inductive(d) => {
            for (_, t) in &mut d.params {
                f(t);
            }
            f(&mut d.sort);
            for c in &mut d.constructors {
                for (_, t) in &mut c.params {
                    f(t);
                }
                f(&mut c.result);
            }
        }
        Stmt::Class(c) => {
            for d in &mut c.methods {
                for t in d.param_types.iter_mut().flatten() {
                    f(t);
                }
                if let Some(r) = &mut d.result {
                    f(r);
                }
            }
        }
        Stmt::Instance(i) => {
            f(&mut i.head);
            for c in &mut i.where_ {
                f(&mut c.ty);
            }
            for d in &mut i.methods {
                for t in d.param_types.iter_mut().flatten() {
                    f(t);
                }
                if let Some(r) = &mut d.result {
                    f(r);
                }
                f(&mut d.body);
            }
        }
        Stmt::Extern { fns, .. } => {
            for d in fns {
                for t in d.param_types.iter_mut().flatten() {
                    f(t);
                }
                if let Some(r) = &mut d.result {
                    f(r);
                }
            }
        }
        Stmt::Return(None)
        | Stmt::Import { .. }
        | Stmt::Syntax { .. }
        | Stmt::Macro { .. }
        | Stmt::Other(..) => {}
    }
}

/// `f` on `t`, and then on each term inside it that `f` left in place.
pub fn term(t: &mut SurfaceTerm, f: &mut dyn FnMut(&mut SurfaceTerm)) {
    f(t);
    children(t, &mut |c| term(c, f));
}

/// `f` on each term directly inside `t`.
pub fn children(t: &mut SurfaceTerm, f: &mut dyn FnMut(&mut SurfaceTerm)) {
    match Arc::make_mut(&mut t.kind) {
        TermKind::App {
            function,
            arguments,
        } => {
            f(function);
            arguments.iter_mut().for_each(|a| f(a));
        }
        TermKind::Pi { params, result, .. } => {
            params.iter_mut().for_each(|(_, p)| f(p));
            f(result);
        }
        TermKind::Exists { domain, body, .. } => {
            f(domain);
            f(body);
        }
        TermKind::Lam { body, types, .. } => {
            types.iter_mut().flatten().for_each(|ty| f(ty));
            f(body);
        }
        TermKind::BorrowLam { lam, .. } => f(lam),
        TermKind::Union(items) | TermKind::Product(items) | TermKind::Tuple(items) => {
            items.iter_mut().for_each(|a| f(a))
        }
        TermKind::Tagged { term: inner, .. }
        | TermKind::Borrow { term: inner, .. }
        | TermKind::Splice(inner) => f(inner),
        TermKind::FnKind { ty, .. } => f(ty),
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            f(condition);
            f(then);
            if let Some(o) = otherwise {
                f(o);
            }
        }
        TermKind::Field { base, .. } => f(base),
        TermKind::Ascribe { term, ty } => {
            f(term);
            f(ty);
        }
        TermKind::Block(stmts) | TermKind::Quote { body: stmts, .. } => {
            stmts.iter_mut().for_each(|s| roots(s, f))
        }
        TermKind::Perform { args, .. } => args.iter_mut().for_each(|a| f(a)),
        TermKind::Handle { body, handlers } => {
            f(body);
            for h in handlers {
                match h {
                    Handler::Return { body, .. } => f(body),
                    Handler::Operation { body, guard, .. } => {
                        if let Some(g) = guard {
                            f(g);
                        }
                        f(body);
                    }
                }
            }
        }
        TermKind::Budget { steps, body, .. } => {
            f(steps);
            f(body);
        }
        TermKind::Match {
            scrutinee,
            result,
            arms,
            ..
        } => {
            f(scrutinee);
            if let Some(r) = result {
                f(r);
            }
            for a in arms {
                if let Some(g) = &mut a.guard {
                    f(g);
                }
                if let Some(g) = &mut a.goal {
                    f(g);
                }
                f(&mut a.body);
            }
        }
        TermKind::Record { fields, base, .. } => {
            fields.iter_mut().for_each(|(_, v)| f(v));
            if let Some(b) = base {
                f(b);
            }
        }
        TermKind::Step(s) => {
            f(&mut s.arg);
            if let Some(b) = &mut s.before {
                f(b);
            }
            for a in &mut s.arms {
                a.binders.iter_mut().for_each(|(_, t)| f(t));
                f(&mut a.goal);
                f(&mut a.body);
            }
        }
        // A macro's literal argument is the macro's to read.
        TermKind::MacroCall { arg, .. } => {
            if !matches!(&*arg.kind, TermKind::SyntaxLit(_)) {
                f(arg)
            }
        }
        TermKind::Var(_)
        | TermKind::Nat(_)
        | TermKind::Float(_)
        | TermKind::Text(_)
        | TermKind::Bool(_)
        | TermKind::Hole(_)
        | TermKind::SyntaxLit(_)
        | TermKind::Row(_)
        | TermKind::Other(_) => {}
    }
}

/// A term or a statement met by [`values`].
pub enum Node<'a> {
    Term(&'a SurfaceTerm),
    Stmt(&'a Stmt),
}

/// `f` on `t` and on each term and statement under it that runs: the parts of
/// a program, not the types, propositions or patterns written in it.
pub fn values<'a>(t: &'a SurfaceTerm, f: &mut impl FnMut(Node<'a>)) {
    f(Node::Term(t));
    match &*t.kind {
        TermKind::App {
            function,
            arguments,
        } => {
            values(function, f);
            arguments.iter().for_each(|a| values(a, f));
        }
        TermKind::Lam { body, .. } => values(body, f),
        TermKind::BorrowLam { lam, .. } => values(lam, f),
        TermKind::Borrow { term, .. } | TermKind::Tagged { term, .. } => values(term, f),
        TermKind::Record { fields, base, .. } => {
            fields.iter().for_each(|(_, v)| values(v, f));
            if let Some(b) = base {
                values(b, f);
            }
        }
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            values(condition, f);
            values(then, f);
            if let Some(o) = otherwise {
                values(o, f);
            }
        }
        TermKind::Field { base, .. } | TermKind::Ascribe { term: base, .. } => values(base, f),
        TermKind::Perform { args, .. } => args.iter().for_each(|a| values(a, f)),
        TermKind::Budget { steps, body, .. } => {
            values(steps, f);
            values(body, f);
        }
        TermKind::Block(stmts) => stmts.iter().for_each(|s| values_stmt(s, f)),
        TermKind::Handle { body, handlers } => {
            values(body, f);
            for h in handlers {
                match h {
                    Handler::Return { body, .. } => values(body, f),
                    Handler::Operation { body, guard, .. } => {
                        if let Some(g) = guard {
                            values(g, f);
                        }
                        values(body, f);
                    }
                }
            }
        }
        TermKind::Match {
            scrutinee, arms, ..
        } => {
            values(scrutinee, f);
            for a in arms {
                if let Some(g) = &a.guard {
                    values(g, f);
                }
                values(&a.body, f);
            }
        }
        _ => {}
    }
}

/// [`values`] from a statement.
pub fn values_stmt<'a>(s: &'a Stmt, f: &mut impl FnMut(Node<'a>)) {
    f(Node::Stmt(s));
    match s {
        Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
            values(value, f)
        }
        Stmt::Fn(d) => values(&d.body, f),
        Stmt::While { condition, body } => {
            values(condition, f);
            values(body, f);
        }
        Stmt::Return(Some(e)) | Stmt::Expr(e) => values(e, f),
        _ => {}
    }
}

/// [`values`], on the terms only.
pub fn value_terms<'a>(t: &'a SurfaceTerm, f: &mut impl FnMut(&'a SurfaceTerm)) {
    values(t, &mut |n| {
        if let Node::Term(u) = n {
            f(u)
        }
    });
}

/// A function with `decreasing_by` as a program runs it: its recursive calls
/// `f(args, proof)` without the proof, which is no value
/// (`crates/tauto-kernel/src/check/wf.rs`). The kernel reads the declaration as written.
pub fn strip_recursion_proofs(f: &mut super::program::FnDecl) {
    if f.decreasing_by.take().is_none() {
        return;
    }
    let (name, arity) = (f.name.clone(), f.params.len());
    term(&mut f.body, &mut |t| {
        if let TermKind::App {
            function,
            arguments,
        } = Arc::make_mut(&mut t.kind)
            && matches!(&*function.kind, TermKind::Var(n) if *n == name)
            && arguments.len() == arity + 1
        {
            arguments.pop();
        }
    });
}

/// [`strip_recursion_proofs`] on each function of the statements.
pub fn strip_proofs_in(stmts: &mut [Stmt]) {
    for s in stmts {
        match s {
            Stmt::Fn(f) => strip_recursion_proofs(f),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => strip_proofs_in(items),
            _ => {}
        }
    }
}
