//! Structural traversal of identifier slots. Labels and display-only strings
//! are not references. This traversal does not resolve or rename a binding.

use super::program::*;
use super::{Name, SurfaceTerm, TermKind};
use std::sync::Arc;

type Visit<'a> = dyn FnMut(&mut Name) + 'a;

fn names(items: &mut [Name], f: &mut Visit<'_>) {
    for name in items {
        f(name);
    }
}
fn optional(term: &mut Option<SurfaceTerm>, f: &mut Visit<'_>) {
    if let Some(t) = term {
        self::term(t, f);
    }
}
fn telescope(params: &mut [(Name, SurfaceTerm)], f: &mut Visit<'_>) {
    for (name, ty) in params {
        f(name);
        term(ty, f);
    }
}
fn constraints(items: &mut [Constraint], f: &mut Visit<'_>) {
    for c in items {
        f(&mut c.class);
        term(&mut c.ty, f);
        for arg in &mut c.arguments {
            term(arg, f);
        }
    }
}
fn function(d: &mut FnDecl, f: &mut Visit<'_>) {
    f(&mut d.name);
    names(&mut d.generics, f);
    for ty in &mut d.generic_types {
        term(ty, f);
    }
    for bound in d.bounds.iter_mut().flatten() {
        if let Some(effects) = bound.effects_mut() {
            names(effects, f);
        }
    }
    names(&mut d.params, f);
    for t in d.param_types.iter_mut().flatten() {
        term(t, f);
    }
    optional(&mut d.result, f);
    if let Some(row) = &mut d.effects {
        names(row, f);
    }
    constraints(&mut d.where_, f);
    optional(&mut d.decreasing_by, f);
    term(&mut d.body, f);
}
fn theorem(d: &mut TheoremDecl, f: &mut Visit<'_>) {
    f(&mut d.name);
    telescope(&mut d.params, f);
    term(&mut d.ty, f);
    optional(&mut d.body, f);
    optional(&mut d.decreasing_by, f);
}
fn laws(items: &mut [LawDecl], f: &mut Visit<'_>) {
    for law in items {
        f(&mut law.name);
        theorem(&mut law.theorem, f);
    }
}
fn data(d: &mut DataDecl, f: &mut Visit<'_>) {
    f(&mut d.name);
    names(&mut d.generics, f);
    for c in &mut d.constructors {
        f(&mut c.name);
        for (_, ty) in &mut c.fields {
            term(ty, f);
        }
    }
}

/// Visits every identifier slot in a statement, including its binders,
/// annotations, patterns, and nested declarations.
pub fn statement(s: &mut Stmt, f: &mut Visit<'_>) {
    match s {
        Stmt::Let {
            name, ty, value, ..
        }
        | Stmt::Var {
            name, ty, value, ..
        } => {
            f(name);
            optional(ty, f);
            term(value, f);
        }
        Stmt::Assign { name, place, value } => {
            f(name);
            optional(place, f);
            term(value, f);
        }
        Stmt::Fn(d) => function(d, f),
        Stmt::Theorem(d) | Stmt::Def(d) => theorem(d, f),
        Stmt::Attributed {
            arg, replace, stmt, ..
        } => {
            term(arg, f);
            if let Some(r) = replace {
                f(&mut r.name);
            }
            statement(stmt, f);
        }
        Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
            for item in items {
                statement(item, f);
            }
        }
        Stmt::Inductive(d) => {
            f(&mut d.name);
            telescope(&mut d.params, f);
            term(&mut d.sort, f);
            for c in &mut d.constructors {
                f(&mut c.name);
                telescope(&mut c.params, f);
                term(&mut c.result, f);
            }
        }
        Stmt::Effect(d) => {
            f(&mut d.name);
            names(&mut d.generics, f);
            names(&mut d.param_names, f);
            for t in d.params.iter_mut().flatten() {
                term(t, f);
            }
            optional(&mut d.result, f);
        }
        Stmt::Struct(d) | Stmt::Enum(d) => data(d, f),
        Stmt::Extern {
            fns,
            instances,
            types,
            ..
        } => {
            for d in fns {
                function(d, f);
            }
            for i in instances {
                f(&mut i.class);
                term(&mut i.ty, f);
            }
            for d in types {
                data(d, f);
            }
        }
        Stmt::Class(c) => {
            f(&mut c.name);
            f(&mut c.param);
            telescope(&mut c.parameters, f);
            for d in &mut c.methods {
                function(d, f);
            }
            laws(&mut c.laws, f);
        }
        Stmt::Instance(i) => {
            names(&mut i.generics, f);
            for ty in &mut i.generic_types {
                term(ty, f);
            }
            for bound in i.bounds.iter_mut().flatten() {
                if let Some(effects) = bound.effects_mut() {
                    names(effects, f);
                }
            }
            f(&mut i.class);
            term(&mut i.head, f);
            for arg in &mut i.arguments {
                term(arg, f);
            }
            constraints(&mut i.where_, f);
            for d in &mut i.methods {
                function(d, f);
            }
            laws(&mut i.laws, f);
        }
        Stmt::While { condition, body } => {
            term(condition, f);
            term(body, f);
        }
        Stmt::Return(value) => optional(value, f),
        Stmt::Expr(t) | Stmt::Called { call: t, .. } => term(t, f),
        Stmt::Syntax { uses, .. } => {
            for use_ in uses {
                f(&mut use_.function);
            }
        }
        Stmt::Import { .. } | Stmt::Macro { .. } | Stmt::Other(..) => {}
    }
}

/// Visits constructor references and binder slots; record field labels are
/// deliberately not identifiers.
pub fn pattern(p: &mut Pattern, f: &mut Visit<'_>) {
    match p {
        Pattern::Bind(n) => f(n),
        Pattern::Ctor { name, args } => {
            f(name);
            for arg in args {
                pattern(arg, f);
            }
        }
        Pattern::Record { name, fields } => {
            f(name);
            for (_, p) in fields {
                pattern(p, f);
            }
        }
        Pattern::Tuple(items) => {
            for p in items {
                pattern(p, f);
            }
        }
        Pattern::Wild
        | Pattern::Int(_)
        | Pattern::Bool(_)
        | Pattern::Text(_)
        | Pattern::Other(_) => {}
    }
}

/// Visits every identifier slot in a term. Blocks and handler annotations
/// receive the same traversal as standalone declarations and terms.
pub fn term(mut t: &mut SurfaceTerm, f: &mut Visit<'_>) {
    // Lists and large constructor values form a last-argument spine.
    while matches!(&*t.kind, TermKind::App { .. }) {
        let TermKind::App {
            function,
            arguments,
        } = Arc::make_mut(&mut t.kind)
        else {
            unreachable!()
        };
        term(function, f);
        let Some((last, init)) = arguments.split_last_mut() else {
            return;
        };
        for arg in init {
            term(arg, f);
        }
        t = last;
    }
    match Arc::make_mut(&mut t.kind) {
        TermKind::Var(n) => f(n),
        TermKind::Row(row) => names(row, f),
        TermKind::App { .. } => unreachable!("applications are visited along their spine"),
        TermKind::Pi {
            params,
            result,
            effects,
        } => {
            for (n, ty) in params {
                if let Some(n) = n {
                    f(n);
                }
                term(ty, f);
            }
            term(result, f);
            if let Some(row) = effects {
                names(row, f);
            }
        }
        TermKind::Exists {
            binder,
            domain,
            body,
        } => {
            f(binder);
            term(domain, f);
            term(body, f);
        }
        TermKind::Lam {
            params,
            body,
            types,
        } => {
            names(params, f);
            for ty in types.iter_mut().flatten() {
                term(ty, f);
            }
            term(body, f);
        }
        TermKind::Union(items) | TermKind::Product(items) | TermKind::Tuple(items) => {
            for t in items {
                term(t, f);
            }
        }
        TermKind::Tagged { term: t, .. }
        | TermKind::Borrow { term: t, .. }
        | TermKind::FnKind { ty: t, .. }
        | TermKind::BorrowLam { lam: t, .. }
        | TermKind::Splice(t)
        | TermKind::MacroCall { arg: t, .. }
        | TermKind::Field { base: t, .. } => term(t, f),
        TermKind::If {
            condition,
            then,
            otherwise,
        } => {
            term(condition, f);
            term(then, f);
            if let Some(t) = otherwise {
                term(t, f);
            }
        }
        TermKind::Ascribe { term: t, ty } => {
            term(t, f);
            term(ty, f);
        }
        TermKind::Block(items) | TermKind::Quote { body: items, .. } => {
            for s in items {
                statement(s, f);
            }
        }
        TermKind::Perform { effect, args } => {
            f(effect);
            for a in args {
                term(a, f);
            }
        }
        TermKind::Handle { body, handlers } => {
            term(body, f);
            for h in handlers {
                match h {
                    Handler::Return { pattern: p, body } => {
                        pattern(p, f);
                        term(body, f);
                    }
                    Handler::Operation {
                        effect,
                        instance,
                        patterns,
                        cont,
                        guard,
                        body,
                    } => {
                        f(effect);
                        names(&mut instance.forall, f);
                        for a in &mut instance.args {
                            term(a, f);
                        }
                        for p in patterns {
                            pattern(p, f);
                        }
                        if let Some(k) = cont {
                            f(k);
                        }
                        optional(guard, f);
                        term(body, f);
                    }
                }
            }
        }
        TermKind::Budget { steps, body, .. } => {
            term(steps, f);
            term(body, f);
        }
        TermKind::Match {
            scrutinee,
            result,
            binder,
            arms,
        } => {
            term(scrutinee, f);
            if let Some(t) = result {
                term(t, f);
            }
            if let Some(n) = binder {
                f(n);
            }
            for a in arms {
                pattern(&mut a.pattern, f);
                optional(&mut a.guard, f);
                optional(&mut a.goal, f);
                term(&mut a.body, f);
            }
        }
        TermKind::Record { name, fields, base } => {
            f(name);
            for (_, v) in fields {
                term(v, f);
            }
            if let Some(t) = base {
                term(t, f);
            }
        }
        TermKind::Step(s) => {
            term(&mut s.arg, f);
            optional(&mut s.before, f);
            for a in &mut s.arms {
                for (name, ty) in &mut a.binders {
                    f(name);
                    term(ty, f);
                }
                term(&mut a.goal, f);
                term(&mut a.body, f);
            }
        }
        TermKind::Declaration(_)
        | TermKind::Nat(_)
        | TermKind::Float(_)
        | TermKind::Text(_)
        | TermKind::Bool(_)
        | TermKind::Hole(_)
        | TermKind::SyntaxLit(_)
        | TermKind::Other(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::identity::{DeclRef, LocalRef};

    #[test]
    fn handler_type_arguments_and_assignment_places_retain_their_references() {
        let a: Name = DeclRef::fresh("same").into();
        let b: Name = DeclRef::fresh("same").into();
        let local: Name = LocalRef::fresh("same").into();
        let at = Default::default();
        let body = SurfaceTerm::new(
            TermKind::Block(vec![Stmt::Assign {
                name: local.clone(),
                place: Some(SurfaceTerm::var(&local, at)),
                value: SurfaceTerm::var(&b, at),
            }]),
            at,
        );
        let mut tree = SurfaceTerm::new(
            TermKind::Handle {
                body: Box::new(SurfaceTerm::var(&a, at)),
                handlers: vec![Handler::Operation {
                    effect: b.clone(),
                    instance: Instance {
                        forall: vec![local.clone()],
                        args: vec![SurfaceTerm::var(&a, at)],
                    },
                    patterns: vec![Pattern::Record {
                        name: a.clone(),
                        fields: vec![("same".into(), Pattern::Bind(local.clone()))],
                    }],
                    cont: None,
                    guard: None,
                    body,
                }],
            },
            at,
        );
        let original = tree.clone();
        let mut seen = Vec::new();
        term(&mut tree, &mut |name| seen.push(name.clone()));
        assert_eq!(tree, original);
        assert_eq!(
            seen,
            vec![
                a.clone(),
                b.clone(),
                local.clone(),
                a.clone(),
                a,
                local.clone(),
                local.clone(),
                local,
                b
            ]
        );
    }
}
