//! Moved from `tauto_surface::resolve`: these resolve against the standard
//! library, which takes the reader.
#![allow(unused_imports)]
use std::collections::HashMap;
use tauto_surface::bindings::Bindings as Declarations;
use tauto_surface::bindings::*;
use tauto_surface::identity::{DeclRef, Name};
use tauto_surface::resolve::*;
use tauto_surface::span::Span;
use tauto_surface::surface::*;

fn parts(term: &SurfaceTerm) -> (&Name, &Name) {
    let TermKind::Lam { params, body, .. } = &*term.kind else {
        panic!("lambda")
    };
    let TermKind::Var(reference) = &*body.kind else {
        panic!("reference")
    };
    (&params[0], reference)
}

fn identity() -> SurfaceTerm {
    let span = Span { start: 0, end: 0 };
    SurfaceTerm::new(
        TermKind::Lam {
            params: vec![Name::from("x")],
            types: Vec::new(),
            body: Box::new(SurfaceTerm::var("x", span)),
            unused_params: Vec::new(),
        },
        span,
    )
}

#[test]
fn a_constructor_alias_does_not_replace_a_declared_type() {
    tauto_parse::install();
    let text = DeclRef::fresh("Text");
    let atom = DeclRef::fresh("Atom");
    let token = atom.constructor(0, "Text");
    let mut declarations = Declarations::default();
    declarations.declare(&text.clone().into());
    declarations.declare(&atom.clone().into());
    declarations.constructor_in(&atom.into(), &token.clone().into());
    declarations.constructor_alias("Text", &token.clone().into());
    assert_eq!(declarations.selection("Text"), Some(Name::Global(token)));
    let mut resolver = Resolver::new(declarations);
    let mut term = SurfaceTerm::var("Text", Span::new(0, 1));
    resolver.term_in_context(&mut term, &[]);
    assert!(matches!(&*term.kind, TermKind::Var(name) if name == &Name::Global(text)));
}

#[test]
fn file_visibility_filters_candidates_without_rebinding_references() {
    tauto_parse::install();
    let first = DeclRef::fresh("First");
    let second = DeclRef::fresh("Second");
    let a = first.constructor(0, "C");
    let b = second.constructor(0, "C");
    let mut declarations = Declarations::default();
    for (owner, constructor) in [(&first, &a), (&second, &b)] {
        declarations.declare(&owner.clone().into());
        declarations.constructor_in(&owner.clone().into(), &constructor.clone().into());
    }
    let mut resolver = Resolver::new(declarations);
    let mut statements = vec![Stmt::Expr(SurfaceTerm::var("C", Span::new(0, 1)))];
    resolver.statements_visible(
        &mut statements,
        &HashMap::from([("First".into(), "First".into())]),
    );
    let Stmt::Expr(term) = &statements[0] else {
        panic!("expression")
    };
    assert!(matches!(&*term.kind, TermKind::Var(name) if name == &Name::Global(a.clone())));
    resolver.statements_visible(
        &mut statements,
        &HashMap::from([("Second".into(), "Second".into())]),
    );
    let Stmt::Expr(term) = &statements[0] else {
        panic!("expression")
    };
    assert!(matches!(&*term.kind, TermKind::Var(name) if name == &Name::Global(a)));
    assert!(matches!(
        resolver.declarations().selection("C"),
        Some(Name::Selection(_))
    ));
}

#[test]
fn quoted_globals_keep_identity_but_quoted_binders_remain_syntax() {
    tauto_parse::install();
    let global = tauto_surface::identity::DeclRef::fresh("x");
    let mut declarations = Declarations::default();
    declarations.source_alias("x", global.clone());
    let resolver = Resolver::new(declarations);
    let mut statements = vec![
        Stmt::Expr(SurfaceTerm::var("x", Span::new(0, 1))),
        Stmt::Expr(identity()),
    ];
    resolver.quote_globals(&mut statements);
    let Stmt::Expr(term) = &statements[0] else {
        unreachable!()
    };
    assert!(matches!(&*term.kind, TermKind::Var(Name::Global(reference)) if reference == &global));
    let Stmt::Expr(term) = &statements[1] else {
        unreachable!()
    };
    let (binder, use_) = parts(term);
    assert_eq!(binder, &Name::from("x"));
    assert_eq!(use_, binder);
    assert_eq!(resolver.source_reference("x"), Some(global.into()));
}

#[test]
fn struct_family_and_constructor_have_distinct_shared_references() {
    tauto_parse::install();
    let mut statements = vec![Stmt::Struct(DataDecl {
        vis: Default::default(),
        kind: None,
        name: "Record".into(),
        generics: vec![],
        unused_generics: Vec::new(),
        unused_fields: Vec::new(),
        rows: vec![],
        host: false,
        borrowed: false,
        coerce: None,
        span: Span::new(0, 1),
        constructors: vec![tauto_surface::surface::DataConstructor {
            name: "Record".into(),
            fields: vec![],
        }],
    })];
    statements.push(Stmt::Expr(SurfaceTerm::var("Mk", Span::new(2, 3))));
    let mut resolver = Resolver::default();
    resolver.statements_visible(&mut statements, &HashMap::new());
    let Stmt::Struct(data) = &statements[0] else {
        unreachable!()
    };
    assert_ne!(data.name, data.constructors[0].name);
    let Stmt::Expr(term) = &statements[1] else {
        unreachable!()
    };
    assert!(matches!(&*term.kind, TermKind::Var(name) if name == &data.constructors[0].name));
    let family = tauto_surface::inductive_data::family(data, true);
    assert_eq!(family.name, data.name);
    assert_eq!(family.constructors[0].name, data.constructors[0].name);
    let TermKind::Var(result) = &*family.constructors[0].result.kind else {
        panic!("constructor result is its family")
    };
    assert_eq!(result, &data.name);
    let mut copied = statements.clone();
    resolver.statements(&mut copied);
    assert_eq!(copied, statements);
}

#[test]
fn existing_references_survive_a_different_environment() {
    tauto_parse::install();
    let mut declarations = Declarations::default();
    let reference = Name::from(declarations.reserve("value"));
    let mut resolver = Resolver::default();
    let span = Span::new(0, 1);
    let mut term = SurfaceTerm::new(TermKind::Var(reference.clone()), span);
    resolver.term_in_context(&mut term, &[Name::from("value")]);
    assert!(matches!(&*term.kind, TermKind::Var(resolved) if resolved == &reference));
}
