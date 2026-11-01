use tauto_parol::NonTerminalKind as Nt;

use super::{SurfaceTerm, TermKind, terms_in};

fn result_type(source: &str) -> SurfaceTerm {
    let mut terms = terms_in(source, Nt::TheoremDecl).unwrap();
    terms.pop().expect("a result type")
}

fn var(term: &SurfaceTerm) -> &str {
    match &*term.kind {
        TermKind::Var(name) => name,
        other => panic!("not a name: {other:?}"),
    }
}

fn app(term: &SurfaceTerm) -> (&str, &[SurfaceTerm]) {
    match &*term.kind {
        TermKind::App {
            function,
            arguments,
        } => (var(function), arguments),
        other => panic!("not an application: {other:?}"),
    }
}

#[test]
fn eq_of_two_names() {
    let t = result_type(r#"theorem t(a: Nat): a = b { Refl }"#);
    // `a = b` stays the operator `=`; the kernel's elaborator fills in
    // `Eq(T, a, b)` with its type `T`.
    let (f, args) = app(&t);
    assert_eq!(f, "=");
    assert_eq!((var(&args[0]), var(&args[1])), ("a", "b"));
}

#[test]
fn a_term_is_an_argument() {
    // `n + 1` is a term, an application of `+`, in the same AST as the type.
    let t = result_type(r#"theorem t(): Vector(i64, n + 1) { Refl }"#);
    let (f, args) = app(&t);
    assert_eq!(f, "Vector");
    assert_eq!(var(&args[0]), "i64");
    let (op, operands) = app(&args[1]);
    assert_eq!(op, "+");
    assert_eq!(var(&operands[0]), "n");
    assert_eq!(*operands[1].kind, TermKind::Nat("1".into()));
}

#[test]
fn a_call_in_a_type_argument() {
    let t = result_type(r#"theorem t(): State(i64, keyOf(config)) { Refl }"#);
    let (f, args) = app(&t);
    assert_eq!(f, "State");
    let (callee, call_args) = app(&args[1]);
    assert_eq!(callee, "keyOf");
    assert_eq!(var(&call_args[0]), "config");
}

#[test]
fn a_function_type_is_an_argument() {
    let t = result_type(r#"theorem t(): List((Nat) -> Nat) { Refl }"#);
    let (_, args) = app(&t);
    let TermKind::Pi { params, result, .. } = &*args[0].kind else {
        panic!("not a Pi: {:?}", args[0])
    };
    assert_eq!(var(&params[0].1), "Nat");
    assert_eq!(var(result), "Nat");
}

#[test]
fn angle_type_arguments_do_not_parse() {
    // A type is applied one way, as a call.
    assert!(
        terms_in(
            r#"theorem t(): Eq<a, b> { Refl }"#,
            Nt::TheoremDecl
        )
        .is_err()
    );
}

#[test]
fn a_term_in_the_place_of_a_type() {
    let t = result_type(r#"theorem t(): { if b { Nat } else { Bool } } { Refl }"#);
    let TermKind::If {
        condition,
        then,
        otherwise,
    } = &*t.kind
    else {
        panic!("not an if: {t:?}")
    };
    assert_eq!(var(condition), "b");
    assert_eq!(var(then), "Nat");
    assert_eq!(var(otherwise.as_ref().unwrap()), "Bool");
}

#[test]
fn quantifiers_and_connectives() {
    let t = result_type(r#"theorem t(): ∀ x: Nat. x = x { Refl }"#);
    let TermKind::Pi { params, result, .. } = &*t.kind else {
        panic!("not a Pi: {t:?}")
    };
    assert_eq!(params[0].0.as_deref(), Some("x"));
    assert_eq!(app(result).0, "=");

    let t = result_type(r#"theorem t(): A ∧ B { Refl }"#);
    assert_eq!(app(&t).0, "And");

    let t = result_type(r#"theorem t(): ∃ x: Nat. x = x { Refl }"#);
    assert!(matches!(&*t.kind, TermKind::Exists { .. }));
}

#[test]
fn function_types_carry_their_effects() {
    let mut terms = terms_in(
        r#"fn f(x: (i64) -> Bool): i64 { 0 }"#,
        Nt::Param,
    )
    .unwrap();
    let TermKind::Pi {
        params,
        result,
        effects,
    } = (*terms.pop().unwrap().kind).clone()
    else {
        panic!("not a Pi")
    };
    assert_eq!(var(&params[0].1), "i64");
    assert_eq!(var(&result), "Bool");
    assert_eq!(effects, None);
}

#[test]
fn unions_and_tags() {
    let t = result_type(r#"theorem t(): @a i64 | Text { Refl }"#);
    let TermKind::Union(members) = &*t.kind else {
        panic!("not a union: {t:?}")
    };
    assert!(matches!(&*members[0].kind, TermKind::Tagged { tag, .. } if tag == "a"));
    assert_eq!(var(&members[1]), "Text");
}

#[test]
fn effects_after_a_function_type() {
    let mut terms = terms_in(
        r#"fn f(x: (i64) -> Bool ! {Div, ask}): i64 { 0 }"#,
        Nt::Param,
    )
    .unwrap();
    let TermKind::Pi { effects, .. } = (*terms.pop().unwrap().kind).clone() else {
        panic!("not a Pi")
    };
    assert_eq!(effects, Some(vec!["Div".to_string(), "ask".to_string()]));
}

/// A function of `std` with a prelude function's name is that builtin's
/// model: it may read the builtin's machine word as a number, and nothing
/// else.
#[test]
fn a_std_model_takes_and_gives_what_its_builtin_does() {
    let model = |source: &str| {
        let stmts = super::parse_program_as_written_at(source, 0).unwrap().stmts;
        super::qualify::std_models(&[stmts], &["std::Model".to_string()])
    };
    assert!(model("module Text {\n  pub fn len(t: Text): Nat {\n    0\n  }\n}\n").is_empty());
    // A type by its full name is the type.
    assert!(model("module Float {\n  pub fn abs(x: std::Float::Float): std::Float::Float {\n    x\n  }\n}\n").is_empty());
    let errors = model("module U64 {\n  pub fn of_nat(n: Nat): Option(U64) {\n    None\n  }\n}\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].0.contains("`std::Model::U64::of_nat`"), "{errors:?}");
}
