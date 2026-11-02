use super::*;

fn report(source: &str) -> RowReport {
    let program = crate::types::expand_classes(
        crate::surface::parse_program_as_written(source).unwrap(),
        1 << 30,
    );
    check_program_rows(&program)
}

fn accepts(source: &str) {
    let r = report(source);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
}

fn rejects(source: &str) {
    let program = crate::types::expand_classes(
        crate::surface::parse_program_as_written(source).unwrap(),
        1 << 30,
    );
    let types = crate::types::check_program(&program);
    assert!(
        types.errors.is_empty(),
        "negative fixture must be value-typed: {:?}",
        types.errors
    );
    assert!(
        !check_program_rows(&program).errors.is_empty(),
        "accepted {source}"
    );
}

#[test]
fn mutable_borrow_contracts_are_invariant_structurally() {
    let mut analysis = Analysis::new(crate::types::prelude());
    let pure = Latent::Known(Callable::simple(Row::new()));
    let effectful = Latent::Known(Callable::simple(Row::from(["ask".into()])));
    analysis.check_value(
        &Latent::Borrow(Box::new(pure), true),
        &Latent::Borrow(Box::new(effectful), true),
        Span::new(0, 0),
        0,
    );
    assert!(!analysis.found.is_empty());
}

#[test]
fn local_calls_have_checked_rows_and_lexical_quantities() {
    for (name, effect) in [
        ("direct-local-call-keeps-inferred-effects", "ask"),
        ("local-recursive-alias-keeps-div", "Div"),
    ] {
        let r = report(&crate::rows::value_tests::case_inputs::source(
            "check/local-function-rows.eure",
            name,
        ));
        assert!(
            r.functions
                .iter()
                .any(|(n, row)| n == "outer" && row.contains(effect))
        );
        assert!(r.calls.values().filter(|row| row.contains(effect)).count() >= 2);
        assert!(r.normalized_calls().is_ok());
    }
    let r = report(
        &r#"fn outer<!e: direct>(captured: () -> Text ! e): Text ! e {
  fn apply<!e: <=1>(callback: () -> Text ! e): Text ! e { callback() }
  apply(captured)
}
"#
        .to_string(),
    );
    let outer = r.declarations.iter().find(|d| d.name == "outer").unwrap();
    let inner = r.declarations.iter().find(|d| d.name == "apply").unwrap();
    let captured = outer.row.iter().next().unwrap();
    let owned = inner.row.iter().next().unwrap();
    assert_ne!(captured, owned);
    assert_eq!(r.quants_of(captured, &|_| false), vec![Quant::Direct]);
    assert!(!r.quants_of(owned, &|_| false).contains(&Quant::Many));
    assert!(r.normalize_row(&outer.row, Some(inner.owner)).is_err());
}

#[test]
fn captured_rows_are_fixed_not_quantified_and_lowering_fails_closed() {
    let source = r#"fn outer<!e>(captured: () -> Text ! e): Text ! e {
  fn inner<!e>(own: () -> Text ! e): Text {
    captured()
    own()
  }
  let alias := inner
  alias(() => "ok")
}
"#
    .to_string();
    let r = report(&source);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    let inner = r.declarations.iter().find(|d| d.name == "inner").unwrap();
    assert_eq!(inner.inferred.len(), 2);
    assert!(r.normalize_row(&inner.inferred, Some(inner.owner)).is_err());
    assert!(r.normalized_calls().is_err());
    assert!(!dump_rows(&r).contains("@row:"));
}

#[test]
fn distinct_declarations_can_share_a_body_without_sharing_row_binders() {
    let source = r#"fn first<!e>(callback: () -> Text ! e): Text ! e { "ok" }
fn second<!e>(callback: () -> Text ! e): Text ! e { "ok" }
"#
    .to_string();
    let mut program = crate::surface::parse_program_as_written(&source).unwrap();
    let body = match &program.stmts[0] {
        Stmt::Fn(f) => f.body.clone(),
        _ => panic!(),
    };
    let Stmt::Fn(second) = &mut program.stmts[1] else {
        panic!()
    };
    second.body = body.clone();
    let r = check_program_rows(&program);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    let a = r.declaration_row("first", body.id()).unwrap().unwrap();
    let b = r.declaration_row("second", body.id()).unwrap().unwrap();
    assert_ne!(a.owner, b.owner);
    assert_ne!(a.row, b.row);
    assert_eq!(
        r.normalize_row(&a.row, Some(a.owner)).unwrap(),
        Row::from(["|e".into()])
    );
}

#[test]
fn ambiguous_shared_call_occurrences_fail_closed() {
    let source = r#"fn first(callback: () -> Text ! {}): Text ! {} { callback() }
fn second(callback: () -> Text ! {}): Text ! {} { callback() }
"#
    .to_string();
    let mut program = crate::surface::parse_program_as_written(&source).unwrap();
    let body = match &program.stmts[0] {
        Stmt::Fn(f) => f.body.clone(),
        _ => panic!(),
    };
    let Stmt::Fn(second) = &mut program.stmts[1] else {
        panic!()
    };
    second.body = body;
    let r = check_program_rows(&program);
    assert!(
        r.errors
            .iter()
            .any(|e| e.message.to_string().contains("ambiguous lexical"))
    );
    assert!(r.normalized_calls().is_err());
}

#[test]
fn repeated_shared_declaration_occurrences_fail_closed() {
    let source = r#"fn outer(): Text ! {} {
  fn outer(): Text ! {} { "inner" }
  outer()
}
"#
    .to_string();
    let mut program = crate::surface::parse_program_as_written(&source).unwrap();
    let Stmt::Fn(mut copy) = program.stmts[0].clone() else {
        panic!()
    };
    copy.name = "copy".into();
    program.stmts.push(Stmt::Fn(copy));
    let r = check_program_rows(&program);
    assert!(r.errors.iter().any(|e| {
        e.message
            .contains("ambiguous lexical occurrence of function")
    }));
    let inner = r
        .declarations
        .iter()
        .find(|d| r.ambiguous_owners.contains(&d.owner))
        .unwrap();
    assert!(r.declaration_row(&inner.name, inner.body).is_err());
}

#[test]
fn independent_reports_merge_only_matching_declaration_evidence() {
    let source = r#"fn first<!e>(callback: () -> Text ! e): Text ! e { "ok" }
fn second<!e>(callback: () -> Text ! e): Text ! e { "ok" }
"#
    .to_string();
    let program = crate::surface::parse_program_as_written(&source).unwrap();
    let mut a = check_program_rows(&program);
    let b = check_program_rows(&program);
    a.merge_prelude(b);
    assert_eq!(
        a.declarations.iter().filter(|d| d.name == "first").count(),
        1
    );
    let mut different = check_program_rows(&program);
    different
        .declarations
        .iter_mut()
        .find(|d| d.name == "first")
        .unwrap()
        .inferred
        .insert("ask".into());
    a.merge_prelude(different);
    let first = a.declarations.iter().find(|d| d.name == "first").unwrap();
    assert!(a.declaration_row("first", first.body).is_err());
}

#[test]
fn local_recursion_does_not_inherit_a_same_named_total_certificate() {
    let source = r#"fn outer(): i64 {
  fn inner(n: i64): i64 {
    let again := inner
    again(n)
  }
  inner(0)
}
"#
    .to_string();
    let program = crate::surface::parse_program_as_written(&source).unwrap();
    let r = check_program_rows_trusted(&program, &HashSet::from(["inner".into()]), false);
    assert!(
        r.declarations
            .iter()
            .find(|d| d.name == "inner")
            .unwrap()
            .inferred
            .contains("Div")
    );
}

#[test]
fn unbound_row_tokens_never_enter_lowering_as_empty_tiers() {
    let r = report(
        &r#"fn outer(): Text {
  let callback: () -> Text ! e := () => "ok"
  callback()
}
"#
        .to_string(),
    );
    assert!(!r.errors.is_empty());
    assert!(r.normalized_calls().is_err());
    assert!(
        r.normalize_row(&Row::from(["|unbound".into()]), None)
            .is_err()
    );
    assert!(
        r.normalize_row(&Row::from(["|@row:missing".into()]), None)
            .is_err()
    );
}

#[test]
fn deferred_constructor_owners_use_only_source_matched_nominal_facts() {
    for name in [
        "constructor-owner-follows-deferred-let-result",
        "constructor-owner-follows-host-argument",
        "constructor-owner-follows-budget-result",
        "constructor-owner-follows-handler-result",
        "constructor-alias-owner-follows-deferred-let-result",
    ] {
        let source =
            crate::rows::value_tests::case_inputs::source("check/local-function-rows.eure", name);
        let program = crate::surface::parse_program_as_written(&source).unwrap();
        let types = crate::types::check_program(&program);
        assert!(types.errors.is_empty(), "{name}: {:?}", types.errors);
        let typed = check_program_rows_with_types(&program, &types);
        assert!(typed.errors.is_empty(), "{name}: {:?}", typed.errors);
        let lazy = check_program_rows(&program);
        assert_eq!(dump_rows(&typed), dump_rows(&lazy), "{name}");
        let foreign = crate::surface::parse_program_as_written(&source).unwrap();
        assert!(types.nominal_owners_for(&foreign).is_none());
        let fallback = check_program_rows_with_types(&foreign, &types);
        assert_eq!(dump_rows(&lazy), dump_rows(&fallback), "{name}");
    }
    let source = r#"effect ask(): Text direct
enum Reader { Read(() -> Text ! {}) }
enum Number { Read(i64) }
fn outer(): Reader ! {} {
  let value := Read(() => perform ask())
  value
}
"#
    .to_string();
    rejects(&source);
    assert!(report(&source).errors.iter().any(|error| {
        error.message == "a function value may perform ask but its type permits {}"
    }));
}

#[test]
fn constructor_owner_cache_rejects_failed_and_mutated_type_evidence() {
    let source = r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
fn outer(): Reader ! {} {
  let value := Read("ok")
  value
}
fn invalid(): i64 { "bad" }
"#
    .to_string();
    let program = crate::surface::parse_program_as_written(&source).unwrap();
    let types = crate::types::check_program(&program);
    assert!(!types.errors.is_empty());
    assert!(types.nominal_owners_for(&program).is_none());
    let rows = check_program_rows_with_types(&program, &types);
    assert!(
        rows.errors
            .iter()
            .any(|error| error.message.to_string().contains("calling `Read`"))
    );
    assert_eq!(dump_rows(&rows), dump_rows(&check_program_rows(&program)));

    let source = r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
fn outer(): Reader ! {} {
  let value := Read("ok")
  value
}
"#
    .to_string();
    let mut program = crate::surface::parse_program_as_written(&source).unwrap();
    let mut types = crate::types::check_program(&program);
    assert!(types.errors.is_empty());
    let owners = types.nominal_owners_for(&program).unwrap().clone();
    for ty in types.terms.values_mut() {
        *ty = crate::types::Ty::Named("Number".into(), Vec::new());
    }
    assert_eq!(types.nominal_owners_for(&program), Some(&owners));
    assert!(
        check_program_rows_with_types(&program, &types)
            .errors
            .is_empty()
    );
    let Stmt::Fn(declaration) = &mut program.stmts[2] else {
        panic!("outer")
    };
    declaration.effects = Some(vec!["ask".into()]);
    assert!(types.nominal_owners_for(&program).is_none());
    let analysis = Analysis::new(&program).with_types(&types);
    assert!(!analysis.nominal_owners_checked);
    assert!(analysis.nominal_owners.is_none());
}

#[test]
fn ordinary_row_checks_do_not_eagerly_recheck_value_types() {
    let source = r#"effect ask(): Text
fn outer(): Text {
  fn inner(): Text { perform ask() }
  inner()
}
"#
    .to_string();
    let program = crate::surface::parse_program_as_written(&source).unwrap();
    let mut analysis = Analysis::new(&program);
    analysis.inferred_row("outer");
    assert!(!analysis.nominal_owners_checked);

    let source = r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
fn outer(): Reader ! {} {
  let value := Read("ok")
  value
}
"#
    .to_string();
    let program = crate::surface::parse_program_as_written(&source).unwrap();
    let mut analysis = Analysis::new(&program);
    analysis.inferred_row("outer");
    assert!(analysis.nominal_owners_checked);
    assert!(analysis.nominal_owners.is_some());
}

const BRANCHED_STEPS: &str = r#"
enum S(V: Type) {
  D(V)
  F(Text)
  N((V) -> S(V) ! {Div})
}
"#;

#[test]
fn branches_of_a_callable_enum_are_checked_against_its_type() {
    for body in [
        r#"fn h(b: Bool): S(i64) { if b { D(1) } else { F("x") } }"#,
        r#"fn h(b: Bool): S(i64) { if b { N((v) => D(v)) } else { F("x") } }"#,
        "fn h(r: Option(i64)): S(i64) {\n  match r {\n    Some(x) => D(x)\n    None => D(0)\n  }\n}",
    ] {
        accepts(&format!("{BRANCHED_STEPS}{body}"));
    }
    let source = format!(
        "{BRANCHED_STEPS}effect ask(): i64\n\
         fn h(b: Bool): S(i64) {{ if b {{ N((v) => D(perform ask())) }} else {{ D(1) }} }}"
    );
    assert!(
        report(&source)
            .errors
            .iter()
            .any(|e| e.message == "a function value may perform ask but its type permits {Div}"),
        "{:?}",
        report(&source).errors
    );
}

#[test]
fn names_the_program_does_not_have_are_named() {
    let r = report("fn main(): i64 { foo(1) }");
    assert!(
        r.errors.iter().any(|e| e
            .message
            .to_string()
            .starts_with("in `main`: `foo` is not defined")),
        "{:?}",
        r.errors
    );
    let r = report(
        "struct H { f: (i64) -> i64 }\nfn need(h: H, x: i64): i64 { h.f(x) }\nfn main(): i64 { need(rt, 1) }",
    );
    assert!(
        r.errors
            .iter()
            .any(|e| e.message.to_string().starts_with("`rt` is not defined")),
        "{:?}",
        r.errors
    );
    assert!(
        r.errors
            .iter()
            .all(|e| !e.message.to_string().contains("cannot follow"))
    );
    let r = report("perform show(\"a\", Nat::lt(1, 2))");
    assert!(
        r.errors.iter().any(|e| e
            .message
            .to_string()
            .starts_with("`Nat::lt` is the kernel's own")),
        "{:?}",
        r.errors
    );
}

#[test]
fn shared_field_holding_new_empty_container_keeps_callable_contract() {
    let source = r#"
effect boom(): () resume 1
shared struct Rt { cell: Ref(List(() -> () ! {∀ A. show(A)})) }
fn add(r: Rt, f: () -> () ! {∀ A. show(A)}): () { Ref::set(r.cell, Cons(f, Ref::get(r.cell))) }
fn run(r: Rt): () ! {∀ A. show(A)} {
  match Ref::get(r.cell) {
    Nil => ()
    Cons(f, t) => f()
  }
}
fn main(): () ! {∀ A. show(A)} {
  let r := Rt { cell: Ref::new(Nil) }
  add(r, () => perform show("y", 1))
  run(r)
}
"#;
    accepts(source);
    rejects(&source.replace(
        "add(r, () => perform show(\"y\", 1))",
        "Ref::set(r.cell, Cons(() => perform boom(), Nil))",
    ));
    rejects(&source.replace("Ref::new(Nil)", "Ref::new(Cons(() => perform boom(), Nil))"));
}

#[test]
fn nat_counted_down_by_match_keeps_its_row() {
    // A `Nat` taken apart by `match` is extracted as `nat` counted down by
    // one, and keeps the row the proof side gave it.
    let source = "effect tick(): ()\nfn ticks(n: nat): () ! {tick} {\n  if n == 0 {\n    ()\n  } else {\n    let m := (n - 1)\n    {\n      perform tick()\n      ticks(m)\n    }\n  }\n}\n";
    accepts(source);
    rejects(&source.replace("nat", "i64"));
}

#[test]
fn host_show_row_hints_agree() {
    // The row the hints for the host's `show` name is one the check accepts.
    accepts("fn main(): () ! {∀ A. show(A)} { perform show(\"a\", 1) }\n");
    let one = report("fn main(): () ! {show(i64)} { perform show(\"a\", 1) }\n");
    assert!(
        one.errors
            .iter()
            .any(|e| e.message.to_string().contains("write `∀ A. show(A)`")),
        "{:?}",
        one.errors
    );
}

/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn source_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
            ("check/local-function-rows.eure", "direct-local-call-keeps-inferred-effects") => {
                r#"effect ask(): Text
fn outer(): Text {
  fn inner(): Text { perform ask() }
  inner()
}
"#
            }
            ("check/local-function-rows.eure", "constructor-owner-follows-deferred-let-result") => {
                r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
fn outer(): Reader ! {} {
  let value := Read("ok")
  value
}
"#
            }
            ("check/local-function-rows.eure", "local-recursive-alias-keeps-div") => {
                r#"fn outer(): i64 {
  fn inner(n: i64): i64 {
    let again := inner
    again(n)
  }
  inner(0)
}
"#
            }
            ("check/local-function-rows.eure", "constructor-owner-follows-budget-result") => {
                r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
fn outer(): Reader ! {Exceeded} { budget(steps: 10) { Read("ok") } }
"#
            }
            ("check/local-function-rows.eure", "constructor-owner-follows-host-argument") => {
                r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
extern { fn consume(value: Reader): Text }
fn outer(): Text ! {} { consume(Read("ok")) }
"#
            }
            (
                "check/local-function-rows.eure",
                "constructor-alias-owner-follows-deferred-let-result",
            ) => {
                r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
fn outer(): Reader ! {} {
  let make := Read
  let value := make("ok")
  value
}
"#
            }
            ("check/local-function-rows.eure", "constructor-owner-follows-handler-result") => {
                r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
fn outer(): Reader ! {} {
  handle { Read("ok") } with { return value => value }
}
"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn source(file: &str, name: &str) -> String {
        source_static(file, name).to_string()
    }
}
