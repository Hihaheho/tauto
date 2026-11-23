use super::*;

fn report(source: &str) -> RowReport {
    let program = crate::types::expand_classes(
        tauto_parse::parse_program_as_written(source).unwrap(),
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
        tauto_parse::parse_program_as_written(source).unwrap(),
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
        ("local-recursive-alias-keeps-div", "div"),
    ] {
        let r = report(&tauto_case_inputs::source(
            "check/local-function-rows.eure",
            name,
        ));
        assert!(
            r.functions
                .iter()
                .any(|(n, row)| n.as_str() == "outer" && row.contains(&Name::from(effect)))
        );
        assert!(
            r.calls
                .values()
                .filter(|row| row.contains(&Name::from(effect)))
                .count()
                >= 2
        );
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
    let outer = r
        .declarations
        .iter()
        .find(|d| d.name.as_str() == "outer")
        .unwrap();
    let inner = r
        .declarations
        .iter()
        .find(|d| d.name.as_str() == "apply")
        .unwrap();
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
  fn inner(own: () -> Text ! {}): Text ! e {
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
    let inner = r
        .declarations
        .iter()
        .find(|d| d.name.as_str() == "inner")
        .unwrap();
    // `inner` writes no row variable of its own (a row holds at most one, and
    // rows are written), so its row is the captured `e` alone.
    assert_eq!(inner.inferred.len(), 1);
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
    let mut program = tauto_parse::parse_program_as_written(&source).unwrap();
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
    let a = r
        .declaration_row(&Name::from("first"), body.id())
        .unwrap()
        .unwrap();
    let b = r
        .declaration_row(&Name::from("second"), body.id())
        .unwrap()
        .unwrap();
    assert_ne!(a.owner, b.owner);
    assert_ne!(a.row, b.row);
    assert_eq!(r.normalize_row(&a.row, Some(a.owner)).unwrap(), a.row);
}

#[test]
fn ambiguous_shared_call_occurrences_fail_closed() {
    let source = r#"fn first(callback: () -> Text ! {}): Text ! {} { callback() }
fn second(callback: () -> Text ! {}): Text ! {} { callback() }
"#
    .to_string();
    let mut program = tauto_parse::parse_program_as_written(&source).unwrap();
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
            .any(|e| tauto_messages::english(&e.message).contains("ambiguous lexical"))
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
    let mut program = tauto_parse::parse_program_as_written(&source).unwrap();
    let Stmt::Fn(mut copy) = program.stmts[0].clone() else {
        panic!()
    };
    copy.name = "copy".into();
    program.stmts.push(Stmt::Fn(copy));
    let r = check_program_rows(&program);
    assert!(
        r.errors
            .iter()
            .any(|e| { e.message.id == "rows-ambiguous-function" })
    );
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
    for resolved in [false, true] {
        let mut program = tauto_parse::parse_program_as_written(&source).unwrap();
        if resolved {
            tauto_surface::resolve::Resolver::default().statements(&mut program.stmts);
        }
        let mut a = check_program_rows(&program);
        let b = check_program_rows(&program);
        a.merge_prelude(b);
        assert_eq!(
            a.declarations
                .iter()
                .filter(|d| d.name.as_str() == "first")
                .count(),
            1
        );
        for declaration in &a.declarations {
            assert!(
                a.normalize_row(&declaration.row, Some(declaration.owner))
                    .is_ok()
            );
        }
        let mut different = check_program_rows(&program);
        different
            .declarations
            .iter_mut()
            .find(|d| d.name.as_str() == "first")
            .unwrap()
            .inferred
            .insert("ask".into());
        a.merge_prelude(different);
        let first = a
            .declarations
            .iter()
            .find(|d| d.name.as_str() == "first")
            .unwrap();
        assert!(a.declaration_row(&first.name, first.body).is_err());
    }
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
    let program = tauto_parse::parse_program_as_written(&source).unwrap();
    let r = check_program_rows_trusted(&program, &HashSet::from(["inner".into()]), Target::Rust);
    assert!(
        r.declarations
            .iter()
            .find(|d| d.name.as_str() == "inner")
            .unwrap()
            .inferred
            .contains(&Name::from("div"))
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
        let source = tauto_case_inputs::source("check/local-function-rows.eure", name);
        let program = tauto_parse::parse_program_as_written(&source).unwrap();
        let types = crate::types::check_program(&program);
        assert!(types.errors.is_empty(), "{name}: {:?}", types.errors);
        let typed = check_program_rows_with_types(&program, &types);
        assert!(typed.errors.is_empty(), "{name}: {:?}", typed.errors);
        let lazy = check_program_rows(&program);
        assert_eq!(dump_rows(&typed), dump_rows(&lazy), "{name}");
        let foreign = tauto_parse::parse_program_as_written(&source).unwrap();
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
        error.message
            == msg!(
                "rows-value-performs",
                effect = "ask".to_string(),
                row = String::new()
            )
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
    let program = tauto_parse::parse_program_as_written(&source).unwrap();
    let types = crate::types::check_program(&program);
    assert!(!types.errors.is_empty());
    assert!(types.nominal_owners_for(&program).is_none());
    let rows = check_program_rows_with_types(&program, &types);
    // The failed types are no evidence for `Read`, so the rows keep their own
    // error: an unfollowed callee stays "cannot follow", it is not replaced by
    // the type error (`check_program_rows_with_types`).
    assert!(
        rows.errors
            .iter()
            .any(|error| tauto_messages::english(&error.message)
                .contains("cannot follow the effects of calling `Read`")),
        "{:?}",
        rows.errors
            .iter()
            .map(|error| tauto_messages::english(&error.message))
            .collect::<Vec<_>>()
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
    let mut program = tauto_parse::parse_program_as_written(&source).unwrap();
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
    let program = tauto_parse::parse_program_as_written(&source).unwrap();
    let mut analysis = Analysis::new(&program);
    let outer = Name::from("outer");
    analysis.inferred_row(&outer);
    assert!(!analysis.nominal_owners_checked);

    let source = r#"enum Reader { Read(Text) }
enum Number { Read(i64) }
fn outer(): Reader ! {} {
  let value := Read("ok")
  value
}
"#
    .to_string();
    let program = tauto_parse::parse_program_as_written(&source).unwrap();
    let mut analysis = Analysis::new(&program);
    let outer = Name::from("outer");
    analysis.inferred_row(&outer);
    assert!(analysis.nominal_owners_checked);
    assert!(analysis.nominal_owners.is_some());
}

const BRANCHED_STEPS: &str = r#"
enum S(V: Type) {
  D(V)
  F(Text)
  N((V) -> S(V) ! {div})
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
        report(&source).errors.iter().any(|e| e.message
            == msg!(
                "rows-value-performs",
                effect = "ask".to_string(),
                row = "div".to_string()
            )),
        "{:?}",
        report(&source).errors
    );
}

#[test]
fn nat_counted_down_by_match_keeps_its_row() {
    // A `Nat` taken apart by `match` is extracted as `nat` counted down by
    // one, and keeps the row the proof side gave it: no `div`. Unbounded
    // `nat` subtraction does not perform `overflow`; the same countdown on
    // `i64` does.
    let source = "effect tick(): ()\nfn ticks(n: nat): () ! {tick} {\n  if n == 0 {\n    ()\n  } else {\n    let m := (n - 1)\n    {\n      perform tick()\n      ticks(m)\n    }\n  }\n}\n";
    accepts(source);
    rejects(&source.replace("nat", "i64"));
}

#[test]
fn a_total_declaration_writes_its_guarded_arithmetic_without_overflow() {
    tauto_parse::install();
    // Fixed-width `-` performs `overflow` unless extraction evidence names
    // the declaration (`in_total`): the same body without the evidence does.
    let source = "fn down(n: i64): i64 {\n  if n == 0 { 0 } else { n - 1 }\n}\n";
    let program = crate::types::expand_classes(
        crate::surface::parse_program_as_written(source).unwrap(),
        1 << 30,
    );
    let overflows = |r: &RowReport| {
        r.declarations
            .iter()
            .find(|d| d.name.as_str() == "down")
            .unwrap()
            .inferred
            .iter()
            .any(|e| e.as_str().ends_with("overflow"))
    };
    let trusted =
        check_program_rows_trusted(&program, &HashSet::from(["down".into()]), Target::Rust);
    assert!(!overflows(&trusted));
    assert!(overflows(&check_program_rows(&program)));
}

#[test]
fn nat_subtraction_does_not_perform_overflow() {
    // Unbounded `nat` arithmetic is not fixed-width: `n - 1` leaves no
    // `overflow` in the row (Succ elimination extracts the same way).
    accepts("fn down(n: nat): nat ! {} {\n  if n == 0 { 0 } else { n - 1 }\n}\n");
}
