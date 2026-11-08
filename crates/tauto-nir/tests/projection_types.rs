use tauto_nir::{ExprKind, Repr, Ty, Use, compile_with};

fn data(name: &str, args: Vec<Ty>) -> Ty {
    Ty::Data(name.into(), args)
}

fn check(source: &str, types: &[Ty], borrowed: Option<Repr>, pair: bool) {
    let package = compile_with(source, true).unwrap();
    fn bound(ty: &Ty, package: &tauto_nir::Package) -> Ty {
        match ty {
            Ty::Data(name, arguments) => {
                let matches: Vec<_> = package
                    .datas
                    .iter()
                    .filter(|data| data.name.as_str() == name.as_str())
                    .collect();
                assert_eq!(
                    matches.len(),
                    1,
                    "the fixture names exactly one declaration: {name}"
                );
                Ty::Data(
                    matches[0].name.clone(),
                    arguments.iter().map(|ty| bound(ty, package)).collect(),
                )
            }
            Ty::Pair(first, second) => Ty::Pair(
                Box::new(bound(first, package)),
                Box::new(bound(second, package)),
            ),
            _ => ty.clone(),
        }
    }
    let types: Vec<_> = types.iter().map(|ty| bound(ty, &package)).collect();
    let mut checked = 0;
    for function in &package.fns {
        if function.source.as_str() != "read" {
            continue;
        }
        function.body.walk(&mut |expression| {
            let ExprKind::Field { field, .. } = &expression.kind else {
                return;
            };
            if field.name.as_str() != "values" {
                return;
            }
            let mut current = expression;
            for (index, ty) in types.iter().enumerate() {
                assert_eq!(&current.ty, ty, "projection {index}: {current:?}");
                if let ExprKind::Field {
                    base, how, field, ..
                } = &current.kind
                {
                    if index > 0 {
                        assert_eq!(*how, Use::Place);
                    }
                    if field.name.as_str() == "fst" {
                        assert!(pair);
                        assert_eq!(field.index, Some(0));
                    }
                    let start = current.span.start as usize;
                    let end = current.span.end as usize;
                    assert!(source[start..end].ends_with(&field.name));
                    current = base;
                } else {
                    let ExprKind::Read { local, how } = &current.kind else {
                        panic!("expected root read: {current:?}");
                    };
                    assert_eq!(index + 1, types.len());
                    assert_eq!(*how, Use::Place);
                    assert_eq!(local.repr, function.params[0].local.repr);
                    if let Some(repr) = borrowed {
                        assert_eq!(local.repr, repr);
                    }
                    assert_eq!(
                        &source[current.span.start as usize..current.span.end as usize],
                        "value"
                    );
                }
            }
            checked += 1;
        });
    }
    assert!(checked > 0);
}

#[test]
fn every_projection_has_its_checked_type_and_source_span() {
    let element = Ty::Int(tauto_nir::Width::U64);
    let list = data("List", vec![element]);
    let inner = data("Inner", vec![]);
    let outer = data("Outer", vec![]);
    for (source, repr) in [
        (
            r#"struct Inner { values: List(u64) }
struct Outer { inner: Inner }
fn read(value: Outer): List(u64) { value.inner.values }"#,
            None,
        ),
        (
            r#"struct Inner { values: List(u64) }
struct Outer { inner: Inner }
fn read(&value: Outer): List(u64) { value.inner.values }"#,
            Some(Repr::Ref),
        ),
        (
            r#"struct Inner { values: List(u64) }
struct Outer { inner: Inner }
fn read(&mut value: Outer): List(u64) { value.inner.values }"#,
            Some(Repr::RefMut),
        ),
    ] {
        check(
            &source,
            &[list.clone(), inner.clone(), outer.clone()],
            repr,
            false,
        );
    }
    let source = r#"struct Inner { values: List(u64) }
struct Outer { inner: Inner }
fn read(value: Pair(Outer, u64)): List(u64) { value.fst.inner.values }"#;
    let pair = Ty::Pair(
        Box::new(outer.clone()),
        Box::new(Ty::Int(tauto_nir::Width::U64)),
    );
    check(
        source,
        &[list.clone(), inner.clone(), outer, pair],
        None,
        true,
    );
    let source = r#"struct Inner { values: List(u64) }
struct Outer { pair: Pair(Inner, u64) }
fn read(value: Outer): List(u64) { value.pair.fst.values }"#;
    let pair = Ty::Pair(
        Box::new(inner.clone()),
        Box::new(Ty::Int(tauto_nir::Width::U64)),
    );
    check(
        source,
        &[list, inner, pair, data("Outer", vec![])],
        None,
        true,
    );
}

#[test]
fn generic_projection_types_retain_the_helper_type_parameter() {
    let source = r#"shared struct Inner(A: Shared) { values: List(A) }
shared struct Outer(B: Shared) { inner: Inner(B) }
shared struct Wrapper(C: Shared) { outer: Outer(C) }
fn read<T: Shared>(&value: Wrapper(T)): List(T) { value.outer.inner.values }
fn run(value: Wrapper(u64)): List(u64) { read(&value) }"#;
    let parameter = Ty::Param("T".into());
    check(
        source,
        &[
            data("List", vec![parameter.clone()]),
            data("Inner", vec![parameter.clone()]),
            data("Outer", vec![parameter.clone()]),
            data("Wrapper", vec![parameter]),
        ],
        Some(Repr::Ref),
        false,
    );
}
