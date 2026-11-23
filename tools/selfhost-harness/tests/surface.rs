//! `totes/surface` against `tauto::surface` (`docs/design/self-host.md`).

use selfhost_harness::{assert_same_dump, corpus, differential, materialize, run_tote_native};
use tauto::surface::{dump::dump_program, parse_program};
use tauto_parse::{parse_program_unresolved_at as parse_program_at};

const STEPS: u64 = 200_000_000_000;

/// What the Rust reader gives, in the form the tote prints: the dump of the
/// program, or `error` (the message of an error is not compared).
fn expected(source: &str, base: u32) -> String {
    std::panic::catch_unwind(|| {
        parse_program_at(source, base)
            .ok()
            .map(|p| dump_program(&p))
    })
    .ok()
    .flatten()
    .unwrap_or_else(|| "error\n".to_string())
}

fn compare_at(label: &str, inputs: Vec<(String, String)>, base: u32) {
    let m = materialize(label, &inputs);
    let mut args = Vec::new();
    if base != 0 {
        args.push("--base".to_string());
        args.push(base.to_string());
    }
    args.extend(m.paths.iter().cloned());
    let out = run_tote_native("parse", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    let mut rust = String::new();
    for (path, (_, source)) in m.paths.iter().zip(&inputs) {
        rust.push_str(&format!("== {path}\n{}", expected(source, base)));
    }
    assert_same_dump("surface", &rust, &out.stdout);
}

fn compare(label: &str, inputs: Vec<(String, String)>) {
    compare_at(label, inputs, 0);
}

/// One part of the corpus, so that the parts run side by side.
fn part(label: &str, n: usize, of: usize) {
    let inputs: Vec<_> = corpus()
        .into_iter()
        .enumerate()
        .filter(|(i, _)| i % of == n)
        .map(|(_, x)| x)
        .collect();
    compare(label, inputs);
}

#[test]
fn surface_matches_the_corpus_0() {
    part("surface-0", 0, 6);
}

#[test]
fn surface_matches_the_corpus_1() {
    part("surface-1", 1, 6);
}

#[test]
fn surface_matches_the_corpus_2() {
    part("surface-2", 2, 6);
}

#[test]
fn surface_matches_the_corpus_3() {
    part("surface-3", 3, 6);
}

#[test]
fn surface_matches_the_corpus_4() {
    part("surface-4", 4, 6);
}

#[test]
fn surface_matches_the_corpus_5() {
    part("surface-5", 5, 6);
}

/// Spans that start at a base, as the prelude's do.
#[test]
fn surface_matches_with_a_base() {
    let inputs: Vec<_> = corpus().into_iter().step_by(40).collect();
    compare_at("surface-base", inputs, 1 << 31);
}

#[test]
fn parse_program_is_the_unresolved_reader_at_base_0() {
    // On a source with no classes or macros, `parse_program` gives what the
    // unresolved reader gives at base 0.
    let source = r#"let a := 1
"#;
    assert_eq!(
        parse_program(source).map(|p| dump_program(&p)).map_err(|m| m.to_string()),
        parse_program_at(source, 0).map(|p| dump_program(&p))
    );
}

/// `coerce` stands before one field of a struct: two in a struct, or one before
/// a field of an enum variant or a record type, is refused by both readers.
#[test]
fn surface_refuses_misplaced_coerce() {
    let case = |name: &str, source: &str| (name.to_string(), source.to_string());
    compare(
        "surface-coerce-refused",
        vec![
            case("ok", "struct P { a: i64 }\nstruct W { coerce inner: P, tag: i64 }\n"),
            case("ok-mut", "struct P { a: i64 }\nstruct W { coerce(mut) inner: P, tag: i64 }\n"),
            case("twice", "struct P { a: i64 }\nstruct W { coerce a: P, coerce b: P }\n"),
            case("enum", "enum E { A { coerce x: i64 }, B }\n"),
            case("record-type", "fn f(p: { coerce x: i64 }): i64 { 0 }\n"),
            case("in-module", "module m {\n  struct P { a: i64 }\n  struct W { coerce a: P, coerce b: P }\n}\n"),
        ],
    );
}

/// `^` on a constructor name with arguments or a field label is refused by both
/// readers. Binding sites (`Some(^x)`, `Point { x: ^y }`, shorthand `Point { ^x }`)
/// keep the mark. Nullary constructors are refused after name resolution, not here.
/// Inputs: `cases/unused-marker.eure` cases with `differential = "surface"`.
#[test]
fn surface_refuses_unused_marker_on_non_bindings() {
    let inputs: Vec<_> = differential("surface")
        .into_iter()
        .filter(|(name, _)| name.contains("unused-marker.eure#"))
        .collect();
    assert!(
        !inputs.is_empty(),
        "unused-marker.eure has no differential = \"surface\" cases"
    );
    compare("surface-unused-marker-not-binding", inputs);
}

/// A row variable written inside a row literal's braces is refused by both readers.
/// Inputs: `cases/check/row-variable-in-literal.eure` cases with `differential = "surface"`.
#[test]
fn surface_refuses_a_row_variable_in_a_row_literal() {
    let inputs: Vec<_> = differential("surface")
        .into_iter()
        .filter(|(name, _)| name.contains("row-variable-in-literal.eure#"))
        .collect();
    assert!(
        !inputs.is_empty(),
        "row-variable-in-literal.eure has no differential = \"surface\" cases"
    );
    compare("surface-row-variable-in-literal", inputs);
}

/// The Product grammar node also wraps every expression without a × operator.
#[test]
fn surface_preserves_singleton_product_wrappers() {
    compare_at(
        "surface-product-wrapper",
        vec![
            (
                "plain-expression".into(),
                r#"fn constant(): u64 { 0 }
"#
                .into(),
            ),
            (
                "generic-type-argument".into(),
                r#"enum Box(A: Type) { Wrap(A) }
fn read(x: Box(u64)): u64 { 0 }
"#
                .into(),
            ),
            (
                "operator-precedence".into(),
                r#"fn arithmetic(): i64 { 1 + 2 * 3 }
"#
                .into(),
            ),
        ],
        1 << 31,
    );
}

/// Two or more members are a product, and `(p: T)` takes a member by its type,
/// read as the Rust reader reads them: never one member, a tuple or a union.
#[test]
fn surface_reads_products_and_typed_projections() {
    compare_at(
        "surface-product",
        vec![
            (
                "product-value".into(),
                r#"let value := #(1, "a", true)
"#
                .into(),
            ),
            (
                "product-type".into(),
                r#"fn first(p: {i64 × Text} × Bool): i64 { 0 }
"#
                .into(),
            ),
            (
                "typed-projection".into(),
                r#"fn read(p: i64 × Text): Text { (p: Text) }
"#
                .into(),
            ),
            (
                "tagged-product".into(),
                r#"let p := #(@x 1, @y 2)
let a: i64 := (p: @x i64)
"#
                .into(),
            ),
        ],
        1 << 31,
    );
}

/// `f(<x: v>, h)`: the implicit arguments written by name come first, as the
/// record `@implicits`, as the Rust reader carries them.
#[test]
fn surface_reads_named_implicit_arguments() {
    compare(
        "surface-named-implicits",
        vec![(
            "named-implicits".into(),
            r#"fn id<A>(x: A): A { x }
fn one(): u64 { id(<A: u64>, 1) }
fn two(): u64 { pick(<x: [1, 2], y: (a + b)>, h, k) }
"#
            .into(),
        )],
    );
}
