//! Schema fields are legal identifiers and unique after normalization.
use selfhost_harness::run_tote_native;
use tauto_syntax::{Payload, TypeDef};

const STEPS: u64 = 200_000_000_000;
const KEYWORDS: &[&str] = &[
    "theorem",
    "def",
    "import",
    "mutual",
    "axiom",
    "inductive",
    "forall",
    "exists",
    "decreasing_by",
    "as",
    "by",
    "let",
    "var",
    "fn",
    "return",
    "while",
    "loop",
    "break",
    "continue",
    "if",
    "else",
    "match",
    "struct",
    "enum",
    "effect",
    "handle",
    "with",
    "perform",
    "budget",
    "brand",
    "copy",
    "shared",
    "affine",
    "linear",
    "view",
    "resume",
    "direct",
    "mut",
    "module",
    "where",
    "class",
    "instance",
    "law",
    "extern",
    "true",
    "false",
    "syntax",
    "macro",
    "quote",
];

fn generate(name: &str, body: &str) -> String {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("tauto-fields-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("grammar.par");
    std::fs::write(
        &path,
        format!("%start Root\n%title \"fields\"\n%%\n{body}\n"),
    )
    .unwrap();
    let out = run_tote_native(
        "syntaxgen",
        &["--gen".into(), path.display().to_string()],
        STEPS,
    );
    assert_eq!(out.error, None);
    assert_eq!(out.exit, Some(0), "{}", out.stderr);
    std::fs::remove_dir_all(dir).unwrap();
    out.stdout
}

fn names(table: &str) -> Vec<String> {
    let tables = tauto_syntax::Tables::read(table).unwrap();
    match &tables.schema().types[0] {
        TypeDef::Struct { fields, .. } => fields.iter().map(|(name, _)| name.clone()).collect(),
        other => panic!("expected struct, got {other:?}"),
    }
}

#[test]
fn keywords_and_metadata_names_have_legal_deterministic_fields() {
    let words = KEYWORDS.iter().chain([&"span"]);
    let rule = |w: &&str| format!("{}{}", w[..1].to_ascii_uppercase(), &w[1..]);
    let body = format!(
        "Root: {};\n{}",
        words
            .clone()
            .map(|w| rule(&w))
            .collect::<Vec<_>>()
            .join(" "),
        words
            .clone()
            .map(|w| format!("{}: '{w}';", rule(&w)))
            .collect::<Vec<_>>()
            .join("\n")
    );
    let first = generate("keywords", &body);
    assert_eq!(first, generate("keywords-again", &body));
    // Literal names are first normalized by the terminal naming rules.
    let expected: Vec<_> = words.map(|w| format!("{w}_field")).collect();
    assert_eq!(names(&first), expected);
    let tables = tauto_syntax::Tables::read(&first).unwrap();
    let text = tauto::syntax::types_text("words", &tables);
    tauto::surface::parse_program(&text).unwrap();
}

#[test]
fn numeric_suffixes_and_normalized_names_cannot_collide() {
    let table = generate(
        "collisions",
        "Root: Foo_2 Foo Foo Foo_2 Span SpanField 'true' TrueField '+' Plus;\nFoo_2: 'a';\nFoo: 'b';\nSpan: 'c';\nSpanField: 'd';\nTrueField: 'e';\nPlus: 'f';",
    );
    assert_eq!(
        names(&table),
        [
            "foo_2",
            "foo",
            "foo_3",
            "foo_2_2",
            "span_field",
            "span_field_2",
            "true_field",
            "true_field_2",
            "plus",
            "plus_2"
        ]
    );
}

#[test]
fn wildcard_spelling_is_not_emitted_as_a_field() {
    let table = generate("wildcard", "Root: ' ' ' ';");
    assert_eq!(names(&table), ["field", "field_2"]);
    let tables = tauto_syntax::Tables::read(&table).unwrap();
    tauto::surface::parse_program(&tauto::syntax::types_text("words", &tables)).unwrap();
}

#[test]
fn option_and_repeat_fields_follow_the_same_rule() {
    let table = generate("containers", "Root: [ 'true' ] { 'false' };");
    assert_eq!(names(&table), ["true_field", "false_field"]);
    let tables = tauto_syntax::Tables::read(&table).unwrap();
    assert!(matches!(&tables.schema().types[0], TypeDef::Struct { .. }));
    // Both enum record fields and ordinary struct fields use the schema mapping.
    let table = generate("enum", "Root: 'true' | 'false';");
    let tables = tauto_syntax::Tables::read(&table).unwrap();
    let TypeDef::Enum { ctors, .. } = &tables.schema().types[0] else {
        panic!()
    };
    for (ctor, field) in ctors.iter().zip(["true_field", "false_field"]) {
        let Payload::Record(fields) = &ctor.payload else {
            panic!()
        };
        assert_eq!(fields[0].0, field);
    }
}
