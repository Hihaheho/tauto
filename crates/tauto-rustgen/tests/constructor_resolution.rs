//! Constructor identity is the owning type and index, not a short name.
use std::process::Command;
use tauto_rustgen::{Bindings, Options, Sources, workspace};

fn compare(source: &str, tag: &str) {
    let expected = tauto::eval::run(source)
        .unwrap()
        .outputs
        .into_iter()
        .map(|(label, value)| format!("{label} = {value}\n"))
        .collect::<String>();
    let pkg = tauto_nir::compile(source).unwrap();
    let dir = std::env::temp_dir().join(format!("tauto-constructors-{tag}-{}", std::process::id()));
    let ws = workspace(
        "constructors",
        &pkg,
        &Sources {
            file: "main.taut",
            text: source,
        },
        &Bindings::default(),
        &Options::default(),
    );
    let binary = ws
        .build(
            "constructors",
            &dir.join("generated"),
            &dir.join("target"),
            false,
        )
        .unwrap();
    let out = Command::new(binary).output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8(out.stdout).unwrap(), expected);
    if tag != "syntax" {
        let js = tauto_jsgen::generate(&pkg).unwrap() + "\nawait run();\n";
        let path = dir.join("main.mjs");
        std::fs::write(&path, js).unwrap();
        let out = Command::new("node")
            .arg(path)
            .output()
            .expect("node is required for backend parity");
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(String::from_utf8(out.stdout).unwrap(), expected);
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn generated_syntax_reuses_empty_and_wildcard_safely() {
    let fixtures =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tauto/tests/syntax_fixtures");
    let grammar = std::fs::read_to_string(fixtures.join("shared_constructors.par")).unwrap();
    tauto::syntax::with_search_dirs(vec![fixtures], || {
        let tables = tauto::syntax::load_tables(&grammar).unwrap();
        let source = format!(
            r#"syntax!(reused, ```par
{}```) {}
{}"#,
            grammar,
            tauto::syntax::generated_clause("reused", &tables, false),
            r#"
enum MetadataCollision { SynSpan(i64), SynToken(Text), SynCtx(i64), SynDiag(Text) }
fn first(x: reused::First): u64 {
  match x { Wildcard(tok) => tok.span.id, Empty { span } => 10 + span.id }
}
fn second(x: reused::Second): u64 {
  match x { Wildcard(tok) => tok.span.id, Empty { span } => 20 + span.id }
}
fn count(text: Text): u64 {
  match reused::parse(text) {
    Ok(root) => first(root.first) + second(root.second)
    Err(diag) => 100 + diag.at
  }
}
perform show("both", count("*:*"))
perform show("neither", count(":"))
perform show("left", count("*:"))
perform show("right", count(":*"))
perform show("bad", count("*"))
"#
        );
        compare(&source, "syntax");
    });
}

#[test]
fn javascript_externs_keep_the_owner_discriminator() {
    let source = r#"
enum Left { Same(Text) }
enum Right { Same(Text) }
extern { fn echo(value: Left): Left
fn right(): Right }
let value: Left := Same("日本語")
let left := echo(value)
perform show("left", match left { Same(text) => text })
perform show("right", match right() { Same(text) => text })
"#;
    let pkg = tauto_nir::compile(source).unwrap();
    let declarations = tauto_jsgen::generate_declarations(&pkg).unwrap();
    assert!(declarations.contains("owner: \"Left\""));
    assert!(declarations.contains("owner: \"Right\""));
    let js = tauto_jsgen::generate(&pkg).unwrap();
    let dir = std::env::temp_dir().join(format!("tauto-constructor-js-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.mjs");
    std::fs::write(
        &path,
        format!(
            r#"{js}
await run(console.log, {{
  echo: value => JSON.parse(JSON.stringify(value)),
  right: () => ({{owner:'Right',tag:'Same',names:[null],fields:['host'],struct:false}})
}});
"#
        ),
    )
    .unwrap();
    let out = Command::new("node").arg(&path).output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8(out.stdout).unwrap(),
        "left = \"日本語\"\nright = \"host\"\n"
    );
    std::fs::write(&path, format!(r#"{js}
await run(console.log, {{echo:v=>v,right:()=>({{tag:'Same',names:[null],fields:['legacy'],struct:false}})}});
"#)).unwrap();
    let out = Command::new("node").arg(&path).output().unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("requires an owner type"));
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn expected_owner_checks_linear_fields() {
    for name in [
        "constructor-linear-owner-order-1",
        "constructor-linear-owner-order-2",
    ] {
        let source = case_inputs::source_static("backend-contracts.eure", name);
        let program = tauto::surface::parse_program_as_written(&source).unwrap();
        let types = tauto::types::check_program(&program);
        assert!(types.errors.is_empty(), "{:?}", types.errors);
        let errors = tauto::lin::check_lin_program(&program).unwrap();
        assert!(
            errors
                .iter()
                .any(|e| e.message.to_string().contains("drops a linear Token")),
            "{errors:?}"
        );
    }
}

#[test]
fn syntax_metadata_structs_keep_their_owner_in_macro_conversion() {
    let dir = std::env::temp_dir().join(format!("tauto-constructor-macro-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let library = dir.join("macro.taut");
    let entry = dir.join("main.taut");
    std::fs::write(
        &library,
        r#"
enum Other { SynSpan(i64), SynToken(Text), SynCtx(i64), SynDiag(Text) }
macro fn keep(e: SynExpr): SynExpr { e }
"#,
    )
    .unwrap();
    std::fs::write(&entry, r#"perform show("macro", keep!(42))"#).unwrap();
    let loaded = tauto::program::load_files(&[library, entry]).unwrap();
    let out =
        tauto::eval::run_program_with(&loaded.program, 1_000_000, Default::default()).unwrap();
    assert_eq!(out.outputs, vec![("macro".into(), "42".into())]);
    std::fs::remove_dir_all(dir).unwrap();
}

/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn source_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
            ("backend-contracts.eure", "constructor-linear-owner-order-1") => {
                r#"linear struct Token {}
enum Left { Same(Token) }
enum Right { Same(i64) }
fn bad(x: Left): i64 { match x { Same(_) => 0 } }"#
            }
            ("backend-contracts.eure", "constructor-linear-owner-order-2") => {
                r#"linear struct Token {}
enum Right { Same(i64) }
enum Left { Same(Token) }
fn bad(x: Left): i64 { match x { Same(_) => 0 } }"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn source(file: &str, name: &str) -> String {
        source_static(file, name).to_string()
    }
}
