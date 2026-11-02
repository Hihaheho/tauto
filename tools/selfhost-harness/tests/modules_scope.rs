//! Lexical bindings survive the Tauto module resolver and leave their scope.
use selfhost_harness::{root, run_tote_at};

#[test]
fn module_resolution_preserves_lexical_bindings() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("module-scopes");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Tauto.eure"),
        "package { name = \"module-scopes\" }",
    )
    .unwrap();
    let source = include_str!("data/modules_scope.taut").replace(
        "../../../../totes",
        &root()
            .join("totes")
            .canonicalize()
            .unwrap()
            .display()
            .to_string(),
    );
    std::fs::write(dir.join("src/main.taut"), source).unwrap();
    let out = run_tote_at(&dir, &[], 10_000_000);
    assert_eq!(out.error, None, "{out:?}");
    assert_eq!(out.stderr, "");
    assert_eq!(
        out.stdout,
        "argument = f\nlambda = f\npattern = f\nhandler = f\nblock = M.f/f\nafter = M.f\n"
    );
}
