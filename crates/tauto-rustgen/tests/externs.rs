//! The error for an `extern` whose Rust does not fit names both places.

use std::path::Path;

use tauto_rustgen::{Bindings, Options, Sources, workspace};

#[test]
fn a_mismatch_points_at_the_declaration_and_the_binding() {
    tauto_messages::install();
    let source = r#"extern {
  fn len_of(n: i64): i64
}
perform show("n", len_of(3))
"#;
    let manifest = tauto::manifest::parse(
        "rust {\n  extern {\n    len_of = \"str::len\"\n  }\n}\n",
        Path::new("Tauto.eure"),
    )
    .unwrap();
    let package = tauto_nir::compile(source).unwrap();
    let bindings = Bindings::resolve(&package, Some(&manifest), None).unwrap();
    let ws = workspace(
        "mismatch",
        &package,
        &Sources {
            file: "main.taut",
            text: source,
        },
        &bindings,
        &Options::default(),
    );
    let scratch = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"));
    let dir = scratch.join("externs-mismatch");
    let target = scratch.join("externs-target");
    let err = ws.build("mismatch", &dir, &target, false).unwrap_err();
    assert!(
        err.starts_with("error: the Rust of extern len_of does not fit its declaration"),
        "{err}"
    );
    assert!(err.contains("declared at main.taut:2:"), "{err}");
    assert!(err.contains("bound at Tauto.eure:3 (str::len)"), "{err}");
}
