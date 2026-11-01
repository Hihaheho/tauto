//! Compiled totes preserve file staging and source locations.
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
fn macros_source() -> &'static str {
    r#"pub macro fn passthrough(input: SynExpr): SynExpr { input }"#
}

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "tauto-macro-build-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).unwrap();
        Self(root)
    }
    fn write(&self, path: &str, text: &str) {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    fn manifest(&self, path: &str, name: &str, extra: &str) {
        self.write(
            path,
            &format!("package {{ name = \"{name}\" sources = [\"main.taut\"] }}\n{extra}\n"),
        );
    }
    fn build(&self, dir: &Path, backend: &str) -> Output {
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(["build", "--emit", backend, "-o"])
            .arg(self.0.join(format!("out-{backend}")))
            .arg(dir)
            .output()
            .unwrap()
    }
    fn succeeds(&self, dir: &Path) {
        for backend in ["javascript", "rust"] {
            let result = self.build(dir, backend);
            assert!(
                result.status.success(),
                "{backend}: {}",
                String::from_utf8_lossy(&result.stderr)
            );
        }
        let result = Command::new("node")
            .arg(self.0.join("out-javascript/main.mjs"))
            .output()
            .expect("node is required for JavaScript backend tests");
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8(result.stdout).unwrap(), "value = 2\n");
        let (_, generated, _) = tauto_build::generate(&dir.join("Tauto.eure"), None).unwrap();
        assert!(generated.contains("pub mod generated"));
    }
    fn rejects(&self, dir: &Path, expected: &str) {
        for backend in ["javascript", "rust"] {
            let result = self.build(dir, backend);
            assert!(
                !result.status.success(),
                "{backend} unexpectedly accepted the source"
            );
            let stderr = String::from_utf8_lossy(&result.stderr);
            assert!(stderr.contains(expected), "{backend}: {stderr}");
        }
        let error = tauto_build::generate(&dir.join("Tauto.eure"), None).unwrap_err();
        assert!(error.contains(expected), "{error}");
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn imported_macro_builds_in_both_backends_and_executes() {
    let macros = macros_source();
    for ending in ["", "\n"] {
        let f = Fixture::new();
        f.manifest("Tauto.eure", "macro-example", "");
        f.write("z_macros.taut", &format!("{macros}{ending}"));
        f.write(
            "main.taut",
            r#"import "z_macros.taut"
perform show("value", passthrough!(2))
"#,
        );
        let reference = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("run")
            .arg(f.0.join("main.taut"))
            .output()
            .unwrap();
        assert!(
            reference.status.success(),
            "{}",
            String::from_utf8_lossy(&reference.stderr)
        );
        assert_eq!(String::from_utf8(reference.stdout).unwrap(), "value = 2\n");
        f.succeeds(&f.0);
    }
}

#[test]
fn dependency_macros_and_transitive_imports_keep_their_order() {
    let f = Fixture::new();
    f.write(
        "support/Tauto.eure",
        "package { name = \"support\" sources = [\"z_macros.taut\"] }\n",
    );
    f.write("support/z_macros.taut", macros_source());
    f.manifest(
        "app/Tauto.eure",
        "consumer",
        "dependencies { support { path = \"../support\" } }",
    );
    f.write(
        "app/helper.taut",
        r#"fn answer(): i64 { passthrough!(2) }
"#,
    );
    f.write(
        "app/main.taut",
        r#"import "helper.taut"
perform show("value", answer())
"#,
    );
    f.succeeds(&f.0.join("app"));
}

#[test]
fn same_file_macros_import_cycles_and_expansion_errors_are_rejected() {
    let macros = macros_source();
    let f = Fixture::new();
    f.manifest("Tauto.eure", "invalid-example", "");
    f.write(
        "main.taut",
        &format!(
            r#"{}
perform show("value", passthrough!(2))
"#,
            macros
        ),
    );
    f.rejects(&f.0, "macro.same_file");
    f.write(
        "main.taut",
        r#"import "other.taut"
"#,
    );
    f.write(
        "other.taut",
        r#"import "main.taut"
"#,
    );
    f.rejects(&f.0, "cycle");
    f.write(
        "main.taut",
        r#"import "z_macros.taut"
perform show("value", unknown_macro!(2))
"#,
    );
    f.write("z_macros.taut", macros_source());
    f.rejects(&f.0, "unknown_macro");
}

#[test]
fn macro_generated_errors_point_to_the_calling_file() {
    let macros = macros_source();
    let f = Fixture::new();
    f.manifest("Tauto.eure", "locations", "");
    f.write("z_macros.taut", &format!("{macros}\n"));
    f.write(
        "main.taut",
        r#"import "z_macros.taut"

perform show("value", passthrough!(missing_value))
"#,
    );
    f.rejects(&f.0, "main.taut:3:");
}

#[test]
fn file_offsets_and_generated_rust_locations_follow_macro_origins() {
    let macros = macros_source();
    let f = Fixture::new();
    f.manifest("Tauto.eure", "locations", "");
    f.write("z_macros.taut", &format!("{macros}\n"));
    f.write(
        "main.taut",
        r#"import "z_macros.taut"
perform show("value", passthrough!(1 + 1))
"#,
    );
    let loaded = tauto_build::tote_program(&f.0).unwrap();
    let text = loaded.source_text();
    for file in &loaded.files {
        assert_eq!(
            &text[file.base as usize..file.base as usize + file.text.len()],
            file.text
        );
        assert_eq!(loaded.locate(file.base).unwrap().0, file.path);
        assert_eq!(
            loaded.locate(file.base + file.text.len() as u32).unwrap().0,
            file.path
        );
    }
    assert!(loaded.locate(tauto::surface::PRELUDE_BASE).is_none());
    let package = tauto_nir::compile_loaded_with_observer(&loaded, false, false, |_| {}).unwrap();
    let mut generated = 0;
    for function in &package.fns {
        function.body.walk(&mut |expr| {
            if (1 << 30..tauto::surface::PRELUDE_BASE).contains(&expr.span.start) {
                let (file, line, _) = package
                    .sources
                    .as_ref()
                    .unwrap()
                    .locate(expr.span.start)
                    .unwrap();
                assert!(file.ends_with("main.taut"), "{}", file.display());
                assert_eq!(line, 2);
                generated += 1;
            }
        });
    }
    assert!(generated > 0);
    let result = f.build(&f.0, "rust");
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let rust = fs::read_to_string(f.0.join("out-rust/src/lib.rs")).unwrap();
    assert!(
        rust.contains(&format!(
            "file: {:?}",
            f.0.join("main.taut").display().to_string()
        )),
        "{rust}"
    );
}

#[test]
fn imported_macro_keeps_relative_include_text_inputs() {
    let f = Fixture::new();
    f.manifest("Tauto.eure", "included-input", "");
    f.write("helpers/macros.taut", macros_source());
    f.write("assets/value.txt", "ab");
    f.write(
        "main.taut",
        r#"import "helpers/macros.taut"
perform show("value", passthrough!(Text::len(include_text!("assets/value.txt"))))
"#,
    );
    f.succeeds(&f.0);
}
