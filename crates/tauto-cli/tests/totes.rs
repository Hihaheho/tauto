//! Totes (`docs/design/self-host.md`): `Tauto.eure`, dependencies between totes,
//! and the order the files are read in.

use std::fs;
use std::path::{Path, PathBuf};

use tauto::eval::{RunOptions, run_program_with};
use tauto::program::{Loaded, load_tote};

fn dir(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tauto-totes-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    d
}

/// `<root>/<name>/Tauto.eure` and the files of its `src/`.
fn tote(root: &Path, name: &str, dependencies: &[&str], files: &[(&str, &str)]) -> PathBuf {
    let d = root.join(name);
    fs::create_dir_all(d.join("src")).unwrap();
    let mut manifest = format!("package {{\n  name = \"{name}\"\n  version = \"0.1.0\"\n}}\n");
    if !dependencies.is_empty() {
        manifest.push_str("\ndependencies {\n");
        for dependency in dependencies {
            manifest.push_str(&format!(
                "  {dependency} {{ path = \"../{dependency}\" }}\n"
            ));
        }
        manifest.push_str("}\n");
    }
    fs::write(d.join("Tauto.eure"), manifest).unwrap();
    for (file, text) in files {
        fs::write(d.join("src").join(file), text).unwrap();
    }
    d
}

fn run(loaded: &Loaded) -> Result<Vec<String>, String> {
    let outcome = run_program_with(&loaded.program, 1_000_000, RunOptions::default())
        .map_err(|e| e.to_string())?;
    Ok(outcome
        .outputs
        .iter()
        .map(|(n, v)| format!("{n} = {v}"))
        .collect())
}

fn names(loaded: &Loaded) -> Vec<String> {
    loaded
        .files
        .iter()
        .map(|f| f.path.file_name().unwrap().to_string_lossy().into_owned())
        .collect()
}

#[test]
fn a_tote_runs_its_main() {
    let root = dir("main");
    let a = tote(&root, "a", &[], &[("main.taut", r#"perform show("x", 1)"#)]);
    assert_eq!(run(&load_tote(&a).unwrap()).unwrap(), ["x = 1"]);
}

#[test]
fn a_tote_uses_its_dependency() {
    let root = dir("uses");
    tote(
        &root,
        "a",
        &[],
        &[("a.taut", r#"pub fn a_one(): i64 { 1 }"#)],
    );
    let b = tote(
        &root,
        "b",
        &["a"],
        &[(
            "main.taut",
            r#"import a::a
perform show("x", a_one() + 1)"#,
        )],
    );
    assert_eq!(run(&load_tote(&b).unwrap()).unwrap(), ["x = 2"]);
}

#[test]
fn a_dependency_keeps_the_prelude_constructor_its_dependent_declares_too() {
    // The tote declares a constructor `Some` of its own: the dependency's
    // `Some`, checked and run, is still the prelude's, and the tote's own
    // `Some` is its own.
    let root = dir("prelude-ctor");
    tote(
        &root,
        "lib",
        &[],
        &[(
            "lib.taut",
            "pub fn two(): Nat { match Some(2) { Some(n) => n, None => 0 } }\n\n\
             pub fn three(): Nat {\n  let o := Some(3)\n  perform show(\"lib\", 0)\n  match o { Some(n) => n, None => 0 }\n}\n",
        )],
    );
    let app = tote(
        &root,
        "app",
        &["lib"],
        &[(
            "main.taut",
            "import lib::lib\n\nenum Piece { Whole(Nat), Some }\n\n\
             fn tag(p: Piece): Nat { match p { Whole(n) => n, Some => 7 } }\n\n\
             perform show(\"two\", two())\n\
             perform show(\"three\", three())\n\
             perform show(\"tag\", tag(Some))\n",
        )],
    );
    assert_eq!(
        run(&load_tote(&app).unwrap()).unwrap(),
        ["two = 2", "lib = 0", "three = 3", "tag = 7"]
    );
}

#[test]
fn a_dependencys_main_is_not_read() {
    let root = dir("dependency-main");
    tote(
        &root,
        "a",
        &[],
        &[
            ("a.taut", r#"pub fn a_one(): i64 { 1 }"#),
            ("main.taut", r#"perform show("a", 0)"#),
        ],
    );
    let b = tote(
        &root,
        "b",
        &["a"],
        &[(
            "main.taut",
            r#"import a::a
perform show("b", a_one())"#,
        )],
    );
    let loaded = load_tote(&b).unwrap();
    assert_eq!(run(&loaded).unwrap(), ["b = 1"]);
    assert_eq!(names(&loaded), ["a.taut", "main.taut"]);
}

#[test]
fn a_tote_that_is_not_listed_is_not_seen() {
    tauto_messages::install();
    let root = dir("not-listed");
    tote(
        &root,
        "a",
        &[],
        &[("a.taut", r#"pub fn a_one(): i64 { 1 }"#)],
    );
    let c = tote(
        &root,
        "c",
        &[],
        &[(
            "main.taut",
            r#"import a::a
perform show("x", a_one())"#,
        )],
    );
    let err = load_tote(&c).err().unwrap();
    assert!(
        err.contains("a is not a dependency of this file's tote"),
        "{err}"
    );
}

#[test]
fn totes_that_depend_on_each_other_are_an_error() {
    tauto_messages::install();
    let root = dir("cycle");
    tote(&root, "a", &["b"], &[]);
    tote(&root, "b", &["a"], &[]);
    let err = load_tote(&root.join("a")).err().unwrap();
    assert_eq!(err, "the totes depend on each other: a -> b -> a");
}

#[test]
fn the_name_is_the_directorys() {
    let root = dir("name");
    let x = tote(&root, "x", &[], &[]);
    fs::write(
        x.join("Tauto.eure"),
        "package {\n  name = \"y\"\n  version = \"0.1.0\"\n}\n",
    )
    .unwrap();
    let err = load_tote(&x).err().unwrap();
    assert!(err.contains("is named y"), "{err}");
    assert!(err.starts_with("the tote in "), "{err}");
    // The message says what to change.
    assert!(err.contains("rename the directory to y"), "{err}");
    assert!(err.contains("`name = \"x\"`"), "{err}");
}

#[test]
fn an_unknown_key_is_an_error() {
    tauto_messages::install();
    let root = dir("unknown");
    let a = tote(&root, "a", &[], &[]);
    fs::write(
        a.join("Tauto.eure"),
        "package {\n  name = \"a\"\n  version = \"0.1.0\"\n  foo = 1\n}\n",
    )
    .unwrap();
    assert_eq!(
        load_tote(&a).err().unwrap(),
        "unknown key foo in Tauto.eure"
    );
}

#[test]
fn the_rust_section_is_ignored() {
    let root = dir("rust");
    let a = tote(&root, "a", &[], &[("main.taut", r#"perform show("x", 1)"#)]);
    let mut manifest = fs::read_to_string(a.join("Tauto.eure")).unwrap();
    manifest.push_str("\nrust {\n  bridge = \"bridge\"\n}\n");
    fs::write(a.join("Tauto.eure"), manifest).unwrap();
    assert_eq!(run(&load_tote(&a).unwrap()).unwrap(), ["x = 1"]);
}

#[test]
fn a_tote_imports_each_source_once() {
    let root = dir("import");
    let a = tote(
        &root,
        "a",
        &[],
        &[
            ("a.taut", r#"pub fn a_one(): i64 { 1 }"#),
            ("main.taut", r#"import "a.taut""#),
        ],
    );
    let loaded = load_tote(&a).unwrap();
    assert_eq!(names(&loaded), ["a.taut", "main.taut"]);
}

#[test]
fn files_are_read_in_path_order_with_main_last() {
    let root = dir("order");
    let a = tote(
        &root,
        "a",
        &[],
        &[
            ("b.taut", r#"pub fn b_one(): i64 { 1 }"#),
            ("a.taut", r#"pub fn a_one(): i64 { 1 }"#),
            (
                "main.taut",
                r#"import "a.taut"
import "b.taut"
perform show("x", a_one() + b_one())"#,
            ),
        ],
    );
    let loaded = load_tote(&a).unwrap();
    assert_eq!(names(&loaded), ["a.taut", "b.taut", "main.taut"]);
}

#[test]
fn dependencies_are_visited_in_name_order() {
    let root = dir("deps-order");
    tote(
        &root,
        "z",
        &[],
        &[("z.taut", r#"pub fn z_one(): i64 { 1 }"#)],
    );
    tote(
        &root,
        "m",
        &[],
        &[("m.taut", r#"pub fn m_one(): i64 { 1 }"#)],
    );
    let a = tote(
        &root,
        "a",
        &["z", "m"],
        &[("main.taut", r#"perform show("x", 1)"#)],
    );
    assert_eq!(
        names(&load_tote(&a).unwrap()),
        ["m.taut", "z.taut", "main.taut"]
    );
}

#[test]
fn the_cli_runs_a_tote() {
    let root = dir("cli");
    let a = tote(&root, "a", &[], &[("main.taut", r#"perform show("x", 1)"#)]);
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(["run", "--tote", a.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(out.status.success());
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "x = 1\n");
    let empty = tote(
        &root,
        "empty",
        &[],
        &[("lib.taut", r#"pub fn e(): i64 { 1 }"#)],
    );
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(["run", "--tote", empty.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(
        String::from_utf8(out.stderr)
            .unwrap()
            .contains("the tote empty has no src/main.taut")
    );
}

#[test]
fn implementation_proof_and_effects_share_one_module() {
    let root = dir("mixed");
    let a = tote(
        &root,
        "a",
        &[],
        &[(
            "main.taut",
            r#"
fn identity(n: Nat): Nat { n }
theorem identity_zero(): identity(Zero) = Zero { Refl }
fn print_it(n: Nat): Unit { perform show("n", n) }
print_it(identity(2))
"#,
        )],
    );
    assert_eq!(run(&load_tote(&a).unwrap()).unwrap(), ["n = 2"]);
}

#[test]
fn failed_and_incomplete_proofs_cannot_become_executable_code() {
    for (name, proof) in [
        ("false", r#"theorem bad(): Zero = Succ(Zero) { Refl }"#),
        ("hole", r#"theorem bad(): Zero = Zero { ?unfinished }"#),
        ("axiom", r#"axiom bad(): Zero = Zero"#),
        (
            "runtime",
            r#"pub fn external_value(): u64 { 0 }
theorem bad(): external_value() = Zero { Refl }"#,
        ),
    ] {
        let root = dir(name);
        let text = format!(
            r#"{}
perform show("ok", 1)
"#,
            proof
        );
        let a = tote(&root, "a", &[], &[("main.taut", &text)]);
        assert!(load_tote(&a).is_err(), "accepted {name}");
    }
}

#[test]
fn native_extension_is_rejected_in_tote_sources() {
    let root = dir("extension");
    let a = tote(&root, "a", &[], &[("main.nib", r#"perform show("x", 1)"#)]);
    assert!(load_tote(&a).err().unwrap().contains("must use .taut"));
}

#[test]
fn a_bound_name_does_not_turn_a_proof_function_into_runtime_code() {
    let root = dir("bound-name");
    let a = tote(
        &root,
        "a",
        &[],
        &[(
            "main.taut",
            r#"
fn Predicate(n: Nat): Prop { ((map: Nat) => map = map)(n) }
theorem good(): Predicate(Zero) { Refl }
perform show("ok", 1)
"#,
        )],
    );
    assert_eq!(run(&load_tote(&a).unwrap()).unwrap(), ["ok = 1"]);
}

#[test]
fn native_text_functions_need_no_proof_library_import() {
    let root = dir("native-text");
    let a = tote(
        &root,
        "a",
        &[],
        &[(
            "main.taut",
            r#"
fn greeting(): Text { "hello" }
perform show("text", greeting())
"#,
        )],
    );
    assert_eq!(run(&load_tote(&a).unwrap()).unwrap(), ["text = \"hello\""]);
}

#[test]
fn native_extension_cannot_be_imported_into_a_tote() {
    let root = dir("import-extension");
    fs::write(root.join("legacy.nib"), r#"pub fn value(): u64 { 1 }"#).unwrap();
    let a = tote(
        &root,
        "a",
        &[],
        &[(
            "main.taut",
            r#"import "../../legacy.nib"
perform show("x", value())"#,
        )],
    );
    assert!(load_tote(&a).err().unwrap().contains("must use .taut"));
}

#[test]
fn both_source_extensions_run_as_tote_entries() {
    for extension in ["taut", "tauto"] {
        let root = dir(&format!("entry-{extension}"));
        let source = format!("main.{extension}");
        let a = tote(&root, "a", &[], &[(&source, r#"perform show("x", 7)"#)]);
        // The default `src` accepts both extensions.
        for manifest in ["package { name = \"a\" }"] {
            fs::write(a.join("Tauto.eure"), manifest).unwrap();
            assert_eq!(run(&load_tote(&a).unwrap()).unwrap(), ["x = 7"]);
            let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
                // The messages below are the English ones, whatever the language here.
                .env("TAUTO_LANG", "en")
                .args(["run", "--tote"])
                .arg(&a)
                .output()
                .unwrap();
            assert!(
                out.status.success(),
                "{}",
                String::from_utf8_lossy(&out.stderr)
            );
            assert_eq!(String::from_utf8(out.stdout).unwrap(), "x = 7\n");
        }
    }
}

#[test]
fn mixed_source_extensions_preserve_imports_and_skip_dependency_entries() {
    let root = dir("mixed-extensions");
    tote(
        &root,
        "a",
        &[],
        &[
            (
                "proof.tauto",
                r#"theorem proof_identity(A: Prop, a: A): A { a }"#,
            ),
            (
                "value.taut",
                r#"import "proof.tauto"
pub fn value(): i64 { 9 }"#,
            ),
            ("main.tauto", r#"perform show("dependency", 0)"#),
        ],
    );
    let app = tote(
        &root,
        "app",
        &["a"],
        &[
            (
                "main.taut",
                r#"import "helper.tauto"
perform show("value", helper())"#,
            ),
            (
                "helper.tauto",
                r#"import a::value

pub fn helper(): i64 { value() }"#,
            ),
        ],
    );
    let loaded = load_tote(&app).unwrap();
    assert_eq!(run(&loaded).unwrap(), ["value = 9"]);
    let files = tauto::program::package_source_files(&app).unwrap();
    assert_eq!(files.len(), 2);
    let bundle = tauto::program::tote_inputs(&app).unwrap();
    assert!(bundle.iter().any(|p| p.ends_with("proof.tauto")));
    assert!(
        !loaded
            .files
            .iter()
            .any(|f| f.path.ends_with("a/src/main.tauto"))
    );
}

/// An extern's host access is in no effect row, so `--allow-*` cannot see
/// it: a dependency that declares one is refused unless the project trusts it.
#[test]
fn a_dependencys_extern_needs_the_projects_trust() {
    tauto_messages::install();
    let root = dir("trust-extern");
    tote(
        &root,
        "a",
        &[],
        &[(
            "a.taut",
            "extern {\n  fn leak(url: Text): Text\n}\n\npub fn one(): u64 { 1 }\n",
        )],
    );
    let b = tote(
        &root,
        "b",
        &["a"],
        &[("main.taut", "import a::a\n\nperform show(\"x\", one())\n")],
    );
    let refused = load_tote(&b).err().expect("an untrusted extern is refused");
    assert!(
        refused.contains("dependency a declares extern functions"),
        "{refused}"
    );
    assert!(refused.contains("extern leak"), "{refused}");
    assert!(refused.contains("trust { extern = [\"a\"] }"), "{refused}");

    let manifest = b.join("Tauto.eure");
    let mut text = fs::read_to_string(&manifest).unwrap();
    text.push_str("\ntrust {\n  extern = [\"a\"]\n}\n");
    fs::write(&manifest, text).unwrap();
    assert_eq!(run(&load_tote(&b).unwrap()).unwrap(), ["x = 1"]);
}

/// The project's own externs are its author's, and need no trust.
#[test]
fn the_projects_own_extern_needs_no_trust() {
    let root = dir("own-extern");
    let a = tote(
        &root,
        "a",
        &[],
        &[(
            "main.taut",
            "extern {\n  fn leak(url: Text): Text\n}\n\nperform show(\"x\", 1)\n",
        )],
    );
    assert_eq!(run(&load_tote(&a).unwrap()).unwrap(), ["x = 1"]);
}

/// A tote's externs are its own: another tote calls the functions it writes
/// around them, never the extern itself, even when the project trusts it.
#[test]
fn an_extern_is_called_only_inside_its_tote() {
    tauto_messages::install();
    let root = dir("sealed-extern");
    tote(
        &root,
        "a",
        &[],
        &[(
            "a.taut",
            "extern {\n  fn leak(url: Text): Text\n}\n\npub fn fetch(url: Text): Text { leak(url) }\n\npub fn one(): u64 { 1 }\n",
        )],
    );
    let trust = "\ntrust {\n  extern = [\"a\"]\n}\n";
    let b = tote(
        &root,
        "b",
        &["a"],
        &[(
            "main.taut",
            "import a::a\n\nfn get(): Text { fetch(\"x\") }\n\nperform show(\"x\", one())\n",
        )],
    );
    let manifest = b.join("Tauto.eure");
    let text = fs::read_to_string(&manifest).unwrap() + trust;
    fs::write(&manifest, &text).unwrap();
    let loaded = load_tote(&b).unwrap();
    assert!(
        loaded.program.errors.is_empty(),
        "{:?}",
        loaded.program.errors
    );
    assert_eq!(run(&loaded).unwrap(), ["x = 1"]);

    fs::write(
        b.join("src/main.taut"),
        "import a::a\n\nfn get(): Text { leak(\"x\") }\n\nperform show(\"x\", one())\n",
    )
    .unwrap();
    let errors = match load_tote(&b) {
        Ok(loaded) => format!("{:?}", loaded.program.errors),
        Err(e) => e,
    };
    assert!(
        errors.contains("`leak` is an extern of the tote a, which only a may call"),
        "{errors}"
    );

    // A local of the same name is not the extern.
    fs::write(
        b.join("src/main.taut"),
        "import a::a\n\nfn get(leak: u64): u64 { leak }\n\nperform show(\"x\", one())\n",
    )
    .unwrap();
    let loaded = load_tote(&b).unwrap();
    assert!(
        loaded.program.errors.is_empty(),
        "{:?}",
        loaded.program.errors
    );
}
