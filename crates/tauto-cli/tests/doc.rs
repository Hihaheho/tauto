use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

struct Temp(PathBuf);
impl Temp {
    fn new() -> Self {
        static ID: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "tauto-doc-{}-{}",
            std::process::id(),
            ID.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, path: &str, text: &str) -> PathBuf {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, text).unwrap();
        path
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn doc(input: &Path, output: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        .arg("doc")
        .arg(input)
        .arg("-o")
        .arg(output)
        .env("TAUTO_CACHE", "off")
        .output()
        .unwrap()
}
fn assert_code(out: &Output, code: i32) {
    assert_eq!(
        out.status.code(),
        Some(code),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn local_docs_show_proofs_axioms_runtime_and_escaped_sources() {
    let tmp = Temp::new();
    let source = tmp.write(
        "api.taut",
        r#"// <script>alert("x")</script> 日本語 & 'text'
axiom assumed(): Zero = Zero
theorem proved(): Zero = Zero { Refl(Nat, Zero) }
theorem dependent(): Zero = Zero { assumed() }
fn twice(n: i64): i64 { n + n }
"#,
    );
    let output = tmp.0.join("docs");
    assert_code(&doc(&source, &output), 0);
    let html = fs::read_to_string(output.join("index.html")).unwrap();
    assert!(html.contains("axiom (assumption, not a proof)"), "{html}");
    assert!(html.contains("Axiom dependencies: assumed"), "{html}");
    assert!(html.contains("fn twice(n: i64): i64"), "{html}");
    assert!(html.contains("not proof-checked"));
    assert!(html.contains("not type-checked or proof-checked"));
    assert!(
        html.contains(
            "&lt;script&gt;alert(&quot;x&quot;)&lt;/script&gt; 日本語 &amp; &#39;text&#39;"
        )
    );
    assert!(!html.contains("<script>"));
    assert!(html.contains("href=\"#source-0-L"));
    assert!(html.contains("id=\"source-0-L1\""));
    let second = tmp.0.join("again");
    assert_code(&doc(&source, &second), 0);
    assert_eq!(html, fs::read_to_string(second.join("index.html")).unwrap());
    let before = fs::read(output.join("index.html")).unwrap();
    assert_code(&doc(&source, &output), 1);
    assert_eq!(before, fs::read(output.join("index.html")).unwrap());
}

#[test]
fn incomplete_and_failed_proofs_are_documented_but_not_successful() {
    let tmp = Temp::new();
    for (name, proof, code, status) in [
        ("hole", r#"?todo"#, 3, "incomplete (not accepted)"),
        ("bad", r#"Zero"#, 1, "failed (not accepted)"),
    ] {
        let source = tmp.write(
            &format!("{name}.taut"),
            &format!(
                r#"theorem unfinished(): Zero = Zero {{ {} }}
"#,
                proof
            ),
        );
        let output = tmp.0.join(name);
        assert_code(&doc(&source, &output), code);
        let html = fs::read_to_string(output.join("index.html")).unwrap();
        assert!(html.contains(status), "{html}");
    }
}

#[test]
fn package_discovery_obeys_sources_and_never_executes_runtime() {
    let tmp = Temp::new();
    tmp.write(
        "Tauto.eure",
        "package { name = \"doc-fixture\"\nversion = \"0.1.0\"\n}\n",
    );
    tmp.write(
        "src/main.taut",
        r#"fn twice(n: i64): i64 { n + n }
perform show("must-not-run", 1)
"#,
    );
    tmp.write("outside.taut", "not valid source !\n");
    let output = tmp.0.join("docs");
    let out = doc(&tmp.0, &output);
    assert_code(&out, 0);
    assert!(!String::from_utf8_lossy(&out.stdout).contains("must-not-run"));
    let html = fs::read_to_string(output.join("index.html")).unwrap();
    assert!(html.contains("twice"));
    assert!(!html.contains("outside.taut"));
}

#[test]
fn imported_parent_paths_and_html_filenames_only_become_escaped_labels() {
    let tmp = Temp::new();
    tmp.write(
        "shared<&>.taut",
        r#"pub theorem r#shared(): Zero = Zero { Refl(Nat, Zero) }
"#,
    );
    let source = tmp.write(
        "src/main.taut",
        r#"import "../shared<&>.taut"
theorem local(): Zero = Zero { r#shared() }
"#,
    );
    let output = tmp.0.join("docs");
    assert_code(&doc(&source, &output), 0);
    let html = fs::read_to_string(output.join("index.html")).unwrap();
    assert!(html.contains("shared&lt;&amp;&gt;.taut"));
    assert!(!html.contains("href=\"../"));
    assert_eq!(fs::read_dir(&output).unwrap().count(), 1);
    assert!(tmp.0.join("shared<&>.taut").exists());
}

#[test]
fn help_usage_and_existing_empty_output_are_safe() {
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["doc", "--help"])
        .output()
        .unwrap();
    assert_code(&out, 0);
    for args in [
        vec!["doc"],
        vec!["doc", "file.taut", "--bad"],
        vec!["doc", "file.taut", "-o"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(args)
            .output()
            .unwrap();
        assert_code(&out, 2);
    }
    let tmp = Temp::new();
    let source = tmp.write(
        "main.taut",
        r#"fn identity(n: i64): i64 { n }
"#,
    );
    let output = tmp.0.join("docs");
    fs::create_dir(&output).unwrap();
    assert_code(&doc(&source, &output), 1);
    assert_eq!(fs::read_dir(&output).unwrap().count(), 0);
}

#[cfg(unix)]
#[test]
fn output_symlinks_are_not_followed() {
    let tmp = Temp::new();
    let source = tmp.write(
        "main.taut",
        r#"fn identity(n: i64): i64 { n }
"#,
    );
    let output = tmp.0.join("docs");
    let missing = tmp.0.join("missing");
    std::os::unix::fs::symlink(&missing, &output).unwrap();
    assert_code(&doc(&source, &output), 1);
    assert!(!missing.exists());
}

#[test]
fn class_law_signatures_are_obligations_not_claimed_proofs() {
    let tmp = Temp::new();
    let source = tmp.write(
        "laws.taut",
        r#"class Identity(A: Type) {
  fn identity(x: A): A
  law same<x: A>(): Identity::identity(x) = x
}
"#,
    );
    let output = tmp.0.join("docs");
    assert_code(&doc(&source, &output), 0);
    let html = fs::read_to_string(output.join("index.html")).unwrap();
    assert!(html.contains("law (obligation) same"), "{html}");
    assert!(html.contains("does not supply their proofs"));
}

#[test]
fn written_instance_methods_and_module_names_survive_runtime_lowering() {
    let tmp = Temp::new();
    let source = tmp.write(
        "api.taut",
        r#"class Twice(A: Type) { fn twice(x: A): A }
instance Twice(i64) { fn twice(x: i64): i64 { x + x } }
module Calc { fn identity(n: i64): i64 { n } }
"#,
    );
    let output = tmp.0.join("docs");
    assert_code(&doc(&source, &output), 0);
    let html = fs::read_to_string(output.join("index.html")).unwrap();
    assert!(html.contains("instance Twice(i64)"), "{html}");
    assert!(html.contains("fn twice(x: i64): i64"));
    assert!(html.contains("fn Calc::identity(n: i64): i64"));
    assert_eq!(html.matches("<code>Calc::identity</code>").count(), 1);
}

#[test]
fn inductive_constructor_generics_are_not_rendered_as_explicit_arguments() {
    let tmp = Temp::new();
    let source = tmp.write(
        "generic.taut",
        r#"inductive Witness: Type1 { Mk<A>(value: A): Witness }
"#,
    );
    let output = tmp.0.join("docs");
    let out = doc(&source, &output);
    assert_code(&out, 0);
    let html = fs::read_to_string(output.join("index.html")).unwrap();
    assert!(
        html.contains("Mk&lt;A: Type&gt;(value: A): Witness"),
        "{html}"
    );
}
