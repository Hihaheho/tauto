//! Bundles are untrusted source inputs, never cached proof certificates.
#![cfg(unix)]
use serde_json::{Value, json};
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "tauto-trust-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::create_dir(path.join("src")).unwrap();
        fs::create_dir(path.join("lib")).unwrap();
        Self(path)
    }
    fn write(&self, path: &str, text: &str) {
        fs::write(self.0.join(path), text).unwrap();
    }
    fn command(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(args)
            .current_dir(&self.0)
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .env("TAUTO_CACHE", self.0.join("poison-cache"))
            .output()
            .unwrap()
    }
    fn bundle(&self) -> Value {
        let out = self.command(&["trust", "bundle", ".", "src/main.taut"]);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        serde_json::from_slice(&out.stdout).unwrap()
    }
    fn verify(&self, bundle: &Value) -> Output {
        self.write("bundle.json", &bundle.to_string());
        self.command(&["trust", "verify", "bundle.json"])
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn fixture() -> Fixture {
    let f = Fixture::new();
    f.write(
        "lib/proof.taut",
        r#"axiom assumed(P: Prop): P
theorem step(P: Prop): P { assumed(P) }
"#,
    );
    f.write(
        "src/main.taut",
        r#"import "../lib/proof.taut"
theorem final_step(P: Prop): P { step(P) }
theorem closed(): True { Trivial }
effect stop(): Never resume 0
extern { fn external(x: i64): i64 }
fn runtime(x: i64): i64 ! {stop} { x }
"#,
    );
    f
}
#[test]
fn offline_replay_inventory_and_determinism() {
    let f = fixture();
    let b = f.bundle();
    assert_eq!(b, f.bundle());
    let relocated = fixture();
    assert_eq!(b, relocated.bundle());
    assert_eq!(b["report"]["explicit_axioms"], json!(["assumed"]));
    assert_eq!(b["report"]["used_axioms"], json!(["assumed"]));
    assert_eq!(b["report"]["extern_functions"], json!(["external"]));
    assert_eq!(b["report"]["declared_effects"], json!(["stop"]));
    assert!(
        b["report"]["declarations"]
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d["name"] == "runtime" && d["status"] == "skipped")
    );
    assert!(
        b["report"]["declarations"]
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d["name"] == "final_step" && d["axioms"] == json!(["assumed"]))
    );
    fs::remove_dir_all(f.0.join("src")).unwrap();
    fs::remove_dir_all(f.0.join("lib")).unwrap();
    assert!(f.verify(&b).status.success());
    assert!(
        !f.0.join("poison-cache").exists(),
        "fresh checking must not access cache"
    );
    let out = f.command(&["trust", "verify", "bundle.json", "--axiom-free"]);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("receiver policy"));
}
#[test]
fn refuses_tampered_claims_sources_proofs_and_missing_dependencies() {
    let f = fixture();
    let b = f.bundle();
    let mut changed = b.clone();
    changed["report"]["used_axioms"] = json!([]);
    assert!(!f.verify(&changed).status.success());
    let mut changed = b.clone();
    changed["sources"]["src/main.taut"]["text"] = json!(r#"theorem bad(): False { Trivial }"#);
    assert!(!f.verify(&changed).status.success());
    let source = r#"theorem bad(): False { Trivial }"#;
    changed["sources"]["src/main.taut"]["sha256"] =
        json!(tauto_syntax::sha256_hex(source.as_bytes()));
    changed["sources"]
        .as_object_mut()
        .unwrap()
        .remove("lib/proof.taut");
    let out = f.verify(&changed);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("bad"));
    let mut changed = b.clone();
    changed["sources"]
        .as_object_mut()
        .unwrap()
        .remove("lib/proof.taut");
    assert!(!f.verify(&changed).status.success());
    let mut changed = b.clone();
    changed["proof_artifact"] = json!("checked");
    assert!(!f.verify(&changed).status.success());
    let mut changed = b.clone();
    changed["format"] = json!("future-v99");
    assert!(!f.verify(&changed).status.success());
}
#[test]
fn source_and_consistent_report_are_editable_not_authenticated() {
    let f = fixture();
    let first = f.bundle();
    f.write(
        "src/main.taut",
        r#"theorem replacement(): True { Trivial }"#,
    );
    let second = f.bundle();
    assert_ne!(first, second);
    assert!(f.verify(&second).status.success());
    f.write("bundle.json", &second.to_string());
    assert!(
        f.command(&["trust", "verify", "bundle.json", "--axiom-free"])
            .status
            .success()
    );
}
#[test]
fn refuses_paths_resources_cycles_and_unreachable_inputs() {
    let f = fixture();
    let b = f.bundle();
    for name in [
        "../escape.taut",
        "/absolute.taut",
        "C:/file.taut",
        "https://example.test/a",
        "a\\b",
        "a//b",
    ] {
        let mut changed = b.clone();
        changed["entry"] = json!(name);
        assert!(!f.verify(&changed).status.success(), "{name}");
    }
    for text in [
        r#"import "../../outside.taut""#,
        r#"import "https://example.test/x""#,
        r#"import "main.taut""#,
        r#"theorem bad(): True { include_text!("secret") }"#,
        r#"macro foo = foo_expand"#,
    ] {
        f.write("src/main.taut", text);
        assert!(
            !f.command(&["trust", "bundle", ".", "src/main.taut"])
                .status
                .success(),
            "{text}"
        );
    }
    let mut changed = b.clone();
    changed["sources"]["extra.taut"] = json!({"text":"", "sha256":tauto_syntax::sha256_hex(b"")});
    assert!(!f.verify(&changed).status.success());
}
#[cfg(unix)]
#[test]
fn export_refuses_source_symlinks() {
    let f = Fixture::new();
    f.write("lib/outside.taut", r#"theorem closed(): True { Trivial }"#);
    std::os::unix::fs::symlink("../lib/outside.taut", f.0.join("src/main.taut")).unwrap();
    assert!(
        !f.command(&["trust", "bundle", ".", "src/main.taut"])
            .status
            .success()
    );
}

#[test]
fn unused_axioms_require_receiver_permission_and_extra_fields_are_refused() {
    let f = Fixture::new();
    f.write(
        "src/main.taut",
        r#"axiom unused(): True
theorem closed(): True { Trivial }"#,
    );
    let b = f.bundle();
    assert_eq!(b["report"]["used_axioms"], json!([]));
    assert!(
        b["report"]["declarations"]
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d["name"] == "unused" && d["status"] == "assumed")
    );
    assert!(f.verify(&b).status.success());
    assert!(
        !f.command(&["trust", "verify", "bundle.json", "--axiom-free"])
            .status
            .success()
    );
    let mut changed = b.clone();
    changed["report"]["checker"]["source_revision"] = json!("claimed-revision");
    assert!(!f.verify(&changed).status.success());
    let mut changed = b.clone();
    changed["report"]["trusted"] = json!(true);
    assert!(!f.verify(&changed).status.success());
    f.write("bundle.json", &format!("{{\"format\":\"tauto-proof-source-bundle-v1\",\"entry\":\"src/main.taut\",\"sources\":{{\"src/main.taut\":{},\"src/main.taut\":{}}},\"report\":{}}}", b["sources"]["src/main.taut"], b["sources"]["src/main.taut"], b["report"]));
    let out = f.command(&["trust", "verify", "bundle.json"]);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("duplicate source"));
}

#[test]
fn bounded_documents_and_source_sizes_are_rejected() {
    let f = Fixture::new();
    f.write("bundle.json", &" ".repeat(8 * 1024 * 1024 + 1));
    assert!(
        !f.command(&["trust", "verify", "bundle.json"])
            .status
            .success()
    );
    f.write("src/main.taut", &" ".repeat(1024 * 1024 + 1));
    assert!(
        !f.command(&["trust", "bundle", ".", "src/main.taut"])
            .status
            .success()
    );
}

#[test]
fn verifier_never_falls_back_to_disk_for_imports_or_resources() {
    let f = fixture();
    let original = f.bundle();
    for source in [
        r#"import "../lib/proof.taut"
theorem borrowed(P: Prop): P { step(P) }"#,
        r#"import "../../escape.taut""#,
        r#"import "https://example.test/proof.taut""#,
        r#"import "main.taut""#,
        r#"theorem resource(): True { include_text!("../lib/proof.taut") }"#,
        r#"theorem tactic(): True { by unavailable!(0): True { } }"#,
    ] {
        let mut b = original.clone();
        b["sources"] = json!({"src/main.taut": {"text": source, "sha256": tauto_syntax::sha256_hex(source.as_bytes())}});
        // The first source's dependency exists on disk, but is absent in the bundle.
        assert!(!f.verify(&b).status.success(), "{source}");
    }
}

#[cfg(unix)]
#[test]
fn export_refuses_symlinked_directories_and_nonregular_sources() {
    let f = Fixture::new();
    f.write("lib/proof.taut", r#"theorem closed(): True { Trivial }"#);
    std::os::unix::fs::symlink("lib", f.0.join("linked")).unwrap();
    f.write("src/main.taut", r#"import "../linked/proof.taut""#);
    assert!(
        !f.command(&["trust", "bundle", ".", "src/main.taut"])
            .status
            .success()
    );
    f.write("src/main.taut", r#"import "../lib""#);
    assert!(
        !f.command(&["trust", "bundle", ".", "src/main.taut"])
            .status
            .success()
    );
}

#[test]
fn nested_assumptions_and_constraint_resources_are_refused() {
    let f = Fixture::new();
    for source in [
        r#"effect stop(): Never resume 0
fn runtime(x: i64): i64 ! {stop} { axiom hidden(): True
 x }"#,
        r#"effect stop(): Never resume 0
fn runtime(x: i64): i64 ! {stop} { extern { fn hidden(x: i64): i64 }
 x }"#,
        r#"extern { fn external(x: Nat): Nat where C(include_text!("secret")) }"#,
    ] {
        f.write("src/main.taut", source);
        let out = f.command(&["trust", "bundle", ".", "src/main.taut"]);
        assert!(!out.status.success(), "{source}");
        assert!(
            String::from_utf8_lossy(&out.stderr).contains("unsupported"),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

#[test]
fn unicode_imports_and_relative_aliases_share_one_source() {
    let f = Fixture::new();
    f.write(
        "lib/証明.taut",
        r#"theorem shared_proof(): True { Trivial }"#,
    );
    f.write(
        "src/main.taut",
        r#"import "../lib/証明.taut"
import "../lib/./証明.taut"
theorem closed(): True { shared_proof() }"#,
    );
    let b = f.bundle();
    assert_eq!(b["sources"].as_object().unwrap().len(), 2);
    assert!(f.verify(&b).status.success());
}

#[test]
fn certified_state_example_replays_offline_and_rejects_rehashed_invalid_transition() {
    let f = Fixture::new();
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let entry = "examples/certified-state/src/state.taut";
    let sources = [
        entry,
        "std/Base.taut",
        "std/Data.taut",
        "std/Nat.taut",
        "std/State.taut",
        "std/Std.taut",
    ];
    for relative in sources {
        let path = f.0.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::copy(root.join(relative), path).unwrap();
    }
    let out = f.command(&["trust", "bundle", ".", entry]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let b: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(b["sources"].as_object().unwrap().len(), sources.len());
    assert_eq!(b["report"]["explicit_axioms"], json!([]));
    assert_eq!(b["report"]["used_axioms"], json!([]));
    let declarations = b["report"]["declarations"].as_array().unwrap();
    let local: Vec<_> = declarations
        .iter()
        .filter(|d| d["source"] == entry)
        .collect();
    assert_eq!(local.len(), 18);
    assert!(
        local
            .iter()
            .all(|d| d["status"] == "checked" && d["axioms"] == json!([]))
    );
    assert!(local.iter().any(|d| d["name"] == "gate_advance_safe"));
    assert!(!declarations.iter().any(|d| d["name"] == "gate_commit"));
    // The runtime adapter and top-level execution are in a different real file.
    assert!(
        b["sources"]
            .get("examples/certified-state/src/main.taut")
            .is_none()
    );
    fs::remove_dir_all(f.0.join("examples")).unwrap();
    fs::remove_dir_all(f.0.join("std")).unwrap();
    f.write("bundle.json", &b.to_string());
    let out = f.command(&["trust", "verify", "bundle.json", "--axiom-free"]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(!f.0.join("poison-cache").exists());

    let mut changed = b.clone();
    let original = changed["sources"][entry]["text"].as_str().unwrap();
    changed["sources"][entry]["text"] = json!(format!("{original}\n// altered bytes\n"));
    assert!(!f.verify(&changed).status.success());

    let mut changed = b.clone();
    let text = changed["sources"][entry]["text"].as_str().unwrap();
    let from = "GateRevoke => GateClosed(gate_balance(state))";
    assert_eq!(text.matches(from).count(), 1);
    let text = text.replace(from, "GateRevoke => GateOpen(gate_balance(state))");
    changed["sources"][entry]["sha256"] = json!(tauto_syntax::sha256_hex(text.as_bytes()));
    changed["sources"][entry]["text"] = json!(text);
    let out = f.verify(&changed);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("gate_revoke_closes"));

    let mut changed = b.clone();
    changed["report"]["declarations"] = json!([]);
    assert!(!f.verify(&changed).status.success());
    let mut changed = b;
    changed["sources"]
        .as_object_mut()
        .unwrap()
        .remove("std/State.taut");
    assert!(!f.verify(&changed).status.success());
}

#[test]
fn std_imports_are_bundled_from_the_standard_library_that_comes_with_tauto() {
    let f = Fixture::new();
    f.write(
        "src/main.taut",
        "import std.Nat\ntheorem t(): (Nat.max(Zero, Zero) = Zero) { Refl }\n",
    );
    let bundle = f.bundle();
    let sources = bundle["sources"].as_object().unwrap();
    assert!(
        sources.contains_key("<std>/Nat.taut"),
        "{:?}",
        sources.keys()
    );
    let out = f.verify(&bundle);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
