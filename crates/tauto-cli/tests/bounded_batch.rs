//! The bundle certifies the pure batch functions, not their runtime caller.
#![cfg(unix)]
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    sync::atomic::{AtomicUsize, Ordering},
    thread,
    time::{Duration, Instant},
};

const ENTRY: &str = "examples/bounded-batch/src/batch.taut";
const MAIN: &str = "examples/bounded-batch/src/main.taut";
static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "tauto-bounded-batch-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, relative: &str, text: &str) {
        let path = self.0.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    fn verify(&self, bundle: &Value) -> Output {
        self.write("source-bundle.json", &bundle.to_string());
        command(
            &self.0,
            &["trust", "verify", "source-bundle.json", "--axiom-free"],
        )
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}
fn command(directory: &Path, args: &[&str]) -> Output {
    let capture = Scratch::new();
    let stdout = capture.0.join("stdout");
    let stderr = capture.0.join("stderr");
    // Files prevent a full output pipe from blocking the deadline check.
    let mut child = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(args)
        .current_dir(directory)
        .env("TAUTO_LANG", "en")
        .env("TAUTO_CACHE", "off")
        .stdin(Stdio::null())
        .stdout(fs::File::create(&stdout).unwrap())
        .stderr(fs::File::create(&stderr).unwrap())
        .spawn()
        .unwrap();
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if started.elapsed() >= Duration::from_secs(30) {
            let _ = child.kill();
            let _ = child.wait();
            panic!("batch command timed out, not a rejection: {args:?}");
        }
        thread::sleep(Duration::from_millis(10));
    };
    Output {
        status,
        stdout: fs::read(stdout).unwrap(),
        stderr: fs::read(stderr).unwrap(),
    }
}
fn successful(output: &Output) {
    assert!(
        output.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
fn rejected(output: &Output, diagnostic: &str) {
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected verifier rejection: {output:?}"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(diagnostic),
        "expected diagnostic {diagnostic:?}: {output:?}"
    );
}

fn bundle() -> Value {
    let output = command(&root(), &["trust", "bundle", ".", ENTRY]);
    successful(&output);
    serde_json::from_slice(&output.stdout).unwrap()
}

#[test]
fn source_replay_is_axiom_free_and_rejects_a_rehashed_bad_implementation() {
    let bundle = bundle();
    let scratch = Scratch::new();
    assert_eq!(bundle["report"]["explicit_axioms"], json!([]));
    assert_eq!(bundle["report"]["used_axioms"], json!([]));
    assert!(bundle["sources"].get(MAIN).is_none());
    let declarations = bundle["report"]["declarations"].as_array().unwrap();
    for name in [
        "batch_items",
        "batch_remaining",
        "batch_reassembles",
        "batch_size_bounded",
        "batch_fills",
        "batch_short_queue",
        "batch_zero_keeps_queue",
        "batch_positive_consumes_head",
    ] {
        assert!(
            declarations.iter().any(|declaration| {
                declaration["source"] == ENTRY
                    && declaration["name"] == name
                    && declaration["status"] == "checked"
                    && declaration["axioms"] == json!([])
            }),
            "missing checked declaration {name}"
        );
    }
    // The receiver directory has no repository source tree.
    assert!(!scratch.0.join("examples").exists());
    successful(&scratch.verify(&bundle));

    let mut changed = bundle.clone();
    let original = changed["sources"][ENTRY]["text"].as_str().unwrap();
    let from = "List::take(limit, pending)";
    assert_eq!(original.matches(from).count(), 1);
    let text = original.replace(from, "pending");
    changed["sources"][ENTRY]["sha256"] = json!(tauto_syntax::sha256_hex(text.as_bytes()));
    changed["sources"][ENTRY]["text"] = json!(text);
    let output = scratch.verify(&changed);
    rejected(&output, "batch_reassembles");

    let mut changed = bundle.clone();
    changed["report"]["declarations"] = json!([]);
    rejected(&scratch.verify(&changed), "recomputed report differs");
    let mut changed = bundle;
    changed["sources"][ENTRY]["text"] = json!("changed bytes");
    rejected(
        &scratch.verify(&changed),
        &format!("source hash mismatch: {ENTRY}"),
    );
}

#[test]
fn wrong_runtime_limit_is_outside_the_proof_bundle_and_changes_execution() {
    let bundle = bundle();
    let scratch = Scratch::new();
    for (path, source) in bundle["sources"].as_object().unwrap() {
        // Module imports use the receiver's checked-in standard library.
        if !path.starts_with("<std>/") {
            scratch.write(path, source["text"].as_str().unwrap());
        }
    }
    let main = fs::read_to_string(root().join(MAIN)).unwrap();
    let from = "batch_items(2, pending)";
    assert_eq!(main.matches(from).count(), 1);
    scratch.write(MAIN, &main);
    let before = command(&scratch.0, &["run", "--backend", "eval", MAIN]);
    successful(&before);
    assert!(String::from_utf8_lossy(&before.stdout).contains("first = Cons(7, Cons(7, Nil))"));

    // A valid proof of the pure functions does not certify this caller's choice of limit.
    scratch.write(MAIN, &main.replace(from, "batch_items(3, pending)"));
    successful(&scratch.verify(&bundle));
    let after = command(&scratch.0, &["run", "--backend", "eval", MAIN]);
    successful(&after);
    assert_ne!(before.stdout, after.stdout);
    assert!(
        String::from_utf8_lossy(&after.stdout).contains("first = Cons(7, Cons(7, Cons(9, Nil)))")
    );
}
