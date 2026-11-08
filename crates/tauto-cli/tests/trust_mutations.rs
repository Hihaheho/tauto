//! Mutate the same source and measure rejection separately from review evidence.
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

const ENTRY: &str = "policy.taut";
const THEOREM: &str = "deny_unauthorized";
static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Probe {
    dir: PathBuf,
    cli: PathBuf,
    calls: usize,
    observations: Vec<Value>,
    command_timings: Vec<Value>,
    deadline: Option<Instant>,
}

impl Probe {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!(
            "tauto-trust-mutations-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&dir).expect("fresh mutation directory");
        let cli = std::env::var_os("TAUTO_MUTATION_CLI")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_tauto")));
        Self {
            dir,
            cli: fs::canonicalize(cli).expect("existing tauto executable"),
            calls: 0,
            observations: Vec::new(),
            command_timings: Vec::new(),
            deadline: None,
        }
    }

    fn write(&self, path: &str, source: &str) {
        fs::write(self.dir.join(path), source).unwrap();
    }

    fn run(&mut self, args: &[&str]) -> Output {
        assert!(
            self.deadline
                .is_none_or(|deadline| Instant::now() < deadline),
            "smoke deadline exceeded, not a rejection"
        );
        self.calls += 1;
        let stdout = self.dir.join(format!("{}.stdout", self.calls));
        let stderr = self.dir.join(format!("{}.stderr", self.calls));
        // Files avoid a pipe filling while the parent waits for the deadline.
        let mut child = Command::new(&self.cli)
            .args(args)
            .current_dir(&self.dir)
            .env("TAUTO_CACHE", "off")
            .env("TAUTO_LANG", "en")
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
            if started.elapsed() >= Duration::from_secs(30)
                || self
                    .deadline
                    .is_some_and(|deadline| Instant::now() >= deadline)
            {
                let _ = child.kill();
                let _ = child.wait();
                panic!("mutation command timed out, not a rejection: {args:?}");
            }
            thread::sleep(Duration::from_millis(10));
        };
        self.command_timings.push(json!({
            "arguments": args,
            "elapsed_ms": started.elapsed().as_millis(),
            "exit_code": status.code(),
        }));
        Output {
            status,
            stdout: fs::read(stdout).unwrap(),
            stderr: fs::read(stderr).unwrap(),
        }
    }

    fn bundle(&mut self) -> Output {
        self.run(&["trust", "bundle", ".", ENTRY])
    }

    fn verify(&mut self, bundle: &Value, strict: bool) -> Output {
        self.write("bundle.json", &bundle.to_string());
        if strict {
            self.run(&["trust", "verify", "bundle.json", "--axiom-free"])
        } else {
            self.run(&["trust", "verify", "bundle.json"])
        }
    }

    fn proof(&mut self) -> Output {
        self.run(&["proof", ENTRY, THEOREM, "--format", "json"])
    }

    fn accepted_source(
        &mut self,
        name: &str,
        source: &str,
        strict: bool,
        evidence: &str,
    ) -> (Value, Value) {
        self.write(ENTRY, source);
        let started = Instant::now();
        let export = self.bundle();
        success(&export, name);
        let bundle = json_output(&export);
        let normal = self.verify(&bundle, false);
        success(&normal, name);
        let axiom_free = self.verify(&bundle, true);
        assert_eq!(
            axiom_free.status.success(),
            strict,
            "{name}: {axiom_free:?}"
        );
        if !strict {
            assert!(String::from_utf8_lossy(&axiom_free.stderr).contains("receiver policy"));
        }
        let proof = self.proof();
        success(&proof, name);
        let proof = json_output(&proof);
        assert_eq!(proof["status"], "ok", "{name}");
        assert_eq!(selected(&proof)["status"], "checked", "{name}");
        self.observations.push(json!({
            "mutation": name,
            "export": "accepted",
            "verify": "accepted",
            "verify_axiom_free": if strict { "accepted" } else { "rejected" },
            "proof": "checked",
            "review_evidence": evidence,
            "source": source,
            "source_sha256": bundle["sources"][ENTRY]["sha256"],
            "goal": selected(&proof)["goal"],
            "goal_tree": selected(&proof)["goal_tree"],
            "parameters": selected(&proof)["parameters"],
            "axioms": selected(&proof)["axioms"],
            "trust_report": bundle["report"],
            "elapsed_ms": started.elapsed().as_millis(),
        }));
        (bundle, proof)
    }

    fn rejected_source(&mut self, name: &str, source: &str, proof_status: &str) {
        self.write(ENTRY, source);
        let started = Instant::now();
        let export = self.bundle();
        assert_eq!(export.status.code(), Some(1), "{name}: {export:?}");
        let proof = self.proof();
        assert_eq!(
            proof.status.code(),
            Some(if proof_status == "incomplete" { 3 } else { 1 }),
            "{name}: {proof:?}"
        );
        let proof = json_output(&proof);
        assert_eq!(selected(&proof)["status"], proof_status, "{name}");
        self.observations.push(json!({
            "mutation": name,
            "export": "rejected",
            "verify": "not-run-no-bundle",
            "verify_axiom_free": "not-run-no-bundle",
            "proof": proof_status,
            "source": source,
            "diagnostic": String::from_utf8_lossy(&export.stderr),
            "elapsed_ms": started.elapsed().as_millis(),
        }));
    }

    fn rejected_bundle(&mut self, name: &str, bundle: &Value, message: &str) {
        let started = Instant::now();
        let out = self.verify(bundle, false);
        assert_eq!(out.status.code(), Some(1), "{name}: {out:?}");
        assert!(
            String::from_utf8_lossy(&out.stderr).contains(message),
            "{name}: {out:?}"
        );
        self.observations.push(json!({
            "mutation": name,
            "verify": "rejected",
            "verify_axiom_free": "not-run",
            "review_evidence": message,
            "diagnostic": String::from_utf8_lossy(&out.stderr),
            "elapsed_ms": started.elapsed().as_millis(),
        }));
    }
}

impl Drop for Probe {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.dir);
    }
}

fn success(output: &Output, name: &str) {
    assert!(output.status.success(), "{name}: {output:?}");
}

fn json_output(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).expect("structured CLI output")
}

fn selected(proof: &Value) -> &Value {
    let proofs = proof["proofs"].as_array().unwrap();
    assert_eq!(proofs.len(), 1);
    assert_eq!(proofs[0]["name"], THEOREM);
    &proofs[0]
}

fn replace_once(source: &str, from: &str, to: &str) -> String {
    assert_eq!(source.matches(from).count(), 1, "mutation anchor: {from}");
    source.replacen(from, to, 1)
}

fn source(bundle: &Value) -> &Value {
    &bundle["sources"][ENTRY]
}

fn report_contains(bundle: &Value, field: &str, name: &str) {
    assert!(
        bundle["report"][field]
            .as_array()
            .unwrap()
            .contains(&json!(name))
    );
}

#[test]
fn distinguish_rejection_from_evidence_and_unchecked_boundaries() {
    let started = Instant::now();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let original = fs::read_to_string(root.join("examples/trust-review/src/policy.taut")).unwrap();
    let mut probe = Probe::new();
    let (baseline, baseline_proof) = probe.accepted_source(
        "baseline",
        &original,
        true,
        "control: the named implementation denies false",
    );
    assert_eq!(selected(&baseline_proof)["parameters"], json!([]));
    assert_eq!(selected(&baseline_proof)["axioms"], json!([]));

    let wrong = replace_once(&original, "{ authorized }", "{ true }");
    probe.rejected_source("implementation-changed", &wrong, "failed");
    let hole = replace_once(&original, "{ Refl }", "{ ?missing }");
    probe.rejected_source("proof-hole", &hole, "incomplete");

    let weakened = replace_once(
        &wrong,
        "Eq(Bool, allow(false), false)",
        "Eq(Bool, allow(false), allow(false))",
    );
    let (weakened_bundle, weakened_proof) = probe.accepted_source(
        "weakened-goal",
        &weakened,
        true,
        "goal_tree changes; neither verification mode enforces the original goal",
    );
    assert_ne!(
        selected(&baseline_proof)["goal_tree"],
        selected(&weakened_proof)["goal_tree"]
    );
    assert_ne!(
        source(&baseline)["sha256"],
        source(&weakened_bundle)["sha256"]
    );

    let premise = replace_once(
        &replace_once(
            &wrong,
            "deny_unauthorized()",
            "deny_unauthorized(h: Eq(Bool, allow(false), false))",
        ),
        "{ Refl }",
        "{ h }",
    );
    let (_, premise_proof) = probe.accepted_source(
        "added-premise",
        &premise,
        true,
        "parameters contains the claimed result as an assumption; not a global axiom",
    );
    assert_eq!(
        selected(&baseline_proof)["goal_tree"],
        selected(&premise_proof)["goal_tree"]
    );
    let parameters = selected(&premise_proof)["parameters"].as_array().unwrap();
    assert_eq!(parameters.len(), 1);
    assert_eq!(parameters[0]["name"], "h");
    assert_eq!(selected(&premise_proof)["axioms"], json!([]));

    let axiom = replace_once(
        &replace_once(&wrong, "{ Refl }", "{ assumed_denial() }"),
        "pub theorem",
        "pub axiom assumed_denial(): Eq(Bool, allow(false), false)\npub theorem",
    );
    let (axiom_bundle, axiom_proof) = probe.accepted_source(
        "added-axiom",
        &axiom,
        false,
        "explicit_axioms, used_axioms and proof axioms identify assumed_denial",
    );
    report_contains(&axiom_bundle, "explicit_axioms", "assumed_denial");
    report_contains(&axiom_bundle, "used_axioms", "assumed_denial");
    assert_eq!(selected(&axiom_proof)["axioms"], json!(["assumed_denial"]));

    let unused = format!("{original}\npub axiom unused(): True\n");
    let (unused_bundle, unused_proof) = probe.accepted_source(
        "unused-axiom",
        &unused,
        false,
        "explicit_axioms identifies unused even when proof axioms is empty",
    );
    report_contains(&unused_bundle, "explicit_axioms", "unused");
    assert_eq!(unused_bundle["report"]["used_axioms"], json!([]));
    assert_eq!(selected(&unused_proof)["axioms"], json!([]));

    let external = format!("{original}\nextern {{ fn live_allow(authorized: Bool): Bool }}\n");
    let (external_bundle, external_proof) = probe.accepted_source(
        "added-extern",
        &external,
        true,
        "extern_functions and unchecked_statements expose a body that was not certified",
    );
    report_contains(&external_bundle, "extern_functions", "live_allow");
    assert!(
        !external_bundle["report"]["unchecked_statements"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert_eq!(
        selected(&baseline_proof)["goal_tree"],
        selected(&external_proof)["goal_tree"]
    );

    let other_target = format!(
        "{}\npub fn allow(authorized: Bool): Bool {{ true }}\n",
        original.replace("allow(", "allow_model(")
    );
    let (_, other_proof) = probe.accepted_source(
        "wrong-target",
        &other_target,
        true,
        "goal_tree names allow_model; the executable allow is not the proved target",
    );
    assert_ne!(
        selected(&baseline_proof)["goal_tree"],
        selected(&other_proof)["goal_tree"]
    );
    assert!(
        selected(&other_proof)["goal"]
            .as_str()
            .unwrap()
            .contains("allow_model")
    );

    let mut tampered = baseline.clone();
    tampered["sources"][ENTRY]["text"] = json!(wrong);
    probe.rejected_bundle("changed-source-stale-hash", &tampered, "hash");
    tampered["sources"][ENTRY]["sha256"] = json!(tauto_syntax::sha256_hex(wrong.as_bytes()));
    probe.rejected_bundle("changed-source-repaired-hash", &tampered, THEOREM);
    let mut concealed = axiom_bundle.clone();
    concealed["report"]["used_axioms"] = json!([]);
    probe.rejected_bundle("concealed-axiom-report", &concealed, "report");

    // An offline bundle certifies its captured sources, not today's checkout.
    probe.write(ENTRY, &wrong);
    success(
        &probe.verify(&baseline, true),
        "old bundle is self-contained",
    );
    let disk_hash = tauto_syntax::sha256_hex(&fs::read(probe.dir.join(ENTRY)).unwrap());
    assert_ne!(source(&baseline)["sha256"], json!(disk_hash));
    probe.observations.push(json!({
        "mutation": "changed-checkout-old-bundle",
        "verify": "not-run",
        "verify_axiom_free": "accepted",
        "bundle_source_sha256": source(&baseline)["sha256"],
        "checkout_source_sha256": disk_hash,
        "review_evidence": "captured source hash differs from the current checkout; verify does not read it",
    }));

    let report = json!({
        "format": "tauto-trust-mutation-observations-v1",
        "checker": baseline["report"]["checker"],
        "cli_override": std::env::var_os("TAUTO_MUTATION_CLI").is_some(),
        "commands": probe.calls,
        "command_timings": probe.command_timings,
        "elapsed_ms": started.elapsed().as_millis(),
        "observations": probe.observations,
        "scope": "These finite mutations measure rejection and visible review evidence, not general soundness, specification adequacy, or executable correspondence.",
    });
    let text = serde_json::to_string_pretty(&report).unwrap();
    if let Some(path) = std::env::var_os("TAUTO_MUTATION_REPORT") {
        use std::io::Write;
        fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .expect("new report file")
            .write_all(text.as_bytes())
            .unwrap();
    }
    println!("{text}");
}

/// A bounded smoke subset, not a substitute for the full mutation matrix.
#[test]
fn trust_smoke_rejects_tampering_but_accepts_a_weakened_goal() {
    let started = Instant::now();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let original = fs::read_to_string(root.join("examples/trust-review/src/policy.taut")).unwrap();
    let mut probe = Probe::new();
    probe.deadline = Some(started + Duration::from_secs(45));
    probe.write(ENTRY, &original);
    let exported = probe.bundle();
    success(&exported, "smoke baseline export");
    let baseline = json_output(&exported);
    success(&probe.verify(&baseline, true), "smoke baseline replay");
    assert_eq!(baseline["report"]["explicit_axioms"], json!([]));
    assert_eq!(baseline["report"]["used_axioms"], json!([]));

    let wrong = replace_once(&original, "{ authorized }", "{ true }");
    let mut tampered = baseline.clone();
    tampered["sources"][ENTRY]["text"] = json!(wrong);
    probe.rejected_bundle("changed-source-stale-hash", &tampered, "hash");
    tampered["sources"][ENTRY]["sha256"] = json!(tauto_syntax::sha256_hex(wrong.as_bytes()));
    probe.rejected_bundle("changed-source-repaired-hash", &tampered, THEOREM);

    let weakened = replace_once(
        &wrong,
        "Eq(Bool, allow(false), false)",
        "Eq(Bool, allow(false), allow(false))",
    );
    probe.write(ENTRY, &weakened);
    let exported = probe.bundle();
    success(&exported, "smoke weakened goal export");
    let weakened_bundle = json_output(&exported);
    success(
        &probe.verify(&weakened_bundle, true),
        "smoke weakened goal replay",
    );
    assert_ne!(
        source(&baseline)["sha256"],
        source(&weakened_bundle)["sha256"]
    );
    assert_eq!(source(&weakened_bundle)["text"], json!(weakened));
    assert_eq!(probe.calls, 6);
    assert!(
        started.elapsed() < Duration::from_secs(45),
        "smoke deadline exceeded"
    );

    let report = json!({
        "format": "tauto-trust-smoke-observations-v1",
        "checker": baseline["report"]["checker"],
        "cli_override": std::env::var_os("TAUTO_MUTATION_CLI").is_some(),
        "commands": probe.calls,
        "command_timings": probe.command_timings,
        "elapsed_ms": started.elapsed().as_millis(),
        "baseline_source": original,
        "weakened_source": weakened,
        "baseline_verify_axiom_free": "accepted",
        "weakened_goal_verify_axiom_free": "accepted",
        "rejections": probe.observations,
        "scope": "Six-command smoke subset: baseline replay, stale-hash and rehashed implementation tampering, and weakened-goal acceptance. No proof inspection, hole, premise, axiom, extern, wrong-target, concealed-report or stale-checkout checks. Not the full matrix or a soundness or executable-correspondence proof.",
    });
    println!("{}", serde_json::to_string_pretty(&report).unwrap());
}
