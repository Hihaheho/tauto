//! A state implementation and its invariant use the same executable transition.
use std::{fs, path::PathBuf};
use tauto::check::{Verdict, check_file};
use tauto::extract::extract_files;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}
fn state_file() -> PathBuf {
    root().join("examples/certified-state/src/state.taut")
}

#[test]
fn false_certificate_rejects_before_extraction() {
    tauto_messages::install();
    let file = root().join("examples/certified-state/rejected/forged.taut");
    let entries = check_file(&file).unwrap();
    assert!(entries.iter().any(
        |e| e.entry.name.as_str() == "forged" && matches!(e.entry.verdict, Verdict::Failed(_))
    ));
    assert!(extract_files(&[file]).is_err());
}

#[test]
fn changing_the_executed_transition_invalidates_the_same_proofs() {
    tauto_messages::install();
    let original = fs::read_to_string(state_file())
        .unwrap()
        .replace("../../../std/", &format!("{}/std/", root().display()));
    let dir = std::env::temp_dir().join(format!("tauto-state-mutations-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    for (name, from, to, failed) in [
        (
            "locked",
            "GateClosed(n) => GateClosed(n)",
            "GateClosed(n) => GateClosed(Nat::pred(n))",
            "gate_spend_denied",
        ),
        (
            "increase",
            "GateOpen(n) => GateOpen(Nat::pred(n))",
            "GateOpen(n) => GateOpen(succ(n))",
            "gate_step_nonincreasing",
        ),
    ] {
        assert_eq!(original.matches(from).count(), 1);
        let file = dir.join(format!("{name}.taut"));
        fs::write(&file, original.replace(from, to)).unwrap();
        let entries = check_file(&file).unwrap();
        assert!(
            entries.iter().any(|e| e.entry.name.as_str() == failed
                && matches!(e.entry.verdict, Verdict::Failed(_))),
            "{name}"
        );
        assert!(
            extract_files(&[file]).is_err(),
            "{name} must not be executable"
        );
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn proof_erasure_keeps_the_actual_interpreter_and_transition() {
    tauto_messages::install();
    let output = extract_files(&[state_file()]).unwrap();
    assert!(output.contains("fn state_certified_run"));
    assert!(output.contains("state_run(step, commands, state)"));
    let advance = output
        .split("fn gate_advance")
        .nth(1)
        .unwrap()
        .split("\n}")
        .next()
        .unwrap();
    assert!(advance.contains("state_run("));
    assert!(advance.contains("=> gate_step("));
    assert!(advance.contains("commands, state)"));
    assert!(output.contains("fn gate_step"));
    assert!(!output.contains("GateInvariant"));
    assert!(!output.contains("StatePreserves"));
}
