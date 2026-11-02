//! Kernel-checked regression equations for the backend's pure type engine.
use selfhost_harness::root;
use tauto::check::{Verdict, check_file};

#[test]
fn generic_substitution_and_numeric_constraints_are_kernel_checked() {
    let entries = check_file(&root().join("totes/rustgen/tests/generic.taut")).unwrap();
    let proofs: Vec<_> = entries
        .iter()
        .filter(|e| e.entry.name.starts_with("rg_") && !e.entry.name.starts_with("rg_test_"))
        .collect();
    assert_eq!(proofs.len(), 15);
    for proof in proofs {
        assert!(
            matches!(&proof.entry.verdict, Verdict::Checked { axioms } if axioms.is_empty()),
            "{}: {:?}",
            proof.entry.name,
            proof.entry.verdict
        );
    }
    for entry in entries
        .iter()
        .filter(|e| e.entry.name.starts_with("rustgen_"))
    {
        assert!(
            !matches!(
                &entry.entry.verdict,
                Verdict::Failed(_) | Verdict::Incomplete { .. }
            ),
            "{}: {:?}",
            entry.entry.name,
            entry.entry.verdict
        );
    }
}
