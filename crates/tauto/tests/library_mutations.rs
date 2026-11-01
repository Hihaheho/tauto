//! Mutating the library's executable operations must invalidate its current proofs.
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use tauto::check::{Verdict, check_file};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[test]
fn matrix_proofs_detect_mutations_of_the_actual_operations() {
    tauto_messages::install();
    for (before, after, failed) in [
        (
            "column => algebra_op(0, R, multiplication)(matrix(row, column), values(column))",
            "column => algebra_op(0, R, multiplication)(values(column), matrix(row, column))",
            "algebra_matrix_apply_scale",
        ),
        (
            "index => algebra_op(0, R, multiplication)(left(row, index), right(index, column))",
            "index => algebra_op(0, R, multiplication)(right(index, column), left(row, index))",
            "algebra_matrix_product_apply",
        ),
    ] {
        let dir = std::env::temp_dir().join(format!(
            "tauto-matrix-mutation-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&dir).unwrap();
        for name in ["Equality", "Monoid", "Semiring", "Finite", "Matrix"] {
            std::fs::copy(
                root().join(format!("totes/algebra/src/{name}.taut")),
                dir.join(format!("{name}.taut")),
            )
            .unwrap();
        }
        let path = dir.join("Matrix.taut");
        let source = std::fs::read_to_string(&path).unwrap();
        let (operations, proofs) = source
            .split_once("theorem algebra_matrix_apply_congr")
            .unwrap();
        assert_eq!(operations.matches(before).count(), 1);
        std::fs::write(
            &path,
            format!(
                "{}theorem algebra_matrix_apply_congr{proofs}",
                operations.replace(before, after)
            ),
        )
        .unwrap();
        let entries = check_file(&path).expect("mutated library still parses");
        std::fs::remove_dir_all(dir).unwrap();
        assert!(
            entries.iter().any(|entry| entry.entry.name == failed
                && matches!(entry.entry.verdict, Verdict::Failed(_))),
            "generic proof {failed} accepted the changed operation"
        );
        assert!(
            entries
                .iter()
                .any(|entry| entry.entry.name == "algebra_sum_swap"
                    && matches!(entry.entry.verdict, Verdict::Checked { .. }))
        );
    }
}

#[test]
fn equality_adapter_rejects_a_congruent_but_wrong_product_operation() {
    tauto_messages::install();
    let dir = std::env::temp_dir().join(format!(
        "tauto-relation-product-mutation-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let original = root().join("totes/algebra/src/RelationMatrix.taut");
    let source = std::fs::read_to_string(original)
        .unwrap()
        .replace(
            "import \"RelationSemiring.taut\"",
            &format!(
                "import {:?}",
                root().join("totes/algebra/src/RelationSemiring.taut")
            ),
        )
        .replace(
            "import \"Matrix.taut\"",
            &format!("import {:?}", root().join("totes/algebra/src/Matrix.taut")),
        );
    let (operations, proofs) = source
        .split_once("theorem algebra_relation_sum_congr")
        .unwrap();
    let before = "index => mul(left(row, index), right(index, column))";
    assert_eq!(operations.matches(before).count(), 1);
    let changed = format!(
        "{}theorem algebra_relation_sum_congr{proofs}",
        operations.replace(
            before,
            "index => add(left(row, index), right(index, column))"
        )
    );
    let file = dir.join("RelationMatrix.taut");
    std::fs::write(&file, changed).unwrap();
    let entries = check_file(&file).expect("mutated implementation still parses");
    std::fs::remove_dir_all(dir).unwrap();
    // Addition is also congruent: representation-independence alone is not product correctness.
    assert!(entries.iter().any(
        |e| e.entry.name == "algebra_relation_matrix_product_equality"
            && matches!(e.entry.verdict, Verdict::Failed(_))
    ));
    assert!(
        entries
            .iter()
            .any(|e| e.entry.name == "algebra_relation_sum_congr"
                && matches!(e.entry.verdict, Verdict::Checked { .. }))
    );
}
