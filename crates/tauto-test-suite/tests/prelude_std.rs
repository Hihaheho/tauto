//! The prelude every program sees (`std/prelude/`) is read by tauto's parser. Most of
//! it is not checked by the kernel (it holds externs and effects), so this is as far
//! as that part is checked; the data the proofs read as families and
//! `std/prelude/Ord.taut` are checked by both kernels
//! (`crates/tauto-kernel/src/check.rs`).

use std::path::Path;

#[test]
fn the_prelude_parses() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std/prelude");
    let mut seen = 0;
    for entry in std::fs::read_dir(&dir).expect("std/prelude exists") {
        let path = entry.expect("an entry").path();
        if tauto::program::is_source_file(&path) {
            let source = std::fs::read_to_string(&path).expect("readable");
            assert_eq!(tauto_parol::check(&source), Ok(()), "{}", path.display());
            seen += 1;
        }
    }
    assert!(seen > 0, "no .taut file under {}", dir.display());
}
