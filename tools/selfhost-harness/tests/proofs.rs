//! The proofs in the llk, nibcheck, scan and text totes (`totes/<name>/src/*.taut`,
//! `docs/design/self-host.md`): every declaration checks, with no hole and no axiom.

use std::fs;

use selfhost_harness::root;
use tauto::check::{Verdict, check_tote_files};

#[test]
fn llk_nibcheck_scan_text_proofs_check() {
    let mut files = Vec::new();
    // These totes hold the certified self-host implementation. Runtime
    // applications and axiom libraries chosen by import are not one proof
    // environment: mixing them can classify a proof's dependencies as runtime.
    for name in ["llk", "lr", "nibcheck", "scan", "text"] {
        let dir = root().join("totes").join(name).join("src");
        files.extend(
            fs::read_dir(dir)
                .unwrap()
                .map(|e| e.unwrap().path())
                .filter(|p| {
                    tauto::program::is_source_file(p)
                        && p.file_name().is_some_and(|n| n != "main.taut")
                }),
        );
    }
    files.sort();
    // Every source module, including imported laws in std, is checked.
    // Every proof is checked again, without the proof cache
    // (`crates/tauto-kernel/src/check/cache.rs`).
    // The kernel normalizes under the arms of a stuck `match`, so comparing
    // with a large literal recurses deeply. These checks use a deep stack, as
    // does `crates/tauto/tests/tauto_lib.rs`.
    let checked = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || check_tote_files(&files, false).unwrap())
        .unwrap()
        .join()
        .unwrap();
    let mut wrong = Vec::new();
    for e in &checked.entries {
        match &e.entry.verdict {
            Verdict::Checked { axioms } if axioms.is_empty() => {}
            v => wrong.push(format!("{}: {}: {v:?}", e.file.display(), e.entry.name)),
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
