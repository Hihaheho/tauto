//! A resolved name is compared by its identity, never by its display
//! (`docs/design/name-identity.md`). This counts, per source file of the
//! crates, the places that compare a name's text to a literal
//! (`n.as_str() == "…"`) and fails when a file has more than it is allowed
//! below. The allowances are the places left from before the rule was
//! checked: printers and tests read the display on purpose, the rest are to
//! be moved to identities. Lower a count when a place goes; never raise one.

use std::path::Path;

const ALLOWED: &[(&str, usize)] = &[
    ("tauto-analyzer/src/assist.rs", 1),
    // A permission key, not a name.
    ("tauto-cli/src/run_prompt.rs", 1),
    ("tauto-cli/src/test.rs", 1),
    ("tauto-kernel/src/check.rs", 2),
    ("tauto-kernel/src/check/core.rs", 1),
    ("tauto-kernel/src/check/derivation.rs", 5),
    ("tauto-macro/src/macros/expand.rs", 2),
    ("tauto-nibcheck/src/host.rs", 2),
    ("tauto-nibcheck/src/rows/tests.rs", 9),
    ("tauto-nibcheck/src/types.rs", 5),
    ("tauto-nibcheck/src/types/classes.rs", 1),
    ("tauto-nibcheck/src/types/operation_instances.rs", 3),
    ("tauto-nir/src/borrow.rs", 1),
    ("tauto-nibcheck/src/lower/mod.rs", 26),
    ("tauto-rustgen/src/operation_instances.rs", 3),
    ("tauto-surface/src/macros/node.rs", 1),
    ("tauto-surface/src/surface/dump.rs", 3),
    ("tauto-surface/src/surface/print.rs", 5),
    ("tauto-vm/src/wire.rs", 1),
    ("tauto/src/extract.rs", 1),
    ("tauto/src/read.rs", 1),
    ("tauto/src/report.rs", 2),
];

fn count(text: &str) -> usize {
    ["as_str() == \"", "as_str()==\"", "as_str() != \"", "as_str()!=\""]
        .iter()
        .map(|pattern| text.matches(pattern).count())
        .sum()
}

fn walk(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap().flatten() {
        let path = entry.path();
        if path.is_dir() {
            walk(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

#[test]
fn no_new_spelling_comparisons() {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut files = Vec::new();
    for entry in std::fs::read_dir(&crates).unwrap().flatten() {
        let src = entry.path().join("src");
        if src.is_dir() {
            walk(&src, &mut files);
        }
    }
    let mut over = Vec::new();
    for path in files {
        let relative = path.strip_prefix(&crates).unwrap().to_string_lossy().replace('\\', "/");
        let found = count(&std::fs::read_to_string(&path).unwrap());
        let allowed = ALLOWED
            .iter()
            .find(|(file, _)| *file == relative)
            .map_or(0, |(_, n)| *n);
        if found > allowed {
            over.push(format!("{relative}: {found} (allowed {allowed})"));
        }
    }
    assert!(
        over.is_empty(),
        "compare a resolved name by its identity (`tauto_surface::bindings::is_library`, \
         a `DeclRef`), not its text:\n{}",
        over.join("\n")
    );
}
