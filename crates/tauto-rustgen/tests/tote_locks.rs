//! A tote's committed `Cargo.lock` must already hold what the generated crate
//! depends on. A change to the generated `Cargo.toml` (a new dependency) leaves
//! the lock stale, and the build then stops with "Cargo.lock is out of date".
//! This is the fast half of the guard; `scripts/check-tote-locks.taut` resolves
//! each lock against the real generated workspace.
use std::fs;
use std::path::Path;

/// The version of package `name` in a `Cargo.lock`, if it is there once.
fn locked_versions(lock: &str, name: &str) -> Vec<String> {
    let mut found = Vec::new();
    let mut current: Option<&str> = None;
    for line in lock.lines() {
        if let Some(n) = line.strip_prefix("name = \"") {
            current = n.strip_suffix('"');
        } else if let Some(v) = line.strip_prefix("version = \"")
            && current == Some(name)
        {
            found.push(v.trim_end_matches('"').to_string());
        }
    }
    found
}

#[test]
fn tote_locks_hold_the_generated_jemalloc_dependency() {
    let totes = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../totes");
    let mut checked = 0;
    for entry in fs::read_dir(&totes).expect("totes directory") {
        let dir = entry.expect("entry").path();
        let lock = dir.join("Cargo.lock");
        if !lock.is_file() {
            continue;
        }
        let text = fs::read_to_string(&lock).expect("read lock");
        assert_eq!(
            locked_versions(&text, "tikv-jemallocator"),
            [tauto_rustgen::JEMALLOC_VERSION],
            "{} is stale: run `tauto build --release --update-lock` in {} (see scripts/check-tote-locks.taut)",
            lock.display(),
            dir.display(),
        );
        checked += 1;
    }
    assert!(
        checked > 0,
        "no tote has a Cargo.lock; the guard checks nothing"
    );
}
