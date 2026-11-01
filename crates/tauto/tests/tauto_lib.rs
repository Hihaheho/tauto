//! The proofs written in tauto itself (`std/` and `meta/`) must all check, and use
//! no axioms: what cannot be proved here stays in `lean/`. The one exception is
//! the prelude's `Quot::sound`, and only in the files of [`QUOT_SOUND_FILES`].

use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

use tauto::check::{Verdict, check_file};

/// The `.taut` files of `std/` (generic lemmas and data) and `meta/` (models and proofs
/// about the object languages), sorted.
fn lib_files() -> Vec<std::path::PathBuf> {
    tauto_files(&["std", "meta"])
}

/// The `.taut` files of the given directories of the repository, sorted.
fn tauto_files(subs: &[&str]) -> Vec<std::path::PathBuf> {
    let mut files = Vec::new();
    for sub in subs {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(sub);
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if tauto::program::is_source_file(&path) {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// The files written by hand under the rules of `std/` and `meta/`: those and the
/// prelude every program sees (`std/prelude/`). The prelude is not checked as files
/// here: what the kernel reads of it is checked, without axioms, when it is declared
/// (`declare_prelude`), and the rest holds externs and effects.
fn written_files() -> Vec<std::path::PathBuf> {
    tauto_files(&["std", "std/prelude", "meta"])
}

/// The files whose declarations may use `Quot::sound` (and list it among their
/// axioms). A declaration of any other file that uses it fails the check.
const QUOT_SOUND_FILES: &[&str] = &["std/Quot.taut", "std/RatField.taut"];

fn check_without_axioms(file: &Path) {
    // A file of macros (`std/Tactic.taut`) has functions that run when a file
    // is expanded, with the macro effects: they are no proofs. That holds of
    // them in a file that imports the macros too.
    let macros = |file: &Path| {
        std::fs::read_to_string(file)
            .is_ok_and(|text| text.lines().any(|l| l.starts_with("macro ")))
    };
    for file_entry in check_file(file).unwrap() {
        let entry = file_entry.entry;
        match entry.verdict {
            Verdict::Skipped(_) if macros(&file_entry.file) => {}
            Verdict::Checked { axioms } => {
                let quot_sound = QUOT_SOUND_FILES
                    .iter()
                    .any(|f| file_entry.file.ends_with(f));
                // An axiom declaration lists itself: it is the axiom, not a use of one.
                let declared = axioms == [entry.name.clone()];
                assert!(
                    axioms.is_empty()
                        || declared
                        || (quot_sound && axioms == [tauto::check::QUOT_SOUND]),
                    "{}: {} uses {axioms:?}",
                    file.display(),
                    entry.name
                )
            }
            other => panic!("{}: {}: {other:?}", file.display(), entry.name),
        }
    }
}

/// The files are independent, so they are checked side by side.
#[test]
fn every_file_in_std_and_meta_checks_without_axioms() {
    tauto_messages::install();
    let files = lib_files();
    assert!(!files.is_empty());
    let next = AtomicUsize::new(0);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get());
    std::thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                std::thread::Builder::new()
                    .stack_size(256 << 20)
                    .spawn_scoped(scope, || {
                        while let Some(file) = files.get(next.fetch_add(1, Ordering::Relaxed)) {
                            check_without_axioms(file);
                        }
                    })
                    .unwrap()
            })
            .collect();
        for worker in workers {
            if let Err(panic) = worker.join() {
                std::panic::resume_unwind(panic);
            }
        }
    });
}

#[test]
fn every_file_in_std_and_meta_is_formatted() {
    tauto_messages::install();
    for path in written_files() {
        let source = std::fs::read_to_string(&path).unwrap();
        let formatted = tauto::fmt::format(&source).unwrap();
        assert!(
            formatted == source,
            "{} is not formatted: run `tauto fmt`",
            path.display()
        );
    }
}

/// A `match` in `std/` and `meta/` names every constructor: no default arm.
#[test]
fn no_default_arm_in_std_and_meta() {
    tauto_messages::install();
    for path in written_files() {
        let source = std::fs::read_to_string(&path).unwrap();
        let found = tauto::lint::lint(&source).unwrap();
        assert!(found.is_empty(), "{}: {found:?}", path.display());
    }
}
