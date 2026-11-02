//! The proofs written in tauto itself (`std/` and `meta/`) must all check, and use
//! no axioms: what cannot be proved here stays in `lean/`. The one exception is
//! the prelude's `Quot::sound`, and only in the files of [`QUOT_SOUND_FILES`].

use std::path::Path;
use std::sync::Mutex;
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

/// What is wrong with the check of `file` (and of what it imports), one line each.
fn problems_without_axioms(file: &Path) -> Vec<String> {
    // A file of macros (`std/Tactic.taut`) has functions that run when a file
    // is expanded, with the macro effects: they are no proofs. That holds of
    // them in a file that imports the macros too.
    let macros = |file: &Path| {
        std::fs::read_to_string(file).is_ok_and(|text| {
            text.lines()
                .any(|l| l.starts_with("macro ") || l.starts_with("pub macro "))
        })
    };
    let entries = match check_file(file) {
        Ok(entries) => entries,
        Err(e) => return vec![format!("{}: {e}", file.display())],
    };
    let mut problems = Vec::new();
    for file_entry in entries {
        let entry = file_entry.entry;
        match entry.verdict {
            Verdict::Skipped(_) if macros(&file_entry.file) => {}
            Verdict::Checked { axioms } => {
                let quot_sound = QUOT_SOUND_FILES
                    .iter()
                    .any(|f| file_entry.file.ends_with(f));
                // An axiom declaration lists itself: it is the axiom, not a use of one.
                let declared = axioms == [entry.name.clone()];
                if !(axioms.is_empty()
                    || declared
                    || (quot_sound && axioms == [tauto::check::QUOT_SOUND]))
                {
                    problems.push(format!(
                        "{}: {} uses {axioms:?}",
                        file.display(),
                        entry.name
                    ));
                }
            }
            other => problems.push(format!("{}: {}: {other:?}", file.display(), entry.name)),
        }
    }
    problems
}

/// The files are independent (each is checked with what it imports, by its own
/// kernel), so a pool of threads, one per core, checks them side by side. The
/// biggest files go first, so that the long ones do not start last and set the
/// time of the whole run. Checking all the files in one run is not the same
/// check: a file would see the names of files it does not import.
#[test]
fn every_file_in_std_and_meta_checks_without_axioms() {
    tauto_messages::install();
    let mut files = lib_files();
    assert!(!files.is_empty());
    files.sort_by_key(|f| std::cmp::Reverse(std::fs::metadata(f).map_or(0, |m| m.len())));
    let next = AtomicUsize::new(0);
    let problems = Mutex::new(Vec::new());
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get());
    std::thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                std::thread::Builder::new()
                    .stack_size(256 << 20)
                    .spawn_scoped(scope, || {
                        while let Some(file) = files.get(next.fetch_add(1, Ordering::Relaxed)) {
                            let found = problems_without_axioms(file);
                            problems.lock().unwrap().extend(found);
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
    let mut problems = problems.into_inner().unwrap();
    problems.sort();
    assert!(problems.is_empty(), "{}", problems.join("\n"));
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
