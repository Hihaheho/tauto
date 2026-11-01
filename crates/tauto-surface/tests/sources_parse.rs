//! Every `.taut` file under `totes/` and `std/` parses with the current
//! grammar, so a syntax change cannot leave a file behind in the old one.

use std::path::{Path, PathBuf};

use tauto_surface::surface::parse_program_unresolved_at;

fn taut_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            taut_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "taut") {
            out.push(path);
        }
    }
}

#[test]
fn every_tote_and_std_file_parses() {
    tauto_messages::install();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = Vec::new();
    for dir in ["totes", "std"] {
        taut_files(&root.join(dir), &mut files);
    }
    assert!(!files.is_empty());
    let failures: Vec<String> = files
        .iter()
        .filter_map(|path| {
            let source = std::fs::read_to_string(path).unwrap();
            let rel = path.strip_prefix(&root).unwrap_or(path).display();
            parse_program_unresolved_at(&source, 0)
                .err()
                .map(|e| format!("{rel}: {e}"))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
