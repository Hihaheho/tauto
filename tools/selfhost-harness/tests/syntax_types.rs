//! The types a syntax's tables make, written by `totes/elaborator`
//! (`--syntax-types`) against `tauto_parse::syntax::types_text`, over every
//! committed table file of the repository.

use std::path::{Path, PathBuf};

use selfhost_harness::{assert_same_dump, run_tote_native};
use tauto_syntax::Tables;

const STEPS: u64 = 200_000_000_000;

fn tables(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if path.is_dir() {
            if name != "target" && name != ".git" && name != "vendor" || name == ".tauto-syntax" {
                tables(&path, out);
            }
        } else if name.ends_with(".tables") {
            out.push(path);
        }
    }
}

#[test]
fn the_schema_of_every_committed_table_file_makes_the_types_the_host_prints() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = Vec::new();
    for sub in ["cases", "crates", "totes", "std", "examples", "tools"] {
        tables(&root.join(sub), &mut files);
    }
    files.sort();
    assert!(files.len() > 10, "found {} table files", files.len());
    let mut rust = String::new();
    let mut paths = Vec::new();
    for f in &files {
        let text = std::fs::read_to_string(f).unwrap();
        // An out-of-date file is not read by the host either.
        let Ok(t) = Tables::read(&text) else { continue };
        let path = f.canonicalize().unwrap().to_string_lossy().into_owned();
        rust.push_str(&format!("== {path}\n{}", tauto_parse::syntax::types_text("syn", &t)));
        paths.push(path);
    }
    let mut args = vec!["--syntax-types".to_string(), "syn".to_string()];
    args.extend(paths);
    let out = run_tote_native("elaborator", &args, STEPS);
    assert_eq!(out.error, None);
    assert_eq!(out.stderr, "");
    assert_same_dump("syntax-types", &rust, &out.stdout);
}
