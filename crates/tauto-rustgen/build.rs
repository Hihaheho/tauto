//! Lists the sources of the crates that a generated workspace carries.
//!
//! The list is read from the crates' directories, so a file added to one of
//! them is bundled without anyone remembering to name it; a hand-kept list
//! drifts and the generated workspace then fails with "file not found for
//! module".

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

/// The crates whose `src` is bundled, by directory name.
const BUNDLED: &[&str] = &["tauto-rt", "tauto-identity", "tauto-rt-signal"];

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let crates = manifest.join("..");
    let mut out = String::from("&[\n");
    for name in BUNDLED {
        let src = crates.join(name).join("src");
        println!("cargo:rerun-if-changed={}", src.display());
        let mut files = Vec::new();
        collect(&src, &mut files);
        files.sort();
        for file in files {
            let rel = file
                .strip_prefix(&src)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            let abs = file.canonicalize().unwrap();
            writeln!(
                out,
                "    ({:?}, include_str!({:?})),",
                format!("{name}/src/{rel}"),
                abs.to_string_lossy()
            )
            .unwrap();
        }
    }
    out.push_str("]\n");
    let dest = PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("bundled_sources.rs");
    std::fs::write(dest, out).unwrap();
}

fn collect(dir: &Path, files: &mut Vec<PathBuf>) {
    println!("cargo:rerun-if-changed={}", dir.display());
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect(&path, files);
        } else if path.extension().is_some_and(|e| e == "rs") {
            files.push(path);
        }
    }
}
