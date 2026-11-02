//! What reading a program depends on besides the text given for its entry: the texts of the
//! files it reads, the files `include_text!` reads and the `Tauto.eure` files that hold each
//! file's limits and dependencies. A result kept for a program is used again only while these
//! are the same (`docs/design/analysis-cache.md`).

use std::path::{Path, PathBuf};

use super::{Order, Source, canonical_path};

#[derive(Debug, Clone, PartialEq)]
pub struct Inputs {
    /// The files read, in order, with their texts.
    pub files: Vec<(PathBuf, String)>,
    /// Each place a `Tauto.eure` was looked for, with its text when there is one.
    pub manifests: Vec<(PathBuf, Option<String>)>,
    /// The files `include_text!` reads, with their texts when they can be read.
    pub included: Vec<(PathBuf, Option<String>)>,
}

impl Inputs {
    /// The inputs of the program of the first `n` files. The included files are not told apart
    /// by the file that includes them: all of them are kept.
    pub fn first(&self, n: usize) -> Inputs {
        let files = self.files[..n.min(self.files.len())].to_vec();
        Inputs {
            manifests: manifests(&files),
            files,
            included: self.included.clone(),
        }
    }
}

/// The files of the program of `entry`, in the order they are read.
pub(super) fn order(entry: &Path, source: &Source<'_>) -> Result<Vec<(PathBuf, String)>, String> {
    let mut order = Order {
        done: Default::default(),
        stack: Vec::new(),
        files: Vec::new(),
        source,
    };
    order.visit(entry)?;
    Ok(order.files)
}

/// The inputs of the program whose files are `files` and which includes `included`.
pub(super) fn of(files: &[(PathBuf, String)], included: &[PathBuf]) -> Inputs {
    Inputs {
        files: files.to_vec(),
        manifests: manifests(files),
        included: texts(included.iter()),
    }
}

/// The inputs as they are now of the program of `entry`, read before with the inputs `before`.
pub fn current(entry: &Path, source: &Source<'_>, before: &Inputs) -> Result<Inputs, String> {
    let files = order(entry, source)?;
    Ok(Inputs {
        manifests: manifests(&files),
        files,
        included: texts(before.included.iter().map(|(p, _)| p)),
    })
}

fn texts<'a>(paths: impl Iterator<Item = &'a PathBuf>) -> Vec<(PathBuf, Option<String>)> {
    paths
        .map(|p| (p.clone(), std::fs::read_to_string(p).ok()))
        .collect()
}

/// Of each file outside the standard library, the nearest `Tauto.eure` above it and each place
/// one was looked for before it.
fn manifests(files: &[(PathBuf, String)]) -> Vec<(PathBuf, Option<String>)> {
    let std_root = Path::new(crate::stdlib::ROOT);
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::new();
    for (path, _) in files {
        if path.starts_with(std_root) {
            continue;
        }
        for dir in canonical_path(path).ancestors().skip(1) {
            let manifest = dir.join("Tauto.eure");
            if !seen.insert(manifest.clone()) {
                break;
            }
            let found = manifest.is_file();
            let text = found
                .then(|| std::fs::read_to_string(&manifest).ok())
                .flatten();
            out.push((manifest, text));
            if found {
                break;
            }
        }
    }
    out
}
