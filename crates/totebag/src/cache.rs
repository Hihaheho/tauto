//! Where fetched totes are kept. A tree is written under its [`SourceId`],
//! and only after its ID is computed from the bytes written: a directory
//! `src/<hex>` is there only when it holds that tree.
//!
//! ```text
//! $TAUTO_TOTES (else $XDG_CACHE_HOME/tauto/totes, else ~/.cache/tauto/totes)
//!   src/<hex>/…        a tree, its files read-only
//!   git/<hex>.git      a bare repository per URL (the hex is the URL's SHA-256)
//!   tmp/               trees being written
//! ```

use std::path::{Path, PathBuf};

use crate::source::Tree;
use crate::spec::SourceId;

#[derive(Debug, Clone)]
pub struct Cache {
    root: PathBuf,
}

impl Cache {
    /// The cache the environment names.
    pub fn from_env() -> Result<Cache, String> {
        let root = match std::env::var("TAUTO_TOTES") {
            Ok(v) if !v.is_empty() => PathBuf::from(v),
            _ => match std::env::var("XDG_CACHE_HOME") {
                Ok(v) if !v.is_empty() => PathBuf::from(v).join("tauto/totes"),
                _ => match std::env::var("HOME") {
                    Ok(h) if !h.is_empty() => PathBuf::from(h).join(".cache/tauto/totes"),
                    _ => return Err(say!("totebag-no-cache-place")),
                },
            },
        };
        Ok(Cache::at(root))
    }

    pub fn at(root: PathBuf) -> Cache {
        Cache { root }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Where the tree `id` is, whether or not it has been fetched.
    pub fn source_dir(&self, id: &SourceId) -> PathBuf {
        self.root.join("src").join(id.hex())
    }

    pub fn has(&self, id: &SourceId) -> bool {
        self.source_dir(id).is_dir()
    }

    /// The bare repository for `url`.
    pub fn mirror_dir(&self, url: &str) -> PathBuf {
        self.root
            .join("git")
            .join(format!("{}.git", tauto_syntax::sha256_hex(url.as_bytes())))
    }

    /// Writes `tree` under its ID, unless it is there already.
    pub fn install(&self, tree: &Tree) -> Result<PathBuf, String> {
        let dest = self.source_dir(&tree.id);
        if dest.is_dir() {
            return Ok(dest);
        }
        let tmp_root = self.root.join("tmp");
        std::fs::create_dir_all(&tmp_root).map_err(|e| {
            say!(
                "totebag-at",
                place = tmp_root.display().to_string(),
                error = e.to_string()
            )
        })?;
        std::fs::create_dir_all(self.root.join("src")).map_err(|e| {
            say!(
                "totebag-at",
                place = self.root.display().to_string(),
                error = e.to_string()
            )
        })?;
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let tmp = tmp_root.join(format!(
            "{}-{}-{nanos}",
            tree.id.short(),
            std::process::id()
        ));
        let written = write_tree(&tmp, tree).and_then(|()| {
            let again = Tree::read_dir(&tmp)?;
            if again.id != tree.id {
                return Err(say!(
                    "totebag-written-tree-differs",
                    dir = tmp.display().to_string(),
                    id = tree.id.to_string()
                ));
            }
            Ok(())
        });
        if let Err(e) = written {
            let _ = remove_tree(&tmp);
            return Err(e);
        }
        match std::fs::rename(&tmp, &dest) {
            Ok(()) => Ok(dest),
            // Another process wrote the same tree first.
            Err(_) if dest.is_dir() => {
                let _ = remove_tree(&tmp);
                Ok(dest)
            }
            Err(e) => {
                let _ = remove_tree(&tmp);
                Err(say!(
                    "totebag-at",
                    place = dest.display().to_string(),
                    error = e.to_string()
                ))
            }
        }
    }

    /// Reads the tree `id` again and checks that it is still that tree.
    pub fn verify(&self, id: &SourceId) -> Result<(), String> {
        let dir = self.source_dir(id);
        let found = Tree::read_dir(&dir)?;
        if found.id == *id {
            Ok(())
        } else {
            Err(say!(
                "totebag-tree-changed",
                dir = dir.display().to_string(),
                found = found.id.to_string(),
                id = id.to_string()
            ))
        }
    }

    /// The root of the fetched tree that `path` is in, if it is in one.
    pub fn tree_of(&self, path: &Path) -> Option<PathBuf> {
        let src = self.root.join("src").canonicalize().ok()?;
        let path = path.canonicalize().ok()?;
        let rest = path.strip_prefix(&src).ok()?;
        let first = rest.components().next()?;
        Some(src.join(first))
    }
}

fn write_tree(dir: &Path, tree: &Tree) -> Result<(), String> {
    std::fs::create_dir(dir).map_err(|e| {
        say!(
            "totebag-at",
            place = dir.display().to_string(),
            error = e.to_string()
        )
    })?;
    for f in tree.files.values() {
        let path = dir.join(&f.path);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).map_err(|e| {
                say!(
                    "totebag-at",
                    place = parent.display().to_string(),
                    error = e.to_string()
                )
            })?;
        }
        std::fs::write(&path, &f.bytes).map_err(|e| {
            say!(
                "totebag-at",
                place = path.display().to_string(),
                error = e.to_string()
            )
        })?;
        read_only(&path, f.executable)?;
    }
    Ok(())
}

#[cfg(unix)]
fn read_only(path: &Path, executable: bool) -> Result<(), String> {
    use std::os::unix::fs::PermissionsExt;
    let mode = if executable { 0o555 } else { 0o444 };
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).map_err(|e| {
        say!(
            "totebag-at",
            place = path.display().to_string(),
            error = e.to_string()
        )
    })
}

#[cfg(not(unix))]
fn read_only(path: &Path, _executable: bool) -> Result<(), String> {
    let mut p = std::fs::metadata(path)
        .map_err(|e| {
            say!(
                "totebag-at",
                place = path.display().to_string(),
                error = e.to_string()
            )
        })?
        .permissions();
    p.set_readonly(true);
    std::fs::set_permissions(path, p).map_err(|e| {
        say!(
            "totebag-at",
            place = path.display().to_string(),
            error = e.to_string()
        )
    })
}

fn remove_tree(dir: &Path) -> std::io::Result<()> {
    std::fs::remove_dir_all(dir)
}
