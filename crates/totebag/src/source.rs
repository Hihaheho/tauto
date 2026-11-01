//! `source-v1`: a source tree as bytes, and its SHA-256, the [`SourceId`].
//!
//! ```text
//! frame(B)  = u64be(length(B)) || B
//! source-v1 = UTF8("tauto-source-v1\0") || u64be(number of files)
//!             || each file, in the byte order of its path:
//!                frame(UTF8(path)) || executable (one byte, 0 or 1) || frame(bytes)
//! SourceId  = SHA256(source-v1)
//! ```
//!
//! A tree is a finite map from relative paths to regular files. Links,
//! submodules and other special files, absolute paths, empty components, `.`,
//! `..`, backslashes and NUL are refused, and so are two paths that would be
//! one file where names are compared without case. Times, owners and how the
//! files were packed are not part of the identity.

use std::collections::BTreeMap;
use std::path::Path;

use tauto_syntax::Sha256;

use crate::spec::SourceId;

/// At most this many files in a tree.
pub const MAX_FILES: usize = 65_536;
/// At most this many bytes in all the files of a tree.
pub const MAX_BYTES: u64 = 512 << 20;

/// One regular file of a tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct File {
    /// Relative, with `/` between components.
    pub path: String,
    pub executable: bool,
    pub bytes: Vec<u8>,
}

/// A checked tree: its files by path, and their [`SourceId`].
#[derive(Debug, Clone)]
pub struct Tree {
    pub files: BTreeMap<String, File>,
    pub id: SourceId,
}

pub fn check_path(path: &str) -> Result<(), String> {
    use crate::core::generated::api::{TbPathProblem as P, tb_check_path};
    let why = match tb_check_path(tauto_rt::Text::from(path)) {
        None => return Ok(()),
        Some(P::PathLength) => "totebag-path-length",
        Some(P::PathCharacters) => "totebag-path-characters",
        Some(P::PathAbsolute) => "totebag-path-relative",
        Some(P::PathComponents) => "totebag-path-components",
    };
    Err(say!(
        "totebag-at",
        place = format!("{path:?}"),
        error = tauto_message::Message::new(why)
    ))
}

impl Tree {
    /// Checks the files and computes their ID.
    pub fn new(files: Vec<File>) -> Result<Tree, String> {
        if files.len() > MAX_FILES {
            return Err(say!("totebag-too-many-files", max = MAX_FILES));
        }
        let mut total = 0u64;
        let mut by_path = BTreeMap::new();
        for f in &files {
            check_path(&f.path)?;
            total += f.bytes.len() as u64;
            if total > MAX_BYTES {
                return Err(say!("totebag-too-many-bytes", max = MAX_BYTES));
            }
        }
        use crate::core::generated::api::{TbTreePath, TbTreeProblem as P, tb_check_tree};
        // Case is folded here, as the file systems that ignore it fold it.
        let paths = crate::list(files.iter().map(|f| TbTreePath {
            path: tauto_rt::Text::from(f.path.as_str()),
            folded: tauto_rt::Text::from(f.path.to_lowercase()),
        }));
        match tb_check_tree(paths) {
            None => {}
            Some(P::PathTwice(path)) => {
                return Err(say!("totebag-path-twice", path = format!("{:?}", &*path)));
            }
            Some(P::PathCaseClash(other, path)) => {
                return Err(say!(
                    "totebag-path-case-clash",
                    other = format!("{:?}", &*other),
                    path = format!("{:?}", &*path)
                ));
            }
            Some(P::FileAndDirectory(file, path)) => {
                return Err(say!(
                    "totebag-file-and-directory",
                    file = format!("{:?}", &*file),
                    path = format!("{:?}", &*path)
                ));
            }
        }
        for f in files {
            by_path.insert(f.path.clone(), f);
        }
        let id = id_of(&by_path);
        Ok(Tree { files: by_path, id })
    }

    /// The tree written under `dir`: regular files only, every other kind refused.
    pub fn read_dir(dir: &Path) -> Result<Tree, String> {
        let mut files = Vec::new();
        read_into(dir, "", &mut files)?;
        Tree::new(files)
    }
}

fn read_into(dir: &Path, prefix: &str, out: &mut Vec<File>) -> Result<(), String> {
    let entries = std::fs::read_dir(dir).map_err(|e| {
        say!(
            "totebag-at",
            place = dir.display().to_string(),
            error = e.to_string()
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|e| {
            say!(
                "totebag-at",
                place = dir.display().to_string(),
                error = e.to_string()
            )
        })?;
        let name = entry.file_name();
        let Some(name) = name.to_str() else {
            return Err(say!(
                "totebag-name-not-utf8",
                place = dir.display().to_string()
            ));
        };
        let path = format!("{prefix}{name}");
        let meta = std::fs::symlink_metadata(entry.path()).map_err(|e| {
            say!(
                "totebag-at",
                place = entry.path().display().to_string(),
                error = e.to_string()
            )
        })?;
        if meta.is_dir() {
            read_into(&entry.path(), &format!("{path}/"), out)?;
        } else if meta.is_file() {
            let bytes = std::fs::read(entry.path()).map_err(|e| {
                say!(
                    "totebag-at",
                    place = entry.path().display().to_string(),
                    error = e.to_string()
                )
            })?;
            out.push(File {
                path,
                executable: executable(&meta),
                bytes,
            });
            if out.len() > MAX_FILES {
                return Err(say!("totebag-too-many-files", max = MAX_FILES));
            }
        } else {
            return Err(say!(
                "totebag-not-file-or-directory",
                path = format!("{path:?}")
            ));
        }
    }
    Ok(())
}

#[cfg(unix)]
fn executable(meta: &std::fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt;
    meta.permissions().mode() & 0o100 != 0
}

#[cfg(not(unix))]
fn executable(_: &std::fs::Metadata) -> bool {
    false
}

fn id_of(files: &BTreeMap<String, File>) -> SourceId {
    let mut h = Sha256::new();
    h.update(b"tauto-source-v1\0");
    h.update(&(files.len() as u64).to_be_bytes());
    // BTreeMap<String, _> is in the byte order of the keys.
    for f in files.values() {
        frame(&mut h, f.path.as_bytes());
        h.update(&[f.executable as u8]);
        frame(&mut h, &f.bytes);
    }
    SourceId::from_hex(h.finish_hex())
}

fn frame(h: &mut Sha256, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_be_bytes());
    h.update(bytes);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn file(path: &str, bytes: &str) -> File {
        File {
            path: path.into(),
            executable: false,
            bytes: bytes.as_bytes().to_vec(),
        }
    }

    /// The bytes of `source-v1`, written out by hand.
    fn spelled(files: &[(&str, u8, &str)]) -> Vec<u8> {
        let mut out = b"tauto-source-v1\0".to_vec();
        out.extend((files.len() as u64).to_be_bytes());
        for (path, x, bytes) in files {
            out.extend((path.len() as u64).to_be_bytes());
            out.extend(path.as_bytes());
            out.push(*x);
            out.extend((bytes.len() as u64).to_be_bytes());
            out.extend(bytes.as_bytes());
        }
        out
    }

    #[test]
    fn the_id_is_the_hash_of_the_spelled_form() {
        let tree = Tree::new(vec![
            file("src/main.taut", "perform show(\"hello\", 42)\n"),
            File {
                executable: true,
                ..file("run.sh", "#!/bin/sh\n")
            },
            file("Tauto.eure", "package { name = \"a\" }\n"),
        ])
        .unwrap();
        // `T` < `r` < `s` in bytes.
        let expected = tauto_syntax::sha256_hex(&spelled(&[
            ("Tauto.eure", 0, "package { name = \"a\" }\n"),
            ("run.sh", 1, "#!/bin/sh\n"),
            ("src/main.taut", 0, "perform show(\"hello\", 42)\n"),
        ]));
        assert_eq!(tree.id.hex(), expected);
    }

    #[test]
    fn the_empty_tree() {
        let tree = Tree::new(Vec::new()).unwrap();
        assert_eq!(
            tree.id.hex(),
            tauto_syntax::sha256_hex(b"tauto-source-v1\0\0\0\0\0\0\0\0\0")
        );
    }

    #[test]
    fn order_and_mode_and_content_count() {
        let a = Tree::new(vec![file("a", "1"), file("b", "2")]).unwrap();
        let b = Tree::new(vec![file("b", "2"), file("a", "1")]).unwrap();
        assert_eq!(a.id, b.id);
        let c = Tree::new(vec![
            file("a", "1"),
            File {
                executable: true,
                ..file("b", "2")
            },
        ])
        .unwrap();
        assert_ne!(a.id, c.id);
        let d = Tree::new(vec![file("a", "1"), file("b", "2\n")]).unwrap();
        assert_ne!(a.id, d.id);
        // The frames keep a path from running into its content.
        let e = Tree::new(vec![file("ab", "")]).unwrap();
        let f = Tree::new(vec![file("a", "b")]).unwrap();
        assert_ne!(e.id, f.id);
    }

    #[test]
    fn bad_trees_are_refused() {
        for bad in ["/abs", "a//b", "./a", "a/..", "a\\b", "a\0b", "", "a/"] {
            assert!(Tree::new(vec![file(bad, "")]).is_err(), "{bad:?}");
        }
        assert!(Tree::new(vec![file("a", ""), file("a", "")]).is_err());
        assert!(Tree::new(vec![file("Read.me", ""), file("read.ME", "")]).is_err());
        assert!(Tree::new(vec![file("a", ""), file("a/b", "")]).is_err());
        assert!(Tree::new(vec![file("A", ""), file("a/b", "")]).is_err());
    }
}
