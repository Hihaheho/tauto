//! `include_text!("path")`: the text of a file, read where the call is
//! written (`docs/design/macro.md`「`include_text!`」).
//!
//! The reader replaces each call in a file it reads, before the macros of the
//! file are expanded, by a `Text` literal that holds the bytes of the file
//! named. The path is relative to the file that writes the call and must stay
//! inside the tote of that file (the nearest directory above it with a
//! `Tauto.eure`; a file outside any tote, inside its own directory): an
//! absolute path, a path that leaves it with `..` and a symbolic link that
//! leads out of it are errors, and so are a file that cannot be read and one
//! that is not UTF-8. What comes after the reader (the macros, the checkers,
//! the kernel) sees only the literal.
//!
//! `include_bytes!("path")` follows the same rules and reads any bytes: it is
//! replaced by `Bytes::of_list([b0, b1, …])`, the bytes of the file as a
//! `Bytes` of `std::prelude::Collections`, with each byte a number literal.
//!
//! The calls are not macros: no user code runs and a macro function cannot
//! read a file through them. A call that a macro makes, or one in a text read
//! without a file, is refused by the expander (`macro.include_text`,
//! `macro.include_bytes`).

use std::path::{Component, Path, PathBuf};
use tauto_message::{Message, msg};

use tauto_parol::Span;

use super::{Source, canonical_path};
use crate::surface::{Stmt, SurfaceTerm, TermKind, walk};

pub const NAME: &str = tauto_macro::macros::expand::INCLUDE_TEXT;
pub const BYTES: &str = tauto_macro::macros::expand::INCLUDE_BYTES;

/// Whether `name` is one of the built-in reads.
pub fn is_include(name: &str) -> bool {
    name == NAME || name == BYTES
}

/// What the reader of one file read for its `include_text!` calls.
#[derive(Default)]
pub struct Included {
    /// What went wrong, at the call.
    pub errors: Vec<(Message, Span)>,
    /// The files read, by canonical path, in the order of the calls.
    pub files: Vec<PathBuf>,
    /// Valid local include paths attempted, including missing or unreadable files.
    pub inputs: Vec<PathBuf>,
}

/// Replaces every `include_text!("path")` written in `stmts`, the statements
/// of the file at `file`, by the text of the file it names, and every
/// `include_bytes!("path")` by its bytes. A file whose text
/// `source` gives is not read from disk. A call that fails is left as syntax
/// the checkers refuse, with its error in `out`.
pub fn read_includes(
    stmts: &mut [Stmt],
    file: &Path,
    source: &Source<'_>,
    out: &mut Included,
) {
    for s in stmts.iter_mut() {
        walk::stmt(s, &mut |t| {
            let TermKind::MacroCall { name, arg } = &*t.kind else {
                return;
            };
            if !is_include(name) {
                return;
            }
            let name = name.clone();
            let bytes = name == BYTES;
            let made = match &*arg.kind {
                TermKind::Text(path) => read(file, path, source, bytes, &mut out.inputs),
                _ => Err(msg!("tauto-include-argument", name = &name)),
            };
            *t = match made {
                Ok((read, path)) => {
                    out.files.push(path);
                    match read {
                        Read::Text(text) => SurfaceTerm::new(TermKind::Text(text), t.span),
                        Read::Bytes(bytes) => bytes_literal(&bytes, t.span),
                    }
                }
                Err(e) => {
                    out.errors.push((e.into(), t.span));
                    SurfaceTerm::new(TermKind::Other(format!("{name}!")), t.span)
                }
            };
        });
    }
}

/// The most bytes one `include_bytes!` reads. The literal is a term for each
/// byte, nested once per byte, and the passes after the reader walk it
/// recursively; a file larger than this is refused rather than overflowing
/// their stack.
pub const BYTES_LIMIT: usize = 16 * 1024;

/// What a call read: a text, or bytes.
enum Read {
    Text(String),
    Bytes(Vec<u8>),
}

/// `Bytes::of_list([b0, b1, …])`, every part at the span of the call.
pub(crate) fn bytes_literal(bytes: &[u8], span: Span) -> SurfaceTerm {
    let list = bytes
        .iter()
        .rev()
        .fold(SurfaceTerm::var("Nil", span), |rest, b| {
            SurfaceTerm::app(
                "Cons",
                vec![SurfaceTerm::new(TermKind::Nat(b.to_string()), span), rest],
                span,
            )
        });
    SurfaceTerm::app("Bytes::of_list", vec![list], span)
}

/// The directory a file's `include_text!` may read in: the nearest directory
/// above the file that holds a `Tauto.eure`, or the file's own directory.
pub fn root_of(file: &Path) -> PathBuf {
    let file = canonical_path(file);
    let dir = file.parent().unwrap_or(Path::new("/"));
    dir.ancestors()
        .find(|d| d.join("Tauto.eure").is_file())
        .unwrap_or(dir)
        .to_path_buf()
}

/// The directories a file's `include_text!` may read in: [`root_of`], and the
/// directories its tote's manifest lists as `package.include-from`, as far as they
/// stay inside the workspace: the outermost directory above the tote that holds
/// a `Tauto.eure`. A tote fetched from elsewhere is its own workspace, so its
/// list reaches nothing new.
pub fn roots_of(file: &Path) -> Vec<PathBuf> {
    let root = root_of(file);
    let mut roots = vec![root.clone()];
    let Ok(manifest) = crate::manifest::read(&root) else {
        return roots;
    };
    if manifest.package.include_from.is_empty() {
        return roots;
    }
    let workspace = root
        .ancestors()
        .filter(|d| d.join("Tauto.eure").is_file())
        .last()
        .unwrap_or(&root)
        .to_path_buf();
    for dir in &manifest.package.include_from {
        let mut target = root.clone();
        for part in Path::new(dir).components() {
            match part {
                Component::CurDir => {}
                Component::ParentDir => {
                    target.pop();
                }
                Component::Normal(p) => target.push(p),
                Component::RootDir | Component::Prefix(_) => {}
            }
        }
        if target.starts_with(&workspace) {
            roots.push(canonical_path(&target));
        }
    }
    roots
}

/// The text (or, with `bytes`, the bytes) of the file `written` names, from
/// `file`, and its canonical path.
fn read(
    file: &Path,
    written: &str,
    source: &Source<'_>,
    bytes: bool,
    inputs: &mut Vec<PathBuf>,
) -> Result<(Read, PathBuf), Message> {
    let root = root_of(file);
    let roots = roots_of(file);
    let file = canonical_path(file);
    let dir = file.parent().unwrap_or(Path::new("/"));
    let rel = Path::new(written);
    if written.is_empty() {
        return Err(msg!("tauto-include-empty"));
    }
    if rel.has_root() || rel.is_absolute() {
        return Err(msg!("tauto-include-absolute-relative", path = written));
    }
    let outside = || {
        msg!(
            "tauto-include-outside",
            path = written,
            root = root.display().to_string()
        )
    };
    let mut target = dir.to_path_buf();
    // Whether the path went out of the tote's own directory on the way.
    let mut left = false;
    for part in rel.components() {
        match part {
            Component::CurDir => {}
            Component::ParentDir => {
                if !target.pop() {
                    return Err(outside());
                }
                if !target.starts_with(&root) {
                    left = true;
                }
            }
            Component::Normal(p) => target.push(p),
            Component::RootDir | Component::Prefix(_) => {
                return Err(msg!("tauto-include-absolute", path = written));
            }
        }
    }
    if !roots.iter().any(|r| target.starts_with(r)) {
        return Err(outside());
    }
    // A path that leaves the tote does not come back into it.
    if left && target.starts_with(&root) {
        return Err(outside());
    }
    // A symbolic link on the way may lead out of the tote.
    let on_disk = crate::program::canonicalize(&target).ok();
    if let Some(real) = &on_disk
        && !roots.iter().any(|r| real.starts_with(r))
    {
        return Err(msg!(
            "tauto-include-symlink",
            path = written,
            root = root.display().to_string()
        ));
    }
    let path = on_disk.unwrap_or_else(|| target.clone());
    // Track the written path too: a local symlink can be retargeted.
    inputs.push(target);
    inputs.push(path.clone());
    let read = match source(&path) {
        Some(given) => {
            let text = given.map_err(|e| read_error(written, e.to_string()))?;
            if bytes {
                Read::Bytes(text.into_bytes())
            } else {
                Read::Text(text)
            }
        }
        None => {
            let read = std::fs::read(&path).map_err(|e| read_error(written, e.to_string()))?;
            if bytes {
                Read::Bytes(read)
            } else {
                Read::Text(
                    String::from_utf8(read)
                        .map_err(|_| msg!("tauto-include-not-utf8", path = written))?,
                )
            }
        }
    };
    if let Read::Bytes(b) = &read
        && b.len() > BYTES_LIMIT
    {
        return Err(msg!(
            "tauto-include-too-large",
            path = written,
            size = b.len().to_string(),
            limit = BYTES_LIMIT.to_string()
        ));
    }
    Ok((read, path))
}

/// "include.read: `WRITTEN`: ERROR".
fn read_error(written: &str, error: String) -> Message {
    msg!("tauto-include-read", path = written, error = error)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn errors_of(dir: &Path, entry: &str) -> Vec<String> {
        tauto_messages::install();
        let loaded = crate::program::load(&dir.join(entry)).unwrap();
        loaded
            .program
            .errors
            .into_iter()
            .map(|(m, _)| m.to_string())
            .collect()
    }

    #[cfg(unix)]
    #[test]
    fn a_symbolic_link_out_of_the_tote_is_refused() {
        let base = std::env::temp_dir().join(format!("tauto-include-link-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        let tote = base.join("tote");
        std::fs::create_dir_all(tote.join("src")).unwrap();
        std::fs::write(tote.join("Tauto.eure"), "").unwrap();
        std::fs::write(base.join("secret.txt"), "no").unwrap();
        std::fs::write(tote.join("inside.txt"), "yes").unwrap();
        std::os::unix::fs::symlink(base.join("secret.txt"), tote.join("src/out.txt")).unwrap();
        std::os::unix::fs::symlink(tote.join("inside.txt"), tote.join("src/in.txt")).unwrap();
        std::fs::write(
            tote.join("src/main.nib"),
            r#"let a := include_text!("out.txt")
"#,
        )
        .unwrap();
        let errors = errors_of(&tote.join("src"), "main.nib");
        assert!(
            errors
                .first()
                .is_some_and(|e| e.starts_with("include.outside") && e.contains("symbolic link")),
            "{errors:?}"
        );
        // A link that stays in the tote is read.
        std::fs::write(
            tote.join("src/main.nib"),
            r#"let a := include_text!("in.txt")
"#,
        )
        .unwrap();
        let loaded = crate::program::load(&tote.join("src/main.nib")).unwrap();
        assert!(
            loaded.program.errors.is_empty(),
            "{:?}",
            loaded.program.errors
        );
        assert_eq!(
            loaded.included,
            vec![tote.join("inside.txt").canonicalize().unwrap()]
        );
        let _ = std::fs::remove_dir_all(&base);
    }

    #[test]
    fn a_given_text_is_read_instead_of_the_disk() {
        let base = std::env::temp_dir().join(format!("tauto-include-given-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(&base).unwrap();
        std::fs::write(
            base.join("main.nib"),
            r#"let a := include_text!("d.txt")
"#,
        )
        .unwrap();
        std::fs::write(base.join("d.txt"), "disk").unwrap();
        let data = base.join("d.txt").canonicalize().unwrap();
        let loaded = crate::program::load_with_source(&base.join("main.nib"), &|p: &Path| {
            (p == data).then(|| Ok("buffer".to_string()))
        })
        .unwrap();
        let printed = crate::surface::print::print_stmts(&loaded.program.stmts);
        assert!(printed.contains("\"buffer\""), "{printed}");
        let _ = std::fs::remove_dir_all(&base);
    }
}
