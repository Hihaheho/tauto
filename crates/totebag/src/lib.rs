//! Totebag: the totes a tote depends on, fetched from Git and fixed by
//! content.
//!
//! A dependency names a Git repository, a ref and a directory
//! ([`spec::GitSource`]). `Tauto.lock` ([`lock`]) fixes the exact commit and
//! the SHA-256 of its source tree ([`source`]) for each one; the trees are kept
//! under their IDs ([`cache`]). Checking, building and running read the lock and
//! the cache and never the network; only fetching, locking and updating do.

/// A message of this crate as text, for the `String` errors it returns:
/// `say!("totebag-…", name = value, …)`, written through the installed writer.
macro_rules! say {
    ($($t:tt)*) => {
        ::tauto_message::msg!($($t)*).to_string()
    };
}

pub mod cache;

/// The checks of `totes/totebag`: what Totebag accepts as a name, URL, ref,
/// directory, ID or tree path. The compiler reads totes through this crate,
/// so the tote cannot be compiled in a build script; its code is kept in
/// `src/core.rs` and `cargo run -p totebag-gen` writes it again.
#[allow(clippy::all, unused)]
#[rustfmt::skip]
mod core {
    include!("core.rs");
}

pub mod git;
pub mod index;
pub mod lock;
pub mod source;
pub mod spec;

use std::path::PathBuf;

use cache::Cache;
use lock::Locked;
use spec::{GitSource, Rev, SourceId};

pub(crate) fn list<A>(items: impl IntoIterator<Item = A>) -> core::generated::List<A> {
    let items: Vec<A> = items.into_iter().collect();
    items
        .into_iter()
        .rev()
        .fold(core::generated::List::Nil, |rest, a| {
            core::generated::List::Cons(a, std::rc::Rc::new(rest).into())
        })
}

pub(crate) fn of_list<A: Clone>(mut list: &core::generated::List<A>) -> Vec<A> {
    let mut out = Vec::new();
    while let core::generated::List::Cons(a, rest) = list {
        out.push(a.clone());
        list = rest;
    }
    out
}

/// A tote name: lowercase letters, digits and `-`, starting with a letter.
pub fn valid_name(name: &str) -> bool {
    core::generated::api::tb_valid_name(tauto_rt::Text::from(name))
}

/// A commit fetched and its tree written to the cache.
#[derive(Debug, Clone)]
pub struct Fetched {
    pub rev: Rev,
    pub id: SourceId,
    pub dir: PathBuf,
}

pub fn fetch_head(cache: &Cache, source: &GitSource) -> Result<Fetched, String> {
    source.check()?;
    let mirror = git::Mirror::open(cache.mirror_dir(&source.url), "sha1")?;
    let rev = mirror.fetch_head(source)?;
    install(cache, &mirror, source, rev)
}

/// Fetches the locked commit, unless its tree is in the cache, and checks
/// that its tree is the locked one. A tree found in the cache is read again
/// and its ID checked before it is used.
pub fn fetch_locked(cache: &Cache, locked: &Locked) -> Result<PathBuf, String> {
    locked.source.check()?;
    if cache.has(&locked.id) {
        cache.verify(&locked.id)?;
        return Ok(tote_dir(cache, locked));
    }
    let mirror = git::Mirror::open(cache.mirror_dir(&locked.source.url), locked.rev.format())?;
    mirror.fetch_rev(&locked.source, &locked.rev)?;
    let fetched = install(cache, &mirror, &locked.source, locked.rev.clone())?;
    if fetched.id != locked.id {
        return Err(say!(
            "totebag-locked-tree-differs",
            name = &locked.name,
            rev = locked.rev.to_string(),
            url = &locked.source.url,
            found = fetched.id.to_string(),
            locked = locked.id.to_string()
        ));
    }
    Ok(fetched.dir)
}

fn install(
    cache: &Cache,
    mirror: &git::Mirror,
    source: &GitSource,
    rev: Rev,
) -> Result<Fetched, String> {
    let tree = mirror.tree(&rev).map_err(|e| {
        say!(
            "totebag-source-at-rev",
            source = source.to_string(),
            rev = rev.short(),
            error = e
        )
    })?;
    if !source.dir.is_empty()
        && !tree
            .files
            .keys()
            .any(|p| p.starts_with(&format!("{}/", source.dir)))
    {
        return Err(say!(
            "totebag-no-directory",
            url = &source.url,
            rev = rev.short(),
            dir = &source.dir
        ));
    }
    let root = cache.install(&tree)?;
    Ok(Fetched {
        rev,
        id: tree.id,
        dir: root.join(&source.dir),
    })
}

/// Where the locked tote is in the cache, whether or not it has been fetched.
pub fn tote_dir(cache: &Cache, locked: &Locked) -> PathBuf {
    cache.source_dir(&locked.id).join(&locked.source.dir)
}

#[cfg(test)]
mod tests {
    /// src/core.rs is what tauto-build makes of totes/totebag now;
    /// `cargo run -p totebag-gen` writes it again.
    #[test]
    fn generated_code_is_current() {
        // Relative to this crate, as the file names it.
        let manifest = std::path::Path::new("../../totes/totebag/Tauto.eure");
        let (_, text, _) = tauto_build::generate(manifest, None).unwrap();
        let current = std::fs::read_to_string("src/core.rs").unwrap();
        assert!(
            current == text,
            "src/core.rs is out of date: run `cargo run -p totebag-gen`"
        );
    }
}
