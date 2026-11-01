//! The project being read: the tote whose `Tauto::lock` fixes the Git
//! dependencies of every tote read with it. A project has one instance of each
//! tote, so a tote reached through a path or from Git finds its own Git
//! dependencies in the project's lock, not in one of its own.
//!
//! Reading a tote ([`crate::program::load_tote`] and the rest) notes the
//! project of each tote it reaches, so that an `import text.Text` read later
//! from one of their files finds the same directory. A tote not reached that
//! way is its own project.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use tauto_message::msg;

use totebag::spec::GitSource;

/// The project of each tote read, both by canonical path.
static PROJECTS: Mutex<BTreeMap<PathBuf, PathBuf>> = Mutex::new(BTreeMap::new());

/// Notes that the tote in `tote` is read as part of `project`.
pub(crate) fn note(tote: &Path, project: &Path) {
    PROJECTS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .insert(tote.to_path_buf(), project.to_path_buf());
}

/// The project the tote in `dir` was last read as part of, or `dir` itself.
pub fn project_of(dir: &Path) -> PathBuf {
    let dir = crate::program::canonical_path(dir);
    PROJECTS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .get(&dir)
        .cloned()
        .unwrap_or(dir)
}

/// Whether the network is off: `TAUTO_OFFLINE` set to anything but `0`
/// (`--offline`).
pub fn offline() -> bool {
    std::env::var("TAUTO_OFFLINE").is_ok_and(|v| !v.is_empty() && v != "0")
}

/// The directory of the Git dependency `name` of the tote in `dir`: where
/// the project's `Tauto::lock` says it was fetched, fetching the locked
/// commit first when its tree is not in the cache.
pub(crate) fn git_dependency(
    dir: &Path,
    name: &str,
    source: &GitSource,
) -> Result<PathBuf, String> {
    let project = project_of(dir);
    let cache = totebag::cache::Cache::from_env()?;
    if cache.tree_of(&project).is_some() {
        return Err(msg!(
            "tauto-dep-fetched-from-git",
            name = name,
            dir = dir.display().to_string()
        )
        .to_string());
    }
    let lock = totebag::lock::read(&project)?;
    let Some(locked) = lock.as_ref().and_then(|l| l.get(name)) else {
        return Err(msg!(
            "tauto-dep-not-locked",
            name = name,
            source = source.to_string(),
            lock = project.join(totebag::lock::FILE).display().to_string()
        )
        .to_string());
    };
    if locked.source != *source {
        return Err(msg!(
            "tauto-dep-lock-differs",
            name = name,
            lock = project.join(totebag::lock::FILE).display().to_string(),
            locked = locked.source.to_string(),
            source = source.to_string(),
            project = project.display().to_string()
        )
        .to_string());
    }
    if cache.has(&locked.id) {
        return Ok(totebag::tote_dir(&cache, locked));
    }
    // What the lock fixes is fetched; the lock itself is never changed here.
    if offline() {
        return Err(msg!(
            "tauto-dep-offline",
            name = name,
            url = locked.source.url.to_string(),
            rev = locked.rev.short().to_string(),
            project = project.display().to_string()
        )
        .to_string());
    }
    eprintln!(
        "{}",
        msg!(
            "tauto-dep-fetching",
            name = name,
            rev = locked.rev.short().to_string(),
            url = locked.source.url.to_string()
        )
    );
    totebag::fetch_locked(&cache, locked)
        .map_err(|e| msg!("tauto-dep-error", name = name, error = e.to_string()).to_string())
}
