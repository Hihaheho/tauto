//! The generated crate of a tote, kept across runs of `tauto run --backend
//! rust` and `tauto build`: reading, checking and generating a tote that has
//! not changed gives the crate it gave before, so the crate is made once and
//! read back while nothing it was made from has changed.
//!
//! What it was made from is recorded as a build reads it, as a depfile is:
//!
//! - tauto itself (the SHA-256 of its executable), the command's arguments and
//!   the tote's directory;
//! - the files the tote is read from, in their order (a file added to a
//!   tote's sources changes it);
//! - the state of every path the reading depended on
//!   (`tauto::program::read_dependencies`): each file's text, each
//!   `Tauto.eure` looked for, each `.tauto-syntax` directory's tables, and
//!   whether each one exists.
//!
//! The paths are known only after a build, so they are kept under the first
//! of these (`rust-crate-reads`), and the crate under all three
//! (`rust-crate`). A crate is kept only when the build succeeded, and a crate
//! read back is written and compiled as a new one is. Nothing is checked less:
//! a result is used again only for the same inputs, as a cached proof is.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use tauto_cache::{Action, BuildCache, Outputs};

/// What a hit gives back: the crate's files and what the build said about
/// trusted code.
pub(crate) struct Kept {
    pub files: Vec<(String, String)>,
    pub trusted: String,
    /// The kinds a run is asked for (`needed_kinds`).
    pub needed: Vec<String>,
}

/// The inputs a lookup computed, for keeping the result it missed.
pub(crate) struct Lookup {
    cache: BuildCache,
    reads: Action,
    order: Vec<u8>,
}

fn executable_sha256() -> Option<String> {
    BuildCache::from_env().ok()?.executable_sha256()
}

/// A path's state: a file's text, a directory's files with their texts, or
/// that there is nothing there.
fn state(path: &Path) -> Vec<u8> {
    let mut out = Vec::new();
    if path.is_file() {
        out.push(b'f');
        out.extend(std::fs::read(path).unwrap_or_default());
    } else if path.is_dir() {
        out.push(b'd');
        let mut names: Vec<PathBuf> = std::fs::read_dir(path)
            .into_iter()
            .flatten()
            .flatten()
            .map(|e| e.path())
            .collect();
        names.sort();
        for p in names {
            let s = tauto_syntax::sha256_hex(&state(&p));
            out.extend(p.file_name().unwrap_or_default().as_encoded_bytes());
            out.push(0);
            out.extend(s.as_bytes());
            out.push(0);
        }
    } else {
        out.push(b'-');
    }
    out
}

fn crate_action(reads: &Action, order: &[u8], paths: &[PathBuf]) -> Action {
    let mut action = reads.clone().input("order", order);
    let mut list = Vec::new();
    for (i, p) in paths.iter().enumerate() {
        list.extend(p.as_os_str().as_encoded_bytes());
        list.push(0);
        action = action.input(&format!("read-{i:06}"), &state(p));
    }
    action.input("paths", &list)
}

/// Looks up what a run of `kind` made from the tote in `dir` with `args`:
/// its outputs by name. None when there is no cache to keep them in;
/// otherwise the lookup, with the outputs if they were kept.
pub(crate) fn lookup_outputs(
    kind: &str,
    dir: &Path,
    args: &[String],
) -> Option<(Lookup, Option<BTreeMap<String, Vec<u8>>>)> {
    let cache = BuildCache::from_env().ok()?;
    let exe = executable_sha256()?;
    let dir = dir.canonicalize().ok()?;
    let (files, totes) = tauto::program::tote_build_order(&dir).ok()?;
    let mut order = Vec::new();
    let manifests: Vec<PathBuf> = totes.iter().map(|t| t.join("Tauto.eure")).collect();
    for p in files.iter().chain(&manifests) {
        order.extend(p.as_os_str().as_encoded_bytes());
        order.push(0);
        order.extend(tauto_syntax::sha256_hex(&state(p)).as_bytes());
        order.push(0);
    }
    let reads = Action::new(&format!("{kind}-reads"), &dir.display().to_string())
        .input("tauto", exe.as_bytes())
        .input("arguments", args.join("\0").as_bytes());
    let kept = (|| {
        let out = cache.get(&reads)?;
        let paths = String::from_utf8(cache.get_blob(out.0.get("paths")?)?).ok()?;
        let paths: Vec<PathBuf> = paths
            .split('\0')
            .filter(|p| !p.is_empty())
            .map(PathBuf::from)
            .collect();
        let out = cache.get(&crate_action(&reads, &order, &paths))?;
        let mut outputs = BTreeMap::new();
        for (name, blob) in &out.0 {
            outputs.insert(name.clone(), cache.get_blob(blob)?);
        }
        Some(outputs)
    })();
    Some((
        Lookup {
            cache,
            reads,
            order,
        },
        kept,
    ))
}

/// Keeps `outputs`, which the run that read `loaded` made.
pub(crate) fn keep_outputs(
    lookup: &Lookup,
    loaded: &tauto::program::Loaded,
    outputs: &[(String, &[u8])],
) {
    let paths = tauto::program::read_dependencies(loaded);
    let list: Vec<String> = paths.iter().map(|p| p.display().to_string()).collect();
    let cache = &lookup.cache;
    let mut out = Outputs::default();
    for (name, bytes) in outputs {
        let Ok(blob) = cache.put_blob(bytes) else {
            return;
        };
        out.0.insert(name.clone(), blob);
    }
    if cache
        .put(&crate_action(&lookup.reads, &lookup.order, &paths), &out)
        .is_err()
    {
        return;
    }
    let Ok(blob) = cache.put_blob(list.join("\0").as_bytes()) else {
        return;
    };
    let mut reads = Outputs::default();
    reads.0.insert("paths".into(), blob);
    let _ = cache.put(&lookup.reads, &reads);
}

/// Looks up the crate of the tote in `dir` built with `args`.
pub(crate) fn lookup(dir: &Path, args: &[String]) -> Option<(Lookup, Option<Kept>)> {
    let (lookup, outputs) = lookup_outputs("rust-crate", dir, args)?;
    let kept = outputs.and_then(|outputs| {
        let trusted = String::from_utf8(outputs.get("trusted")?.clone()).ok()?;
        let mut files = Vec::new();
        for (name, bytes) in &outputs {
            if let Some(path) = name.strip_prefix("file:") {
                files.push((path.to_string(), String::from_utf8(bytes.clone()).ok()?));
            }
        }
        let needed = String::from_utf8(outputs.get("permissions")?.clone()).ok()?;
        let needed = needed.lines().map(String::from).collect();
        Some(Kept {
            files,
            trusted,
            needed,
        })
    });
    Some((lookup, kept))
}

/// Keeps the crate `files` that the build which read `loaded` made.
pub(crate) fn keep(
    lookup: &Lookup,
    loaded: &tauto::program::Loaded,
    files: &[(String, String)],
    trusted: &str,
    needed: &[String],
) {
    let needed = needed.join("\n");
    let mut outputs: Vec<(String, &[u8])> = vec![
        ("trusted".into(), trusted.as_bytes()),
        ("permissions".into(), needed.as_bytes()),
    ];
    for (path, text) in files {
        outputs.push((format!("file:{path}"), text.as_bytes()));
    }
    keep_outputs(lookup, loaded, &outputs);
}
