//! The host filesystem boundary for the Tauto module loader.
//!
//! This module enumerates an explicit source root. It does not parse sources or
//! resolve imports; those operations belong to `totes/rustgen/src/loader.taut`.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::{self, Read},
    path::Path,
};

const MAX_BYTES: usize = 16 * 1024 * 1024;
const MAX_FILES: usize = 4096;
const MAX_ID_BYTES: usize = 4096;
const MAX_PATH_PARTS: usize = 256;

/// Original UTF-8 inputs and ordered source roots. Selection is trusted build
/// metadata; only the Tauto loader follows language imports and resource uses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BundlePlan {
    pub roots: Vec<String>,
    pub files: BTreeMap<String, String>,
}

/// Portable IDs are canonical, relative and unambiguous on supported hosts.
pub fn validate_portable_id(id: &str) -> io::Result<()> {
    if id.is_empty()
        || id.len() > MAX_ID_BYTES
        || id.split('/').count() > MAX_PATH_PARTS
        || id
            .chars()
            .any(|c| matches!(c, '\\' | ':' | '\n' | '\r' | '\t' | '\0'))
        || id
            .split('/')
            .any(|part| part.is_empty() || part == "." || part == "..")
    {
        return Err(io::Error::other("noncanonical bundle path"));
    }
    Ok(())
}

/// Resolve manifest metadata without reading, parsing or rewriting Tauto code.
pub fn normalize_relative(base: &str, path: &str) -> io::Result<String> {
    if path.is_empty()
        || path.len() > MAX_ID_BYTES
        || path.split('/').count() > MAX_PATH_PARTS
        || path.starts_with('/')
        || path
            .chars()
            .any(|c| matches!(c, '\\' | ':' | '\n' | '\r' | '\t' | '\0'))
    {
        return Err(io::Error::other("invalid metadata path"));
    }
    let mut parts: Vec<&str> = if base.is_empty() {
        Vec::new()
    } else {
        validate_portable_id(base)?;
        base.split('/').collect()
    };
    for part in path.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                parts
                    .pop()
                    .ok_or_else(|| io::Error::other("metadata path escapes bundle"))?;
            }
            p => parts.push(p),
        }
    }
    let id = parts.join("/");
    validate_portable_id(&id)?;
    Ok(id)
}

impl BundlePlan {
    /// Read only explicitly permitted files. No tree walk, extension discovery,
    /// source parser, import scan, extraction or host compiler participates.
    pub fn from_allowed_files(
        root: &Path,
        allowed: &[String],
        roots: Vec<String>,
    ) -> io::Result<Self> {
        let mut prefix = std::path::PathBuf::new();
        for part in root.components() {
            prefix.push(part);
            if fs::symlink_metadata(&prefix)?.file_type().is_symlink() {
                return Err(io::Error::other("source root contains a symlink"));
            }
        }
        let root = root.canonicalize()?;
        let mut files = BTreeMap::new();
        let mut total = 0usize;
        if allowed.len() > MAX_FILES {
            return Err(io::Error::other("too many source bundle files"));
        }
        for id in allowed {
            validate_portable_id(id)?;
            if files.contains_key(id) {
                return Err(io::Error::other("duplicate allowed input"));
            }
            let mut path = root.clone();
            for part in id.split('/') {
                path.push(part);
                if fs::symlink_metadata(&path)?.file_type().is_symlink() {
                    return Err(io::Error::other("source input contains a symlink"));
                }
            }
            let metadata = fs::metadata(&path)?;
            if !metadata.is_file() {
                return Err(io::Error::other("source input is not a regular file"));
            }
            if !path.canonicalize()?.starts_with(&root) {
                return Err(io::Error::other("source input escapes root"));
            }
            if metadata.len() > MAX_BYTES as u64 {
                return Err(io::Error::other("source bundle exceeds limit"));
            }
            // Bound allocation as well as the declared file size: a backing
            // file can grow between metadata inspection and the actual read.
            let input = fs::File::open(&path)?;
            let opened = input.metadata()?;
            if !opened.is_file() || opened.len() > MAX_BYTES as u64 {
                return Err(io::Error::other("invalid or oversized source input"));
            }
            let mut bytes = Vec::new();
            input.take(MAX_BYTES as u64 + 1).read_to_end(&mut bytes)?;
            total = total
                .checked_add(bytes.len())
                .and_then(|n| n.checked_add(id.len()))
                .filter(|n| *n <= MAX_BYTES)
                .ok_or_else(|| io::Error::other("source bundle exceeds limit"))?;
            let text = String::from_utf8(bytes)
                .map_err(|_| io::Error::other(format!("input is not UTF-8: {id}")))?;
            files.insert(id.clone(), text);
        }
        Ok(Self { roots, files })
    }

    pub fn from_tote(root: &Path, tote: &str, allowed: &[String]) -> io::Result<Self> {
        let input = Self::from_allowed_files(root, allowed, Vec::new())?;
        Self::from_tote_files(tote, input.files)
    }

    /// Interpret package selection metadata from the same captured manifest
    /// bytes that enter the bundle. Dependency mains are not roots.
    pub fn from_tote_files(tote: &str, files: BTreeMap<String, String>) -> io::Result<Self> {
        validate_portable_id(tote)?;
        fn visit(
            id: &str,
            entry: bool,
            files: &BTreeMap<String, String>,
            done: &mut BTreeSet<String>,
            stack: &mut Vec<String>,
            roots: &mut Vec<String>,
            expected: Option<&str>,
        ) -> io::Result<()> {
            let manifest_id = format!("{id}/Tauto.eure");
            let raw = files.get(&manifest_id).ok_or_else(|| {
                io::Error::other(format!("manifest is not an allowed input: {manifest_id}"))
            })?;
            // This is Eure manifest metadata, not the Tauto language parser.
            let manifest =
                tauto::manifest::parse(raw, Path::new(&manifest_id)).map_err(|m| io::Error::other(m.to_string()))?;
            if expected.is_some_and(|name| name != manifest.package.name) {
                return Err(io::Error::other(format!(
                    "dependency name differs from package: {manifest_id}"
                )));
            }
            if manifest.rust != Default::default() || manifest.javascript != Default::default() {
                return Err(io::Error::other("bundle host configuration is unsupported"));
            }
            if stack.iter().any(|p| p == id) {
                return Err(io::Error::other("package dependency cycle"));
            }
            if done.contains(id) {
                return Ok(());
            }
            stack.push(id.into());
            let mut dependencies = manifest.dependencies;
            dependencies.sort();
            for (name, dependency) in dependencies {
                // A bundle holds the files it is given; a tote fetched from
                // Git is not among them.
                let tauto::manifest::Dependency::Path(path) = dependency else {
                    return Err(io::Error::other("bundle Git dependencies are unsupported"));
                };
                visit(
                    &normalize_relative(id, &path)?,
                    false,
                    files,
                    done,
                    stack,
                    roots,
                    Some(&name),
                )?;
            }
            stack.pop();
            done.insert(id.into());
            let mut selected = Vec::new();
            for source in manifest.package.source_paths() {
                let prefix = normalize_relative(id, &source)?;
                if files.contains_key(&prefix) {
                    if !matches!(
                        Path::new(&prefix).extension().and_then(|x| x.to_str()),
                        Some("taut" | "tauto")
                    ) {
                        return Err(io::Error::other("tote sources must use .taut or .tauto"));
                    }
                    selected.push(prefix);
                } else {
                    let prefix = format!("{prefix}/");
                    let before = selected.len();
                    for path in files.keys().filter(|p| p.starts_with(&prefix)) {
                        match Path::new(path).extension().and_then(|x| x.to_str()) {
                            Some("taut" | "tauto") => selected.push(path.clone()),
                            Some("nib") => {
                                return Err(io::Error::other(
                                    "tote sources must use .taut or .tauto",
                                ));
                            }
                            _ => {}
                        }
                    }
                    if selected.len() == before && source != tauto::manifest::DEFAULT_SOURCE {
                        return Err(io::Error::other(format!(
                            "source selection has no allowed files: {prefix}"
                        )));
                    }
                }
            }
            selected.sort();
            let (mains, others): (Vec<_>, Vec<_>) = selected
                .into_iter()
                .partition(|p| Path::new(p).file_stem().is_some_and(|s| s == "main"));
            roots.extend(others);
            if entry {
                roots.extend(mains);
            }
            Ok(())
        }
        let mut roots = Vec::new();
        visit(
            tote,
            true,
            &files,
            &mut BTreeSet::new(),
            &mut Vec::new(),
            &mut roots,
            None,
        )?;
        Ok(Self { roots, files })
    }

    /// V2 adds ordered roots while retaining the original file record framing.
    /// Manifest and resource bytes are ordinary files, not generated source.
    pub fn encode(&self) -> io::Result<String> {
        if self.roots.is_empty() || self.roots.len() > MAX_FILES || self.files.len() > MAX_FILES {
            return Err(io::Error::other("invalid source bundle root or file count"));
        }
        let mut out = format!("TAUTO-SOURCES-2\n{}\n", self.roots.len());
        for id in &self.roots {
            validate_portable_id(id)?;
            if !self.files.contains_key(id) {
                return Err(io::Error::other(format!(
                    "root is not an allowed input: {id}"
                )));
            }
            out.push_str(&format!("{}\n{id}\n", id.len()));
            if out.len() > MAX_BYTES {
                return Err(io::Error::other("source bundle exceeds limit"));
            }
        }
        out.push_str(&format!("{}\n", self.files.len()));
        for (id, contents) in &self.files {
            validate_portable_id(id)?;
            let header = format!("{}\n{}\n", id.len(), contents.len());
            let next = out
                .len()
                .checked_add(header.len())
                .and_then(|n| n.checked_add(id.len()))
                .and_then(|n| n.checked_add(contents.len()))
                .and_then(|n| n.checked_add(1))
                .filter(|n| *n <= MAX_BYTES);
            if next.is_none() {
                return Err(io::Error::other("source bundle exceeds limit"));
            }
            out.push_str(&header);
            out.push_str(id);
            out.push_str(contents);
            out.push('\n');
        }
        if out.len() > MAX_BYTES {
            return Err(io::Error::other("source bundle exceeds limit"));
        }
        Ok(out)
    }
}

/// Packs regular `.taut` files under `root`, sorted by portable relative ID.
/// Symlinks are rejected, including the root, so the bundle cannot silently
/// acquire source from outside the selected tree. No absolute path is emitted.
pub fn source_bundle(root: &Path) -> io::Result<String> {
    if fs::symlink_metadata(root)?.file_type().is_symlink() {
        return Err(io::Error::other("source root is a symlink"));
    }
    let root = root.canonicalize()?;
    let mut files = Vec::new();
    let mut bytes = 0;
    collect(&root, &root, &mut files, &mut bytes)?;
    files.sort_by(|a, b| a.0.cmp(&b.0));
    let mut out = format!("TAUTO-SOURCES-1\n{}\n", files.len());
    for (id, source) in files {
        out.push_str(&format!("{}\n{}\n", id.len(), source.len()));
        out.push_str(&id);
        out.push_str(&source);
        out.push('\n');
        if out.len() > MAX_BYTES {
            return Err(io::Error::other("source bundle exceeds limit"));
        }
    }
    Ok(out)
}

fn collect(
    root: &Path,
    dir: &Path,
    files: &mut Vec<(String, String)>,
    bytes: &mut usize,
) -> io::Result<()> {
    // Sort before traversal as well, so an invalid tree has deterministic errors.
    let mut entries = fs::read_dir(dir)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let kind = entry.file_type()?;
        if kind.is_symlink() {
            return Err(io::Error::other("source tree contains a symlink"));
        }
        let path = entry.path();
        if kind.is_dir() {
            collect(root, &path, files, bytes)?;
        } else if kind.is_file() && tauto::program::is_source_file(&path) {
            if files.len() == MAX_FILES || entry.metadata()?.len() > MAX_BYTES as u64 {
                return Err(io::Error::other("source bundle exceeds limit"));
            }
            let canonical = path.canonicalize()?;
            let relative = canonical
                .strip_prefix(root)
                .map_err(|_| io::Error::other("source escapes root"))?;
            let id = relative
                .components()
                .map(|p| {
                    p.as_os_str()
                        .to_str()
                        .ok_or_else(|| io::Error::other("non-UTF-8 source path"))
                })
                .collect::<Result<Vec<_>, _>>()?
                .join("/");
            if id
                .chars()
                .any(|c| matches!(c, '\\' | ':' | '\n' | '\r' | '\t' | '\0'))
            {
                return Err(io::Error::other("invalid module path"));
            }
            let source = fs::read_to_string(&canonical)?;
            *bytes += source.len() + id.len();
            if *bytes > MAX_BYTES {
                return Err(io::Error::other("source bundle exceeds limit"));
            }
            files.push((id, source));
        }
    }
    Ok(())
}
