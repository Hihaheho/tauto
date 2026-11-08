//! Content-addressed native test tools. Only executables are reused; each
//! invocation still runs the tote, including its independent proof checker.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use tauto_syntax::{Sha256, sha256_hex};

type Result<T> = std::result::Result<T, String>;
const FORMAT: &str = "tauto-native-artifact-1";

/// The environment is hashed, never persisted: flags, target, profile,
/// wrappers, feature controls and backend switches all affect the identity.
fn environment() -> Vec<(OsString, OsString)> {
    normalized_environment(std::env::vars_os())
}

fn normalized_environment(
    vars: impl IntoIterator<Item = (OsString, OsString)>,
) -> Vec<(OsString, OsString)> {
    let mut vars: Vec<_> = vars
        .into_iter()
        // The reusable launcher clears test-runner metadata and Cargo's
        // validated caller library path; the compiler supplies its own paths.
        .filter(|(key, _)| !caller_metadata(key))
        .collect();
    vars.sort();
    vars
}

fn caller_metadata(key: &std::ffi::OsStr) -> bool {
    key == "LD_LIBRARY_PATH"
        || key == "DYLD_FALLBACK_LIBRARY_PATH"
        || key == "CARGO_TARGET_DIR"
        || key == "CARGO_BUILD_BUILD_DIR"
        || key == "TAUTO_SELFHOST_CACHE_TRACE"
        || key == "_"
        || key == "NEXTEST"
        || key
            .to_str()
            .is_some_and(|k| k.starts_with("CARGO_BIN_EXE_") || k.starts_with("NEXTEST_"))
}

fn normalize_command(command: &mut Command, keys: impl IntoIterator<Item = OsString>) {
    for key in keys {
        if caller_metadata(&key) {
            command.env_remove(key);
        }
    }
}

fn compiler_environment(
    command: &mut Command,
    caller_keys: impl IntoIterator<Item = OsString>,
    compiler_target: &Path,
    tote_target: &Path,
) {
    normalize_command(command, caller_keys);
    command
        .env("TAUTO_TARGET_DIR", tote_target)
        .env("CARGO_TARGET_DIR", compiler_target)
        .env("CARGO_BUILD_BUILD_DIR", compiler_target);
}

struct Digest(Sha256);
impl Digest {
    fn new() -> Self {
        let mut out = Self(Sha256::new());
        out.add(FORMAT.as_bytes());
        out
    }
    fn add(&mut self, bytes: &[u8]) {
        self.0.update(&(bytes.len() as u64).to_le_bytes());
        self.0.update(bytes);
    }
    fn path(&mut self, path: &Path) {
        self.add(path.as_os_str().as_encoded_bytes());
    }
    fn finish(self) -> String {
        self.0.finish_hex()
    }
}

fn err(path: &Path, e: impl std::fmt::Display) -> String {
    format!("{}: {e}", path.display())
}

/// Missing optional files are part of the identity, not silently omitted.
fn digest_files(files: &BTreeSet<PathBuf>, extra: &[u8]) -> Result<String> {
    let mut digest = Digest::new();
    digest.add(extra);
    for path in files {
        digest.path(path);
        for ancestor in path.ancestors() {
            reject_link(ancestor)?;
        }
        match fs::read(path) {
            Ok(bytes) => {
                digest.add(b"file");
                digest.add(&bytes);
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => digest.add(b"missing"),
            Err(e) => return Err(err(path, e)),
        }
    }
    Ok(digest.finish())
}

fn tree(dir: &Path, files: &mut BTreeSet<PathBuf>, compiler: bool) -> Result<()> {
    if !dir.exists() {
        files.insert(dir.to_path_buf());
        return Ok(());
    }
    for entry in fs::read_dir(dir).map_err(|e| err(dir, e))? {
        let entry = entry.map_err(|e| err(dir, e))?;
        let path = entry.path();
        let name = entry.file_name();
        // Build output is not a compiler input. Hidden syntax tables are.
        if name == "target"
            || name == ".git"
            || (compiler && (name == "tests" || name == "benches"))
        {
            continue;
        }
        let kind = entry.file_type().map_err(|e| err(&path, e))?;
        if kind.is_symlink() {
            return Err(err(&path, "cache inputs must not contain symlinks"));
        } else if kind.is_dir() {
            tree(&path, files, compiler)?;
        } else if kind.is_file() {
            files.insert(path);
        }
    }
    Ok(())
}

fn manifests(
    dir: &Path,
    seen: &mut BTreeSet<PathBuf>,
    files: &mut BTreeSet<PathBuf>,
) -> Result<bool> {
    let dir = dir.canonicalize().map_err(|e| err(dir, e))?;
    if !seen.insert(dir.clone()) {
        return Ok(true);
    }
    let manifest = tauto::manifest::load(&dir)?;
    let mut closed = manifest.rust.bridge.is_none()
        && manifest.rust.dependencies.is_empty()
        && manifest.rust.executor.as_deref() != Some("tokio");
    files.insert(dir.join("Tauto.eure"));
    files.extend(manifest.rust.bindings.iter().map(|p| dir.join(p)));
    files.extend(tauto::program::package_source_files(&dir)?);
    for (name, dependency) in &manifest.dependencies {
        let target = tauto::manifest::dependency_dir(&dir, name, dependency)?;
        closed &= manifests(&target, seen, files)?;
    }
    Ok(closed)
}

fn formatter_configuration(root: &Path, files: &mut BTreeSet<PathBuf>) -> bool {
    let Some(home) = std::env::var_os("HOME").map(PathBuf::from) else {
        return false;
    };
    let config = std::env::var_os("XDG_CONFIG_HOME").map(PathBuf::from);
    if !home.is_absolute() || config.as_ref().is_some_and(|p| !p.is_absolute()) {
        return false;
    }
    formatter_config_paths(root, &home, config.as_deref(), files)
}

fn formatter_config_paths(
    root: &Path,
    home: &Path,
    config: Option<&Path>,
    files: &mut BTreeSet<PathBuf>,
) -> bool {
    let mut dirs: Vec<_> = root.ancestors().map(Path::to_path_buf).collect();
    dirs.extend([
        home.to_path_buf(),
        home.join(".config/rustfmt"),
        home.join("Library/Application Support/rustfmt"),
        home.join("Library/Preferences/rustfmt"),
    ]);
    if let Some(config) = config {
        dirs.push(config.join("rustfmt"));
    }
    let mut closed = true;
    for dir in dirs {
        for name in ["rustfmt.toml", ".rustfmt.toml"] {
            let path = dir.join(name);
            // Formatter settings can refer to further files. Unknown settings
            // keep the normal build behavior without executable reuse.
            closed &= !path.exists();
            files.insert(path);
        }
    }
    closed
}

fn syntax_tables(files: &mut BTreeSet<PathBuf>) -> Result<()> {
    let dirs: BTreeSet<_> = files
        .iter()
        .flat_map(|p| p.parent().into_iter().flat_map(Path::ancestors))
        .map(|p| p.join(".tauto-syntax"))
        .collect();
    for dir in dirs {
        if let Some(parent) = dir.parent() {
            files.insert(parent.join("Tauto.eure"));
        }
        tree(&dir, files, false)?;
    }
    Ok(())
}

/// Discovery is repeated when a manifest, source or directory membership
/// changes. A warm request hashes the known include files without reparsing
/// the whole compiler tote; new imports are discovered on the next edit.
fn tote_files(dir: &Path) -> Result<(BTreeSet<PathBuf>, bool)> {
    type Discovery = BTreeMap<PathBuf, (String, Vec<PathBuf>)>;
    static DISCOVERED: OnceLock<Mutex<Discovery>> = OnceLock::new();
    let mut files = BTreeSet::new();
    let closed = manifests(dir, &mut BTreeSet::new(), &mut files)?;
    syntax_tables(&mut files)?;
    let mut known = DISCOVERED
        .get_or_init(Default::default)
        .lock()
        .map_err(|e| e.to_string())?;
    let mut discovery_files = files.clone();
    if let Some((_, imports)) = known.get(dir) {
        discovery_files.extend(imports.iter().cloned());
    }
    syntax_tables(&mut discovery_files)?;
    let discovery = digest_files(&discovery_files, b"discovery")?;
    let imports = match known.get(dir) {
        Some((saved, imports)) if *saved == discovery => imports.clone(),
        _ => {
            let imports = tauto::program::tote_inputs(dir)?;
            discovery_files = files.clone();
            discovery_files.extend(imports.iter().cloned());
            syntax_tables(&mut discovery_files)?;
            let discovery = digest_files(&discovery_files, b"discovery")?;
            known.insert(dir.to_path_buf(), (discovery, imports.clone()));
            imports
        }
    };
    files.extend(imports);
    syntax_tables(&mut files)?;
    Ok((files, closed))
}

fn compiler_files(root: &Path, files: &mut BTreeSet<PathBuf>) -> Result<bool> {
    tree(&root.join("crates"), files, true)?;
    tree(&root.join("std/prelude"), files, false)?;
    for name in [
        "Cargo.toml",
        "Cargo.lock",
        "Tauto.eure",
        "rust-toolchain",
        "rust-toolchain.toml",
    ] {
        files.insert(root.join(name));
    }
    // Cargo reads configuration at the working directory and its ancestors,
    // and from CARGO_HOME; both spellings and absent candidates matter.
    for dir in root.ancestors() {
        for name in [".cargo/config", ".cargo/config.toml"] {
            files.insert(dir.join(name));
        }
    }
    let home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|p| PathBuf::from(p).join(".cargo")));
    if let Some(home) = home {
        files.insert(home.join("config"));
        files.insert(home.join("config.toml"));
    }
    let configurations: Vec<_> = files
        .iter()
        .filter(|p| {
            matches!(
                p.file_name().and_then(|n| n.to_str()),
                Some("config" | "config.toml")
            )
        })
        .cloned()
        .collect();
    let mut closed = true;
    for path in configurations {
        match fs::read_to_string(&path) {
            Ok(text) => match configuration_inputs(&text) {
                Some(inputs) => files.extend(inputs),
                None => closed = false,
            },
            Err(_) => closed &= !path.exists(),
        }
    }
    Ok(closed && formatter_configuration(root, files))
}

/// Certificate bundles are build inputs too. Only literal absolute paths
/// are followed; other HTTP settings leave discovery open.
fn configuration_inputs(text: &str) -> Option<BTreeSet<PathBuf>> {
    let mut inputs = BTreeSet::new();
    let mut ordinary = String::new();
    let mut http = false;
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            http = trimmed == "[http]";
            if http {
                continue;
            }
        }
        if http {
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            let (key, value) = trimmed.split_once('=')?;
            if key.trim() != "cainfo" {
                return None;
            }
            let value = value.trim().strip_prefix('"')?.strip_suffix('"')?;
            if value.contains(['"', '\\']) {
                return None;
            }
            let path = PathBuf::from(value);
            if !path.is_absolute() {
                return None;
            }
            inputs.insert(path);
        } else {
            ordinary.push_str(line);
            ordinary.push('\n');
        }
    }
    closed_config(&ordinary).then_some(inputs)
}

/// Unknown configuration may name other files or arbitrary build tools. It
/// still builds normally, but cannot use a closed-input executable cache.
fn closed_config(text: &str) -> bool {
    text.lines().all(|line| {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            return true;
        }
        if line.starts_with('[') {
            return matches!(line, "[build]" | "[registry]" | "[resolver]")
                || line.starts_with("[profile.");
        }
        let Some((key, value)) = line.split_once('=') else {
            return false;
        };
        match key.trim() {
            "global-min-publish-age"
            | "incompatible-publish-age"
            | "jobs"
            | "target-dir"
            | "opt-level"
            | "debug"
            | "strip"
            | "debug-assertions"
            | "overflow-checks"
            | "lto"
            | "panic"
            | "incremental"
            | "codegen-units" => true,
            "rustflags" => {
                let compact: String = value.chars().filter(|c| !c.is_whitespace()).collect();
                matches!(compact.as_str(), "[]" | "[\"-Znext-solver=coherence\"]")
            }
            _ => false,
        }
    })
}

fn executable_path(command: &std::ffi::OsStr) -> Result<PathBuf> {
    let path = Path::new(command);
    let found = if path.components().count() > 1 {
        Some(path.to_path_buf())
    } else {
        std::env::var_os("PATH").and_then(|p| {
            std::env::split_paths(&p)
                .map(|dir| dir.join(path))
                .find(|p| p.is_file())
        })
    }
    .ok_or_else(|| format!("{}: executable not found", command.to_string_lossy()))?;
    found.canonicalize().map_err(|e| err(&found, e))
}

/// Rustup installs `cargo`, `rustc` and `rustfmt` as links to one proxy that
/// selects a toolchain from the working directory and environment. Identity
/// is taken from the binary the proxy would run, not from the proxy itself.
fn toolchain_tool(command: &std::ffi::OsStr, root: &Path) -> Result<PathBuf> {
    let path = executable_path(command)?;
    if path.file_stem().is_none_or(|s| s != "rustup") {
        return Ok(path);
    }
    let name = Path::new(command)
        .file_name()
        .ok_or_else(|| format!("{}: no tool name", command.to_string_lossy()))?;
    let out = Command::new(&path)
        .args(["which", "--"])
        .arg(name)
        .current_dir(root)
        .output()
        .map_err(|e| err(&path, e))?;
    if !out.status.success() {
        return Err(format!(
            "rustup which {} failed: {}",
            name.to_string_lossy(),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let found = PathBuf::from(
        String::from_utf8(out.stdout)
            .map_err(|e| e.to_string())?
            .trim(),
    );
    found.canonicalize().map_err(|e| err(&found, e))
}

#[cfg(test)]
fn tool(command: &std::ffi::OsStr, root: &Path) -> Result<Vec<u8>> {
    let path = executable_path(command)?;
    let out = Command::new(command)
        .arg("-vV")
        .current_dir(root)
        .output()
        .map_err(|e| format!("{}: {e}", command.to_string_lossy()))?;
    if !out.status.success() {
        return Err(format!(
            "{} -vV failed: {}",
            command.to_string_lossy(),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let mut digest = Digest::new();
    digest.path(&path);
    digest.add(checksum(&path)?.as_bytes());
    digest.add(&out.stdout);
    Ok(digest.finish().into_bytes())
}

fn untracked_override(key: &std::ffi::OsStr, value: &std::ffi::OsStr) -> bool {
    if value.is_empty() {
        return false;
    }
    let name = key.to_string_lossy();
    (name.starts_with("LD_") && name != "LD_LIBRARY_PATH")
        || (name.starts_with("CARGO_TARGET_")
            && ["_LINKER", "_RUNNER", "_AR"]
                .iter()
                .any(|suffix| name.ends_with(suffix)))
        || [
            "RUSTC_WRAPPER",
            "RUSTC_WORKSPACE_WRAPPER",
            "CARGO_BUILD_RUSTC_WRAPPER",
            "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
            "CARGO_BUILD_RUSTC",
            "RUSTFMT",
            "RUST_TARGET_PATH",
            "LD_PRELOAD",
            "LIBRARY_PATH",
        ]
        .iter()
        .any(|name| key == *name)
}

fn closed_environment() -> bool {
    for name in ["CARGO_HOME", "HOME"] {
        if std::env::var_os(name).is_some_and(|v| !Path::new(&v).is_absolute()) {
            return false;
        }
    }
    if std::env::var_os("PATH").is_none_or(|v| std::env::split_paths(&v).any(|p| !p.is_absolute()))
    {
        return false;
    }
    for (key, value) in std::env::vars_os() {
        if untracked_override(&key, &value) {
            trace(&format!(
                "untracked environment key: {}",
                key.to_string_lossy()
            ));
            return false;
        }
        let key = key.to_string_lossy();
        let value = value.to_string_lossy();
        if (key.starts_with("DYLD_")
            && !(cfg!(target_os = "macos") && key == "DYLD_FALLBACK_LIBRARY_PATH"))
            || (key.starts_with("CARGO_TARGET_") && key.ends_with("_LINKER"))
            || (key.contains("RUSTFLAGS")
                && !value
                    .split([' ', '\x1f'])
                    .all(|flag| matches!(flag, "" | "-Znext-solver=coherence")))
            || (key == "CARGO_BUILD_TARGET" && value.ends_with(".json"))
            || key.ends_with("_CODEGEN_BACKEND")
            || (key == "RUSTC"
                && Path::new(value.as_ref())
                    .file_stem()
                    .is_none_or(|s| s != "rustc"))
        {
            trace(&format!("untracked environment key: {key}"));
            return false;
        }
    }
    true
}

#[cfg(unix)]
fn toolchain_snapshot(sysroot: &Path) -> Result<Option<(BTreeSet<PathBuf>, String)>> {
    use std::os::unix::fs::MetadataExt;
    let mut files = BTreeSet::from([
        sysroot.join("bin/rustc"),
        sysroot.join("bin/cargo"),
        sysroot.join("bin/rustfmt"),
    ]);
    fn collect(dir: &Path, files: &mut BTreeSet<PathBuf>) -> Result<()> {
        for entry in fs::read_dir(dir).map_err(|e| err(dir, e))? {
            let entry = entry.map_err(|e| err(dir, e))?;
            let path = entry.path();
            if entry.file_type().map_err(|e| err(&path, e))?.is_dir() {
                collect(&path, files)?;
            } else {
                files.insert(path);
            }
        }
        Ok(())
    }
    collect(&sysroot.join("lib"), &mut files)?;
    let mut stamps = Digest::new();
    for path in &files {
        let canonical = path.canonicalize().map_err(|e| err(path, e))?;
        if !canonical.starts_with(sysroot) || !canonical.is_file() {
            return Ok(None);
        }
        stamps.path(path);
        stamps.path(&canonical);
        for metadata in [fs::symlink_metadata(path), fs::metadata(path)] {
            let m = metadata.map_err(|e| err(path, e))?;
            // Local nanosecond ctime notices replacement and byte edits even
            // when mtime was restored. Coarse or unsupported stamps bypass.
            if m.ctime_nsec() == 0 {
                return Ok(None);
            }
            for value in [
                m.dev(),
                m.ino(),
                m.size(),
                m.mode() as u64,
                m.mtime() as u64,
                m.mtime_nsec() as u64,
                m.ctime() as u64,
                m.ctime_nsec() as u64,
            ] {
                stamps.add(&value.to_le_bytes());
            }
        }
    }
    Ok(Some((files, stamps.finish())))
}

#[cfg(unix)]
fn toolchain_tree_identity(sysroot: &Path) -> Result<Option<String>> {
    type Memo = BTreeMap<PathBuf, (String, String)>;
    static MEMO: OnceLock<Mutex<Memo>> = OnceLock::new();
    let Some((files, stamp)) = toolchain_snapshot(sysroot)? else {
        return Ok(None);
    };
    let mut memo = MEMO
        .get_or_init(Default::default)
        .lock()
        .map_err(|e| e.to_string())?;
    if let Some((old, digest)) = memo.get(sysroot)
        && old == &stamp
    {
        return Ok(Some(digest.clone()));
    }
    let mut digest = Digest::new();
    let mut contents = BTreeMap::new();
    for path in files {
        let canonical = path.canonicalize().map_err(|e| err(&path, e))?;
        let hash = match contents.get(&canonical) {
            Some(hash) => hash,
            None => contents.entry(canonical).or_insert(checksum(&path)?),
        };
        digest.path(&path);
        digest.add(hash.as_bytes());
    }
    if toolchain_snapshot(sysroot)?.is_none_or(|(_, after)| stamp != after) {
        return Err("toolchain changed while its identity was read".into());
    }
    let digest = digest.finish();
    memo.insert(sysroot.to_path_buf(), (stamp, digest.clone()));
    Ok(Some(digest))
}

fn closed_library_paths(root: &Path, sysroot: &Path) -> bool {
    let target = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::current_exe().ok().and_then(|exe| {
                exe.ancestors()
                    .find(|dir| dir.join(".rustc_info.json").is_file())
                    .map(Path::to_path_buf)
            })
        })
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target"));
    let target = tauto::program::canonical_path(&root.join(target));
    if let Some(value) = std::env::var_os("LD_LIBRARY_PATH")
        && !known_library_paths(&value, &target, sysroot)
    {
        return false;
    }
    if let Some(value) = std::env::var_os("DYLD_FALLBACK_LIBRARY_PATH") {
        let Some(home) = std::env::var_os("HOME").map(PathBuf::from) else {
            return false;
        };
        if !cfg!(target_os = "macos")
            || !known_fallback_library_paths(&value, &target, sysroot, &home)
        {
            return false;
        }
    }
    true
}

fn known_fallback_library_paths(
    value: &std::ffi::OsStr,
    target: &Path,
    sysroot: &Path,
    home: &Path,
) -> bool {
    let defaults = [
        home.join("lib"),
        PathBuf::from("/usr/local/lib"),
        PathBuf::from("/usr/lib"),
    ];
    std::env::split_paths(value).all(|path| {
        let known = defaults.contains(&path) || known_library_path(&path, target, sysroot);
        if !known {
            trace(&format!(
                "untracked fallback library directory: {}",
                path.display()
            ));
        }
        known
    })
}

fn known_library_paths(value: &std::ffi::OsStr, target: &Path, sysroot: &Path) -> bool {
    std::env::split_paths(value).all(|path| known_library_path(&path, target, sysroot))
}

fn known_library_path(path: &Path, target: &Path, sysroot: &Path) -> bool {
    if !path.is_absolute() {
        return false;
    }
    let path = tauto::program::canonical_path(&path);
    if path.starts_with(sysroot.join("lib")) {
        return true;
    }
    let Ok(relative) = path.strip_prefix(target) else {
        return false;
    };
    if !target.join(".rustc_info.json").is_file() {
        return false;
    }
    let Some(components): Option<Vec<_>> = relative.iter().map(|s| s.to_str()).collect() else {
        return false;
    };
    // Only Cargo output shapes in the caller's established target are
    // normalized. That local Cargo target is a trusted build boundary.
    matches!(
        components.as_slice(),
        ["debug" | "release"]
            | ["debug" | "release", "deps"]
            | ["debug" | "release", "build", _, _, "out"]
            | ["debug" | "release", "build", _, "out"]
    )
}

#[cfg(unix)]
fn toolchain_identity(root: &Path, rustc: &std::ffi::OsStr) -> Result<Option<String>> {
    let executable = toolchain_tool(rustc, root)?;
    let Some(installed) = executable.parent().and_then(Path::parent) else {
        return Ok(bypass("rustc has no installation directory"));
    };
    if !closed_library_paths(root, installed) {
        return Ok(bypass(
            "dynamic library search paths name unknown directories",
        ));
    }
    let mut command = Command::new(rustc);
    normalize_command(&mut command, std::env::vars_os().map(|(key, _)| key));
    let out = command
        .args(["--print", "sysroot"])
        .current_dir(root)
        .output()
        .map_err(|e| format!("rustc sysroot: {e}"))?;
    if !out.status.success() {
        return Ok(bypass("rustc --print sysroot failed"));
    }
    let sysroot = PathBuf::from(
        String::from_utf8(out.stdout)
            .map_err(|e| e.to_string())?
            .trim(),
    )
    .canonicalize()
    .map_err(|e| e.to_string())?;
    if toolchain_tool(rustc, root)?
        != sysroot
            .join("bin/rustc")
            .canonicalize()
            .map_err(|e| e.to_string())?
    {
        return Ok(bypass("rustc is not the sysroot's rustc"));
    }
    let cargo = sysroot
        .join("bin/cargo")
        .canonicalize()
        .map_err(|e| e.to_string())?;
    if toolchain_tool("rustfmt".as_ref(), root)?
        != sysroot
            .join("bin/rustfmt")
            .canonicalize()
            .map_err(|e| e.to_string())?
    {
        return Ok(bypass("rustfmt is not the sysroot's rustfmt"));
    }
    for command in [
        OsString::from(env!("CARGO")),
        std::env::var_os("CARGO").unwrap_or_else(|| env!("CARGO").into()),
    ] {
        if toolchain_tool(&command, root)? != cargo {
            return Ok(bypass("cargo is not the sysroot's cargo"));
        }
    }
    if !closed_library_paths(root, &sysroot) {
        return Ok(bypass(
            "dynamic library search paths name unknown directories",
        ));
    }
    toolchain_tree_identity(&sysroot)
}

#[cfg(not(unix))]
fn toolchain_identity(_root: &Path, _rustc: &std::ffi::OsStr) -> Result<Option<String>> {
    Ok(None)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Identity {
    /// Toolchain, environment, and checkout only. Names the Cargo build
    /// directories, which Cargo itself keeps correct across source edits.
    build: String,
    compiler: String,
    tote: String,
}

fn keys(
    compiler_files: &BTreeSet<PathBuf>,
    tote_files: &BTreeSet<PathBuf>,
    context: &[u8],
) -> Result<Identity> {
    let build = sha256_hex(context);
    let compiler = digest_files(compiler_files, context)?;
    let tote = digest_files(tote_files, compiler.as_bytes())?;
    Ok(Identity {
        build,
        compiler,
        tote,
    })
}

fn input_key(root: &Path, dir: &Path) -> Result<Option<Identity>> {
    let (files, closed) = tote_files(dir)?;
    let mut compiler = BTreeSet::new();
    if !compiler_files(root, &mut compiler)? {
        return Ok(bypass("open compiler configuration"));
    }
    if !closed {
        return Ok(bypass("open tote configuration"));
    }
    if !closed_environment() {
        return Ok(bypass("open build environment"));
    }
    for command in [
        OsString::from(env!("CARGO")),
        std::env::var_os("CARGO").unwrap_or_else(|| env!("CARGO").into()),
        std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into()),
    ] {
        let written = Path::new(&command);
        if written.components().count() > 1 && !written.is_absolute() {
            return Ok(bypass("relative tool path"));
        }
        let executable = toolchain_tool(&command, root)?;
        if !matches!(
            executable.file_stem().and_then(|s| s.to_str()),
            Some("cargo" | "rustc")
        ) {
            return Ok(bypass("tool is not named cargo or rustc"));
        }
        let mut head = [0; 2];
        File::open(&executable)
            .and_then(|mut f| f.read_exact(&mut head))
            .map_err(|e| err(&executable, e))?;
        if head == *b"#!" {
            return Ok(bypass("tool is a script"));
        }
    }
    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let Some(toolchain) = toolchain_identity(root, &rustc)? else {
        return Ok(None);
    };
    let mut extra = Digest::new();
    extra.add(toolchain.as_bytes());
    extra.path(root);
    extra.add(b"cargo run --locked -q -p tauto-cli -- build --release; native rust executable");
    for (key, value) in environment() {
        extra.add(key.as_encoded_bytes());
        extra.add(value.as_encoded_bytes());
    }
    Ok(Some(keys(&compiler, &files, extra.finish().as_bytes())?))
}

fn cache_root(root: &Path) -> PathBuf {
    let target = std::env::var_os("TAUTO_TARGET_DIR")
        .or_else(|| std::env::var_os("CARGO_TARGET_DIR"))
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join("target"));
    let target = if target.is_absolute() {
        target
    } else {
        root.join(target)
    };
    target.join("selfhost-harness-cache/v1")
}

fn checksum(path: &Path) -> Result<String> {
    let mut file = File::open(path).map_err(|e| err(path, e))?;
    let mut hash = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = file.read(&mut buffer).map_err(|e| err(path, e))?;
        if count == 0 {
            break;
        }
        hash.update(&buffer[..count]);
    }
    Ok(hash.finish_hex())
}

fn verified(entry: &Path, key: &str) -> Option<PathBuf> {
    let bin = entry.join(format!("tool{}", std::env::consts::EXE_SUFFIX));
    reject_link(entry).ok()?;
    reject_link(&entry.join("artifact")).ok()?;
    let record = fs::read_to_string(entry.join("artifact")).ok()?;
    let metadata = fs::symlink_metadata(&bin).ok()?;
    if !metadata.is_file() || metadata.len() == 0 {
        return None;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if metadata.permissions().mode() & 0o111 == 0 {
            return None;
        }
    }
    let wanted = format!(
        "{FORMAT}\n{key}\n{}\n{}\n",
        metadata.len(),
        checksum(&bin).ok()?
    );
    (record == wanted).then_some(bin)
}

fn unique_id() -> String {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    format!(
        "{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )
}

fn reject_link(path: &Path) -> Result<()> {
    match fs::symlink_metadata(path) {
        Ok(m) if m.file_type().is_symlink() => Err(err(path, "cache paths must not be symlinks")),
        Ok(_) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(err(path, e)),
    }
}

fn safe_dir(path: &Path) -> Result<()> {
    let mut prefix = PathBuf::new();
    for part in path.components() {
        prefix.push(part);
        reject_link(&prefix)?;
        match fs::create_dir(&prefix) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists && prefix.is_dir() => {}
            Err(e) => return Err(err(&prefix, e)),
        }
        reject_link(&prefix)?;
    }
    Ok(())
}

fn reject_tree_links(dir: &Path) -> Result<()> {
    for entry in fs::read_dir(dir).map_err(|e| err(dir, e))? {
        let entry = entry.map_err(|e| err(dir, e))?;
        let path = entry.path();
        let kind = entry.file_type().map_err(|e| err(&path, e))?;
        if kind.is_symlink() {
            return Err(err(&path, "compiler cache must not contain symlinks"));
        }
        if kind.is_dir() {
            reject_tree_links(&path)?;
        }
    }
    Ok(())
}

#[cfg(test)]
fn cached_build(
    cache: &Path,
    namespace: &str,
    key: &str,
    build: impl FnOnce(&Path) -> Result<PathBuf>,
) -> Result<PathBuf> {
    build_artifact(cache, namespace, Some(key), build)
}

fn bypass<T>(reason: &str) -> Option<T> {
    trace(&format!("identity unavailable: {reason}"));
    None
}

fn trace(message: &str) {
    if std::env::var_os("TAUTO_SELFHOST_CACHE_TRACE").is_some() {
        eprintln!("tauto selfhost cache: {message}");
    }
}

/// One process owns a tote's build directory at a time; OS locks are released
/// on process exit. The record is renamed last, after copying and hashing the
/// executable. A failed build never creates a valid record.
fn build_artifact(
    cache: &Path,
    namespace: &str,
    key: Option<&str>,
    build: impl FnOnce(&Path) -> Result<PathBuf>,
) -> Result<PathBuf> {
    let tote = cache.join(namespace);
    safe_dir(&tote)?;
    let lock_path = tote.join("lock");
    reject_link(&lock_path)?;
    let lock = File::options()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(&lock_path)
        .map_err(|e| err(&lock_path, e))?;
    lock.lock().map_err(|e| err(&lock_path, e))?;
    let entry = if let Some(key) = key {
        tote.join(key)
    } else {
        loop {
            let entry = tote.join(format!("uncached-{}", unique_id()));
            match fs::create_dir(&entry) {
                Ok(()) => break entry,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(err(&entry, e)),
            }
        }
    };
    reject_link(&entry)?;
    for name in ["artifact", "tool", "tool.exe"] {
        reject_link(&entry.join(name))?;
    }
    if let Some(key) = key
        && let Some(bin) = verified(&entry, key)
    {
        trace("hit: input identity and executable SHA-256 verified");
        return Ok(bin);
    }
    trace(if key.is_some() {
        "miss: building an isolated native artifact"
    } else {
        "bypass: building a one-off native artifact"
    });
    // Create rather than adopt a scratch directory: only a directory created
    // by this call can be removed. Published paths remain valid until cleaned
    // explicitly together with the target directory.
    let work = loop {
        let work = tote.join(format!("work-{}", unique_id()));
        match fs::create_dir(&work) {
            Ok(()) => break work,
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(err(&work, e)),
        }
    };
    let result = (|| {
        let source = build(&work)?;
        reject_link(&source)?;
        if !source
            .canonicalize()
            .map_err(|e| err(&source, e))?
            .starts_with(work.canonicalize().map_err(|e| err(&work, e))?)
        {
            return Err("build returned an executable outside its staging directory".into());
        }
        let source_meta = fs::metadata(&source).map_err(|e| err(&source, e))?;
        if !source_meta.is_file() || source_meta.len() == 0 {
            return Err(err(&source, "build returned no executable"));
        }
        safe_dir(&entry)?;
        let bin = entry.join(format!("tool{}", std::env::consts::EXE_SUFFIX));
        let pending = entry.join(format!("tool.pending-{}", unique_id()));
        let mut copy = File::options()
            .write(true)
            .create_new(true)
            .open(&pending)
            .map_err(|e| err(&pending, e))?;
        std::io::copy(
            &mut File::open(&source).map_err(|e| err(&source, e))?,
            &mut copy,
        )
        .map_err(|e| err(&pending, e))?;
        copy.set_permissions(source_meta.permissions())
            .map_err(|e| err(&pending, e))?;
        copy.sync_all().map_err(|e| err(&pending, e))?;
        drop(copy);
        let digest = checksum(&pending)?;
        if checksum(&source)? != digest {
            return Err("native executable changed while publishing".into());
        }
        File::open(&pending)
            .and_then(|f| f.sync_all())
            .map_err(|e| err(&pending, e))?;
        fs::rename(&pending, &bin).map_err(|e| err(&bin, e))?;
        let Some(key) = key else {
            return Ok(bin);
        };
        let pending_record = entry.join(format!("artifact.pending-{}", unique_id()));
        let mut record = File::options()
            .write(true)
            .create_new(true)
            .open(&pending_record)
            .map_err(|e| err(&pending_record, e))?;
        write!(record, "{FORMAT}\n{key}\n{}\n{digest}\n", source_meta.len())
            .map_err(|e| err(&pending_record, e))?;
        record.sync_all().map_err(|e| err(&pending_record, e))?;
        fs::rename(&pending_record, entry.join("artifact")).map_err(|e| err(&entry, e))?;
        verified(&entry, key).ok_or_else(|| "native artifact verification failed".into())
    })();
    let _ = fs::remove_dir_all(&work);
    if key.is_none() && result.is_err() {
        let _ = fs::remove_dir_all(&entry);
    }
    result
}

#[cfg(test)]
static TEST_COMPILER_INVOCATIONS: AtomicU64 = AtomicU64::new(0);

pub(super) fn build_tote(name: &str) -> Result<PathBuf> {
    if name.is_empty()
        || !name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
    {
        return Err("invalid tote name".into());
    }
    let root = super::root().canonicalize().map_err(|e| e.to_string())?;
    let dir = root.join("totes").join(name);
    // Cache-only discovery failures do not change which programs can build.
    let key = match input_key(&root, &dir) {
        Ok(key) => key,
        Err(error) => {
            trace(&format!("identity unavailable: {error}"));
            None
        }
    };
    let namespace = sha256_hex(dir.as_os_str().as_encoded_bytes());
    let cache = cache_root(&root);
    let result = build_artifact(
        &cache,
        &namespace,
        key.as_ref().map(|k| k.tote.as_str()),
        |work| {
            // The artifact key changes with every source edit; the Cargo
            // build directories do not, so an edit recompiles only what
            // changed instead of the whole release compiler and its
            // dependencies. Cargo locks and fingerprints these directories.
            let (compiler_target, tote_target) = match &key {
                Some(k) => (
                    cache.join("compiler").join(&k.build),
                    cache.join(&namespace).join(format!("target-{}", k.build)),
                ),
                None => (work.join("compiler"), work.join("tote")),
            };
            for dir in [&compiler_target, &tote_target] {
                safe_dir(dir)?;
                reject_tree_links(dir)?;
            }
            #[cfg(test)]
            TEST_COMPILER_INVOCATIONS.fetch_add(1, Ordering::Relaxed);
            let mut command = Command::new(env!("CARGO"));
            command
                .current_dir(&root)
                .args([
                    "run",
                    "--locked",
                    "-q",
                    "-p",
                    "tauto-cli",
                    "--",
                    "build",
                    "--release",
                ])
                .arg(format!("totes/{name}"));
            if key.is_some() {
                trace("normalized caller Cargo process metadata for compiler execution");
            }
            compiler_environment(
                &mut command,
                std::env::vars_os().filter_map(|(name, _)| key.is_some().then_some(name)),
                &compiler_target,
                &tote_target,
            );
            let out = command.output().map_err(|e| format!("cargo: {e}"))?;
            if !out.status.success() {
                return Err(format!(
                    "tauto build totes/{name} failed: {}",
                    String::from_utf8_lossy(&out.stderr)
                ));
            }
            let printed = String::from_utf8(out.stdout).map_err(|e| e.to_string())?;
            let path = PathBuf::from(printed.lines().last().ok_or("build returned no path")?);
            let path = if path.is_absolute() {
                path
            } else {
                root.join(path)
            };
            // A source edit during compilation must not publish under the old key.
            if key.is_some() && input_key(&root, &dir)? != key {
                return Err(
                    "native build inputs changed during compilation; retry the build".into(),
                );
            }
            // Publish a copy from the staging directory; the build directory
            // is reused and overwritten by the next build.
            let staged = work.join(path.file_name().ok_or("build returned no file name")?);
            fs::copy(&path, &staged).map_err(|e| err(&path, e))?;
            Ok(staged)
        },
    )?;
    // A caller may have waited for another process holding the build lock.
    // If the inputs changed during that wait, the hit no longer matches them.
    if key.is_some() && input_key(&root, &dir)? != key {
        return Err(
            "native build inputs changed while acquiring the artifact; retry the build".into(),
        );
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::AtomicUsize;

    #[test]
    fn compiler_output_directories_replace_caller_metadata() {
        let mut command = Command::new("unused");
        for key in [
            "CARGO_TARGET_DIR",
            "CARGO_BUILD_BUILD_DIR",
            "TAUTO_TARGET_DIR",
            "NEXTEST_RUN_ID",
        ] {
            command.env(key, "caller");
        }
        compiler_environment(
            &mut command,
            [
                "CARGO_TARGET_DIR",
                "CARGO_BUILD_BUILD_DIR",
                "TAUTO_TARGET_DIR",
                "NEXTEST_RUN_ID",
            ]
            .map(OsString::from),
            Path::new("compiler-target"),
            Path::new("tote-target"),
        );
        let env: BTreeMap<_, _> = command.get_envs().collect();
        for key in ["CARGO_TARGET_DIR", "CARGO_BUILD_BUILD_DIR"] {
            assert_eq!(
                env[std::ffi::OsStr::new(key)],
                Some(std::ffi::OsStr::new("compiler-target"))
            );
        }
        assert_eq!(
            env[std::ffi::OsStr::new("TAUTO_TARGET_DIR")],
            Some(std::ffi::OsStr::new("tote-target"))
        );
        assert_eq!(env[std::ffi::OsStr::new("NEXTEST_RUN_ID")], None);
    }

    struct Scratch(PathBuf);
    impl Scratch {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let path = std::env::temp_dir().canonicalize().unwrap().join(format!(
                "tauto-native-cache-test-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
        fn write(&self, path: &str, text: &str) {
            let path = self.0.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, text).unwrap();
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn executable(work: &Path, text: &str) -> PathBuf {
        let path = work.join("built");
        fs::write(&path, text).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
        }
        path
    }

    fn fixture() -> Scratch {
        let s = Scratch::new();
        s.write(
            "totes/app/Tauto.eure",
            "package { name = \"app\" }\ndependencies { dep { path = \"../dep\" } }\n",
        );
        s.write(
            "totes/app/src/main.taut",
            r#"let payload := include_text!("data.txt")
perform show("payload", payload)
"#,
        );
        s.write("totes/app/src/data.txt", "alpha");
        s.write("totes/dep/Tauto.eure", "package { name = \"dep\" }\n");
        s.write(
            "totes/dep/src/lib.taut",
            r#"fn identity(x: u64): u64 { x }
"#,
        );
        s.write(
            "totes/unrelated/Tauto.eure",
            "package { name = \"unrelated\" }\n",
        );
        s.write(
            "totes/unrelated/src/main.taut",
            r#"let unrelated := 4
"#,
        );
        s.write("crates/compiler/src/lib.rs", "compiler");
        s.write("crates/tauto-rt/src/lib.rs", "runtime");
        s.write("std/prelude/Std.taut", "prelude");
        s.write("Cargo.lock", "locked dependencies");
        s.write("Cargo.toml", "compiler profiles/features");
        s.write(".cargo/config.toml", "compiler config");
        s.write("rust-toolchain.toml", "toolchain");
        s
    }

    fn fixture_key(s: &Scratch) -> String {
        let (mut files, _) = tote_files(&s.0.join("totes/app")).unwrap();
        compiler_files(&s.0, &mut files).unwrap();
        digest_files(&files, b"fixed toolchain/environment").unwrap()
    }

    #[test]
    fn mutations_invalidate_only_the_transitive_inputs_in_the_same_process() {
        let s = fixture();
        let initial = fixture_key(&s);
        assert_eq!(initial, fixture_key(&s));
        s.write("totes/unrelated/src/main.taut", "changed unrelated tote");
        assert_eq!(initial, fixture_key(&s));
        s.write("crates/compiler/tests/test.rs", "unrelated test");
        assert_eq!(initial, fixture_key(&s));
        for path in [
            "totes/app/src/main.taut",
            "totes/dep/src/lib.taut",
            "totes/app/Tauto.eure",
            "totes/dep/Tauto.eure",
            "totes/app/src/data.txt",
            "crates/compiler/src/lib.rs",
            "crates/tauto-rt/src/lib.rs",
            "std/prelude/Std.taut",
            "Cargo.lock",
            "Cargo.toml",
            ".cargo/config.toml",
            "rust-toolchain.toml",
        ] {
            let old = fs::read_to_string(s.0.join(path)).unwrap();
            s.write(path, &(old.clone() + "\n  \n"));
            assert_ne!(initial, fixture_key(&s), "{path}");
            s.write(path, &old);
            assert_eq!(initial, fixture_key(&s), "restored {path}");
        }
        s.write(
            "totes/dep/src/extra.taut",
            r#"fn extra(): u64 { 7 }
"#,
        );
        assert_ne!(initial, fixture_key(&s), "new source file");
        fs::remove_file(s.0.join("totes/dep/src/extra.taut")).unwrap();
        assert_eq!(initial, fixture_key(&s));
        s.write("totes/dep/src/.tauto-syntax/example.tables", "syntax table");
        let tables = fixture_key(&s);
        assert_ne!(initial, tables);
        s.write(
            "totes/dep/src/.tauto-syntax/example.tables",
            "changed table",
        );
        assert_ne!(tables, fixture_key(&s));
    }

    #[test]
    fn imported_files_can_introduce_further_imports_after_discovery() {
        let s = fixture();
        s.write(
            "totes/app/src/main.taut",
            r#"import "../../../imports/first.taut"
"#,
        );
        s.write(
            "imports/first.taut",
            r#"fn first(): u64 { 1 }
"#,
        );
        let before = fixture_key(&s);
        s.write(
            "imports/first.taut",
            r#"import "second.taut"
fn first(): u64 { second() }
"#,
        );
        s.write(
            "imports/second.taut",
            r#"fn second(): u64 { 2 }
"#,
        );
        let after = fixture_key(&s);
        assert_ne!(before, after);
        s.write(
            "imports/second.taut",
            r#"fn second(): u64 { 3 }
"#,
        );
        assert_ne!(after, fixture_key(&s));
    }

    #[test]
    fn path_provenance_and_build_variants_are_distinct() {
        let a = fixture();
        let b = fixture();
        assert_ne!(fixture_key(&a), fixture_key(&b));
        let (files, _) = tote_files(&a.0.join("totes/app")).unwrap();
        let base = digest_files(&files, b"rustc v1;release;host;sync=0;flags=").unwrap();
        for variant in [
            "rustc v2;release;host;sync=0;flags=",
            "rustc v1;debug;host;sync=0;flags=",
            "rustc v1;release;other;sync=0;flags=",
            "rustc v1;release;host;sync=1;flags=",
            "rustc v1;release;host;sync=0;flags=-Copt-level=1",
        ] {
            assert_ne!(base, digest_files(&files, variant.as_bytes()).unwrap());
        }
    }

    #[test]
    fn failed_builds_and_empty_artifacts_are_not_committed_or_memoized() {
        let s = Scratch::new();
        assert!(cached_build(&s.0, "app", "key", |_| Err("failed".into())).is_err());
        assert!(!s.0.join("app/key/artifact").exists());
        assert!(cached_build(&s.0, "app", "key", |work| Ok(executable(work, ""))).is_err());
        assert!(!s.0.join("app/key/artifact").exists());
        let bin = cached_build(&s.0, "app", "key", |work| Ok(executable(work, "good"))).unwrap();
        assert_eq!(fs::read_to_string(bin).unwrap(), "good");
        assert!(!fs::read_dir(s.0.join("app")).unwrap().any(|e| {
            e.unwrap()
                .file_name()
                .to_string_lossy()
                .starts_with("work-")
        }));
    }

    #[test]
    fn stale_truncated_mismatched_and_non_executable_artifacts_are_rebuilt() {
        let s = Scratch::new();
        let calls = AtomicUsize::new(0);
        let build = |work: &Path| {
            calls.fetch_add(1, Ordering::Relaxed);
            Ok(executable(work, "original executable"))
        };
        let bin = cached_build(&s.0, "app", "key", build).unwrap();
        assert_eq!(bin, cached_build(&s.0, "app", "key", build).unwrap());
        assert_eq!(calls.load(Ordering::Relaxed), 1);
        for bad in ["short", "wrong but same size!", ""] {
            fs::write(&bin, bad).unwrap();
            cached_build(&s.0, "app", "key", build).unwrap();
            assert_eq!(fs::read_to_string(&bin).unwrap(), "original executable");
        }
        fs::write(
            s.0.join("app/key/artifact"),
            "different key or incomplete record",
        )
        .unwrap();
        cached_build(&s.0, "app", "key", build).unwrap();
        assert_eq!(calls.load(Ordering::Relaxed), 5);
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&bin, fs::Permissions::from_mode(0o644)).unwrap();
            cached_build(&s.0, "app", "key", build).unwrap();
            assert_eq!(calls.load(Ordering::Relaxed), 6);
        }
    }

    #[test]
    fn concurrent_callers_publish_once_and_never_observe_partial_artifacts() {
        let s = Scratch::new();
        let calls = Arc::new(AtomicUsize::new(0));
        let barrier = Arc::new(std::sync::Barrier::new(8));
        let handles: Vec<_> = (0..8)
            .map(|_| {
                let (path, calls, barrier) = (s.0.clone(), calls.clone(), barrier.clone());
                std::thread::spawn(move || {
                    barrier.wait();
                    cached_build(&path, "app", "key", |work| {
                        calls.fetch_add(1, Ordering::Relaxed);
                        std::thread::sleep(std::time::Duration::from_millis(20));
                        Ok(executable(work, "complete executable"))
                    })
                    .unwrap()
                })
            })
            .collect();
        for handle in handles {
            assert_eq!(
                fs::read_to_string(handle.join().unwrap()).unwrap(),
                "complete executable"
            );
        }
        assert_eq!(calls.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn cache_records_never_redirect_to_an_external_executable() {
        let s = Scratch::new();
        s.write("outside", "not a build result");
        s.write(
            "app/key/artifact",
            &format!("key\n{}", s.0.join("outside").display()),
        );
        let bin = cached_build(&s.0, "app", "key", |work| Ok(executable(work, "owned"))).unwrap();
        assert_eq!(fs::read_to_string(bin).unwrap(), "owned");
        assert_eq!(
            fs::read_to_string(s.0.join("outside")).unwrap(),
            "not a build result"
        );
    }

    #[test]
    fn a_new_nested_manifest_invalidates_include_boundaries() {
        let s = fixture();
        s.write(
            "totes/app/src/main.taut",
            r#"let data := include_text!("../data.txt")
"#,
        );
        s.write("totes/app/data.txt", "outside nested boundary");
        let initial = fixture_key(&s);
        s.write(
            "totes/app/src/Tauto.eure",
            "package { name = \"nested\" }\n",
        );
        assert_ne!(initial, fixture_key(&s));
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_source_or_ancestor_bypasses_reuse() {
        use std::os::unix::fs::symlink;
        let s = fixture();
        s.write(
            "totes/app/a/main.taut",
            r#"let data := include_text!("data.txt")
"#,
        );
        s.write(
            "totes/app/b/main.taut",
            r#"let data := include_text!("data.txt")
"#,
        );
        s.write("totes/app/a/data.txt", "alpha");
        s.write("totes/app/b/data.txt", "beta");
        fs::remove_file(s.0.join("totes/app/src/main.taut")).unwrap();
        symlink("../a/main.taut", s.0.join("totes/app/src/main.taut")).unwrap();
        assert!(tote_files(&s.0.join("totes/app")).is_err());
        fs::remove_file(s.0.join("totes/app/src/main.taut")).unwrap();
        symlink("../b/main.taut", s.0.join("totes/app/src/main.taut")).unwrap();
        assert!(tote_files(&s.0.join("totes/app")).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn toolchain_memo_rehashes_byte_edits_replacement_and_membership() {
        let s = Scratch::new();
        s.write("bin/rustc", "compiler");
        s.write("bin/cargo", "builder");
        s.write("bin/rustfmt", "formatter");
        s.write("lib/runtime", "alpha");
        let initial = toolchain_tree_identity(&s.0).unwrap().unwrap();
        assert_eq!(
            Some(initial.clone()),
            toolchain_tree_identity(&s.0).unwrap()
        );
        s.write("bin/rustfmt", "changed formatter");
        assert_ne!(
            Some(initial.clone()),
            toolchain_tree_identity(&s.0).unwrap()
        );
        s.write("bin/rustfmt", "formatter");
        let path = s.0.join("lib/runtime");
        let old_modified = fs::metadata(&path).unwrap().modified().unwrap();
        s.write("lib/runtime", "bravo");
        File::options()
            .write(true)
            .open(&path)
            .unwrap()
            .set_modified(old_modified)
            .unwrap();
        let changed = toolchain_tree_identity(&s.0).unwrap().unwrap();
        assert_ne!(initial, changed);
        fs::remove_file(&path).unwrap();
        s.write("lib/runtime", "alpha");
        assert_eq!(
            Some(initial.clone()),
            toolchain_tree_identity(&s.0).unwrap()
        );
        s.write("lib/extra", "extra");
        assert_ne!(Some(initial), toolchain_tree_identity(&s.0).unwrap());
    }

    #[test]
    fn compiler_namespace_is_shared_only_for_identical_compiler_provenance() {
        let s = fixture();
        let mut compiler = BTreeSet::new();
        compiler_files(&s.0, &mut compiler).unwrap();
        let (app, _) = tote_files(&s.0.join("totes/app")).unwrap();
        let (dep, _) = tote_files(&s.0.join("totes/dep")).unwrap();
        let first = keys(&compiler, &app, b"same context").unwrap();
        let other = keys(&compiler, &dep, b"same context").unwrap();
        assert_eq!(first.compiler, other.compiler);
        assert_ne!(first.tote, other.tote);
        s.write("totes/app/src/data.txt", "changed tote");
        let changed = keys(&compiler, &app, b"same context").unwrap();
        assert_eq!(first.compiler, changed.compiler);
        assert_ne!(first.tote, changed.tote);
        s.write("crates/compiler/src/lib.rs", "changed compiler");
        let changed = keys(&compiler, &app, b"same context").unwrap();
        assert_ne!(first.compiler, changed.compiler);
        assert_ne!(first.tote, changed.tote);
        // Source edits reuse the Cargo build directories; build context does not.
        assert_eq!(first.build, changed.build);
        assert_eq!(first.build, other.build);
        let release = keys(&compiler, &app, b"other context").unwrap();
        assert_ne!(first.build, release.build);
    }

    #[test]
    fn imported_include_boundary_changes_refresh_discovery() {
        let s = fixture();
        s.write(
            "totes/app/src/main.taut",
            r#"import "../../../external/deep/main.taut"
"#,
        );
        s.write("external/Tauto.eure", "package { name = \"outer\" }\n");
        s.write("external/deep/Tauto.eure", "package { name = \"inner\" }\n");
        s.write(
            "external/deep/main.taut",
            r#"let data := include_text!("../payload.txt")
"#,
        );
        s.write("external/payload.txt", "alpha");
        let blocked = fixture_key(&s);
        fs::remove_file(s.0.join("external/deep/Tauto.eure")).unwrap();
        let allowed = fixture_key(&s);
        assert_ne!(blocked, allowed);
        s.write("external/payload.txt", "beta");
        assert_ne!(allowed, fixture_key(&s));
        let inputs = tauto::program::tote_inputs(&s.0.join("totes/app")).unwrap();
        let dependency = inputs
            .iter()
            .position(|p| tauto::program::canonical_path(p).ends_with("totes/dep/src/lib.taut"))
            .unwrap();
        let own = inputs
            .iter()
            .position(|p| p.ends_with("totes/app/src/main.taut"))
            .unwrap();
        assert!(
            dependency < own,
            "loader input order must stay dependency-first"
        );
    }

    #[test]
    fn cargo_caller_library_paths_normalize_but_custom_paths_bypass() {
        let s = Scratch::new();
        s.write("target/.rustc_info.json", "{}");
        fs::create_dir_all(s.0.join("target/debug/build/tests/first/out")).unwrap();
        fs::create_dir_all(s.0.join("target/debug/build/tests/second/out")).unwrap();
        let first = s.0.join("target/debug/build/tests/first/out");
        let second = s.0.join("target/debug/build/tests/second/out");
        for path in [&first, &second] {
            assert!(known_library_paths(
                path.as_os_str(),
                &s.0.join("target"),
                &s.0.join("sysroot")
            ));
        }
        let env = |path: &Path| {
            normalized_environment([
                (
                    OsString::from("LD_LIBRARY_PATH"),
                    path.as_os_str().to_owned(),
                ),
                (
                    OsString::from("RUSTFLAGS"),
                    OsString::from("-Znext-solver=coherence"),
                ),
            ])
        };
        assert_eq!(env(&first), env(&second));
        for path in [
            s.0.join("custom"),
            s.0.join("target/arbitrary"),
            PathBuf::from("relative"),
        ] {
            assert!(!known_library_paths(
                path.as_os_str(),
                &s.0.join("target"),
                &s.0.join("sysroot")
            ));
        }
    }

    #[test]
    fn unit_and_integration_caller_metadata_do_not_change_compiler_identity() {
        let base = vec![(
            OsString::from("RUSTFLAGS"),
            OsString::from("-Znext-solver=coherence"),
        )];
        let mut unit = base.clone();
        unit.push(("_".into(), "cargo".into()));
        let mut integration = base;
        integration.push(("_".into(), "timeout".into()));
        integration.push((
            "CARGO_BIN_EXE_source-bundle".into(),
            "/caller/helper".into(),
        ));
        unit.push(("CARGO_TARGET_DIR".into(), "/caller/target".into()));
        unit.push(("CARGO_BUILD_BUILD_DIR".into(), "/caller/build".into()));
        unit.push(("TAUTO_SELFHOST_CACHE_TRACE".into(), "1".into()));
        unit.push((
            "DYLD_FALLBACK_LIBRARY_PATH".into(),
            "/validated/separately".into(),
        ));
        unit.push(("NEXTEST_RUN_ID".into(), "first-run".into()));
        unit.push(("NEXTEST".into(), "1".into()));
        unit.push(("NEXTEST_TEST_NAME".into(), "unit-test".into()));
        integration.push(("NEXTEST_RUN_ID".into(), "second-run".into()));
        integration.push(("NEXTEST_TEST_NAME".into(), "integration-test".into()));
        integration.push(("NEXTEST_ATTEMPT_ID".into(), "second-run:test".into()));
        integration.push(("NEXTEST_TEST_GLOBAL_SLOT".into(), "5".into()));
        assert_eq!(
            normalized_environment(unit),
            normalized_environment(integration.clone())
        );
        let mut command = Command::new("unused");
        for (key, value) in &integration {
            command.env(key, value);
        }
        normalize_command(&mut command, integration.into_iter().map(|(key, _)| key));
        for (key, value) in command.get_envs() {
            if caller_metadata(key) {
                assert!(value.is_none());
            } else {
                assert_eq!(value.unwrap(), "-Znext-solver=coherence");
            }
        }
    }

    #[test]
    fn repaired_missing_and_invalid_utf8_includes_remain_tracked() {
        let s = fixture();
        fs::remove_file(s.0.join("totes/app/src/data.txt")).unwrap();
        let missing = fixture_key(&s);
        s.write("totes/app/src/data.txt", "repaired");
        let repaired = fixture_key(&s);
        assert_ne!(missing, repaired);
        fs::write(s.0.join("totes/app/src/data.txt"), [0xff]).unwrap();
        let invalid = fixture_key(&s);
        assert_ne!(repaired, invalid);
        s.write("totes/app/src/data.txt", "changed again");
        assert_ne!(invalid, fixture_key(&s));
        assert_ne!(repaired, fixture_key(&s));
    }

    #[test]
    fn cargo_darwin_fallbacks_normalize_but_custom_paths_do_not() {
        let s = fixture();
        let target = s.0.join("target");
        let sysroot = s.0.join("sysroot");
        let home = s.0.join("home");
        s.write("target/.rustc_info.json", "{}");
        // Cargo includes its dependency directory even before it exists.
        assert!(!target.join("debug/deps").exists());
        let paths = std::env::join_paths([
            target.join("debug/deps"),
            sysroot.join("lib"),
            home.join("lib"),
            PathBuf::from("/usr/local/lib"),
            PathBuf::from("/usr/lib"),
        ])
        .unwrap();
        assert!(known_fallback_library_paths(
            &paths, &target, &sysroot, &home
        ));
        for path in [s.0.join("custom"), PathBuf::from("relative")] {
            assert!(!known_fallback_library_paths(
                path.as_os_str(),
                &target,
                &sysroot,
                &home
            ));
        }
        assert!(caller_metadata("DYLD_FALLBACK_LIBRARY_PATH".as_ref()));
        assert!(!caller_metadata("DYLD_LIBRARY_PATH".as_ref()));
    }

    #[test]
    fn absolute_certificate_inputs_invalidate_the_compiler_identity() {
        let s = fixture();
        let certificate = s.0.join("certificate.pem");
        let config = format!("[http]\ncainfo = {:?}\n", certificate);
        let files = configuration_inputs(&config).unwrap();
        assert_eq!(files, BTreeSet::from([certificate]));
        s.write("certificate.pem", "first certificate");
        let first = digest_files(&files, b"compiler").unwrap();
        s.write("certificate.pem", "replacement certificate");
        assert_ne!(first, digest_files(&files, b"compiler").unwrap());
        for config in [
            "[http]\ncainfo = \"relative.pem\"",
            "[http]\ncainfo = \"/escaped\\\\path.pem\"",
            "[http]\nproxy = \"unknown\"",
        ] {
            assert!(configuration_inputs(config).is_none());
        }
    }

    #[test]
    fn indirect_configuration_and_host_dependencies_bypass_reuse() {
        for key in [
            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER",
            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_AR",
            "LD_AUDIT",
            "LD_ORIGIN_PATH",
        ] {
            assert!(untracked_override(key.as_ref(), "/untracked/tool".as_ref()));
        }
        assert!(!untracked_override(
            "LD_LIBRARY_PATH".as_ref(),
            "/validated/separately".as_ref()
        ));
        assert!(closed_config(
            "[build]\nrustflags = [\"-Znext-solver=coherence\"]\n"
        ));
        for text in [
            "include = \"elsewhere.toml\"",
            "[build]\nrustc = \"custom\"",
            "[target.host]\nlinker = \"custom\"",
            "[env]\nRUSTFLAGS = \"other\"",
            "[source.local]\ndirectory = \"vendor\"",
        ] {
            assert!(!closed_config(text), "{text}");
        }
        let s = fixture();
        s.write(
            "totes/app/Tauto.eure",
            "package { name = \"app\" }\nrust { bridge = \"bridge\" }\n",
        );
        assert!(!tote_files(&s.0.join("totes/app")).unwrap().1);
        let first = build_artifact(&s.0.join("cache"), "app", None, |work| {
            Ok(executable(work, "first"))
        })
        .unwrap();
        let second = build_artifact(&s.0.join("cache"), "app", None, |work| {
            Ok(executable(work, "second"))
        })
        .unwrap();
        assert_ne!(first, second);
        assert_eq!(fs::read_to_string(first).unwrap(), "first");
        assert_eq!(fs::read_to_string(&second).unwrap(), "second");
        assert!(!second.parent().unwrap().join("artifact").exists());
    }

    #[test]
    fn formatter_configuration_bypasses_until_removed() {
        assert!(untracked_override(
            "RUSTFMT".as_ref(),
            "custom-formatter".as_ref()
        ));
        assert!(!untracked_override("RUSTFMT".as_ref(), "".as_ref()));
        let s = fixture();
        let home = s.0.join("home");
        let config = s.0.join("xdg");
        let mut files = BTreeSet::new();
        assert!(formatter_config_paths(
            &s.0,
            &home,
            Some(&config),
            &mut files
        ));
        for name in ["rustfmt.toml", ".rustfmt.toml"] {
            assert!(files.contains(&s.0.join(name)));
            for dir in ["", "home", "home/.config/rustfmt", "xdg/rustfmt"] {
                let relative = Path::new(dir).join(name);
                s.write(
                    relative.to_str().unwrap(),
                    "license_template_path = \"elsewhere\"\n",
                );
                assert!(!formatter_config_paths(
                    &s.0,
                    &home,
                    Some(&config),
                    &mut BTreeSet::new()
                ));
                fs::remove_file(s.0.join(relative)).unwrap();
                assert!(formatter_config_paths(
                    &s.0,
                    &home,
                    Some(&config),
                    &mut BTreeSet::new()
                ));
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn executable_bytes_matter_even_when_version_output_is_unchanged() {
        let s = Scratch::new();
        let command = executable(&s.0, "#!/bin/sh\necho unchanged-version\n# first\n");
        let first = tool(command.as_os_str(), &s.0).unwrap();
        fs::write(&command, "#!/bin/sh\necho unchanged-version\n# other\n").unwrap();
        assert_ne!(first, tool(command.as_os_str(), &s.0).unwrap());
    }

    #[cfg(unix)]
    #[test]
    fn compiler_target_symlinks_are_rejected_before_cargo_writes() {
        let s = Scratch::new();
        s.write("outside/sentinel", "unchanged");
        fs::create_dir_all(s.0.join("compiler/key")).unwrap();
        std::os::unix::fs::symlink(s.0.join("outside"), s.0.join("compiler/key/debug")).unwrap();
        assert!(reject_tree_links(&s.0.join("compiler/key")).is_err());
        assert_eq!(
            fs::read_to_string(s.0.join("outside/sentinel")).unwrap(),
            "unchanged"
        );
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_cache_components_and_records_never_write_outside() {
        use std::os::unix::fs::symlink;
        for attacked in [
            "app",
            "app/key",
            "app/lock",
            "app/key/artifact",
            "app/key/tool",
        ] {
            let s = Scratch::new();
            s.write("outside/sentinel", "unchanged");
            let path = s.0.join("cache").join(attacked);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            let target = if attacked == "app" || attacked == "app/key" {
                s.0.join("outside")
            } else {
                s.0.join("outside/sentinel")
            };
            symlink(&target, &path).unwrap();
            assert!(
                cached_build(&s.0.join("cache"), "app", "key", |_| panic!(
                    "must reject before build"
                ))
                .is_err(),
                "{attacked}"
            );
            assert_eq!(
                fs::read_to_string(s.0.join("outside/sentinel")).unwrap(),
                "unchanged"
            );
            assert_eq!(fs::read_dir(s.0.join("outside")).unwrap().count(), 1);
        }
    }

    #[test]
    #[ignore = "builds a release native tote and measures cold and verified warm requests"]
    fn native_cache_timing() {
        let root = super::super::root().canonicalize().unwrap();
        let hash_start = std::time::Instant::now();
        let identity = input_key(&root, &root.join("totes/fmt")).unwrap();
        eprintln!(
            "initial toolchain and input identity: {:?}",
            hash_start.elapsed()
        );
        assert!(
            identity.is_some(),
            "production cache must be eligible; LD_LIBRARY_PATH={:?}",
            std::env::var_os("LD_LIBRARY_PATH")
        );
        let identity = identity.unwrap();
        let namespace = sha256_hex(root.join("totes/fmt").as_os_str().as_encoded_bytes());
        assert!(
            !cache_root(&root)
                .join(namespace)
                .join(&identity.tote)
                .join("artifact")
                .exists(),
            "timing needs a fresh caller-selected cache directory"
        );
        let before = TEST_COMPILER_INVOCATIONS.load(Ordering::Relaxed);
        let start = std::time::Instant::now();
        let cold = build_tote("fmt").unwrap();
        let cold_time = start.elapsed();
        let start = std::time::Instant::now();
        let warm = build_tote("fmt").unwrap();
        let warm_time = start.elapsed();
        assert_eq!(cold, warm);
        assert_eq!(
            TEST_COMPILER_INVOCATIONS.load(Ordering::Relaxed),
            before + 1
        );
        let input = Scratch::new();
        input.write(
            "format.taut",
            r#"let answer:=42
"#,
        );
        let input_path = input.0.join("format.taut");
        let out = Command::new(&warm)
            .args(["--allow-read", "--"])
            .arg(&input_path)
            .output()
            .unwrap();
        assert!(out.status.success());
        let expected = format!(
            "== {}\n{}",
            input_path.display(),
            tauto::fmt::format(
                r#"let answer:=42
"#
            )
            .unwrap()
        );
        assert_eq!(String::from_utf8(out.stdout).unwrap(), expected);
        eprintln!(
            "native cache cold={cold_time:?} warm={warm_time:?}; executable bytes={}; run exit={:?}",
            fs::metadata(warm).unwrap().len(),
            out.status.code()
        );
    }
}
