//! A debug build for the host without Cargo for the generated crate.
//!
//! `tauto-rt` and what it depends on are built once by Cargo, for one rustc,
//! feature set and profile, and kept in the build cache (`tauto-cache`) for
//! every project on this machine. The generated library and its `main` are
//! then given to rustc directly, with rustc's own incremental compilation in
//! the project's target directory.
//!
//! Only a crate that depends on `tauto-rt` alone is built this way; one with
//! `rust.dependencies` or a bridge crate, a release build and a build for
//! another target go through Cargo. So does a feature set whose dependencies
//! link native libraries from their build directory, which a kept `rlib`
//! cannot carry.

use std::path::{Path, PathBuf};
use std::process::Command;

use tauto_cache::{Action, BuildCache, Outputs};
use tauto_message::msg;

use crate::Workspace;

/// Why a direct build was not made, so that Cargo builds the crate instead,
/// or the error to report.
pub(crate) enum Failed {
    /// The runtime could not be built or kept for reuse.
    Fallback,
    Error(String),
}

impl Workspace {
    /// The features of `tauto-rt` when the crate depends on it alone.
    pub(crate) fn rt_features_alone(&self) -> Option<Vec<String>> {
        let cargo = &self.files.iter().find(|(p, _)| p == "Cargo.toml")?.1;
        let deps = cargo.split("[dependencies]\n").nth(1)?;
        let deps = deps.split("\n[").next()?;
        let mut lines = deps.lines().filter(|l| !l.trim().is_empty());
        let rt = lines.next()?.strip_prefix("tauto-rt = ")?;
        if lines.next().is_some() {
            return None;
        }
        let features = match rt.split_once("features = [") {
            Some((_, rest)) => rest
                .split(']')
                .next()?
                .split(',')
                .map(|f| f.trim().trim_matches('"').to_string())
                .filter(|f| !f.is_empty())
                .collect(),
            None => Vec::new(),
        };
        Some(features)
    }

    /// Builds the crate written in `dir` with rustc, against the runtime kept
    /// for its features.
    pub(crate) fn build_direct(
        &self,
        name: &str,
        dir: &Path,
        target_dir: &Path,
        features: &[String],
    ) -> Result<PathBuf, Failed> {
        // rustc runs in `dir`, so every path it is given is absolute.
        let target_dir = &std::path::absolute(target_dir).map_err(|_| Failed::Fallback)?;
        let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
        let rt =
            runtime(&self.rt_files(), dir, target_dir, &rustc, features).ok_or(Failed::Fallback)?;
        let ident = name.replace('-', "_");
        let out = target_dir.join("debug");
        let libs = out.join("direct");
        std::fs::create_dir_all(&libs).map_err(|_| Failed::Fallback)?;
        let rustc_in =
            |crate_type: &str, crate_name: &str, src: &str| {
                let mut cmd = Command::new(&rustc);
                cmd.current_dir(dir)
                    .args(["--edition", "2024", "--crate-type", crate_type])
                    .args(["--crate-name", crate_name])
                    .args(["-C", "debuginfo=2"])
                    .arg("-C")
                    .arg(format!(
                        "incremental={}",
                        target_dir.join("incremental").display()
                    ))
                    .arg("-L")
                    .arg(format!("dependency={}", rt.dir.display()))
                    .arg("-L")
                    .arg(format!("dependency={}", libs.display()))
                    .arg("--extern")
                    .arg(format!("tauto_rt={}", rt.lib.display()))
                    .args(rt.meta.iter().flat_map(|m| {
                        ["--extern".to_string(), format!("tauto_rt={}", m.display())]
                    }))
                    .arg("--color=never")
                    .arg(src);
                cmd
            };
        let mut lib = rustc_in("rlib", &ident, "src/lib.rs");
        lib.arg("--out-dir").arg(&libs);
        self.run_rustc(lib, dir)?;
        // The binary's crate is named apart from the library it calls.
        let mut bin = rustc_in("bin", &format!("{ident}_main"), "src/main.rs");
        let path = out.join(name);
        bin.arg("--extern")
            .arg(format!(
                "{ident}={}",
                libs.join(format!("lib{ident}.rlib")).display()
            ))
            .arg("-o")
            .arg(&path);
        self.run_rustc(bin, dir)?;
        Ok(path)
    }

    fn run_rustc(&self, mut cmd: Command, dir: &Path) -> Result<(), Failed> {
        let out = cmd.output().map_err(|e| {
            Failed::Error(msg!("rustgen-cannot-run-cargo", error = e.to_string()).to_string())
        })?;
        if out.status.success() {
            return Ok(());
        }
        let stderr = String::from_utf8_lossy(&out.stderr);
        Err(Failed::Error(self.rejected(&stderr, dir)))
    }
}

impl Workspace {
    /// The runtime's files as this crate has them, its `Cargo.toml` among them.
    fn rt_files(&self) -> Vec<(&str, &str)> {
        self.files
            .iter()
            .filter(|(p, _)| p.starts_with("tauto-rt/"))
            .map(|(p, t)| (p.as_str(), t.as_str()))
            .collect()
    }
}

struct Runtime {
    /// Where its `rlib`s are, by the names Cargo gave them.
    dir: PathBuf,
    lib: PathBuf,
    /// Its metadata, when its `rlib` holds only a stub of it.
    meta: Option<PathBuf>,
}

/// The runtime for `features`: from the build cache, else built by Cargo and
/// kept there. It is laid out under `target_dir/rt/<key>`.
fn runtime(
    files: &[(&str, &str)],
    dir: &Path,
    target_dir: &Path,
    rustc: &str,
    features: &[String],
) -> Option<Runtime> {
    let cache = BuildCache::from_env().ok()?;
    let version = Command::new(rustc)
        .current_dir(dir)
        .arg("-vV")
        .output()
        .ok()
        .filter(|o| o.status.success())?
        .stdout;
    let mut rt = Vec::new();
    for (path, text) in files {
        rt.extend_from_slice(&(path.len() as u64).to_be_bytes());
        rt.extend_from_slice(path.as_bytes());
        rt.extend_from_slice(&(text.len() as u64).to_be_bytes());
        rt.extend_from_slice(text.as_bytes());
    }
    let action = Action::new("rust-runtime", &features.join(","))
        .input("rustc", &version)
        .input("tauto-rt", &rt)
        .input("features", features.join(",").as_bytes())
        .input("profile", b"dev");
    let outputs = match cache.get(&action) {
        Some(o) => o,
        None => {
            let built = build_runtime(files, target_dir, features)?;
            let mut outputs = Outputs::default();
            for file in built {
                let bytes = std::fs::read(&file).ok()?;
                let name = file.file_name()?.to_str()?.to_string();
                outputs.0.insert(name, cache.put_blob(&bytes).ok()?);
            }
            cache.put(&action, &outputs).ok()?;
            outputs
        }
    };
    let at = target_dir.join("rt").join(action.key().hex());
    std::fs::create_dir_all(&at).ok()?;
    let mut lib = None;
    for (name, d) in &outputs.0 {
        let dest = at.join(name);
        if !dest.is_file() {
            let tmp = at.join(format!(".{name}.{}", std::process::id()));
            let blob = cache.blob_path(d);
            if std::fs::hard_link(&blob, &tmp).is_err() {
                std::fs::copy(&blob, &tmp).ok()?;
            }
            std::fs::rename(&tmp, &dest).ok()?;
        }
        if name.starts_with("libtauto_rt-") && name.ends_with(".rlib") {
            lib = Some(dest);
        }
    }
    let lib = lib?;
    let meta = Some(lib.with_extension("rmeta")).filter(|m| m.is_file());
    Some(Runtime { dir: at, lib, meta })
}

/// Builds `tauto-rt` with `features` by Cargo in `target_dir/rt-build`, and
/// returns the `rlib`s (and `rmeta`s) it and its dependencies are; none when a dependency
/// links what an `rlib` does not hold.
fn build_runtime(
    files: &[(&str, &str)],
    target_dir: &Path,
    features: &[String],
) -> Option<Vec<PathBuf>> {
    let ws = target_dir.join("rt-build");
    for (path, text) in files {
        let p = ws.join(path);
        let text = if *path == "tauto-rt/Cargo.toml" {
            format!("{text}\n[workspace]\n\n[profile.dev.package.tauto-rt]\nopt-level = 3\n")
        } else {
            text.to_string()
        };
        std::fs::create_dir_all(p.parent()?).ok()?;
        if std::fs::read_to_string(&p).ok() != Some(text.clone()) {
            std::fs::write(&p, text).ok()?;
        }
    }
    let mut cmd = Command::new(std::env::var("CARGO").unwrap_or_else(|_| "cargo".into()));
    cmd.arg("build")
        .arg("--quiet")
        .arg("--lib")
        .arg("--message-format=json")
        .arg("--manifest-path")
        .arg(ws.join("tauto-rt/Cargo.toml"))
        .env("CARGO_TARGET_DIR", ws.join("target"))
        .env("CARGO_BUILD_BUILD_DIR", ws.join("target"))
        .env("CARGO_TERM_COLOR", "never");
    crate::cargo::offline_if_requested(&mut cmd);
    if !features.is_empty() {
        cmd.arg("--features").arg(features.join(","));
    }
    let out = cmd.output().ok().filter(|o| o.status.success())?;
    let mut rlibs = Vec::new();
    for line in String::from_utf8_lossy(&out.stdout).lines() {
        if line.contains("\"reason\":\"build-script-executed\"")
            && !line.contains("\"linked_paths\":[]")
        {
            return None;
        }
        if !line.contains("\"reason\":\"compiler-artifact\"") {
            continue;
        }
        // An `rlib` may hold only a stub of its metadata, with the rest in
        // the `rmeta` beside it. The root crate's `rlib` is also copied out
        // of that directory under another name, so each pair is taken from
        // where the `rmeta` is.
        let files = strings_of(line, "\"filenames\":[")?;
        let rmetas: Vec<_> = files.iter().filter(|f| f.ends_with(".rmeta")).collect();
        if rmetas.is_empty() {
            rlibs.extend(
                files
                    .iter()
                    .filter(|f| f.ends_with(".rlib"))
                    .map(PathBuf::from),
            );
        }
        for m in rmetas {
            let m = PathBuf::from(m);
            let lib = m.with_extension("rlib");
            if lib.is_file() {
                rlibs.push(lib);
            }
            rlibs.push(m);
        }
    }
    rlibs
        .iter()
        .any(|f| {
            f.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("libtauto_rt-") && n.ends_with(".rlib"))
        })
        .then_some(rlibs)
}

/// The JSON strings of the array that starts after `key` on `line`.
fn strings_of(line: &str, key: &str) -> Option<Vec<String>> {
    let rest = &line[line.find(key)? + key.len()..];
    let mut out = Vec::new();
    let mut chars = rest.chars();
    loop {
        match chars.next()? {
            ']' => return Some(out),
            ',' | ' ' => {}
            '"' => {
                let mut s = String::new();
                loop {
                    match chars.next()? {
                        '"' => break,
                        '\\' => match chars.next()? {
                            'n' => s.push('\n'),
                            't' => s.push('\t'),
                            c => s.push(c),
                        },
                        c => s.push(c),
                    }
                }
                out.push(s);
            }
            _ => return None,
        }
    }
}
