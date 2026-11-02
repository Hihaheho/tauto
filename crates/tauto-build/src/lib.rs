//! `tauto-build`: compiles a tote from a Rust crate's `build.rs`.
//!
//! ```ignore
//! // build.rs
//! fn main() {
//!     tauto_build::compile("logic/Tauto.eure").unwrap();
//! }
//!
//! // src/lib.rs
//! mod logic {
//!     include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs"));
//! }
//! ```

use std::path::{Path, PathBuf};

use tauto_message::msg;
use tauto_nir::CompileError;
use tauto_rustgen::{Bindings, Sources};

/// Compiles the tote whose `Tauto.eure` is at `manifest`, and writes
/// `$OUT_DIR/tauto_<package>.rs`, with each `-` of the package name written
/// `_`. Cargo is told to rerun the build script when a source, the manifest
/// or a bindings file changes.
pub fn compile(manifest: impl AsRef<Path>) -> Result<(), String> {
    #[cfg(feature = "messages")]
    tauto_messages::install();
    let out_dir = std::env::var_os("OUT_DIR")
        .map(PathBuf::from)
        .ok_or_else(|| msg!("tautobuild-no-out-dir").to_string())?;
    let crate_dir = std::env::var_os("CARGO_MANIFEST_DIR").map(PathBuf::from);
    let cargo_toml = crate_dir
        .as_ref()
        .and_then(|d| std::fs::read_to_string(d.join("Cargo.toml")).ok());
    let (file, text, warnings) = generate(manifest.as_ref(), cargo_toml.as_deref())?;
    let m = tauto::manifest::load(manifest.as_ref().parent().unwrap_or(Path::new(".")))?;
    for path in watched(&m, manifest.as_ref())? {
        println!("cargo:rerun-if-changed={}", path.display());
    }
    for w in warnings {
        println!("cargo:warning={w}");
    }
    let target = out_dir.join(file);
    std::fs::write(&target, text).map_err(|e| format!("{}: {e}", target.display()))
}

/// The files the output depends on.
fn watched(m: &tauto::manifest::Manifest, manifest: &Path) -> Result<Vec<PathBuf>, String> {
    let dir = manifest.parent().unwrap_or(Path::new("."));
    let mut out = vec![manifest.to_path_buf()];
    out.extend(m.rust.bindings.iter().map(|b| dir.join(b)));
    let source_files = tauto::program::tote_inputs(dir)?;
    // Tables may live beside any source or in an ancestor. Watching existing
    // table directories also notices a regenerated table with the same grammar SHA.
    for source in &source_files {
        for parent in source.parent().into_iter().flat_map(Path::ancestors) {
            let tables = parent.join(".tauto-syntax");
            if tables.is_dir() && !out.contains(&tables) {
                out.push(tables);
            }
        }
    }
    out.extend(source_files);
    if let Some(b) = &m.rust.bridge {
        out.push(dir.join(b));
    }
    Ok(out)
}

/// Loads a tote's executable declarations with their file boundaries and
/// macro stages intact. A build directory need not match the package name.
pub fn tote_program(dir: &Path) -> Result<tauto::program::Loaded, String> {
    tauto::program::load_tote_for_build(dir)
}

/// Joins a tote's executable source for display. Compilation uses
/// [`tote_program`]: joining text alone does not preserve macro stages.
pub fn tote_source(dir: &Path) -> Result<String, String> {
    Ok(tote_program(dir)?.source_text())
}

/// The output file's name, its text and the warnings. `cargo_toml` is the
/// text of the using crate's `Cargo.toml`, when there is one to check.
pub fn generate(
    manifest: &Path,
    cargo_toml: Option<&str>,
) -> Result<(String, String, Vec<String>), String> {
    #[cfg(feature = "messages")]
    tauto_messages::install();
    let dir = manifest.parent().unwrap_or(Path::new("."));
    let m = tauto::manifest::load(dir)?;
    if let Some(toml) = cargo_toml {
        let mut needs: Vec<String> = m.rust.dependencies.keys().cloned().collect();
        if m.rust.bridge.is_some() {
            needs.push(format!("{}-bridge", m.package.name));
        }
        if m.rust.uniffi {
            needs.push("uniffi".into());
        }
        for n in needs {
            if !depends_on(toml, &n) {
                return Err(msg!("tautobuild-needs-dependency", name = n).to_string());
            }
        }
    }
    let loaded = tote_program(dir)?;
    let source = loaded.source_text();
    let mut package = tauto_nir::compile_loaded_with_observer(&loaded, true, false, |_| {})
        .map_err(|error| {
            let message = match error {
                CompileError::Front(m) | CompileError::Build(m) => m,
                CompileError::Unsupported(u) => {
                    if let Some((file, line, col)) =
                        u.span.and_then(|span| loaded.locate(span.start))
                    {
                        return format!("{}:{line}:{col}: {u}", file.display());
                    }
                    u.to_string()
                }
            };
            // The offset is read from the text of the error, because `tauto-nir`
            // does not give it as a message.
            match message
                .rsplit_once(" (byte ")
                .and_then(|(message, offset)| {
                    Some((
                        message,
                        loaded.locate(offset.trim_end_matches(')').parse().ok()?)?,
                    ))
                }) {
                Some((message, (file, line, col))) => {
                    format!("{}:{line}:{col}: {message}", file.display())
                }
                None => message,
            }
        })?;
    if let Some(selected) = &m.rust.exports {
        let mut seen = std::collections::BTreeSet::new();
        for name in selected {
            if !seen.insert(name) {
                return Err(msg!("tautobuild-export-twice", name = name.as_str()).to_string());
            }
            if !package.exports.iter().any(|e| &e.name == name) {
                return Err(msg!("tautobuild-export-unknown", name = name.as_str()).to_string());
            }
        }
        // Lowering already checked the whole package. Selection changes only
        // the facade, not which helpers are compiled or validated.
        package.exports.retain(|e| seen.contains(&e.name));
    }
    let bridge = m
        .rust
        .bridge
        .as_ref()
        .map(|_| format!("{}_bridge", m.package.name.replace('-', "_")));
    let bindings = Bindings::resolve(&package, Some(&m), bridge.as_deref())?;
    let name = m.package.name.replace('-', "_");
    let (items, warnings) = tauto_rustgen::emit_lib_tokens(
        &package,
        &Sources {
            file: &manifest.display().to_string(),
            text: &source,
        },
        &bindings,
    );
    if m.rust.exports.is_some() && !warnings.is_empty() {
        return Err(msg!("tautobuild-exports-invalid", warnings = warnings.join("; ")).to_string());
    }
    let lints = tauto_rustgen::allow_lints();
    let module = quote::quote!(
        #[allow(#lints)]
        #[doc(hidden)]
        pub mod generated {
            #items
        }
        // A tote that exports nothing (a program run through `generated::run`)
        // leaves the facade unused.
        #[allow(unused_imports)]
        pub use generated::api::*;
    );
    let text = format!(
        "// Generated by tauto-build from {}. Do not edit.\n{}",
        manifest.display(),
        tauto_rustgen::render(module),
    );
    Ok((format!("tauto_{name}.rs"), text, warnings))
}

/// Whether the `[dependencies]` of `toml` name `dep`.
fn depends_on(toml: &str, dep: &str) -> bool {
    let mut in_deps = false;
    for line in toml.lines() {
        let l = line.trim();
        if l.starts_with('[') {
            in_deps = l == "[dependencies]";
            if l == format!("[dependencies.{dep}]") {
                return true;
            }
            continue;
        }
        if in_deps {
            let key = l.split(['=', '.']).next().unwrap_or("").trim();
            if key == dep {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dependency_discovery_errors_are_not_empty_watch_lists() {
        let root = std::env::temp_dir().join(format!(
            "tauto-build-watch-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&root).unwrap();
        let result = watched(
            &tauto::manifest::Manifest::default(),
            &root.join("Tauto.eure"),
        );
        assert!(result.is_err());
        std::fs::remove_dir_all(root).unwrap();
    }
}
