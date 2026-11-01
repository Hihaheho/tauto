//! The Cargo workspace around the generated module: the library, a `main`, and `tauto-rt` as sources.

use quote::quote;
use tauto_message::msg;
use tauto_nir::Package;

use crate::tok::{id, render};
use crate::{Bindings, Sources, emit_module};

impl Options {
    /// The dependencies and the bridge crate of a tote's manifest. The bridge
    /// crate is `<package>-bridge`, in the directory `rust.bridge` names.
    pub fn from_manifest(m: &tauto::manifest::Manifest) -> Options {
        let dir = m.file.parent().map(|d| d.to_path_buf()).unwrap_or_default();
        let dir = std::fs::canonicalize(&dir).unwrap_or(dir);
        Options {
            threads: m.rust.executor.as_deref() == Some("threads"),
            dependencies: m
                .rust
                .dependencies
                .iter()
                .map(|(k, e)| (k.clone(), e.value.clone()))
                .collect(),
            bridge: m.rust.bridge.as_ref().map(|b| {
                (
                    format!("{}-bridge", m.package.name),
                    dir.join(b).display().to_string(),
                )
            }),
        }
    }
}

/// What the manifest adds to the generated crate.
#[derive(Default)]
pub struct Options {
    /// `rust.executor = "threads"`: each task has a thread of its own. Else a
    /// program that starts tasks runs them on the reactor
    /// (`tauto_rt::reactor`, on tokio).
    pub threads: bool,
    /// `rust.dependencies`: `(name, Cargo.toml value)`.
    pub dependencies: Vec<(String, String)>,
    /// The bridge crate: its name and the path of its directory.
    pub bridge: Option<(String, String)>,
}

/// The targets other than the host's that a generated crate builds for:
/// `wasm32-wasip1`, where a WASI host answers the standard effects, and
/// `wasm32-unknown-unknown`, where the embedder does (`tauto_rt::host`).
pub const WASM_TARGETS: [&str; 2] = ["wasm32-wasip1", "wasm32-unknown-unknown"];

/// The files of a generated crate: `(path, contents)`.
pub struct Workspace {
    pub files: Vec<(String, String)>,
}

/// Generated files reused by content equality or written to the output directory.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WriteStats {
    pub unchanged: usize,
    pub written: usize,
}

/// Boundaries of generated-file writing and native compilation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuildEvent {
    Write,
    Written(WriteStats),
    NativeCompile,
}

impl Workspace {
    /// Writes the files under `dir`, leaving the ones that are unchanged.
    pub fn write(&self, dir: &std::path::Path) -> std::io::Result<()> {
        self.write_with_stats(dir).map(|_| ())
    }

    /// As `write`, counting reused and written files only after a successful write.
    pub fn write_with_stats(&self, dir: &std::path::Path) -> std::io::Result<WriteStats> {
        let mut stats = WriteStats::default();
        for (path, text) in &self.files {
            let p = dir.join(path);
            if let Some(parent) = p.parent() {
                std::fs::create_dir_all(parent)?;
            }
            if std::fs::read_to_string(&p).is_ok_and(|old| old == *text) {
                stats.unchanged += 1;
                continue;
            }
            std::fs::write(&p, text)?;
            stats.written += 1;
        }
        Ok(stats)
    }
}

macro_rules! rt_files {
    ($($name:literal),* $(,)?) => {
        &[$(
            (concat!("tauto-rt/src/", $name), include_str!(concat!("../../tauto-rt/src/", $name))),
        )*]
    };
}

const RT: &[(&str, &str)] = rt_files!(
    "a.rs",
    "budget.rs",
    "budget_contract.rs",
    "cps.rs",
    "ct.rs",
    "ev.rs",
    "exec.rs",
    "float.rs",
    "float_math.rs",
    "host.rs",
    "int.rs",
    "lib.rs",
    "link.rs",
    "messages.rs",
    "nat.rs",
    "o.rs",
    "permissions.rs",
    "probe.rs",
    "reactor.rs",
    "show.rs",
    "signal.rs",
    "stdlib.rs",
    "tcp.rs",
    "tls.rs",
    "tls_host.rs"
);

const RT_CARGO: &str = "\
[package]
name = \"tauto-rt\"
version = \"0.1.0\"
edition = \"2024\"

[features]
sync = []
net = [\"dep:reqwest\", \"dep:url\"]
reactor = [\"sync\", \"dep:tokio\"]
tls = [\"dep:rustls\", \"dep:rustls-platform-verifier\"]

[dependencies]
reqwest = { version = \"=0.13.5\", optional = true, default-features = false, features = [\"blocking\", \"rustls\"] }
url = { version = \"=2.5.8\", optional = true }
rustls = { version = \"=0.23.46\", optional = true, default-features = false, features = [\"aws_lc_rs\", \"std\", \"tls12\"] }
rustls-platform-verifier = { version = \"=0.7.1\", optional = true }

[target.'cfg(not(all(target_arch = \"wasm32\", target_os = \"unknown\")))'.dependencies]
getrandom = \"=0.3.4\"

[target.'cfg(not(target_family = \"wasm\"))'.dependencies]
tokio = { version = \"=1.53.3\", optional = true, default-features = false, features = [\"rt\", \"time\", \"sync\"] }
";

/// The crate for `package`, named `name`.
pub fn workspace(
    name: &str,
    package: &Package,
    sources: &Sources<'_>,
    bindings: &Bindings,
    opts: &Options,
) -> Workspace {
    let lib = emit_module(package, sources, bindings);
    let reactor = package.sync && !opts.threads;
    let features: Vec<&str> = [
        package
            .sync
            .then_some(if reactor { "\"reactor\"" } else { "\"sync\"" }),
        package
            .permissions
            .iter()
            .any(|p| p == "net")
            .then_some("\"net\""),
        // TLS rides on the streams of `net`, and the HTTP client already
        // brings rustls.
        package
            .permissions
            .iter()
            .any(|p| p == "net")
            .then_some("\"tls\""),
    ]
    .into_iter()
    .flatten()
    .collect();
    let mut deps = if features.is_empty() {
        String::from("tauto-rt = { path = \"tauto-rt\" }\n")
    } else {
        format!(
            "tauto-rt = {{ path = \"tauto-rt\", features = [{}] }}\n",
            features.join(", ")
        )
    };
    for (n, v) in &opts.dependencies {
        deps.push_str(&format!("{n} = {v}\n"));
    }
    if let Some((n, p)) = &opts.bridge {
        deps.push_str(&format!("{n} = {{ path = {p:?} }}\n"));
    }
    // A debug build optimizes tauto-rt alone: the generated crate stays at
    // opt-level 0 and rebuilds quickly after an edit, while tauto-rt, built
    // once into the target directory, does not run unoptimized. Its
    // debug-assertions, and with them the drop bomb, stay on.
    let cargo = format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
         [dependencies]\n{deps}\n[workspace]\n\n\
         [profile.dev.package.tauto-rt]\nopt-level = 3\n\n\
         [profile.release]\npanic = \"unwind\"\nlto = \"thin\"\n"
    );
    let ident = crate_ident(&name.replace('-', "_"));
    let main = if reactor {
        quote!(
            fn main() -> std::process::ExitCode {
                tauto_rt::reactor::install();
                tauto_rt::run_main(#ident::run)
            }
        )
    } else {
        quote!(
            fn main() -> std::process::ExitCode {
                tauto_rt::run_main(#ident::run)
            }
        )
    };
    let main = render(main);
    let mut files = vec![
        ("Cargo.toml".to_string(), cargo),
        ("src/lib.rs".to_string(), lib),
        ("src/main.rs".to_string(), main),
        ("tauto-rt/Cargo.toml".to_string(), RT_CARGO.to_string()),
    ];
    for (p, t) in RT {
        files.push((p.to_string(), t.to_string()));
    }
    Workspace { files }
}

impl Workspace {
    /// When rustc's first error is inside the wrapper of an `extern`, the
    /// error is the extern's: its Rust does not fit its declaration. The
    /// message points at the declaration and at the binding.
    fn extern_error(&self, stderr: &str) -> Option<String> {
        let lib = &self.files.iter().find(|(p, _)| p == "src/lib.rs")?.1;
        let head = marker_item(lib, rustc_place(stderr)?, "extern ")?;
        // `NAME  declared F:L:C  bound AT  -> PATH`
        let mut parts = head.split("  ");
        let name = parts.next()?;
        let declared = parts.next()?.strip_prefix("declared ")?;
        let bound = parts.next()?.strip_prefix("bound ")?;
        let path = parts.next()?.strip_prefix("-> ")?;
        let first = stderr.lines().find(|l| l.starts_with("error"))?;
        Some(
            msg!(
                "rustgen-extern-misfit",
                name = name,
                declared = declared,
                bound = bound,
                path = path,
                first = first,
                stderr = stderr
                    .lines()
                    .skip_while(|l| !l.starts_with("error"))
                    .collect::<Vec<_>>()
                    .join("\n")
            )
            .to_string(),
        )
    }

    /// When the first error is the check that an extern type may cross
    /// threads (a program that starts tasks), the message names the type
    /// and says what to do about it.
    fn extern_type_error(&self, stderr: &str) -> Option<String> {
        let lib = &self.files.iter().find(|(p, _)| p == "src/lib.rs")?.1;
        let head = marker_item(lib, rustc_place(stderr)?, "extern type ")?;
        let (name, at) = head.split_once(" must cross threads, bound at ")?;
        let first = stderr.lines().find(|l| l.starts_with("error"))?;
        Some(
            msg!(
                "rustgen-extern-type-not-send",
                name = name,
                at = at,
                first = first
            )
            .to_string(),
        )
    }

    /// Builds the crate in `dir` with Cargo (its target directory is shared
    /// through `target_dir`) and returns the path of the binary.
    pub fn build(
        &self,
        name: &str,
        dir: &std::path::Path,
        target_dir: &std::path::Path,
        release: bool,
    ) -> Result<std::path::PathBuf, String> {
        self.build_with_observer(name, dir, target_dir, release, None, |_| {})
    }

    /// As `build`, notifying an observer at the write and Cargo boundaries.
    /// `Written` describes generated source reuse, not Cargo's artifact cache.
    /// `target` is a Rust target triple other than the host's, one of
    /// [`WASM_TARGETS`]; the path returned is then the `.wasm` module.
    pub fn build_with_observer(
        &self,
        name: &str,
        dir: &std::path::Path,
        target_dir: &std::path::Path,
        release: bool,
        target: Option<&str>,
        mut observe: impl FnMut(BuildEvent),
    ) -> Result<std::path::PathBuf, String> {
        observe(BuildEvent::Write);
        let stats = self.write_with_stats(dir).map_err(|e| {
            msg!(
                "rustgen-write-failed",
                dir = dir.display().to_string(),
                error = e.to_string()
            )
            .to_string()
        })?;
        observe(BuildEvent::Written(stats));
        observe(BuildEvent::NativeCompile);
        if !release
            && target.is_none()
            && let Some(features) = self.rt_features_alone()
        {
            match self.build_direct(name, dir, target_dir, &features) {
                Ok(bin) => return Ok(bin),
                Err(crate::direct::Failed::Error(e)) => return Err(e),
                Err(crate::direct::Failed::Fallback) => {}
            }
        }
        let mut cmd =
            std::process::Command::new(std::env::var("CARGO").unwrap_or_else(|_| "cargo".into()));
        cmd.arg("build")
            .arg("--quiet")
            .arg("--manifest-path")
            .arg(dir.join("Cargo.toml"))
            .env("CARGO_TARGET_DIR", target_dir)
            .env("CARGO_BUILD_BUILD_DIR", target_dir)
            .env("CARGO_TERM_COLOR", "never");
        if release {
            cmd.arg("--release");
        }
        if let Some(t) = target {
            cmd.arg("--target").arg(t);
        }
        let out = cmd
            .output()
            .map_err(|e| msg!("rustgen-cannot-run-cargo", error = e.to_string()).to_string())?;
        if !out.status.success() {
            return Err(self.rejected(&String::from_utf8_lossy(&out.stderr), dir));
        }
        let profile = if release { "release" } else { "debug" };
        Ok(match target {
            None => target_dir.join(profile).join(name),
            Some(t) => target_dir
                .join(t)
                .join(profile)
                .join(format!("{name}.wasm")),
        })
    }
}

impl Workspace {
    /// The error for rustc's `stderr` on the crate in `dir`.
    pub(crate) fn rejected(&self, stderr: &str, dir: &std::path::Path) -> String {
        if let Some(e) = self.extern_type_error(stderr) {
            return e;
        }
        if let Some(e) = self.extern_error(stderr) {
            return e;
        }
        msg!(
            "rustgen-rustc-rejected",
            dir = dir.display().to_string(),
            stderr = stderr.to_string()
        )
        .to_string()
    }
}

/// The line and column of the first place in `src/lib.rs` that rustc's
/// message points at.
fn rustc_place(stderr: &str) -> Option<(usize, usize)> {
    let at = stderr
        .lines()
        .find_map(|l| l.trim_start().strip_prefix("--> src/lib.rs:"))?;
    let mut it = at.split(':');
    let line = it.next()?.trim().parse().ok()?;
    let col = it.next()?.trim().parse().ok()?;
    Some((line, col))
}

/// The text of the marker (`#[doc = " <prefix>…"]`, which `to_string` may space as `# [doc = …]`) of the item that holds
/// the place `(line, col)` of the generated library: the generator writes one
/// before each item whose errors are explained in other terms. The library
/// is laid out by `rustfmt` or, without it, one item to a line, so the place
/// is found by its offset.
fn marker_item(lib: &str, (line, col): (usize, usize), prefix: &str) -> Option<String> {
    let start: usize = lib
        .split_inclusive('\n')
        .take(line.checked_sub(1)?)
        .map(str::len)
        .sum();
    let at = start
        + lib[start..]
            .char_indices()
            .nth(col.checked_sub(1)?)
            .map_or(lib.len() - start, |(i, _)| i);
    let open = format!("[doc = \" {prefix}");
    let m = lib[..at].rfind(&open)?;
    // The marker's text, and where its literal ends.
    let mut text = String::new();
    let mut escaped = false;
    let mut literal_end = None;
    for (i, c) in lib[m + open.len()..].char_indices() {
        match (escaped, c) {
            (true, c) => {
                text.push(c);
                escaped = false;
            }
            (false, '\\') => escaped = true,
            (false, '"') => {
                literal_end = Some(m + open.len() + i + 1);
                break;
            }
            (false, c) => text.push(c),
        }
    }
    // The item ends where the braces opened after the marker close.
    let mut depth = 0usize;
    let mut end = None;
    for (i, c) in lib[literal_end?..].char_indices() {
        match c {
            '{' => depth += 1,
            '}' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    end = Some(literal_end? + i);
                    break;
                }
            }
            _ => {}
        }
    }
    if at > end? {
        return None;
    }
    Some(text)
}

/// The library crate's name as a path segment in `main.rs`. A tote may be
/// named after a Rust keyword (`gen` is reserved since Rust 2024); Cargo
/// accepts such a package, and the path reaches it as a raw identifier.
fn crate_ident(name: &str) -> proc_macro2::Ident {
    id(name)
}

#[cfg(test)]
mod crate_ident_tests {
    use super::crate_ident;

    #[test]
    fn a_keyword_tote_is_reached_as_a_raw_identifier() {
        assert_eq!(crate_ident("gen").to_string(), "r#gen");
        assert_eq!(crate_ident("highlight").to_string(), "highlight");
    }
}
