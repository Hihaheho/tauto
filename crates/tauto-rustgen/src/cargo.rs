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
            stack_mb: m.rust.stack_mb,
            main_thread: m.rust.main_thread,
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
            baked_permissions: None,
        }
    }
}

#[derive(Default)]
pub struct Options {
    /// `rust.executor = "threads"`: each task has a thread of its own. Else a
    /// program that starts tasks runs them on the reactor
    /// (`tauto_rt::reactor`, on tokio).
    pub threads: bool,
    /// `rust.stack-mb`: the stack the generated `main` asks for, in MiB.
    pub stack_mb: Option<u32>,
    /// `rust.main-thread`: the generated `main` runs the program on the
    /// process's main thread.
    pub main_thread: bool,
    /// `rust.dependencies`: `(name, Cargo.toml value)`.
    pub dependencies: Vec<(String, String)>,
    /// The bridge crate: its name and the path of its directory.
    pub bridge: Option<(String, String)>,
    /// The permissions the program is built with (`--allow-*` flags), fixed
    /// in the binary: it then reads no `--allow-*` of its own and gives its
    /// whole command line to the program. `None` for a crate that is run by
    /// whoever starts it with the flags (the test harnesses).
    pub baked_permissions: Option<Vec<String>>,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuildEvent {
    Write,
    Written(WriteStats),
    NativeCompile,
    /// There was no `Cargo.lock` beside `Tauto.eure`, so one was made there.
    LockCreated,
}

/// The tote's own lockfile, which pins what a Cargo build resolves.
#[derive(Clone, Debug)]
pub struct Lock {
    /// `Cargo.lock` beside `Tauto.eure`; `Tauto.Cargo.lock` when a `Cargo.toml`
    /// sits there too, for then `Cargo.lock` is that crate's (`Lock::beside`).
    pub file: std::path::PathBuf,
    /// Resolve again (`cargo update`) and write the result back to `file`.
    pub update: bool,
}

impl Lock {
    /// The lock of the tote whose `Tauto.eure` is in `tote`. A `Cargo.lock`
    /// beside a `Cargo.toml` belongs to the crate that `Cargo.toml` makes, not
    /// to the tote, so the tote then keeps its lock in `Tauto.Cargo.lock`
    /// and never reads or writes the crate's.
    pub fn beside(tote: &std::path::Path, update: bool) -> Lock {
        let name = if tote.join("Cargo.toml").exists() {
            "Tauto.Cargo.lock"
        } else {
            "Cargo.lock"
        };
        Lock {
            file: tote.join(name),
            update,
        }
    }
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

/// tauto's git repository, which a bridge crate names to depend on tauto-rt.
pub const TAUTO_GIT: &str = "https://github.com/Hihaheho/tauto";

/// Every `.rs` file under `src` of tauto-rt, tauto-identity and
/// tauto-rt-signal, listed by `build.rs` from the directories themselves.
const BUNDLED: &[(&str, &str)] = include!(concat!(env!("OUT_DIR"), "/bundled_sources.rs"));

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
tauto-identity = { path = \"../tauto-identity\" }
tauto-rt-signal = { path = \"../tauto-rt-signal\" }
reqwest = { version = \"=0.13.5\", optional = true, default-features = false, features = [\"blocking\", \"rustls\"] }
url = { version = \"=2.5.8\", optional = true }
rustls = { version = \"=0.23.46\", optional = true, default-features = false, features = [\"aws_lc_rs\", \"std\", \"tls12\"] }
rustls-platform-verifier = { version = \"=0.7.1\", optional = true }

[target.'cfg(not(all(target_arch = \"wasm32\", target_os = \"unknown\")))'.dependencies]
getrandom = \"=0.3.4\"

[target.'cfg(unix)'.dependencies]
rustix = { version = \"=1.1.2\", default-features = false, features = [\"std\", \"fs\", \"event\", \"net\"] }

[target.'cfg(not(target_family = \"wasm\"))'.dependencies]
tokio = { version = \"=1.53.3\", optional = true, default-features = false, features = [\"rt\", \"time\", \"sync\", \"net\"] }
";

/// Where a generated release binary allocates with jemalloc: not on wasm,
/// and not with MSVC, where jemalloc does not build.
/// The `tikv-jemallocator` version a generated crate pins. A tote's committed
/// `Cargo.lock` has to hold this exact version (`tests/tote_locks.rs`).
pub const JEMALLOC_VERSION: &str = "0.6.1";

const JEMALLOC_CFG: &str = "all(not(target_family = \"wasm\"), not(target_env = \"msvc\"))";

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
    // A bridge crate that uses tauto-rt depends on it from tauto's git
    // repository; the patch makes that the embedded tauto-rt, so the program
    // and the bridge share one runtime (one main thread, one set of statics).
    let cargo = format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
         [dependencies]\n{deps}\n\
         [target.'cfg({JEMALLOC_CFG})'.dependencies]\n\
         tikv-jemallocator = \"={JEMALLOC_VERSION}\"\n\n[workspace]\n\n\
         [patch.\"{TAUTO_GIT}\"]\ntauto-rt = {{ path = \"tauto-rt\" }}\n\n\
         [profile.dev.package.tauto-rt]\nopt-level = 3\n\n\
         [profile.release]\npanic = \"unwind\"\nlto = \"thin\"\n"
    );
    let ident = crate_ident(&name.replace('-', "_"));
    let stack = opts
        .stack_mb
        .map(|mb| {
            let mb = mb as usize;
            quote!(tauto_rt::set_default_stack_mb(#mb);)
        })
        .unwrap_or_default();
    let stack = if opts.main_thread {
        quote!(#stack tauto_rt::set_run_on_main_thread();)
    } else {
        stack
    };
    let run = match &opts.baked_permissions {
        Some(_) => quote!(tauto_rt::run_main_baked(include_str!("permissions.txt"), #ident::run)),
        None => quote!(tauto_rt::run_main(#ident::run)),
    };
    let main = if reactor {
        quote!(
            fn main() -> std::process::ExitCode {
                #stack
                tauto_rt::reactor::install();
                #run
            }
        )
    } else {
        quote!(
            fn main() -> std::process::ExitCode {
                #stack
                #run
            }
        )
    };
    // A release binary allocates with jemalloc where it builds; a debug
    // build keeps the system allocator, so it stays a direct rustc build.
    let cfg: proc_macro2::TokenStream = format!("all(not(debug_assertions), {JEMALLOC_CFG})")
        .parse()
        .expect("cfg");
    let main = quote!(
        #[cfg(#cfg)]
        #[global_allocator]
        static ALLOCATOR: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;
        #main
    );
    let main = render(main);
    let mut files = vec![
        ("Cargo.toml".to_string(), cargo),
        (".cargo/config.toml".to_string(), cargo_config()),
        ("src/lib.rs".to_string(), lib),
        ("src/main.rs".to_string(), main),
        (
            "src/permissions.txt".to_string(),
            opts.baked_permissions
                .as_ref()
                .map(|flags| flags.join("\n"))
                .unwrap_or_default(),
        ),
        ("tauto-rt/Cargo.toml".to_string(), RT_CARGO.to_string()),
        (
            "tauto-identity/Cargo.toml".into(),
            "[package]\nname = \"tauto-identity\"\nversion = \"0.1.0\"\nedition = \"2024\"\n"
                .into(),
        ),
        (
            "tauto-rt-signal/Cargo.toml".into(),
            "[package]\nname = \"tauto-rt-signal\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[target.'cfg(unix)'.dependencies]\nlibc = \"=0.2.190\"\n"
                .into(),
        ),
    ];
    for (p, t) in BUNDLED {
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
                name = name.to_string(),
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
                name = name.to_string(),
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
        self.build_with_observer(name, dir, target_dir, release, None, None, |_| {})
    }

    /// As `build`, notifying an observer at the write and Cargo boundaries.
    /// `Written` describes generated source reuse, not Cargo's artifact cache.
    /// `target` is a Rust target triple other than the host's, one of
    /// [`WASM_TARGETS`]; the path returned is then the `.wasm` module.
    /// With `lock`, a Cargo build resolves exactly what the tote's
    /// `Cargo.lock` says (`--locked`), making that file first if it is missing.
    #[allow(clippy::too_many_arguments)]
    pub fn build_with_observer(
        &self,
        name: &str,
        dir: &std::path::Path,
        target_dir: &std::path::Path,
        release: bool,
        target: Option<&str>,
        lock: Option<&Lock>,
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
            && !lock.is_some_and(|lock| lock.update)
            && let Some(features) = self.rt_features_alone()
        {
            match self.build_direct(name, dir, target_dir, &features) {
                Ok(bin) => return Ok(bin),
                Err(crate::direct::Failed::Error(e)) => return Err(e),
                Err(crate::direct::Failed::Fallback) => {}
            }
        }
        cooldown_enforced()?;
        match lock {
            Some(lock) => {
                if self.sync_lock(dir, target_dir, lock)? {
                    observe(BuildEvent::LockCreated);
                }
            }
            // No tote: the workspace keeps its own lock, resolved once under
            // the cooldown, so the build below still runs `--locked`.
            None => ensure_lock(&dir.join("Cargo.toml"), target_dir)?,
        }
        let locked = true;
        let mut cmd = cargo_command();
        cmd.arg("build")
            .arg("--quiet")
            .arg("--manifest-path")
            .arg(dir.join("Cargo.toml"))
            .env("CARGO_TARGET_DIR", target_dir)
            .env("CARGO_BUILD_BUILD_DIR", target_dir)
            .env("CARGO_TERM_COLOR", "never");
        offline_if_requested(&mut cmd);
        if locked {
            cmd.arg("--locked");
        }
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
            let stderr = String::from_utf8_lossy(&out.stderr);
            if locked && lock_out_of_date(&stderr) {
                if lock.is_none() {
                    // The workspace's own lock is stale (its manifest
                    // changed): resolve it afresh and build once more.
                    let _ = std::fs::remove_file(dir.join("Cargo.lock"));
                    return self.build_with_observer(
                        name, dir, target_dir, release, target, lock, observe,
                    );
                }
                return Err(msg!("rustgen-lock-out-of-date").to_string());
            }
            return Err(self.rejected(&stderr, dir));
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
    /// Puts the tote's `Cargo.lock` in the workspace, or makes it there
    /// (`generate-lockfile`, or `update` when asked) and writes it back to the
    /// tote. True when the tote had no lock and now has one.
    fn sync_lock(
        &self,
        dir: &std::path::Path,
        target_dir: &std::path::Path,
        lock: &Lock,
    ) -> Result<bool, String> {
        let inner = dir.join("Cargo.lock");
        let io = |path: &std::path::Path, e: std::io::Error| {
            msg!(
                "rustgen-write-failed",
                dir = path.display().to_string(),
                error = e.to_string()
            )
            .to_string()
        };
        let existed = lock.file.exists();
        if existed {
            let text = std::fs::read(&lock.file).map_err(|e| io(&lock.file, e))?;
            if std::fs::read(&inner).ok().as_deref() != Some(&text[..]) {
                std::fs::write(&inner, &text).map_err(|e| io(&inner, e))?;
            }
            if !lock.update {
                return Ok(false);
            }
        } else if inner.exists() {
            // A lock from an earlier build is not the tote's: resolve afresh.
            std::fs::remove_file(&inner).map_err(|e| io(&inner, e))?;
        }
        let mut cmd = cargo_command();
        cmd.arg(if existed {
            "update"
        } else {
            "generate-lockfile"
        })
        .arg("--quiet")
        .arg("--manifest-path")
        .arg(dir.join("Cargo.toml"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("CARGO_TERM_COLOR", "never");
        offline_if_requested(&mut cmd);
        let out = cmd
            .output()
            .map_err(|e| msg!("rustgen-cannot-run-cargo", error = e.to_string()).to_string())?;
        if !out.status.success() {
            return Err(msg!(
                "rustgen-lock-failed",
                stderr = String::from_utf8_lossy(&out.stderr).trim_end().to_string()
            )
            .to_string());
        }
        let text = std::fs::read(&inner).map_err(|e| io(&inner, e))?;
        std::fs::write(&lock.file, text).map_err(|e| io(&lock.file, e))?;
        Ok(!existed)
    }

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

/// Cargo for a generated crate. Its lock is resolved with the supply-chain
/// cooldown of this repository's `.cargo/config.toml`: a crate version, the
/// runtime's dependencies and theirs alike, is taken only once it has been
/// published for 14 days. The generated crate lives outside the repository,
/// so the cooldown is given to Cargo here rather than found in a config file.
pub(crate) fn cargo_command() -> std::process::Command {
    let mut cmd =
        std::process::Command::new(std::env::var("CARGO").unwrap_or_else(|_| "cargo".into()));
    // Only Cargo 1.100 or later enforces the cooldown; older Cargo ignores
    // the keys. A `cargo` found through rustup runs this repository's pinned
    // toolchain.
    if std::env::var_os("CARGO").is_none() {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain());
    }
    cmd.env("CARGO_REGISTRY_GLOBAL_MIN_PUBLISH_AGE", MIN_PUBLISH_AGE)
        .env("CARGO_RESOLVER_INCOMPATIBLE_PUBLISH_AGE", "deny");
    cmd
}

/// Refuses to resolve with a Cargo that ignores the publish-age cooldown:
/// only Cargo 1.100 or later enforces it, and an older one would take a
/// crate version published a moment ago without saying so.
pub(crate) fn cooldown_enforced() -> Result<(), String> {
    static CHECKED: std::sync::OnceLock<Result<(), String>> = std::sync::OnceLock::new();
    CHECKED
        .get_or_init(|| {
            let out = cargo_command()
                .arg("-V")
                .output()
                .map_err(|e| format!("could not run Cargo: {e}"))?;
            let version = String::from_utf8_lossy(&out.stdout).trim().to_string();
            if out.status.success() && enforces_cooldown(&version) {
                Ok(())
            } else {
                Err(format!(
                    "Cargo `{version}` does not enforce the 14-day publish-age cooldown on \
                     crate versions; a generated crate is built only with Cargo 1.100 or later \
                     (`{}`, through rustup, or such a `CARGO`)",
                    toolchain()
                ))
            }
        })
        .clone()
}

/// Whether `cargo -V` names Cargo 1.100 or later, the first to enforce the
/// publish-age keys.
fn enforces_cooldown(version: &str) -> bool {
    let mut parts = version
        .strip_prefix("cargo ")
        .unwrap_or("")
        .split(['.', '-', ' ']);
    let major = parts.next().and_then(|p| p.parse::<u32>().ok());
    let minor = parts.next().and_then(|p| p.parse::<u32>().ok());
    matches!((major, minor), (Some(m), Some(n)) if m > 1 || (m == 1 && n >= 100))
}

pub(crate) const MIN_PUBLISH_AGE: &str = "14 days";

/// The generated crate's `.cargo/config.toml`. Tauto gives the cooldown to
/// the Cargo it runs itself (`cargo_command`); this file holds the same
/// cooldown for a Cargo someone runs by hand in the generated crate.
fn cargo_config() -> String {
    format!(
        "# Supply-chain cooldown: refuse crate versions published less than\n\
         # {MIN_PUBLISH_AGE} ago when resolving.\n\
         [registry]\n\
         global-min-publish-age = \"{MIN_PUBLISH_AGE}\"\n\
         \n\
         [resolver]\n\
         incompatible-publish-age = \"deny\"\n"
    )
}

/// The channel of this repository's `rust-toolchain.toml`.
pub(crate) fn toolchain() -> &'static str {
    include_str!("../../../rust-toolchain.toml")
        .lines()
        .find_map(|l| l.strip_prefix("channel = \""))
        .and_then(|l| l.strip_suffix('"'))
        .expect("rust-toolchain.toml names a channel")
}

/// Makes `Cargo.lock` beside `manifest` when there is none, resolving with the
/// publish-age cooldown, so that a build can run with `--locked`.
pub(crate) fn ensure_lock(
    manifest: &std::path::Path,
    target_dir: &std::path::Path,
) -> Result<(), String> {
    if manifest.with_file_name("Cargo.lock").exists() {
        return Ok(());
    }
    let mut cmd = cargo_command();
    cmd.arg("generate-lockfile")
        .arg("--quiet")
        .arg("--manifest-path")
        .arg(manifest)
        .env("CARGO_TARGET_DIR", target_dir)
        .env("CARGO_TERM_COLOR", "never");
    offline_if_requested(&mut cmd);
    let out = cmd
        .output()
        .map_err(|e| msg!("rustgen-cannot-run-cargo", error = e.to_string()).to_string())?;
    if !out.status.success() {
        return Err(msg!(
            "rustgen-lock-failed",
            stderr = String::from_utf8_lossy(&out.stderr).trim_end().to_string()
        )
        .to_string());
    }
    Ok(())
}

/// Whether Cargo refused a `--locked` build because the lock no longer
/// matches the manifest.
fn lock_out_of_date(stderr: &str) -> bool {
    stderr.contains("--locked") && stderr.contains("lock file")
}

/// Makes a Cargo build of a generated crate fail at once, with Cargo's own
/// message that a package is missing, instead of retrying the network, when
/// `CARGO_NET_OFFLINE=true` says there is none.
pub(crate) fn offline_if_requested(cmd: &mut std::process::Command) {
    if std::env::var("CARGO_NET_OFFLINE").is_ok_and(|v| v == "true") {
        cmd.arg("--offline");
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

#[cfg(test)]
mod bundled_tests {
    use super::BUNDLED;

    #[test]
    fn generated_crates_resolve_with_a_cargo_that_enforces_the_cooldown() {
        assert!(super::enforces_cooldown(&format!(
            "cargo {}.0",
            super::toolchain()
        )));
        assert!(super::enforces_cooldown("cargo 1.100.0 (abc 2026-11-01)"));
        assert!(super::enforces_cooldown(
            "cargo 1.101.0-nightly (f3865b2a4 2026-09-29)"
        ));
        assert!(!super::enforces_cooldown("cargo 1.99.0 (abc 2026-09-01)"));
        assert!(!super::enforces_cooldown(""));
    }

    /// Every module a bundled crate declares must be bundled with it, or a
    /// generated workspace fails with "file not found for module".
    #[test]
    fn bundled_crates_carry_every_source_file() {
        for (dir, names) in [
            ("tauto-rt", ["lib.rs", "clock.rs", "show.rs"].as_slice()),
            ("tauto-identity", ["lib.rs", "forked.rs"].as_slice()),
            ("tauto-rt-signal", ["lib.rs"].as_slice()),
        ] {
            for name in names {
                let path = format!("{dir}/src/{name}");
                assert!(
                    BUNDLED.iter().any(|(p, _)| *p == path),
                    "{path} is not bundled"
                );
            }
        }
    }
}
