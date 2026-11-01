//! Fixed-version Cargo workspace releases with explicit, reviewable checkpoints.
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, ExitCode};
use tauto_syntax::sha256_hex;

use crate::i18n;

type Result<T> = std::result::Result<T, String>;
fn help() -> String {
    i18n::t!("publish-crates-help")
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Package {
    name: String,
    version: String,
    manifest: String,
    files: Vec<String>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Plan {
    schema: u32,
    cargo: String,
    config_hash: String,
    registry: String,
    source: String,
    manifest: String,
    packages: Vec<Package>,
    excluded: Vec<String>,
    files: BTreeMap<String, String>,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Journal {
    plan_hash: String,
    // An unsuccessful Cargo workspace invocation may already have uploaded any
    // subset. Never infer which uploads failed from human-readable Cargo output.
    phase: Phase,
    artifacts: BTreeMap<String, String>,
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum Phase {
    Checked,
    SubmittedUnknown,
    CargoConfirmed,
}

pub fn command(args: &[String]) -> ExitCode {
    if matches!(args, []) || args == ["--help"] || args == ["-h"] {
        println!("{}", help());
        return if args.is_empty() {
            ExitCode::from(2)
        } else {
            ExitCode::SUCCESS
        };
    }
    match run(args) {
        Ok(message) => {
            println!("{message}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!(
                "{}",
                crate::i18n::t!("publish-crates-error", error = error.to_string())
            );
            ExitCode::from(1)
        }
    }
}
fn run(args: &[String]) -> Result<String> {
    match args.first().map(String::as_str) {
        Some("plan") => plan(&args[1..]),
        Some("check") if args.len() == 2 => check(Path::new(&args[1])),
        Some("apply" | "resume") if args.len() == 4 && args[2] == "--confirm" => {
            apply(Path::new(&args[1]), &args[3], args[0] == "resume")
        }
        _ => Err(help()),
    }
}
fn io<T>(value: std::io::Result<T>) -> Result<T> {
    value.map_err(|e| e.to_string())
}
fn encode<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    serde_json::to_vec_pretty(value).map_err(|e| e.to_string())
}
fn digest<T: Serialize>(value: &T) -> Result<String> {
    Ok(sha256_hex(&encode(value)?))
}
fn read_json<T: for<'a> Deserialize<'a>>(path: &Path) -> Result<T> {
    regular(path)?;
    if io(fs::metadata(path))?.len() > 16 * 1024 * 1024 {
        return Err(i18n::t!("publish-crates-release-metadata-exceeds-16-mib"));
    }
    let bytes = io(fs::read(path))?;
    serde_json::from_slice(&bytes)
        .map_err(|e| i18n::t!("publish-crates-invalid-metadata", error = e.to_string()))
}
fn regular(path: &Path) -> Result<()> {
    if !io(fs::symlink_metadata(path))?.file_type().is_file() {
        return Err(i18n::t!(
            "publish-crates-not-regular",
            path = path.display().to_string()
        ));
    }
    Ok(())
}
fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut options = OpenOptions::new();
    options.create_new(true).write(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut f = io(options.open(path))?;
    io(f.write_all(bytes))?;
    io(f.sync_all())
}
fn relative(value: &str) -> Result<&Path> {
    let path = Path::new(value);
    if value.is_empty()
        || value.contains('\\')
        || path
            .components()
            .any(|p| !matches!(p, Component::Normal(_)))
    {
        return Err(i18n::t!("publish-crates-release-paths-must-be-nonempty"));
    }
    Ok(path)
}
fn name(value: &str) -> Result<()> {
    if value.is_empty()
        || !value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
    {
        return Err(i18n::t!("publish-crates-package-and-registry-names-must"));
    }
    Ok(())
}
fn execution_environment() -> Result<()> {
    for key in ["HOME", "CARGO_HOME", "RUSTUP_HOME"] {
        if let Some(value) = std::env::var_os(key) {
            if !Path::new(&value).is_absolute() {
                return Err(i18n::t!("publish-crates-env-not-absolute", variable = key));
            }
        }
    }
    let path =
        std::env::var_os("PATH").ok_or_else(|| i18n::t!("publish-crates-path-is-required"))?;
    if std::env::split_paths(&path).any(|p| !p.is_absolute()) {
        return Err(i18n::t!("publish-crates-path-entries-must-be-absolute"));
    }
    for key in [
        "RUSTC",
        "RUSTDOC",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
    ] {
        if let Some(value) = std::env::var_os(key) {
            let path = Path::new(&value);
            if path.components().count() > 1 && !path.is_absolute() {
                return Err(i18n::t!("publish-crates-tool-not-absolute", variable = key));
            }
        }
    }
    Ok(())
}
fn cargo(root: &Path, args: &[String]) -> Result<Vec<u8>> {
    execution_environment()?;
    // Do not relay Cargo output: credential providers and build scripts can
    // include secrets. Operators can run Cargo directly for detailed diagnosis.
    let output = io(Command::new("cargo").current_dir(root).args(args).output())?;
    if !output.status.success() {
        return Err(i18n::t!(
            "publish-crates-cargo-failed",
            command = args.first().map(String::as_str).unwrap_or("command"),
            status = output.status.to_string()
        ));
    }
    Ok(output.stdout)
}
fn cargo_version(root: &Path) -> Result<String> {
    let version = String::from_utf8(cargo(root, &["--version".into()])?)
        .map_err(|_| i18n::t!("publish-crates-invalid-cargo-identity"))?;
    let executable = std::env::split_paths(
        &std::env::var_os("PATH").ok_or_else(|| i18n::t!("publish-crates-path-is-required"))?,
    )
    .map(|p| p.join("cargo"))
    .find(|p| p.is_file())
    .ok_or_else(|| i18n::t!("publish-crates-cargo-executable-not-found"))?;
    let executable = io(fs::canonicalize(executable))?;
    Ok(format!(
        "{}:{}:{}",
        version.trim(),
        executable.display(),
        sha256_hex(&io(fs::read(&executable))?)
    ))
}
fn config_digest(path: &Path) -> Result<String> {
    regular(path)?;
    let bytes = io(fs::read(path))?;
    let text = std::str::from_utf8(&bytes)
        .map_err(|_| i18n::t!("publish-crates-cargo-configuration-must-be-utf"))?;
    // Accept a conservative subset, not a second TOML parser. Cargo validates
    // syntax; quoted/escaped keys and includes are refused rather than guessed.
    // False positives in multiline strings are intentionally fail-closed.
    for line in text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
    {
        let key = if line.starts_with('[') {
            line
        } else {
            line.split_once('=').map_or("", |(k, _)| k)
        };
        if key.contains(['\"', '\'', '\\']) || key.to_ascii_lowercase().contains("include") {
            return Err(i18n::t!("publish-crates-cargo-config-includes-and-quoted"));
        }
    }
    Ok(sha256_hex(&bytes))
}
fn cargo_config(root: &Path) -> Result<String> {
    let mut config = BTreeMap::new();
    // Ancestor config affects Cargo even with an explicit manifest. Bind hashes,
    // never configuration contents or credential files, into the plan.
    for ancestor in root.ancestors() {
        for file in ["config", "config.toml"] {
            let path = ancestor.join(".cargo").join(file);
            if path.exists() {
                regular(&path)?;
                config.insert(path.display().to_string(), config_digest(&path)?);
            }
        }
    }
    let home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cargo")));
    if let Some(home) = home {
        for file in ["config", "config.toml"] {
            let path = home.join(file);
            if path.exists() {
                regular(&path)?;
                config.insert(path.display().to_string(), config_digest(&path)?);
            }
        }
    }
    for (key, value) in std::env::vars_os() {
        let Some(key) = key.to_str() else { continue };
        if (key.starts_with("CARGO_")
            || matches!(
                key,
                "PATH"
                    | "RUSTC"
                    | "RUSTC_WRAPPER"
                    | "RUSTC_WORKSPACE_WRAPPER"
                    | "RUSTDOC"
                    | "RUSTFLAGS"
                    | "RUSTDOCFLAGS"
                    | "RUSTUP_TOOLCHAIN"
                    | "RUSTUP_HOME"
            ))
            && key != "CARGO_REGISTRY_TOKEN"
            && !(key.starts_with("CARGO_REGISTRIES_") && key.ends_with("_TOKEN"))
        {
            let value = value
                .to_str()
                .ok_or_else(|| i18n::t!("publish-crates-release-environment-must-be-utf"))?;
            config.insert(format!("env:{key}"), sha256_hex(value.as_bytes()));
        }
    }
    digest(&config)
}
fn reject_sensitive(path: &Path) -> Result<()> {
    for c in path.components() {
        let Component::Normal(c) = c else {
            return Err(i18n::t!("publish-crates-invalid-snapshot-path"));
        };
        let s = c.to_string_lossy().to_ascii_lowercase();
        if s == ".env"
            || s.starts_with(".env.")
            || matches!(
                s.as_str(),
                "credentials" | "credentials.toml" | ".ssh" | ".aws" | "id_rsa" | "id_ed25519"
            )
            || s.ends_with(".pem")
            || s.ends_with(".key")
        {
            return Err(i18n::t!(
                "publish-crates-snapshot-includes-a-credential-like"
            ));
        }
    }
    Ok(())
}
fn scan(root: &Path) -> Result<BTreeMap<String, String>> {
    if io(Command::new("git")
        .current_dir(root)
        .args(["rev-parse", "--is-inside-work-tree"])
        .output())?
    .status
    .success()
    {
        let output = io(Command::new("git")
            .current_dir(root)
            .args(["ls-files", "-z", "--cached", "--", "."])
            .output())?;
        if !output.status.success() {
            return Err(i18n::t!(
                "publish-crates-cannot-enumerate-tracked-release-files"
            ));
        }
        let mut files = BTreeMap::new();
        for bytes in output.stdout.split(|b| *b == 0).filter(|s| !s.is_empty()) {
            let rel = std::str::from_utf8(bytes)
                .map_err(|_| i18n::t!("publish-crates-non-utf-8-tracked-path"))?;
            let path = relative(rel)?;
            reject_sensitive(path)?;
            regular(&root.join(path))?;
            files.insert(rel.to_string(), sha256_hex(&io(fs::read(root.join(path)))?));
        }
        return Ok(files);
    }
    fn visit(root: &Path, dir: &Path, files: &mut BTreeMap<String, String>) -> Result<()> {
        for entry in io(fs::read_dir(dir))? {
            let entry = io(entry)?;
            if dir == root && matches!(entry.file_name().to_str(), Some(".git" | "target")) {
                continue;
            }
            let path = entry.path();
            let ty = io(entry.file_type())?;
            reject_sensitive(
                path.strip_prefix(root)
                    .map_err(|_| i18n::t!("publish-crates-invalid-snapshot-path"))?,
            )?;
            if ty.is_dir() {
                visit(root, &path, files)?;
            } else if ty.is_file() {
                let rel = path
                    .strip_prefix(root)
                    .map_err(|e| e.to_string())?
                    .to_str()
                    .ok_or_else(|| i18n::t!("publish-crates-non-utf-8-release-path"))?
                    .to_owned();
                relative(&rel)?;
                reject_sensitive(Path::new(&rel))?;
                files.insert(rel, sha256_hex(&io(fs::read(path))?));
            } else {
                return Err(i18n::t!("publish-crates-release-snapshots-do-not-accept"));
            }
        }
        Ok(())
    }
    let mut files = BTreeMap::new();
    visit(root, root, &mut files)?;
    Ok(files)
}
fn clean(root: &Path) -> Result<()> {
    let output = io(Command::new("git")
        .current_dir(root)
        .args(["rev-parse", "--show-toplevel"])
        .output())?;
    if !output.status.success() {
        return Ok(());
    }
    let status = io(Command::new("git")
        .current_dir(root)
        .args(["status", "--porcelain", "--untracked-files=all", "--", "."])
        .output())?;
    if !status.status.success() || !status.stdout.is_empty() {
        return Err(i18n::t!("publish-crates-source-checkout-must-be-clean"));
    }
    Ok(())
}
fn artifact_dir(plan: &Path) -> PathBuf {
    plan.with_extension("release")
}
fn snapshot(plan: &Path) -> PathBuf {
    artifact_dir(plan).join("source")
}
fn journal_path(plan: &Path) -> PathBuf {
    artifact_dir(plan).join("state.json")
}
struct Lock(PathBuf);
impl Drop for Lock {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}
fn lock(plan: &Path) -> Result<Lock> {
    let dir = artifact_dir(plan);
    if !io(fs::symlink_metadata(&dir))?.is_dir() {
        return Err(i18n::t!("publish-crates-release-directory-is-missing-or"));
    }
    let path = dir.join("lock");
    write_new(&path, b"release operation in progress\n")
        .map_err(|_| i18n::t!("publish-crates-release-is-locked-an-interrupted"))?;
    Ok(Lock(path))
}
fn store_journal(plan: &Path, state: &Journal) -> Result<()> {
    let path = journal_path(plan);
    let tmp = path.with_extension("new");
    write_new(&tmp, &encode(state)?)?;
    io(fs::rename(tmp, path))?;
    io(File::open(artifact_dir(plan)).and_then(|d| d.sync_all()))
}
fn load(plan_path: &Path) -> Result<(Plan, String)> {
    let plan: Plan = read_json(plan_path)?;
    if plan.schema != 1 || plan.packages.is_empty() {
        return Err(i18n::t!("publish-crates-unsupported-or-empty-release-plan"));
    }
    relative(&plan.manifest)?;
    if !Path::new(&plan.source).is_absolute() {
        return Err(i18n::t!("publish-crates-source-root-must-be-absolute"));
    }
    name(&plan.registry)?;
    let mut names = BTreeSet::new();
    for package in &plan.packages {
        name(&package.name)?;
        if !names.insert(&package.name) {
            return Err(i18n::t!("publish-crates-duplicate-release-package"));
        }
        relative(&package.manifest)?;
        for file in &package.files {
            relative(file)?;
        }
    }
    for file in plan.files.keys() {
        relative(file)?;
    }
    let hash = digest(&plan)?;
    Ok((plan, hash))
}
fn require_snapshot_config(root: &Path, files: &BTreeMap<String, String>) -> Result<()> {
    for file in [".cargo/config", ".cargo/config.toml"] {
        if root.join(file).exists() && !files.contains_key(file) {
            return Err(i18n::t!(
                "publish-crates-active-workspace-cargo-configuration-is"
            ));
        }
    }
    Ok(())
}
fn reject_ancestor_config(root: &Path) -> Result<()> {
    let home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cargo")));
    let home = home.and_then(|h| fs::canonicalize(h).ok());
    for parent in root.parent().into_iter().flat_map(Path::ancestors) {
        if home.is_some() && fs::canonicalize(parent.join(".cargo")).ok() == home {
            continue;
        }
        if parent.join(".cargo/config").exists() || parent.join(".cargo/config.toml").exists() {
            return Err(i18n::t!(
                "publish-crates-ancestor-cargo-configuration-outside-the"
            ));
        }
    }
    Ok(())
}
fn inventory(root: &Path, manifest: &str) -> Result<Vec<String>> {
    let bytes = cargo(
        root,
        &[
            "package".into(),
            "--list".into(),
            "--offline".into(),
            "--locked".into(),
            "--manifest-path".into(),
            manifest.into(),
        ],
    )?;
    let text = String::from_utf8(bytes)
        .map_err(|_| i18n::t!("publish-crates-non-utf-8-package-inventory"))?;
    let mut files: Vec<String> = text
        .lines()
        .filter(|s| *s != ".cargo_vcs_info.json")
        .map(str::to_owned)
        .collect();
    files.sort();
    for file in &files {
        relative(file)?;
        reject_sensitive(Path::new(file))?;
    }
    Ok(files)
}
fn validate(plan_path: &Path, plan: &Plan) -> Result<PathBuf> {
    let root = snapshot(plan_path);
    if io(fs::symlink_metadata(&root))?.file_type().is_symlink() {
        return Err(i18n::t!("publish-crates-snapshot-cannot-be-a-symlink"));
    }
    let root = io(fs::canonicalize(root))?;
    if scan(&root)? != plan.files {
        return Err(i18n::t!(
            "publish-crates-snapshot-changed-create-and-review"
        ));
    }
    let source = Path::new(&plan.source);
    reject_ancestor_config(source)?;
    reject_ancestor_config(&root)?;
    clean(source)?;
    require_snapshot_config(source, &plan.files)?;
    if scan(source)? != plan.files {
        return Err(i18n::t!(
            "publish-crates-source-changed-since-planning-create"
        ));
    }
    if cargo_version(&root)? != plan.cargo || cargo_config(source)? != plan.config_hash {
        return Err(i18n::t!(
            "publish-crates-cargo-identity-or-configuration-changed"
        ));
    }
    for package in &plan.packages {
        if inventory(source, &package.manifest)? != package.files
            || inventory(&root, &package.manifest)? != package.files
        {
            return Err(i18n::t!(
                "publish-crates-cargo-package-inventory-differs-from"
            ));
        }
    }
    Ok(root)
}
fn selections(plan: &Plan) -> Vec<String> {
    let mut args = vec![
        "--manifest-path".into(),
        plan.manifest.clone(),
        "--registry".into(),
        plan.registry.clone(),
        "--locked".into(),
    ];
    for package in &plan.packages {
        args.extend(["--package".into(), package.name.clone()]);
    }
    args
}
fn package_hashes(root: &Path, plan: &Plan) -> Result<BTreeMap<String, String>> {
    let mut hashes = BTreeMap::new();
    for p in &plan.packages {
        let file = format!("{}-{}.crate", p.name, p.version);
        relative(&file)?;
        let path = root.join("target/package").join(&file);
        regular(&path)?;
        hashes.insert(file, sha256_hex(&io(fs::read(path))?));
    }
    Ok(hashes)
}
fn verify(plan_path: &Path, plan: &Plan) -> Result<BTreeMap<String, String>> {
    let root = validate(plan_path, plan)?;
    for directory in ["target", "target/package"] {
        let path = root.join(directory);
        if path.exists() && !io(fs::symlink_metadata(path))?.file_type().is_dir() {
            return Err(i18n::t!(
                "publish-crates-package-output-directories-must-not"
            ));
        }
    }
    let mut args = vec![
        "package".into(),
        "--offline".into(),
        "--target-dir".into(),
        "target".into(),
    ];
    args.extend(selections(plan));
    cargo(&root, &args)?;
    if scan(&root)? != plan.files {
        return Err(i18n::t!(
            "publish-crates-verification-changed-the-snapshot-no"
        ));
    }
    package_hashes(&root, plan)
}
fn check(path: &Path) -> Result<String> {
    let _lock = lock(path)?;
    let (plan, hash) = load(path)?;
    let old_state = if journal_path(path).exists() {
        let old: Journal = read_json(&journal_path(path))?;
        if old.phase != Phase::Checked {
            return Err(i18n::t!("publish-crates-a-submitted-release-cannot-be"));
        }
        Some(old)
    } else {
        None
    };
    let artifacts = verify(path, &plan)?;
    if let Some(old) = old_state {
        if old.plan_hash != hash || old.artifacts != artifacts {
            return Err(i18n::t!("publish-crates-checked-plan-or-archive-changed"));
        }
    }
    store_journal(
        path,
        &Journal {
            plan_hash: hash.clone(),
            phase: Phase::Checked,
            artifacts,
        },
    )?;
    Ok(i18n::t!(
        "publish-crates-checked",
        n = plan.packages.len(),
        hash = &hash
    ))
}
fn apply(path: &Path, confirm: &str, resume: bool) -> Result<String> {
    let _lock = lock(path)?;
    let (plan, hash) = load(path)?;
    if confirm != hash {
        return Err(i18n::t!("publish-crates-confirm-must-equal-the-complete"));
    }
    let mut state: Journal = read_json(&journal_path(path))
        .map_err(|_| i18n::t!("publish-crates-run-check-successfully-before-apply"))?;
    if state.plan_hash != hash {
        return Err(i18n::t!("publish-crates-checked-plan-hash-differs-no"));
    }
    match state.phase {
        Phase::CargoConfirmed => {
            return if resume {
                Ok(i18n::t!(
                    "publish-crates-cargo-already-confirmed-this-release"
                ))
            } else {
                Err(i18n::t!(
                    "publish-crates-release-already-submitted-use-resume"
                ))
            };
        }
        Phase::SubmittedUnknown => {
            return Err(i18n::t!("publish-crates-cargo-may-have-uploaded-some"));
        }
        Phase::Checked => {}
    }
    if verify(path, &plan)? != state.artifacts {
        return Err(i18n::t!(
            "publish-crates-packaged-artifacts-differ-from-check"
        ));
    }
    let root = validate(path, &plan)?;
    // Persist and fsync before starting the network operation, including the
    // possibility that the parent dies before it observes the child's exit.
    state.phase = Phase::SubmittedUnknown;
    store_journal(path, &state)?;
    let mut args = vec!["publish".into(), "--target-dir".into(), "target".into()];
    args.extend(selections(&plan));
    cargo(&root, &args).map_err(|e| i18n::t!("publish-crates-submitted-unknown", error = e))?;
    if scan(&root)? != plan.files || package_hashes(&root, &plan)? != state.artifacts {
        return Err(i18n::t!(
            "publish-crates-cargo-returned-success-but-release"
        ));
    }
    state.phase = Phase::CargoConfirmed;
    store_journal(path, &state)?;
    Ok(i18n::t!(
        "publish-crates-confirmed",
        n = plan.packages.len(),
        registry = &plan.registry
    ))
}
fn plan(args: &[String]) -> Result<String> {
    let mut manifest = None;
    let mut registry = None;
    let mut out = None;
    let mut workspace = false;
    let mut requested = BTreeSet::new();
    let mut i = 0;
    while i < args.len() {
        let flag = args[i].as_str();
        if flag == "--workspace" {
            if workspace {
                return Err(i18n::t!("publish-crates-duplicate-workspace"));
            }
            workspace = true;
            i += 1;
            continue;
        }
        let value = args.get(i + 1).ok_or_else(help)?.clone();
        match flag {
            "--manifest-path" if manifest.is_none() => manifest = Some(value),
            "--registry" if registry.is_none() => {
                name(&value)?;
                registry = Some(value);
            }
            "--out" if out.is_none() => out = Some(value),
            "-p" | "--package" => {
                name(&value)?;
                if !requested.insert(value) {
                    return Err(i18n::t!("publish-crates-duplicate-package-selection"));
                }
            }
            _ => return Err(help()),
        }
        i += 2;
    }
    if workspace == !requested.is_empty() {
        return Err(i18n::t!("publish-crates-select-exactly-one-of-workspace"));
    }
    let manifest = io(fs::canonicalize(manifest.ok_or_else(help)?))?;
    regular(&manifest)?;
    let registry =
        registry.ok_or_else(|| i18n::t!("publish-crates-registry-is-required-no-implicit"))?;
    let out = PathBuf::from(out.ok_or_else(help)?);
    let out_parent = io(fs::canonicalize(
        out.parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new(".")),
    ))?;
    let out = out_parent.join(
        out.file_name()
            .ok_or_else(|| i18n::t!("publish-crates-plan-must-name-a-file"))?,
    );
    if out.exists() || artifact_dir(&out).exists() {
        return Err(i18n::t!("publish-crates-plan-or-release-directory-already"));
    }
    let metadata_bytes = cargo(
        manifest
            .parent()
            .ok_or_else(|| i18n::t!("publish-crates-manifest-has-no-parent"))?,
        &[
            "metadata".into(),
            "--format-version".into(),
            "1".into(),
            "--no-deps".into(),
            "--offline".into(),
            "--locked".into(),
            "--manifest-path".into(),
            manifest.display().to_string(),
        ],
    )?;
    let metadata: Value = serde_json::from_slice(&metadata_bytes)
        .map_err(|_| i18n::t!("publish-crates-invalid-cargo-workspace-metadata"))?;
    let root = io(fs::canonicalize(
        metadata["workspace_root"]
            .as_str()
            .ok_or_else(|| i18n::t!("publish-crates-cargo-metadata-lacks-workspace-root"))?,
    ))?;
    if out.starts_with(&root) {
        return Err(i18n::t!("publish-crates-write-the-release-plan-outside"));
    }
    // Cargo resolves ancestor configuration by process cwd. Do not silently
    // alter that contract while moving the source to its release snapshot.
    reject_ancestor_config(&root)?;
    reject_ancestor_config(&snapshot(&out))?;
    clean(&root)?;
    let files = scan(&root)?;
    require_snapshot_config(&root, &files)?;
    let members: BTreeSet<&str> = metadata["workspace_members"]
        .as_array()
        .ok_or_else(|| i18n::t!("publish-crates-missing-workspace-members"))?
        .iter()
        .filter_map(Value::as_str)
        .collect();
    let mut packages = Vec::new();
    let mut excluded = Vec::new();
    let mut seen = BTreeSet::new();
    for p in metadata["packages"]
        .as_array()
        .ok_or_else(|| i18n::t!("publish-crates-missing-packages"))?
    {
        if !members.contains(
            p["id"]
                .as_str()
                .ok_or_else(|| i18n::t!("publish-crates-package-lacks-id"))?,
        ) {
            continue;
        }
        let package_name = p["name"]
            .as_str()
            .ok_or_else(|| i18n::t!("publish-crates-package-lacks-name"))?;
        name(package_name)?;
        seen.insert(package_name.to_string());
        if !workspace && !requested.contains(package_name) {
            excluded.push(format!("{package_name}: not selected"));
            continue;
        }
        if let Some(allowed) = p["publish"].as_array() {
            if allowed.is_empty() {
                if !workspace {
                    return Err(i18n::t!(
                        "publish-crates-publish-false",
                        name = package_name
                    ));
                }
                excluded.push(format!("{package_name}: publish = false"));
                continue;
            }
            if !allowed.iter().any(|v| v.as_str() == Some(&registry)) {
                return Err(i18n::t!(
                    "publish-crates-registry-not-permitted",
                    name = package_name,
                    registry = &registry
                ));
            }
        }
        for dep in p["dependencies"]
            .as_array()
            .ok_or_else(|| i18n::t!("publish-crates-missing-package-dependencies"))?
        {
            if let Some(path) = dep["path"].as_str() {
                if !io(fs::canonicalize(path))?.starts_with(&root) {
                    return Err(i18n::t!(
                        "publish-crates-path-dependency",
                        name = package_name
                    ));
                }
            }
        }
        let package_manifest =
            io(fs::canonicalize(p["manifest_path"].as_str().ok_or_else(
                || i18n::t!("publish-crates-package-lacks-manifest"),
            )?))?;
        let rel = package_manifest
            .strip_prefix(&root)
            .map_err(|_| i18n::t!("publish-crates-package-manifest-escapes-workspace"))?
            .to_str()
            .ok_or_else(|| i18n::t!("publish-crates-non-utf-8-manifest-path"))?
            .to_owned();
        relative(&rel)?;
        let version = p["version"]
            .as_str()
            .ok_or_else(|| i18n::t!("publish-crates-package-lacks-version"))?
            .to_owned();
        if version.is_empty()
            || !version
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b".-+".contains(&b))
        {
            return Err(i18n::t!("publish-crates-unsupported-package-version"));
        }
        let inventory = inventory(&root, &rel)?;
        packages.push(Package {
            name: package_name.to_owned(),
            version,
            manifest: rel,
            files: inventory,
        });
    }
    if !requested.is_subset(&seen) {
        return Err(i18n::t!("publish-crates-selected-package-is-not-a"));
    }
    if packages.is_empty() {
        return Err(i18n::t!("publish-crates-no-publishable-packages-selected"));
    }
    packages.sort_by(|a, b| a.name.cmp(&b.name));
    excluded.sort();
    if scan(&root)? != files {
        return Err(i18n::t!(
            "publish-crates-planning-changed-workspace-files-no"
        ));
    }
    let manifest = manifest
        .strip_prefix(&root)
        .map_err(|_| i18n::t!("publish-crates-manifest-is-outside-workspace"))?
        .to_str()
        .ok_or_else(|| i18n::t!("publish-crates-non-utf-8-manifest-path"))?
        .to_owned();
    let plan = Plan {
        schema: 1,
        cargo: cargo_version(&root)?,
        config_hash: cargo_config(&root)?,
        registry,
        source: root.display().to_string(),
        manifest,
        packages,
        excluded,
        files,
    };
    let mut directory = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        directory.mode(0o700);
    }
    io(directory.create(artifact_dir(&out)))?;
    let snapshot = snapshot(&out);
    io(fs::create_dir(&snapshot))?;
    for file in plan.files.keys() {
        let path = snapshot.join(relative(file)?);
        io(fs::create_dir_all(path.parent().ok_or_else(|| {
            i18n::t!("publish-crates-snapshot-path-lacks-parent")
        })?))?;
        io(fs::copy(root.join(file), path))?;
    }
    for package in &plan.packages {
        if inventory(&snapshot, &package.manifest)? != package.files {
            return Err(i18n::t!(
                "publish-crates-snapshot-package-inventory-differs-from"
            ));
        }
    }
    if scan(&snapshot)? != plan.files {
        return Err(i18n::t!("publish-crates-snapshot-copy-differs-from-source"));
    }
    write_new(&out, &encode(&plan)?)?;
    Ok(i18n::t!(
        "publish-crates-planned",
        n = plan.packages.len(),
        registry = &plan.registry,
        path = out.display().to_string(),
        hash = digest(&plan)?
    ))
}
