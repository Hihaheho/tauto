//! Stable host inputs; Cargo still checks freshness and every test still runs.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;
use tauto_syntax::Sha256;

pub struct Fixture {
    name: String,
    files: RefCell<BTreeMap<String, String>>,
}

pub fn scratch(name: &str) -> Fixture {
    Fixture {
        name: name.into(),
        files: RefCell::default(),
    }
}

pub fn write(fixture: &Fixture, path: &str, text: &str) {
    assert!(
        Path::new(path)
            .components()
            .all(|c| matches!(c, std::path::Component::Normal(_)))
    );
    fixture.files.borrow_mut().insert(path.into(), text.into());
}

impl Fixture {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn files(&self) -> BTreeMap<String, String> {
        self.files.borrow().clone()
    }
    pub fn get(&self, path: &str) -> Option<String> {
        self.files.borrow().get(path).cloned()
    }
    pub fn read(&self, path: &str) -> String {
        self.get(path).unwrap()
    }
    pub fn remove_prefix(&self, prefix: &str) {
        self.files
            .borrow_mut()
            .retain(|p, _| !p.starts_with(prefix));
    }

    fn key(&self) -> String {
        let mut hash = Sha256::new();
        part(&mut hash, b"fixture-package-identity-v1");
        part(&mut hash, self.name.as_bytes());
        for (path, text) in self.files.borrow().iter() {
            part(&mut hash, path.as_bytes());
            part(&mut hash, text.as_bytes());
        }
        hash.finish_hex()
    }

    // The generated manifests use double-quoted package names and inline
    // direct path dependencies; this is not a general Cargo manifest editor.
    fn materialized_files(&self, key: &str) -> BTreeMap<String, String> {
        let mut files = self.files();
        // Cargo may consider a same-named path package fresh after relocation.
        // Give each fixture-local package its own identity, while preserving
        // dependency aliases used by the Rust host and generated code.
        let mut packages = BTreeMap::new();
        for (path, text) in &files {
            if !path.ends_with("Cargo.toml") {
                continue;
            }
            let mut package = false;
            for line in text.lines() {
                let line = line.trim();
                if line.starts_with('[') {
                    package = line == "[package]";
                }
                if package
                    && line
                        .split_once('=')
                        .is_some_and(|(name, _)| name.trim() == "name")
                {
                    let name = line.split_once('=').unwrap().1.trim().trim_matches('"');
                    assert!(
                        packages
                            .insert(name.to_owned(), format!("{name}-{key}"))
                            .is_none(),
                        "duplicate fixture package: {name}"
                    );
                }
            }
        }
        for (path, text) in &mut files {
            if !path.ends_with("Cargo.toml") {
                continue;
            }
            let mut package = false;
            let mut rewritten = String::new();
            for line in text.lines() {
                let trimmed = line.trim();
                if trimmed.starts_with('[') {
                    package = trimmed == "[package]";
                }
                let line = if let Some((name, value)) = trimmed.split_once('=') {
                    let name = name.trim();
                    if package && name == "name" {
                        format!("name = {:?}", packages[value.trim().trim_matches('"')])
                    } else if let Some(identity) = packages.get(name) {
                        assert!(
                            value.contains("path") && !value.contains("package"),
                            "fixture dependency must be a direct path alias: {line}"
                        );
                        line.replacen('{', &format!("{{ package = {identity:?},"), 1)
                    } else {
                        line.to_owned()
                    }
                } else {
                    line.to_owned()
                };
                rewritten.push_str(&line);
                rewritten.push('\n');
            }
            *text = rewritten;
        }
        files
    }

    pub fn join(&self, path: &str) -> PathBuf {
        self.with_materialized(|dir, _| dir.join(path))
    }

    pub fn with_materialized<T>(&self, run: impl FnOnce(&Path, &Path) -> T) -> T {
        let root = cache_root();
        let key = self.key();
        safe_dir(&root.join("locks"));
        check_namespace(root);
        let lock = open_lock(&root.join("locks").join(&key));
        lock.lock().unwrap();
        let dir = root.join("fixtures").join(format!("{}-{key}", self.name));
        safe_dir(&dir);
        let files = self.materialized_files(&key);
        reconcile(&dir, &files);
        for (path, text) in files.iter() {
            // A resolved lockfile is validated separately before Cargo runs.
            if path == "Cargo.lock"
                && dir.join(".resolved-lock").is_file()
                && dir.join("Cargo.lock").is_file()
            {
                continue;
            }
            write_unchanged(&dir.join(path), text.as_bytes());
        }
        run(&dir, &root.join("target"))
    }
}

fn write_unchanged(path: &Path, bytes: &[u8]) {
    if fs::read(path).ok().as_deref() == Some(bytes) {
        return;
    }
    safe_dir(path.parent().unwrap());
    fs::write(path, bytes).unwrap();
}

fn reconcile(dir: &Path, files: &BTreeMap<String, String>) {
    fn visit(root: &Path, dir: &Path, files: &BTreeMap<String, String>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries {
            let entry = entry.unwrap();
            let path = entry.path();
            let kind = entry.file_type().unwrap();
            if kind.is_dir() {
                let prefix = format!("{}/", path.strip_prefix(root).unwrap().to_str().unwrap());
                assert!(
                    files.keys().any(|p| p.starts_with(&prefix)),
                    "unexpected fixture directory {}; preserved",
                    path.display()
                );
                visit(root, &path, files);
            } else {
                let relative = path.strip_prefix(root).unwrap().to_str().unwrap();
                assert!(
                    kind.is_file()
                        && (files.contains_key(relative) || relative == ".resolved-lock"),
                    "unexpected fixture entry {}; preserved without following or deleting it",
                    path.display()
                );
            }
        }
    }
    visit(dir, dir, files);
}

pub fn invocation_dir() -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let root = cache_root().join("runs");
    safe_dir(&root);
    loop {
        let dir = root.join(format!(
            "{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        match fs::create_dir(&dir) {
            Ok(()) => return dir,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("{}: {error}", dir.display()),
        }
    }
}

pub fn cargo(fixture: &Fixture, args: &[&str]) -> Output {
    cargo_with(fixture, args, |_, output| output)
}

pub fn cargo_with<T>(
    fixture: &Fixture,
    args: &[&str],
    after: impl FnOnce(&Path, Output) -> T,
) -> T {
    fixture.with_materialized(|dir, target| {
        // Cargo's own lock ends before its final executable is consumed.
        // Keep same-named hosts from replacing it during the caller's checks.
        let lock = open_lock(&cache_root().join("target.lock"));
        lock.lock().unwrap();
        safe_dir(target);
        safe_dir(&target.join("build"));
        let command = || {
            let mut cmd = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()));
            cmd.current_dir(dir)
                .env("CARGO_TARGET_DIR", target)
                .env("CARGO_BUILD_BUILD_DIR", target.join("build"))
                .env("CARGO_TERM_COLOR", "never");
            cmd
        };
        let lock_path = dir.join("Cargo.lock");
        let lock_key = || {
            format!(
                "workspace-update-v1:{}",
                tauto_syntax::sha256_hex(&fs::read(&lock_path).unwrap())
            )
        };
        if fs::read_to_string(dir.join(".resolved-lock"))
            .ok()
            .as_deref()
            != Some(&lock_key())
        {
            write_unchanged(&lock_path, fixture.read("Cargo.lock").as_bytes());
            // Refresh fixture-local packages without upgrading the seeded dependencies.
            let out = command()
                .args(["update", "--workspace", "--quiet", "--offline"])
                .output()
                .unwrap();
            assert!(
                out.status.success(),
                "{}",
                String::from_utf8_lossy(&out.stderr)
            );
            write_unchanged(&dir.join(".resolved-lock"), lock_key().as_bytes());
        }
        let output = command()
            .args(args)
            .args(
                ["--locked", "--offline"]
                    .into_iter()
                    .filter(|flag| !args.contains(flag)),
            )
            .output()
            .unwrap();
        after(dir, output)
    })
}

fn open_lock(path: &Path) -> File {
    if let Ok(metadata) = fs::symlink_metadata(path) {
        assert!(
            metadata.is_file() && !metadata.file_type().is_symlink(),
            "invalid cache lock: {}",
            path.display()
        );
    }
    File::options()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(path)
        .unwrap()
}

fn check_namespace(root: &Path) {
    for dir in [
        root.parent().unwrap().to_path_buf(),
        root.to_path_buf(),
        root.join("fixtures"),
    ] {
        let config = dir.join(".cargo");
        assert!(
            matches!(fs::symlink_metadata(&config), Err(error) if error.kind() == std::io::ErrorKind::NotFound),
            "unexpected ancestor Cargo configuration {}; preserved",
            config.display()
        );
    }
}

fn safe_dir(path: &Path) {
    if let Some(parent) = path.parent() {
        safe_dir(parent);
    }
    match fs::symlink_metadata(path) {
        Ok(metadata) => assert!(
            metadata.is_dir() && !metadata.file_type().is_symlink(),
            "cache directory is not an ordinary directory: {}",
            path.display()
        ),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => match fs::create_dir(path) {
            Ok(()) => (),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => safe_dir(path),
            Err(error) => panic!("{}: {error}", path.display()),
        },
        Err(error) => panic!("{}: {error}", path.display()),
    }
}

fn part(hash: &mut Sha256, bytes: &[u8]) {
    hash.update(&(bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

fn cache_root() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .unwrap();
        let mut hash = Sha256::new();
        part(&mut hash, b"tauto-build-host-v1");
        part(&mut hash, root.as_os_str().as_encoded_bytes());
        // Path identity matters for env!(CARGO_MANIFEST_DIR), as well as bytes.
        for path in [
            "crates",
            "std",
            "meta",
            "Cargo.toml",
            "Cargo.lock",
            "Tauto.eure",
            ".cargo/config.toml",
            "rust-toolchain.toml",
        ] {
            hash_path(&mut hash, &root.join(path));
        }
        let mut env: Vec<_> = std::env::vars_os()
            .filter(|(key, _)| {
                let key = key.to_string_lossy();
                (key.starts_with("CARGO_")
                    || key.starts_with("RUST")
                    || key.starts_with("TAUTO_")
                    || matches!(
                        &*key,
                        "PATH" | "CC" | "CXX" | "AR" | "LD" | "CFLAGS" | "CXXFLAGS"
                    ))
                    && key != "CARGO_MAKEFLAGS"
            })
            .collect();
        env.sort();
        for (key, value) in env {
            part(&mut hash, key.as_encoded_bytes());
            part(&mut hash, value.as_encoded_bytes());
        }
        for (var, fallback) in [("RUSTC", "rustc"), ("CARGO", "cargo")] {
            let tool = std::env::var_os(var).unwrap_or_else(|| fallback.into());
            let output = Command::new(tool).arg("-vV").output().unwrap();
            assert!(output.status.success());
            part(&mut hash, &output.stdout);
        }
        for var in ["RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"] {
            if let Some(path) = std::env::var_os(var).filter(|v| !v.is_empty()) {
                let path = PathBuf::from(path);
                let resolved = if path.components().count() == 1 {
                    std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
                        .map(|dir| dir.join(&path))
                        .find(|candidate| candidate.is_file())
                        .unwrap_or(path)
                } else {
                    path
                };
                hash_path(&mut hash, &resolved);
            }
        }
        let home = std::env::var_os("CARGO_HOME")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|p| PathBuf::from(p).join(".cargo")));
        if let Some(home) = home {
            for name in ["config", "config.toml"] {
                hash_path(&mut hash, &home.join(name));
            }
        }
        let temp = std::env::temp_dir().canonicalize().unwrap();
        for ancestor in temp.ancestors() {
            for name in ["config", "config.toml"] {
                hash_path(&mut hash, &ancestor.join(".cargo").join(name));
            }
        }
        temp.join("tauto-build-tests").join(hash.finish_hex())
    })
}

fn hash_path(hash: &mut Sha256, path: &Path) {
    part(hash, path.as_os_str().as_encoded_bytes());
    if path.is_dir() {
        let mut entries: Vec<_> = fs::read_dir(path)
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect();
        entries.sort();
        for entry in entries {
            // Fixture bytes have their own identity; compiler output is not an input.
            if matches!(
                entry.file_name().unwrap().to_str(),
                Some("target" | "tests" | "benches" | ".git")
            ) {
                continue;
            }
            hash_path(hash, &entry);
        }
    } else {
        match fs::read(path) {
            Ok(bytes) => {
                part(hash, b"file");
                part(hash, &bytes);
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => part(hash, b"missing"),
            Err(error) => panic!("{}: {error}", path.display()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixture_identity_includes_names_paths_contents_and_removed_files() {
        let a = scratch("identity");
        write(&a, "src/lib.rs", "one");
        let original = a.key();
        let b = scratch("identity");
        write(&b, "src/lib.rs", "one");
        assert_eq!(original, b.key());
        write(&b, "src/lib.rs", "two");
        assert_ne!(original, b.key());
        write(&b, "src/lib.rs", "one");
        write(&b, "src/extra.rs", "");
        assert_ne!(original, b.key());
        b.remove_prefix("src/extra.rs");
        assert_eq!(original, b.key());
        let c = scratch("other-name");
        write(&c, "src/lib.rs", "one");
        assert_ne!(original, c.key());
    }

    #[test]
    fn fixture_package_names_change_without_renaming_dependency_aliases() {
        let fixture = scratch("package-aliases");
        write(
            &fixture,
            "Cargo.toml",
            "[package]\nname = \"host\"\nversion = \"0.1.0\"\n[dependencies]\nlocal = { path = \"local\" }\ntauto-rt = { path = \"/compiler/tauto-rt\" }\n[build-dependencies]\ntauto-build = { path = \"/compiler/tauto-build\" }\n",
        );
        write(
            &fixture,
            "local/Cargo.toml",
            "[package]\nname = \"local\"\nversion = \"0.1.0\"\n",
        );
        let key = fixture.key();
        let files = fixture.materialized_files(&key);
        assert!(files["Cargo.toml"].contains(&format!("name = \"host-{key}\"")));
        assert!(files["local/Cargo.toml"].contains(&format!("name = \"local-{key}\"")));
        assert!(files["Cargo.toml"].contains(&format!(
            "local = {{ package = \"local-{key}\", path = \"local\" }}"
        )));
        assert!(files["Cargo.toml"].contains("tauto-rt = { path = \"/compiler/tauto-rt\" }"));
        assert!(files["Cargo.toml"].contains("tauto-build = { path = \"/compiler/tauto-build\" }"));
    }

    #[test]
    fn stable_sources_keep_mtimes_and_repair_owned_file_tampering() {
        let fixture = scratch("materialization-safety");
        write(&fixture, "src/lib.rs", "expected");
        let path = fixture.join("src/lib.rs");
        let modified = fs::metadata(&path).unwrap().modified().unwrap();
        assert_eq!(fixture.join("src/lib.rs"), path);
        assert_eq!(fs::metadata(&path).unwrap().modified().unwrap(), modified);
        fs::write(&path, "tampered").unwrap();
        assert_eq!(fixture.join("src/lib.rs"), path);
        assert_eq!(fs::read_to_string(path).unwrap(), "expected");
    }

    #[test]
    fn dependency_identity_distinguishes_paths_runtime_variants_and_equal_mtimes() {
        let fixture = scratch("dependency-identity");
        write(&fixture, "runtime-a.rs", "normal runtime");
        write(&fixture, "runtime-b.rs", "normal runtime");
        fixture.with_materialized(|dir, _| {
            let a = dir.join("runtime-a.rs");
            let b = dir.join("runtime-b.rs");
            let digest = |path: &Path| {
                let mut hash = Sha256::new();
                hash_path(&mut hash, path);
                hash.finish_hex()
            };
            let original = digest(&a);
            assert_ne!(original, digest(&b), "embedded manifest paths cannot alias");
            let times =
                fs::FileTimes::new().set_modified(fs::metadata(&a).unwrap().modified().unwrap());
            fs::write(&a, "instrumented runtime").unwrap();
            File::options()
                .write(true)
                .open(&a)
                .unwrap()
                .set_times(times)
                .unwrap();
            assert_ne!(
                original,
                digest(&a),
                "content, not only mtime, identifies a runtime"
            );
        });
    }

    #[test]
    fn unexpected_entries_are_preserved_and_directory_links_are_rejected() {
        let base = std::env::temp_dir()
            .canonicalize()
            .unwrap()
            .join(format!("tauto-fixture-safety-{}", std::process::id()));
        safe_dir(&base);
        let files = BTreeMap::from([("expected".to_owned(), "value".to_owned())]);
        let unexpected = base.join("unexpected");
        fs::write(&unexpected, "user data").unwrap();
        let result = std::panic::catch_unwind(|| reconcile(&base, &files));
        assert!(result.is_err());
        assert_eq!(fs::read_to_string(&unexpected).unwrap(), "user data");
        fs::remove_file(unexpected).unwrap();
        #[cfg(unix)]
        {
            let outside = base.join("outside");
            fs::create_dir(&outside).unwrap();
            let link = base.join("link");
            std::os::unix::fs::symlink(&outside, &link).unwrap();
            assert!(std::panic::catch_unwind(|| safe_dir(&link.join("child"))).is_err());
            assert!(!outside.join("child").exists());
            fs::remove_file(link).unwrap();
            fs::remove_dir(outside).unwrap();
        }
        fs::remove_dir(base).unwrap();
    }

    #[test]
    fn native_runtime_variants_and_manifest_paths_cannot_reuse_stale_artifacts() {
        fn fixture(marker: &str) -> Fixture {
            let fixture = scratch("native-cache-marker");
            write(
                &fixture,
                "Cargo.toml",
                "[package]\nname = \"cache-marker\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\nmarker-runtime = { path = \"runtime\" }\n[workspace]\n",
            );
            write(
                &fixture,
                "Cargo.lock",
                &fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../Cargo.lock"))
                    .unwrap(),
            );
            write(
                &fixture,
                "runtime/Cargo.toml",
                "[package]\nname = \"marker-runtime\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
            );
            write(
                &fixture,
                "runtime/src/lib.rs",
                &format!(
                    "pub fn marker() -> &'static str {{ {marker:?} }}\npub fn manifest() -> &'static str {{ env!(\"CARGO_MANIFEST_DIR\") }}\n"
                ),
            );
            write(
                &fixture,
                "src/main.rs",
                "fn main() { println!(\"{}|{}|{}\", marker_runtime::marker(), marker_runtime::manifest(), env!(\"CARGO_MANIFEST_DIR\")); }\n",
            );
            fixture
        }
        let normal = fixture("normal");
        let instrumented = fixture("instrumented");
        for fixture in [&normal, &instrumented] {
            fixture.with_materialized(|dir, _| {
                for name in ["src/main.rs", "runtime/src/lib.rs"] {
                    File::options()
                        .write(true)
                        .open(dir.join(name))
                        .unwrap()
                        .set_times(fs::FileTimes::new().set_modified(std::time::UNIX_EPOCH))
                        .unwrap();
                }
            });
        }
        for (fixture, marker) in [
            (&normal, "normal"),
            (&instrumented, "instrumented"),
            (&normal, "normal"),
        ] {
            let expected = fixture.with_materialized(|dir, _| {
                format!(
                    "{marker}|{}|{}\n",
                    dir.join("runtime").display(),
                    dir.display()
                )
            });
            let out = cargo(fixture, &["run", "--quiet"]);
            assert!(
                out.status.success(),
                "{}",
                String::from_utf8_lossy(&out.stderr)
            );
            // The oracle lives outside the possibly stale executable.
            assert_eq!(String::from_utf8(out.stdout).unwrap(), expected);
        }
        // A marker alone must not make a deleted or corrupted lockfile reusable.
        let lock = normal.join("Cargo.lock");
        fs::remove_file(&lock).unwrap();
        let out = cargo(&normal, &["check", "--quiet"]);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        fs::write(lock, "invalid lockfile").unwrap();
        let out = cargo(&normal, &["check", "--quiet"]);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
}
