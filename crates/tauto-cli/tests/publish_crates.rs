//! All upload paths use a local fake Cargo. No registry requests are made.
#![cfg(unix)]
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture {
    dir: PathBuf,
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.dir);
    }
}
impl Fixture {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!(
            "tauto-release-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(dir.join("source/src")).unwrap();
        fs::create_dir(dir.join("bin")).unwrap();
        fs::create_dir(dir.join("cargo-home")).unwrap();
        fs::write(
            dir.join("source/Cargo.toml"),
            "[package]\nname = \"alpha\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        fs::write(
            dir.join("source/src/lib.rs"),
            "pub fn value() -> u64 { 1 }\n",
        )
        .unwrap();
        fs::write(dir.join("source/Cargo.lock"), "version = 4\n").unwrap();
        let root = dir.join("source");
        fs::write(
            dir.join("metadata.json"),
            serde_json::to_vec(&serde_json::json!({
                "workspace_root": root, "workspace_members": ["alpha"],
                "packages": [{"id":"alpha", "name":"alpha", "version":"0.1.0", "publish":null,
                    "manifest_path": root.join("Cargo.toml"), "dependencies":[]}]
            }))
            .unwrap(),
        )
        .unwrap();
        fs::write(
            dir.join("bin/cargo"),
            r#"#!/bin/sh
set -eu
printf '%s\n' "$*" >> "$MOCK_ROOT/calls"
case "$1" in
--version) printf 'cargo release-test\n';;
metadata) cat "$MOCK_ROOT/metadata.json";;
package)
  case " $* " in *' --list '*) printf 'Cargo.lock\nCargo.toml\nCargo.toml.orig\nsrc/lib.rs\n'; exit 0;; esac
  mkdir -p target/package
  printf 'deterministic package' > target/package/alpha-0.1.0.crate
  test ! -f "$MOCK_ROOT/change-artifact" || printf 'changed' >> target/package/alpha-0.1.0.crate
  test ! -f "$MOCK_ROOT/failed-check" || { printf 'TOP_SECRET\n' >&2; exit 7; }
  ;;
publish)
  mkdir -p target/package
  printf 'deterministic package' > target/package/alpha-0.1.0.crate
  case " $* " in
    *' --dry-run '*)
      test ! -f "$MOCK_ROOT/change-artifact" || printf 'changed' >> target/package/alpha-0.1.0.crate
      test ! -f "$MOCK_ROOT/failed-check" || { printf 'TOP_SECRET\n' >&2; exit 7; }
      ;;
    *) printf 'upload\n' >> "$MOCK_ROOT/uploads"
       test ! -f "$MOCK_ROOT/unknown" || { printf 'TOP_SECRET\n' >&2; exit 8; };;
  esac;;
*) exit 9;;
esac
"#,
        )
        .unwrap();
        fs::set_permissions(dir.join("bin/cargo"), fs::Permissions::from_mode(0o700)).unwrap();
        Self { dir }
    }
    fn plan_path(&self) -> PathBuf {
        self.dir.join("release.json")
    }
    fn call(&self, args: &[&str]) -> Output {
        self.call_env(args, &[])
    }
    fn call_env(&self, args: &[&str], vars: &[(&str, &str)]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("publish-crates")
            .args(args)
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .env(
                "PATH",
                format!(
                    "{}:{}",
                    self.dir.join("bin").display(),
                    std::env::var("PATH").unwrap_or_default()
                ),
            )
            .env("CARGO_HOME", self.dir.join("cargo-home"))
            .env("MOCK_ROOT", &self.dir)
            .envs(vars.iter().copied())
            .current_dir(&self.dir)
            .output()
            .unwrap()
    }
    fn plan(&self) -> String {
        let out = self.call(&[
            "plan",
            "--manifest-path",
            "source/Cargo.toml",
            "--registry",
            "crates-io",
            "--workspace",
            "--out",
            "release.json",
        ]);
        success(&out);
        String::from_utf8(out.stdout)
            .unwrap()
            .lines()
            .find_map(|l| l.strip_prefix("Plan hash: ").map(str::to_owned))
            .unwrap()
    }
    fn state(&self) -> serde_json::Value {
        serde_json::from_slice(&fs::read(self.dir.join("release.release/state.json")).unwrap())
            .unwrap()
    }
    fn touch(&self, file: &str) {
        fs::write(self.dir.join(file), "").unwrap();
    }
    fn uploads(&self) -> usize {
        fs::read_to_string(self.dir.join("uploads"))
            .unwrap_or_default()
            .lines()
            .count()
    }
    fn edit_plan(&self, f: impl FnOnce(&mut serde_json::Value)) {
        let mut p: serde_json::Value =
            serde_json::from_slice(&fs::read(self.plan_path()).unwrap()).unwrap();
        f(&mut p);
        fs::write(self.plan_path(), serde_json::to_vec(&p).unwrap()).unwrap();
    }
}
fn success(out: &Output) {
    assert!(
        out.status.success(),
        "stdout={} stderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}
fn fails(out: &Output, message: &str) {
    assert!(!out.status.success());
    assert!(
        String::from_utf8_lossy(&out.stderr).contains(message),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
#[test]
fn release_requires_check_exact_hash_and_does_not_resend_confirmed() {
    let f = Fixture::new();
    let hash = f.plan();
    assert_eq!(f.uploads(), 0);
    fails(
        &f.call(&["apply", "release.json", "--confirm", &hash]),
        "run check",
    );
    success(&f.call(&["check", "release.json"]));
    fails(
        &f.call(&["apply", "release.json", "--confirm", "yes"]),
        "complete reviewed plan hash",
    );
    assert_eq!(f.uploads(), 0);
    success(&f.call(&["apply", "release.json", "--confirm", &hash]));
    assert_eq!(f.uploads(), 1);
    assert_eq!(f.state()["phase"], "cargo-confirmed");
    success(&f.call(&["resume", "release.json", "--confirm", &hash]));
    assert_eq!(f.uploads(), 1);
    fails(&f.call(&["check", "release.json"]), "cannot be reset");
    let calls = fs::read_to_string(f.dir.join("calls")).unwrap();
    for line in calls.lines().filter(|l| {
        l.starts_with("metadata") || l.starts_with("package") || l.contains("--dry-run")
    }) {
        assert!(line.contains("--offline"), "{line}");
    }
    assert!(calls.contains("--registry crates-io --locked --package alpha"));
}
#[test]
fn uncertain_upload_never_retries_or_exposes_cargo_output() {
    let f = Fixture::new();
    let hash = f.plan();
    success(&f.call(&["check", "release.json"]));
    f.touch("unknown");
    let out = f.call(&["apply", "release.json", "--confirm", &hash]);
    fails(&out, "submitted-unknown");
    assert!(!String::from_utf8_lossy(&out.stderr).contains("TOP_SECRET"));
    assert_eq!(f.state()["phase"], "submitted-unknown");
    fails(
        &f.call(&["resume", "release.json", "--confirm", &hash]),
        "Automatic retry is forbidden",
    );
    assert_eq!(f.uploads(), 1);
}
#[test]
fn source_snapshot_config_and_artifact_changes_block_upload() {
    for change in [
        "source/src/lib.rs",
        "release.release/source/src/lib.rs",
        "cargo-home/config.toml",
        "change-artifact",
    ] {
        let f = Fixture::new();
        let hash = f.plan();
        success(&f.call(&["check", "release.json"]));
        f.touch(change);
        let out = f.call(&["apply", "release.json", "--confirm", &hash]);
        assert!(!out.status.success(), "{change}");
        assert_eq!(f.uploads(), 0, "{change}");
    }
}
#[test]
fn invalid_plan_paths_and_unknown_schema_fail_closed() {
    for bad in [
        "../outside",
        "/tmp/outside",
        "a/../../outside",
        "a\\outside",
    ] {
        let f = Fixture::new();
        f.plan();
        f.edit_plan(|p| p["manifest"] = bad.into());
        fails(&f.call(&["check", "release.json"]), "relative paths");
        assert_eq!(f.uploads(), 0);
    }
    let f = Fixture::new();
    f.plan();
    f.edit_plan(|p| p["schema"] = 9.into());
    fails(&f.call(&["check", "release.json"]), "unsupported");
}
#[test]
fn publish_false_and_registry_restrictions_are_not_overridden() {
    for allowed in [serde_json::json!([]), serde_json::json!(["other"])] {
        let f = Fixture::new();
        let path = f.dir.join("metadata.json");
        let mut value: serde_json::Value =
            serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        value["packages"][0]["publish"] = allowed;
        fs::write(path, serde_json::to_vec(&value).unwrap()).unwrap();
        let out = f.call(&[
            "plan",
            "--manifest-path",
            "source/Cargo.toml",
            "--registry",
            "crates-io",
            "-p",
            "alpha",
            "--out",
            "release.json",
        ]);
        assert!(!out.status.success());
        assert!(!f.plan_path().exists());
        assert_eq!(f.uploads(), 0);
    }
}
#[test]
fn failed_check_and_stale_lock_do_not_authorize_upload() {
    let f = Fixture::new();
    let hash = f.plan();
    f.touch("failed-check");
    fails(&f.call(&["check", "release.json"]), "output withheld");
    fails(
        &f.call(&["apply", "release.json", "--confirm", &hash]),
        "run check",
    );
    f.touch("release.release/lock");
    fails(&f.call(&["check", "release.json"]), "locked");
    assert_eq!(f.uploads(), 0);
}
#[test]
fn symlinks_are_not_snapshotted_or_followed_as_release_state() {
    let f = Fixture::new();
    std::os::unix::fs::symlink("src/lib.rs", f.dir.join("source/link")).unwrap();
    fails(
        &f.call(&[
            "plan",
            "--manifest-path",
            "source/Cargo.toml",
            "--registry",
            "crates-io",
            "--workspace",
            "--out",
            "release.json",
        ]),
        "symlinks",
    );
    assert!(!f.plan_path().exists());
}
#[test]
fn existing_plan_and_in_source_output_are_rejected() {
    let f = Fixture::new();
    f.plan();
    fails(
        &f.call(&[
            "plan",
            "--manifest-path",
            "source/Cargo.toml",
            "--registry",
            "crates-io",
            "--workspace",
            "--out",
            "release.json",
        ]),
        "refusing to overwrite",
    );
    fails(
        &f.call(&[
            "plan",
            "--manifest-path",
            "source/Cargo.toml",
            "--registry",
            "crates-io",
            "--workspace",
            "--out",
            "source/new.json",
        ]),
        "outside the source",
    );
}

#[test]
fn ignored_credentials_are_not_read_or_copied() {
    let f = Fixture::new();
    let source = f.dir.join("source");
    fs::write(source.join(".gitignore"), ".env\n").unwrap();
    fs::write(source.join(".env"), "PRIVATE_SENTINEL").unwrap();
    for args in [
        vec!["init", "-q"],
        vec!["add", "."],
        vec![
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "commit",
            "-qm",
            "fixture",
        ],
    ] {
        assert!(
            Command::new("git")
                .current_dir(&source)
                .args(args)
                .status()
                .unwrap()
                .success()
        );
    }
    f.plan();
    assert!(!f.dir.join("release.release/source/.env").exists());
    let text = fs::read_to_string(f.plan_path()).unwrap();
    assert!(!text.contains("PRIVATE_SENTINEL"));
    assert!(!text.contains(".env\""));
}
#[test]
fn added_snapshot_ancestor_configuration_blocks_check() {
    let f = Fixture::new();
    f.plan();
    fs::create_dir(f.dir.join(".cargo")).unwrap();
    fs::write(
        f.dir.join(".cargo/config.toml"),
        "[registry]\ndefault = \"other\"\n",
    )
    .unwrap();
    fails(
        &f.call(&["check", "release.json"]),
        "ancestor Cargo configuration",
    );
    assert_eq!(f.uploads(), 0);
}
#[test]
fn oversized_metadata_is_refused_before_deserialization() {
    let f = Fixture::new();
    f.plan();
    fs::OpenOptions::new()
        .write(true)
        .open(f.plan_path())
        .unwrap()
        .set_len(17 * 1024 * 1024)
        .unwrap();
    fails(&f.call(&["check", "release.json"]), "exceeds 16 MiB");
}
#[test]
fn registry_names_containing_secret_still_bind_index_configuration() {
    let f = Fixture::new();
    let out = f.call_env(
        &[
            "plan",
            "--manifest-path",
            "source/Cargo.toml",
            "--registry",
            "secret",
            "--workspace",
            "--out",
            "release.json",
        ],
        &[(
            "CARGO_REGISTRIES_SECRET_INDEX",
            "https://registry.invalid/original",
        )],
    );
    success(&out);
    success(&f.call_env(
        &["check", "release.json"],
        &[(
            "CARGO_REGISTRIES_SECRET_INDEX",
            "https://registry.invalid/original",
        )],
    ));
    let hash = f.state()["plan_hash"].as_str().unwrap().to_owned();
    fails(
        &f.call_env(
            &["apply", "release.json", "--confirm", &hash],
            &[(
                "CARGO_REGISTRIES_SECRET_INDEX",
                "https://registry.invalid/changed",
            )],
        ),
        "configuration changed",
    );
    assert_eq!(f.uploads(), 0);
}
#[test]
fn relative_environment_locations_are_refused() {
    for (key, value) in [
        ("CARGO_HOME", "../cargo-home"),
        ("HOME", "."),
        ("RUSTC", "./rustc"),
    ] {
        let f = Fixture::new();
        let out = f.call_env(
            &[
                "plan",
                "--manifest-path",
                "source/Cargo.toml",
                "--registry",
                "crates-io",
                "--workspace",
                "--out",
                "release.json",
            ],
            &[(key, value)],
        );
        fails(&out, "absolute path");
        assert!(!f.plan_path().exists());
    }
}
#[test]
fn relative_plan_path_still_checks_snapshot_only_ancestor_config() {
    let f = Fixture::new();
    fs::create_dir_all(f.dir.join("plans/nested")).unwrap();
    success(&f.call(&[
        "plan",
        "--manifest-path",
        "source/Cargo.toml",
        "--registry",
        "crates-io",
        "--workspace",
        "--out",
        "plans/nested/release.json",
    ]));
    fs::create_dir(f.dir.join("plans/.cargo")).unwrap();
    fs::write(
        f.dir.join("plans/.cargo/config.toml"),
        "[registry]\ndefault = \"other\"\n",
    )
    .unwrap();
    fails(
        &f.call(&["check", "plans/nested/release.json"]),
        "ancestor Cargo configuration",
    );
    assert_eq!(f.uploads(), 0);
}
#[test]
fn repeated_check_does_not_reapprove_changed_archive() {
    let f = Fixture::new();
    f.plan();
    success(&f.call(&["check", "release.json"]));
    let before = fs::read(f.dir.join("release.release/state.json")).unwrap();
    f.touch("change-artifact");
    fails(&f.call(&["check", "release.json"]), "not overwritten");
    assert_eq!(
        fs::read(f.dir.join("release.release/state.json")).unwrap(),
        before
    );
}
#[test]
fn ignored_active_workspace_config_cannot_change_snapshot_registry() {
    let f = Fixture::new();
    let source = f.dir.join("source");
    fs::create_dir(source.join(".cargo")).unwrap();
    fs::write(source.join(".gitignore"), ".cargo/config.toml\n").unwrap();
    fs::write(
        source.join(".cargo/config.toml"),
        "[registries.demo]\nindex = \"https://registry.invalid/source\"\n",
    )
    .unwrap();
    for args in [
        vec!["init", "-q"],
        vec!["add", "."],
        vec![
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "commit",
            "-qm",
            "fixture",
        ],
    ] {
        assert!(
            Command::new("git")
                .current_dir(&source)
                .args(args)
                .status()
                .unwrap()
                .success()
        );
    }
    fails(
        &f.call(&[
            "plan",
            "--manifest-path",
            "source/Cargo.toml",
            "--registry",
            "demo",
            "--workspace",
            "--out",
            "release.json",
        ]),
        "not included in the snapshot",
    );
    assert!(!f.plan_path().exists());
}
#[test]
fn symlinked_target_directory_is_refused() {
    let f = Fixture::new();
    f.plan();
    std::os::unix::fs::symlink(
        f.dir.join("source"),
        f.dir.join("release.release/source/target"),
    )
    .unwrap();
    fails(&f.call(&["check", "release.json"]), "output directories");
}
#[test]
fn config_includes_and_escaped_keys_fail_closed() {
    for config in [
        "include = [\"/external/registry.toml\"]\n",
        "[[include]]\npath = \"/external/registry.toml\"\n",
        "\"include\" = [\"/external/registry.toml\"]\n",
        "\"\\u0069nclude\" = [\"/external/registry.toml\"]\n",
        "['include']\npath = \"/external/registry.toml\"\n",
    ] {
        let f = Fixture::new();
        fs::write(f.dir.join("cargo-home/config.toml"), config).unwrap();
        fails(
            &f.call(&[
                "plan",
                "--manifest-path",
                "source/Cargo.toml",
                "--registry",
                "secret",
                "--workspace",
                "--out",
                "release.json",
            ]),
            "includes and quoted/escaped keys",
        );
        assert!(!f.plan_path().exists());
        assert_eq!(f.uploads(), 0);
    }
}
#[test]
fn metadata_and_snapshots_have_private_permissions() {
    let f = Fixture::new();
    f.plan();
    assert_eq!(
        fs::metadata(f.plan_path()).unwrap().permissions().mode() & 0o077,
        0
    );
    assert_eq!(
        fs::metadata(f.dir.join("release.release"))
            .unwrap()
            .permissions()
            .mode()
            & 0o077,
        0
    );
    success(&f.call(&["check", "release.json"]));
    assert_eq!(
        fs::metadata(f.dir.join("release.release/state.json"))
            .unwrap()
            .permissions()
            .mode()
            & 0o077,
        0
    );
}

#[test]
fn real_offline_package_detects_missing_resources_and_verifies_included_assets() {
    let f = Fixture::new();
    let source = f.dir.join("source");
    fs::create_dir(source.join(".tauto-syntax")).unwrap();
    fs::write(
        source.join(".tauto-syntax/demo.tables"),
        "local table fixture\n",
    )
    .unwrap();
    fs::write(
        source.join("src/lib.rs"),
        "pub const TABLE: &str = include_str!(\"../.tauto-syntax/demo.tables\");\n",
    )
    .unwrap();
    let path = std::env::var("PATH").unwrap();
    let real_env = [("PATH", path.as_str())];
    let lock = Command::new("cargo")
        .args(["generate-lockfile", "--offline", "--manifest-path"])
        .arg(source.join("Cargo.toml"))
        .env("CARGO_HOME", f.dir.join("cargo-home"))
        .output()
        .unwrap();
    success(&lock);
    success(&f.call_env(
        &[
            "plan",
            "--manifest-path",
            "source/Cargo.toml",
            "--registry",
            "crates-io",
            "--workspace",
            "--out",
            "missing.json",
        ],
        &real_env,
    ));
    fails(
        &f.call_env(&["check", "missing.json"], &real_env),
        "Cargo package failed",
    );
    assert!(!f.dir.join("missing.release/state.json").exists());
    fs::write(source.join("Cargo.toml"), "[package]\nname = \"alpha\"\nversion = \"0.1.0\"\nedition = \"2024\"\ninclude = [\"src/**\", \".tauto-syntax/**\", \"Cargo.toml\", \"Cargo.lock\"]\n").unwrap();
    success(&f.call_env(
        &[
            "plan",
            "--manifest-path",
            "source/Cargo.toml",
            "--registry",
            "crates-io",
            "--workspace",
            "--out",
            "included.json",
        ],
        &real_env,
    ));
    success(&f.call_env(&["check", "included.json"], &real_env));
    success(&f.call_env(&["check", "included.json"], &real_env));
    let plan: serde_json::Value =
        serde_json::from_slice(&fs::read(f.dir.join("included.json")).unwrap()).unwrap();
    assert!(
        plan["packages"][0]["files"]
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v == ".tauto-syntax/demo.tables")
    );
    assert!(
        f.dir
            .join("included.release/source/target/package/alpha-0.1.0/.tauto-syntax/demo.tables")
            .is_file()
    );
    assert_eq!(f.uploads(), 0);
}
