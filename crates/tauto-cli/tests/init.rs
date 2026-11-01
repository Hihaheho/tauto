use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

struct Temp(PathBuf);
impl Temp {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "tauto-init-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn cli(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(dir)
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(args)
        .output()
        .unwrap()
}
fn success(output: Output) {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn current_directory_template_checks_and_runs() {
    let temp = Temp::new();
    success(cli(&temp.0, &["init"]));
    success(cli(&temp.0, &["check", "src/main.taut"]));
    let run = cli(&temp.0, &["run", "--tote", "."]);
    assert!(String::from_utf8_lossy(&run.stdout).contains("42"));
    success(run);
    assert!(!temp.0.join(".git").exists());
    assert!(!temp.0.join("Cargo.toml").exists());
}

#[test]
fn new_directory_under_unicode_parent_and_no_external_tools() {
    let temp = Temp::new();
    fs::create_dir(temp.0.join("日本語")).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(&temp.0)
        .env("PATH", "")
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(["init", "日本語/hello-world"])
        .output()
        .unwrap();
    success(result);
    let manifest = fs::read_to_string(temp.0.join("日本語/hello-world/Tauto.eure")).unwrap();
    assert!(manifest.contains("name = \"hello-world\""));
    success(cli(
        &temp.0.join("日本語/hello-world"),
        &["run", "--tote", "."],
    ));
}

#[test]
fn existing_files_and_repeated_init_are_unchanged() {
    let temp = Temp::new();
    fs::write(temp.0.join("keep.txt"), "keep").unwrap();
    success(cli(&temp.0, &["init"]));
    let manifest = fs::read(temp.0.join("Tauto.eure")).unwrap();
    let source = fs::read(temp.0.join("src/main.taut")).unwrap();
    assert!(!cli(&temp.0, &["init"]).status.success());
    assert_eq!(fs::read(temp.0.join("Tauto.eure")).unwrap(), manifest);
    assert_eq!(fs::read(temp.0.join("src/main.taut")).unwrap(), source);
    assert_eq!(fs::read_to_string(temp.0.join("keep.txt")).unwrap(), "keep");
}

#[test]
fn source_collision_does_not_create_manifest() {
    let temp = Temp::new();
    fs::create_dir(temp.0.join("src")).unwrap();
    fs::write(temp.0.join("src/main.taut"), "keep").unwrap();
    assert!(!cli(&temp.0, &["init"]).status.success());
    assert!(!temp.0.join("Tauto.eure").exists());
    assert_eq!(
        fs::read_to_string(temp.0.join("src/main.taut")).unwrap(),
        "keep"
    );
}

#[test]
fn manifest_collision_does_not_create_source_directory() {
    let temp = Temp::new();
    fs::write(temp.0.join("Tauto.eure"), "keep").unwrap();
    assert!(!cli(&temp.0, &["init"]).status.success());
    assert!(!temp.0.join("src").exists());
    assert_eq!(
        fs::read_to_string(temp.0.join("Tauto.eure")).unwrap(),
        "keep"
    );
}

#[test]
fn invalid_names_and_missing_parents_do_not_write() {
    let temp = Temp::new();
    for name in [
        "日本語",
        "0start",
        "bad name",
        "bad\"name",
        "",
        "Upper",
        "under_score",
    ] {
        assert!(!cli(&temp.0, &["init", name]).status.success());
        assert!(!temp.0.join("sample").exists());
    }
    assert!(!cli(&temp.0, &["init", "日本語"]).status.success());
    assert!(!cli(&temp.0, &["init", "missing/sample"]).status.success());
    assert!(!temp.0.join("missing").exists());
    assert!(!cli(&temp.0, &["init", "sample/../other"]).status.success());
    assert_eq!(fs::read_dir(&temp.0).unwrap().count(), 0);
}

#[test]
fn arguments_and_help() {
    let temp = Temp::new();
    success(cli(&temp.0, &["init", "--help"]));
    assert!(
        String::from_utf8_lossy(&cli(&temp.0, &["--help"]).stdout).contains("tauto init [DIR]")
    );
    for args in [
        vec!["init", "--name"],
        vec!["init", "one", "two"],
        vec!["init", "--force"],
    ] {
        assert_eq!(cli(&temp.0, &args).status.code(), Some(2));
    }
    assert_eq!(fs::read_dir(&temp.0).unwrap().count(), 0);
}

#[cfg(unix)]
#[test]
fn refuses_symlink_root_source_ancestor_and_destination() {
    use std::os::unix::fs::symlink;
    let temp = Temp::new();
    fs::create_dir(temp.0.join("target")).unwrap();
    symlink(temp.0.join("target"), temp.0.join("alias")).unwrap();
    assert!(!cli(&temp.0, &["init", "alias"]).status.success());
    assert!(!cli(&temp.0, &["init", "alias/child"]).status.success());
    symlink(temp.0.join("target"), temp.0.join("src")).unwrap();
    assert!(!cli(&temp.0, &["init"]).status.success());
    fs::remove_file(temp.0.join("src")).unwrap();
    symlink(temp.0.join("absent"), temp.0.join("Tauto.eure")).unwrap();
    assert!(!cli(&temp.0, &["init"]).status.success());
    assert_eq!(fs::read_dir(temp.0.join("target")).unwrap().count(), 0);
    assert!(!temp.0.join("absent").exists());
}

#[cfg(unix)]
#[test]
fn write_failure_rolls_back_only_created_manifest() {
    use std::os::unix::fs::PermissionsExt;
    let temp = Temp::new();
    let src = temp.0.join("src");
    fs::create_dir(&src).unwrap();
    fs::write(src.join("keep.txt"), "keep").unwrap();
    fs::set_permissions(&src, fs::Permissions::from_mode(0o555)).unwrap();
    // Privileged test runners can write despite the mode; the failure cannot be induced there.
    let probe = src.join("probe");
    if fs::write(&probe, "").is_ok() {
        fs::remove_file(probe).unwrap();
        fs::set_permissions(&src, fs::Permissions::from_mode(0o755)).unwrap();
        return;
    }
    let result = cli(&temp.0, &["init"]);
    fs::set_permissions(&src, fs::Permissions::from_mode(0o755)).unwrap();
    assert!(!result.status.success());
    assert!(!temp.0.join("Tauto.eure").exists());
    assert!(!src.join("main.taut").exists());
    assert_eq!(fs::read_to_string(src.join("keep.txt")).unwrap(), "keep");
}
