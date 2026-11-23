//! The crate a tote's Rust build generates is read back while nothing it was
//! made from has changed, and made again when anything has: a file of a
//! dependency tote, a `Tauto.eure`, a file added to a tote's sources, or a
//! file imported by path from outside the totes.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn write(root: &Path, path: &str, text: &str) {
    let file = root.join(path);
    fs::create_dir_all(file.parent().unwrap()).unwrap();
    fs::write(file, text).unwrap();
}

struct Project(PathBuf);

impl Drop for Project {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

impl Project {
    fn new(name: &str) -> Project {
        let root = std::env::temp_dir().join(format!("tauto-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        write(
            &root,
            "lib/Tauto.eure",
            "package {\n  name = \"lib\"\n  version = \"0.1.0\"\n}\n",
        );
        write(&root, "lib/src/lib.taut", "pub fn base(): i64 {\n  1\n}\n");
        write(&root, "shared/more.taut", "pub fn more(): i64 {\n  10\n}\n");
        write(
            &root,
            "app/Tauto.eure",
            "package {\n  name = \"app\"\n  version = \"0.1.0\"\n}\n\ndependencies {\n  lib {\n    path = \"../lib\"\n  }\n}\n",
        );
        write(
            &root,
            "app/src/main.taut",
            "import lib::lib\nimport \"../../shared/more.taut\"\n\nshow(&(base() + more()))\n",
        );
        Project(root)
    }

    /// The program's output and whether the front end ran.
    fn run(&self) -> (String, bool) {
        let build = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(["build", "--timings"])
            .arg(self.0.join("app"))
            .env("TAUTO_LANG", "en")
            .env("TAUTO_HOME", self.0.join("home"))
            .env("TAUTO_BUILD", self.0.join("cache"))
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&build.stderr);
        assert!(build.status.success(), "{stderr}");
        let bin = String::from_utf8_lossy(&build.stdout).trim().to_string();
        let out = Command::new(bin).output().unwrap();
        assert!(out.status.success());
        (
            String::from_utf8_lossy(&out.stdout).trim().to_string(),
            stderr.contains("tote_load_check_extract"),
        )
    }
}

#[test]
fn a_tote_crate_is_made_again_only_when_what_it_was_made_from_changes() {
    let p = Project::new("rust-crate-cache");
    assert_eq!(p.run(), ("11".to_string(), true));
    // Nothing changed: the crate is read back.
    assert_eq!(p.run(), ("11".to_string(), false));
    // A dependency's source.
    write(&p.0, "lib/src/lib.taut", "pub fn base(): i64 {\n  2\n}\n");
    assert_eq!(p.run(), ("12".to_string(), true));
    assert_eq!(p.run(), ("12".to_string(), false));
    // A file imported by its path.
    write(&p.0, "shared/more.taut", "pub fn more(): i64 {\n  20\n}\n");
    assert_eq!(p.run(), ("22".to_string(), true));
    // A file added to a tote's sources.
    write(
        &p.0,
        "lib/src/extra.taut",
        "pub fn extra(): i64 {\n  0\n}\n",
    );
    assert_eq!(p.run(), ("22".to_string(), true));
    assert_eq!(p.run(), ("22".to_string(), false));
    // A manifest.
    let manifest = fs::read_to_string(p.0.join("lib/Tauto.eure")).unwrap();
    write(&p.0, "lib/Tauto.eure", &format!("{manifest}\n"));
    assert_eq!(p.run(), ("22".to_string(), true));
}

#[test]
fn a_tote_that_fails_to_check_is_not_kept() {
    let p = Project::new("rust-crate-cache-fails");
    assert_eq!(p.run().0, "11");
    write(
        &p.0,
        "lib/src/lib.taut",
        "pub fn base(): i64 {\n  true\n}\n",
    );
    for _ in 0..2 {
        let build = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("build")
            .arg(p.0.join("app"))
            .env("TAUTO_HOME", p.0.join("home"))
            .env("TAUTO_BUILD", p.0.join("cache"))
            .output()
            .unwrap();
        assert!(!build.status.success());
    }
}
