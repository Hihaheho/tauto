//! The bytecode `tauto run` compiles a tote to is read back while nothing it
//! was made from has changed, and made again when anything has: a file of a
//! dependency tote, a file imported by path from outside the totes, a file
//! added to a tote's sources, or a `Tauto.eure`.

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
            "import lib::lib\nimport \"../../shared/more.taut\"\n\nperform main(() => {\n  show(&(base() + more()))\n})\n",
        );
        Project(root)
    }

    fn command(&self) -> Command {
        let mut c = Command::new(env!("CARGO_BIN_EXE_tauto"));
        c.current_dir(self.0.join("app"))
            .args(["run", "."])
            .env("TAUTO_LANG", "en")
            .env("TAUTO_HOME", self.0.join("home"))
            .env("TAUTO_BUILD", self.0.join("cache"))
            .env_remove("TAUTO_VM");
        // A session of its own: no terminal to ask a permission at.
        #[cfg(unix)]
        unsafe {
            use std::os::unix::process::CommandExt;
            c.pre_exec(|| {
                libc::setsid();
                Ok(())
            });
        }
        c
    }

    /// The program's output, and whether the run kept a new result (the
    /// tote was read, checked and compiled) rather than reading one back.
    fn run(&self) -> (String, bool) {
        let before = self.records();
        let out = self.command().output().unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        (
            String::from_utf8_lossy(&out.stdout).trim().to_string(),
            self.records() != before,
        )
    }

    fn records(&self) -> usize {
        fs::read_dir(self.0.join("cache/actions-v2"))
            .map(|d| d.count())
            .unwrap_or(0)
    }
}

#[test]
fn a_tote_program_is_compiled_again_only_when_what_it_was_made_from_changes() {
    let p = Project::new("vm-program-cache");
    assert_eq!(p.run(), ("11".to_string(), true));
    // Nothing changed: the bytecode is read back.
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
fn a_kept_program_still_needs_its_permissions() {
    let p = Project::new("vm-program-cache-permissions");
    write(
        &p.0,
        "app/src/main.taut",
        "import std::builtin::os\n\nperform main(() => {\n  show(&(perform env(\"PATH\")))\n})\n",
    );
    let first = p.command().arg("--yes").output().unwrap();
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    for _ in 0..2 {
        let denied = p.command().output().unwrap();
        assert_eq!(denied.status.code(), Some(2));
        assert!(String::from_utf8_lossy(&denied.stderr).contains("+ env:"));
    }
}

#[test]
fn a_tote_that_fails_to_check_is_not_kept() {
    let p = Project::new("vm-program-cache-fails");
    assert_eq!(p.run().0, "11");
    write(
        &p.0,
        "lib/src/lib.taut",
        "pub fn base(): i64 {\n  true\n}\n",
    );
    for _ in 0..2 {
        assert!(!p.command().output().unwrap().status.success());
    }
}
