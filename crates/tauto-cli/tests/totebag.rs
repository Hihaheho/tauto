//! `tauto add / remove / update / lock / fetch / deps` against repositories on
//! disk (`file:///`), and the loaders reading what they lock.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

struct Temp(PathBuf);
impl Temp {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "tauto-totebag-{}-{}",
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

/// A project `app` and a repository `libs` holding the totes `greet` and
/// `word`, `greet` depending on `word` by path.
struct World {
    temp: Temp,
}

impl World {
    fn new() -> World {
        let w = World { temp: Temp::new() };
        let libs = w.libs();
        fs::create_dir_all(&libs).unwrap();
        w.git(&["init", "--quiet"]);
        write(
            &libs.join("word/Tauto.eure"),
            "package {\n  name = \"word\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}\n",
        );
        write(
            &libs.join("word/src/word.taut"),
            "pub fn word(): i64 { 41 }\n",
        );
        write(
            &libs.join("greet/Tauto.eure"),
            "package {\n  name = \"greet\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}\ndependencies {\n  word { path = \"../word\" }\n}\n",
        );
        write(
            &libs.join("greet/src/greet.taut"),
            "pub fn greet(): i64 { word() + 1 }\n",
        );
        w.commit("first");
        let app = w.app();
        write(
            &app.join("Tauto.eure"),
            "// The app.\npackage {\n  name = \"app\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}\n",
        );
        write(
            &app.join("src/main.taut"),
            "perform show(\"answer\", greet())\n",
        );
        w
    }

    fn libs(&self) -> PathBuf {
        self.temp.0.join("libs")
    }

    fn app(&self) -> PathBuf {
        self.temp.0.join("app")
    }

    fn url(&self) -> String {
        format!("file://{}", self.libs().display())
    }

    fn git(&self, args: &[&str]) {
        let out = Command::new("git")
            .arg("-C")
            .arg(self.libs())
            .args([
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@example.org",
                "-c",
                "commit.gpgsign=false",
                "-c",
                "init.defaultBranch=main",
            ])
            .args(args)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    fn commit(&self, message: &str) {
        self.git(&["add", "."]);
        self.git(&["commit", "--quiet", "-m", message]);
    }

    fn tauto(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .current_dir(self.app())
            .env("TAUTO_TOTES", self.temp.0.join("cache"))
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .env_remove("TAUTO_OFFLINE")
            .args(args)
            .output()
            .unwrap()
    }

    fn ok(&self, args: &[&str]) -> String {
        let out = self.tauto(args);
        assert!(
            out.status.success(),
            "tauto {args:?}: {}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8(out.stdout).unwrap()
    }

    fn fails(&self, args: &[&str]) -> String {
        let out = self.tauto(args);
        assert!(!out.status.success(), "tauto {args:?} succeeded");
        format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        )
    }

    fn read(&self, name: &str) -> String {
        fs::read_to_string(self.app().join(name)).unwrap()
    }
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

#[test]
fn add_locks_fetches_and_run_reads_the_lock() {
    let w = World::new();
    let url = w.url();
    // Two totes and no hint: the user is asked to choose.
    let err = w.fails(&["add", "--git", &url]);
    assert!(
        err.contains("has 2 totes; choose one with --dir: greet, word"),
        "{err}"
    );
    assert!(!w.app().join("Tauto.lock").exists());

    // The tote named greet is in the directory greet.
    let out = w.ok(&["add", "--git", &url, "greet"]);
    assert!(out.contains("Added greet"), "{out}");
    assert!(out.contains("Locked    greet"), "{out}");
    let manifest = w.read("Tauto.eure");
    assert!(manifest.starts_with("// The app.\n"), "{manifest}");
    assert!(
        manifest.ends_with(&format!(
            "dependencies {{\n  greet {{\n    git = \"{url}\"\n    ref = \"refs/heads/main\"\n    dir = \"greet\"\n  }}\n}}\n"
        )),
        "{manifest}"
    );
    let lock = w.read("Tauto.lock");
    assert!(
        lock.contains("name = \"greet\"") && lock.contains("rev = \"sha1:"),
        "{lock}"
    );

    assert_eq!(w.ok(&["run", "--tote", "."]), "answer = 42\n");
    assert!(w.ok(&["check", "--tote", "."]).contains("0 failed"));
    let deps = w.ok(&["deps"]);
    assert!(deps.contains("app 0.1.0\n└── greet ("), "{deps}");
    assert!(deps.contains("    └── word (path ../word)"), "{deps}");
    assert!(w.ok(&["lock", "--check"]).contains("up to date"));

    let err = w.fails(&["add", "--git", &url, "greet"]);
    assert!(err.contains("greet is already a dependency"), "{err}");
}

#[test]
fn update_takes_a_new_commit_only_when_asked() {
    let w = World::new();
    w.ok(&["add", "--git", &w.url(), "--dir", "greet"]);
    let lock = w.read("Tauto.lock");
    write(
        &w.libs().join("word/src/word.taut"),
        "pub fn word(): i64 { 99 }\n",
    );
    w.commit("second");

    // A new commit upstream changes nothing until `update`.
    assert_eq!(w.ok(&["run", "--tote", "."]), "answer = 42\n");
    assert_eq!(
        w.ok(&["lock"]),
        "Tauto.lock is up to date (1 Git dependency)\n"
    );
    let dry = w.ok(&["update", "--dry-run"]);
    assert!(dry.starts_with("update    greet "), "{dry}");
    assert!(dry.contains("nothing was written"), "{dry}");
    assert_eq!(w.read("Tauto.lock"), lock);

    let out = w.ok(&["update", "greet"]);
    assert!(out.starts_with("Updated   greet "), "{out}");
    assert_ne!(w.read("Tauto.lock"), lock);
    assert_eq!(w.ok(&["run", "--tote", "."]), "answer = 100\n");
    let err = w.fails(&["update", "nothing"]);
    assert!(err.contains("nothing is not a Git dependency"), "{err}");
}

#[test]
fn the_cache_is_filled_from_the_lock_unless_offline() {
    let w = World::new();
    w.ok(&["add", "--git", &w.url(), "greet"]);
    fs::remove_dir_all(w.temp.0.join("cache")).unwrap();

    let err = w.fails(&["run", "--offline", "--tote", "."]);
    assert!(
        err.contains("has not been fetched, and the network is off; run `tauto fetch`"),
        "{err}"
    );
    assert_eq!(w.ok(&["fetch"]), "1 tote fetched\n");
    assert_eq!(w.ok(&["run", "--offline", "--tote", "."]), "answer = 42\n");
    assert!(w.ok(&["fetch", "--verify"]).contains(": ok"));

    // Gone again: `run` fetches what the lock fixes by itself.
    fs::remove_dir_all(w.temp.0.join("cache")).unwrap();
    let out = w.tauto(&["run", "--tote", "."]);
    assert!(out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("Fetching greet "));
}

#[test]
fn a_stale_lock_is_reported_not_resolved() {
    let w = World::new();
    w.ok(&["add", "--git", &w.url(), "greet"]);
    let manifest = w.read("Tauto.eure");
    fs::write(
        w.app().join("Tauto.eure"),
        manifest.replace("refs/heads/main", "refs/heads/other"),
    )
    .unwrap();
    let err = w.fails(&["lock", "--check"]);
    assert!(
        err.contains("Tauto.lock is not up to date; run `tauto lock`"),
        "{err}"
    );
    let err = w.fails(&["run", "--tote", "."]);
    assert!(err.contains("run `tauto lock`"), "{err}");
}

#[test]
fn remove_takes_out_the_entry_and_the_lock() {
    let w = World::new();
    w.ok(&["add", "--git", &w.url(), "greet"]);
    let out = w.ok(&["remove", "greet"]);
    assert!(
        out.contains("Removed greet") && out.contains("Unlocked  greet"),
        "{out}"
    );
    assert_eq!(
        w.read("Tauto.eure"),
        "// The app.\npackage {\n  name = \"app\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}\n"
    );
    assert!(!w.app().join("Tauto.lock").exists());
    let err = w.fails(&["remove", "greet"]);
    assert!(err.contains("greet is not a dependency"), "{err}");
}

#[test]
fn a_project_has_one_tote_of_each_name() {
    let w = World::new();
    w.ok(&["add", "--git", &w.url(), "greet"]);
    // A local word besides the one greet brings.
    write(
        &w.temp.0.join("word/Tauto.eure"),
        "package {\n  name = \"word\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}\n",
    );
    write(
        &w.temp.0.join("word/src/word.taut"),
        "pub fn word(): i64 { 1 }\n",
    );
    let err = w.fails(&["add", "--path", "../word"]);
    assert!(
        err.contains("word is asked for twice, differently"),
        "{err}"
    );
    // The manifest is as it was when the dependency cannot be locked.
    assert!(!w.read("Tauto.eure").contains("../word"));
}

#[test]
fn a_fetched_tote_may_not_name_a_local_repository() {
    let w = World::new();
    write(
        &w.libs().join("greet/Tauto.eure"),
        &format!(
            "package {{\n  name = \"greet\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}}\ndependencies {{\n  word {{\n    git = \"{}\"\n    ref = \"refs/heads/main\"\n    dir = \"word\"\n  }}\n}}\n",
            w.url()
        ),
    );
    w.commit("word from git");
    let err = w.fails(&["add", "--git", &w.url(), "greet"]);
    assert!(
        err.contains("a fetched tote may not name a file:// repository"),
        "{err}"
    );
}
