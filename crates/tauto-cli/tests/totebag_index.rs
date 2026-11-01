//! A project with `Trust.eure`: `tauto index sync / status / check`, and
//! `add` and `update` taking a commit only when the trusted index allows it.
//! The index is the user's own, in a repository on disk.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use totebag::cache::Cache;
use totebag::git::Mirror;
use totebag::index::checkpoint;
use totebag::index::strict::{hex_of, time_text};
use totebag::spec::GitSource;

const PROJECT: &str = "sha256:5555555555555555555555555555555555555555555555555555555555555555";
const INDEX: &str = "format = 1\nkind = \"index\"\nname = \"me\"\nhistory = \"commit-batches\"\ngit_object_format = \"sha1\"\n";

struct Temp(PathBuf);
impl Temp {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "tauto-totebag-index-{}-{}",
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

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
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
        "git {args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

fn now() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs() as i64
}

/// The time `offset` seconds from now.
fn at(offset: i64) -> String {
    time_text((now() + offset) as u64)
}

/// A repository `lib` with the tote `word` at its root, an index `me`, and a
/// project `app`.
struct World {
    temp: Temp,
    batches: u64,
}

impl World {
    fn new() -> World {
        let w = World {
            temp: Temp::new(),
            batches: 0,
        };
        fs::create_dir_all(w.lib()).unwrap();
        git(&w.lib(), &["init", "--quiet"]);
        write(
            &w.lib().join("Tauto.eure"),
            "package {\n  name = \"word\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}\n",
        );
        w.word(41);
        fs::create_dir_all(w.index()).unwrap();
        git(&w.index(), &["init", "--quiet"]);
        write(&w.index().join("Index.eure"), INDEX);
        w.publish(0, "events = []\n");
        write(
            &w.app().join("Tauto.eure"),
            "package {\n  name = \"app\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}\n",
        );
        write(
            &w.app().join("src/main.taut"),
            "perform show(\"answer\", word())\n",
        );
        w.user_trust("@ require {\n  min_age_seconds = 0\n}\n");
        w
    }

    /// The user policy, in the file `TAUTO_USER_TRUST` names.
    fn user_trust(&self, rest: &str) {
        write(
            &self.user_trust_file(),
            &format!(
                "format = 1\nkind = \"user-policy\"\ntrack = \"dependency-closure\"\n\n{rest}"
            ),
        );
    }

    fn user_trust_file(&self) -> PathBuf {
        self.temp.0.join("user-trust.eure")
    }

    /// Where the user policy is looked for when `TAUTO_USER_TRUST` is not set.
    fn config(&self) -> PathBuf {
        self.temp.0.join("config")
    }

    fn lib(&self) -> PathBuf {
        self.temp.0.join("lib")
    }
    fn index(&self) -> PathBuf {
        self.temp.0.join("index")
    }
    fn app(&self) -> PathBuf {
        self.temp.0.join("app")
    }
    fn url(&self, dir: &Path) -> String {
        format!("file://{}", dir.display())
    }

    /// A new commit of `word` answering `n`.
    fn word(&self, n: i64) {
        write(
            &self.lib().join("src/word.taut"),
            &format!("pub fn word(): i64 {{ {n} }}\n"),
        );
        git(&self.lib(), &["add", "."]);
        git(&self.lib(), &["commit", "--quiet", "-m", "word"]);
    }

    /// The head of `lib` and the ID of its tree.
    fn head(&self) -> (String, String) {
        let fetched = totebag::fetch_head(
            &Cache::at(self.temp.0.join("probe-cache")),
            &GitSource {
                url: self.url(&self.lib()),
                reference: "refs/heads/main".into(),
                dir: String::new(),
                project: None,
            },
        )
        .unwrap();
        (fetched.rev.hex().to_string(), fetched.id.to_string())
    }

    fn publish(&self, sequence: u64, events: &str) {
        write(
            &self.index().join("observations.eure"),
            &format!(
                "format = 1\nkind = \"batch\"\nsequence = {sequence}\nissued_at = \"{}\"\nvalid_until = \"{}\"\n{events}",
                at(-3600 + sequence as i64),
                at(86_400)
            ),
        );
        git(&self.index(), &["add", "."]);
        git(&self.index(), &["commit", "--quiet", "-m", "batch"]);
    }

    /// The index observes the head of `lib` and accepts it.
    fn vouch(&mut self) {
        let (rev, source) = self.head();
        self.batches += 1;
        self.publish(
            self.batches,
            &format!(
                "@ events[] {{\n  kind = \"observation\"\n  project = \"{PROJECT}\"\n  rev = \"{rev}\"\n  source_sha256 = \"{source}\"\n  first_seen_at = \"{}\"\n}}\n\
                 @ events[] {{\n  kind = \"decision\"\n  project = \"{PROJECT}\"\n  rev = \"{rev}\"\n  verdict = \"accept\"\n  reason = \"read it\"\n}}\n",
                at(-3600)
            ),
        );
    }

    /// `Trust.eure` trusting the index `me`, read from its repository.
    fn trust(&self) {
        let mirror = Mirror::open(self.temp.0.join("probe-index"), "sha1").unwrap();
        let head = mirror
            .fetch_history(&self.url(&self.index()), "refs/heads/main")
            .unwrap();
        let history = checkpoint::history(&mirror, &head).unwrap();
        let root = &history.checkpoints[0];
        write(
            &self.app().join("Trust.eure"),
            &format!(
                "format = 1\nkind = \"policy\"\ntrack = \"dependency-closure\"\n\n\
                 @ indexes[] {{\n  alias = \"me\"\n  id = \"sha256:{}\"\n  transport = \"local-owned\"\n  repository = \"{}\"\n  ref = \"refs/heads/main\"\n  pin_rev = \"{}\"\n  pin_sha256 = \"sha256:{}\"\n}}\n\n\
                 @ defaults {{\n  require = \"all\"\n  observers = [\"me\"]\n  age_witnesses = [\"local\"]\n  min_age_seconds = 0\n  max_checkpoint_lifetime_seconds = 172800\n  max_source_check_age_seconds = 600\n}}\n",
                hex_of(&history.id()),
                self.url(&self.index()),
                root.rev,
                hex_of(&root.digest)
            ),
        );
    }

    fn tauto(&self, args: &[&str]) -> Output {
        let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
        if self.user_trust_file().exists() {
            command.env("TAUTO_USER_TRUST", self.user_trust_file());
        } else {
            command.env_remove("TAUTO_USER_TRUST");
        }
        command
            .env("XDG_CONFIG_HOME", self.config())
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .current_dir(self.app())
            .env("TAUTO_TOTES", self.temp.0.join("cache"))
            .env("TAUTO_INDEX_STATE", self.temp.0.join("state"))
            .env("GIT_AUTHOR_NAME", "t")
            .env("GIT_AUTHOR_EMAIL", "t@example.org")
            .env("GIT_COMMITTER_NAME", "t")
            .env("GIT_COMMITTER_EMAIL", "t@example.org")
            .env_remove("TAUTO_OFFLINE")
            .args(args)
            .output()
            .unwrap()
    }

    fn ok(&self, args: &[&str]) -> String {
        let out = self.tauto(args);
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(out.status.success(), "tauto {args:?}: {text}");
        text
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

#[test]
fn a_commit_is_adopted_only_once_the_index_allows_it() {
    let mut w = World::new();
    w.trust();
    let lib = w.url(&w.lib());

    // Not observed yet: add refuses, and leaves the manifest as it was.
    let manifest = w.read("Tauto.eure");
    let err = w.fails(&["add", "--git", &lib, "--project", PROJECT]);
    assert!(err.contains("may not be adopted under Trust.eure"), "{err}");
    assert!(err.contains("me: has not observed it"), "{err}");
    assert_eq!(w.read("Tauto.eure"), manifest);

    // Observed and accepted: add syncs the index and takes it.
    w.vouch();
    let out = w.ok(&["add", "--git", &lib, "--project", PROJECT]);
    assert!(out.contains("Syncing index me"), "{out}");
    assert!(out.contains("Locked    word"), "{out}");
    assert!(
        w.read("Tauto.eure")
            .contains(&format!("project = \"{PROJECT}\""))
    );
    assert!(
        w.read("Tauto.lock")
            .contains(&format!("project = \"{PROJECT}\""))
    );
    assert_eq!(w.ok(&["run", "--tote", "."]), "answer = 41\n");
    assert!(w.ok(&["index", "check"]).contains("may be adopted"));

    // A new commit the index has not seen: update holds the locked one.
    let lock = w.read("Tauto.lock");
    w.word(42);
    let out = w.ok(&["update"]);
    assert!(out.contains("Held      word"), "{out}");
    assert!(out.contains("me: has not observed it"), "{out}");
    assert_eq!(w.read("Tauto.lock"), lock);

    // Once it is vouched for, update takes it.
    w.vouch();
    let out = w.ok(&["update"]);
    assert!(out.contains("Updated   word"), "{out}");
    assert_eq!(w.ok(&["run", "--tote", "."]), "answer = 42\n");

    let status = w.ok(&["index", "status"]);
    assert!(status.contains("me (file://"), "{status}");
    assert!(status.contains("taken in through"), "{status}");
    assert!(!status.contains("STOPPED"), "{status}");
}

#[test]
fn under_a_policy_every_git_dependency_names_its_project() {
    let mut w = World::new();
    w.vouch();
    let lib = w.url(&w.lib());
    w.ok(&["add", "--git", &lib]);
    w.trust();
    w.word(42);
    let err = w.fails(&["update"]);
    assert!(
        err.contains("every Git dependency names its project"),
        "{err}"
    );
}

#[test]
fn a_rewritten_index_stops_and_adopts_nothing() {
    let mut w = World::new();
    w.trust();
    w.vouch();
    let lib = w.url(&w.lib());
    w.ok(&["add", "--git", &lib, "--project", PROJECT]);
    // The index's history is rewritten under what was taken in.
    git(&w.index(), &["reset", "--quiet", "--hard", "HEAD~1"]);
    w.batches -= 1;
    w.word(42);
    w.vouch();
    let out = w.fails(&["index", "sync"]);
    assert!(out.contains("STOPPED"), "{out}");
    assert!(out.contains("no longer holds"), "{out}");
    let out = w.ok(&["update"]);
    assert!(out.contains("Held      word"), "{out}");
    assert!(out.contains("me: stopped at"), "{out}");
    let out = w.fails(&["index", "check"]);
    assert!(out.contains("may not be adopted"), "{out}");
}

#[test]
fn ones_own_index_vouches_for_a_commit() {
    let w = World::new();
    let mine = w.temp.0.join("mine");
    let out = w.ok(&["index", "new", mine.to_str().unwrap(), "--name", "mine"]);
    let start = out.find("@ indexes[] {").expect(&out);
    let block = &out[start..out[start..].find("\n}").unwrap() + start + 2];
    assert!(block.contains("alias = \"mine\""), "{block}");
    write(
        &w.app().join("Trust.eure"),
        &format!(
            "format = 1\nkind = \"policy\"\ntrack = \"dependency-closure\"\n\n{block}\n\n\
             @ defaults {{\n  require = \"all\"\n  observers = [\"mine\"]\n  age_witnesses = [\"local\"]\n  min_age_seconds = 0\n  max_checkpoint_lifetime_seconds = 172800\n  max_source_check_age_seconds = 600\n}}\n"
        ),
    );
    let lib = w.url(&w.lib());

    let err = w.fails(&["add", "--git", &lib, "--project", PROJECT]);
    assert!(err.contains("mine: has not observed it"), "{err}");
    assert!(err.contains("`tauto index --help`"), "{err}");

    // Vouched for in one's own index: observe, accept, publish.
    let out = w.ok(&["index", "observe", "--project", PROJECT, "--git", &lib]);
    assert!(out.contains("Observed project sha256:555555555"), "{out}");
    assert_eq!(
        git(&mine, &["status", "--porcelain"]),
        "M observations.eure"
    );
    w.ok(&[
        "index",
        "decide",
        "--project",
        PROJECT,
        "accept",
        "--reason",
        "read it",
    ]);
    // The same revision cannot be observed twice.
    let err = w.fails(&["index", "observe", "--project", PROJECT, "--git", &lib]);
    assert!(err.contains("not allowed"), "{err}");
    // A later observation goes into the batch being written, which was
    // started a while before it.
    std::thread::sleep(std::time::Duration::from_millis(1100));
    let other = format!("sha256:{}", "6".repeat(64));
    w.ok(&["index", "observe", "--project", &other, "--git", &lib]);
    let out = w.ok(&["index", "publish"]);
    assert!(out.contains("Published batch 1 of mine"), "{out}");
    assert!(out.contains("(3 events)"), "{out}");
    assert_eq!(git(&mine, &["status", "--porcelain"]), "");
    let out = w.ok(&["add", "--git", &lib, "--project", PROJECT]);
    assert!(out.contains("Locked    word"), "{out}");

    // A new commit, observed and rejected: update holds the locked one.
    w.word(42);
    w.ok(&["index", "observe", "word"]);
    w.ok(&[
        "index",
        "decide",
        "word",
        "reject",
        "--reason",
        "it says 42",
    ]);
    w.ok(&["index", "publish"]);
    let out = w.ok(&["update"]);
    assert!(out.contains("Held      word"), "{out}");
    assert!(out.contains("mine: rejected it"), "{out}");

    // An empty batch keeps the index valid.
    let out = w.ok(&["index", "publish", "--valid-for", "3600"]);
    assert!(out.contains("Published batch 3 of mine"), "{out}");
    assert!(out.contains("(0 events)"), "{out}");
    let err = w.fails(&["index", "decide", "word", "maybe", "--reason", "x"]);
    assert!(err.contains("accept or reject"), "{err}");
}

#[test]
fn without_a_user_policy_a_commit_waits_14_days() {
    let mut w = World::new();
    fs::remove_file(w.user_trust_file()).unwrap();
    w.trust();
    w.vouch();
    let lib = w.url(&w.lib());
    let err = w.fails(&["add", "--git", &lib, "--project", PROJECT]);
    assert!(err.contains("may not be adopted under Trust.eure"), "{err}");
    assert!(err.contains("it waits until"), "{err}");
    assert!(
        err.contains("the wait of 14d 0h is from the safe default, as there is no"),
        "{err}"
    );
    assert!(err.contains("Trust.eure waits 0s"), "{err}");
    let status = w.ok(&["index", "status"]);
    assert!(
        status.contains("user policy: the safe default, as there is no"),
        "{status}"
    );
    assert!(status.contains("waits 14d 0h"), "{status}");

    // The same user policy in the place it is looked for.
    fs::create_dir_all(w.config().join("tauto")).unwrap();
    fs::write(
        w.config().join("tauto/trust.eure"),
        "format = 1\nkind = \"user-policy\"\ntrack = \"dependency-closure\"\n\n@ require {\n  min_age_seconds = 0\n}\n",
    )
    .unwrap();
    let out = w.ok(&["add", "--git", &lib, "--project", PROJECT]);
    assert!(out.contains("Locked    word"), "{out}");
}

#[test]
fn a_user_policy_adds_to_trust_eure() {
    let mut w = World::new();
    w.trust();
    w.vouch();
    w.user_trust("@ require {\n  min_age_seconds = 7200\n  max_source_check_age_seconds = 60\n}\n");
    let lib = w.url(&w.lib());
    let err = w.fails(&["add", "--git", &lib, "--project", PROJECT]);
    assert!(err.contains("it waits until"), "{err}");
    assert!(err.contains("the wait of 2h 0m is from"), "{err}");
    let status = w.ok(&["index", "status"]);
    assert!(status.contains("user-trust.eure"), "{status}");
    assert!(
        status.contains("waits 2h 0m; checkpoints valid 2d 0h; origin checked within 1m"),
        "{status}"
    );

    // It may add to an index of Trust.eure, not read it from elsewhere.
    let trust = w.read("Trust.eure");
    let me = &trust[trust.find("@ indexes[]").unwrap()..trust.find("@ defaults").unwrap()];
    w.user_trust(&me.replace("refs/heads/main", "refs/heads/other"));
    let err = w.fails(&["index", "status"]);
    assert!(err.contains("may add to it, not change it"), "{err}");

    // A user policy named but not there is an error, not the default.
    fs::remove_file(w.user_trust_file()).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(w.app())
        .env("TAUTO_INDEX_STATE", w.temp.0.join("state"))
        .env("TAUTO_USER_TRUST", w.user_trust_file())
        .args(["index", "status"])
        .output()
        .unwrap();
    assert!(!out.status.success());
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("user-trust.eure"), "{err}");
}
