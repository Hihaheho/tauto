//! Reading an index's history from a repository on disk: a line of commits,
//! each adding one batch, and the digests that chain them.

use std::path::{Path, PathBuf};
use std::process::Command;

use totebag::git::Mirror;
use totebag::index::checkpoint::{self, History};
use totebag::index::ledger::Event;

struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Scratch {
        let dir = std::env::temp_dir().join(format!(
            "totebag-index-{name}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        Scratch(dir)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
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

const CONFIG: &str = "format = 1\nkind = \"index\"\nname = \"alice\"\nhistory = \"commit-batches\"\ngit_object_format = \"sha1\"\n";
const PROJECT: &str = "sha256:2222222222222222222222222222222222222222222222222222222222222222";
const SOURCE: &str = "sha256:3333333333333333333333333333333333333333333333333333333333333333";
const REV: &str = "0123456789abcdef0123456789abcdef01234567";

fn batch(sequence: u64, events: &str) -> String {
    let events = if events.is_empty() {
        "events = []\n".to_string()
    } else {
        events.to_string()
    };
    format!(
        "format = 1\nkind = \"batch\"\nsequence = {sequence}\nissued_at = \"2026-10-0{}T12:00:00Z\"\nvalid_until = \"2026-10-0{}T12:00:00Z\"\n{events}",
        sequence + 1,
        sequence + 2
    )
}

fn observation() -> String {
    format!(
        "@ events[] {{\n  kind = \"observation\"\n  project = \"{PROJECT}\"\n  rev = \"{REV}\"\n  source_sha256 = \"{SOURCE}\"\n  first_seen_at = \"2026-10-02T11:00:00Z\"\n}}\n"
    )
}

/// Writes the two files and commits them; gives the commit's ID.
fn commit(repo: &Path, config: &str, batch: &str) -> String {
    std::fs::write(repo.join("Index.eure"), config).unwrap();
    std::fs::write(repo.join("observations.eure"), batch).unwrap();
    git(repo, &["add", "."]);
    git(repo, &["commit", "--quiet", "--allow-empty", "-m", "batch"]);
    git(repo, &["rev-parse", "HEAD"])
}

fn index(at: &Path) -> Vec<String> {
    std::fs::create_dir_all(at).unwrap();
    git(at, &["init", "--quiet"]);
    vec![
        commit(at, CONFIG, &batch(0, "")),
        commit(at, CONFIG, &batch(1, &observation())),
        commit(at, CONFIG, &batch(2, "")),
    ]
}

fn read(s: &Scratch, repo: &Path, name: &str) -> Result<History, String> {
    let mirror = Mirror::open(s.0.join(name), "sha1").unwrap();
    let head = mirror.fetch_history(&format!("file://{}", repo.display()), "refs/heads/main")?;
    checkpoint::history(&mirror, &head)
}

#[test]
fn a_history_is_read_root_first_and_chained() {
    tauto_messages::install();
    let s = Scratch::new("chain");
    let repo = s.0.join("repo");
    let revs = index(&repo);
    let history = read(&s, &repo, "mirror").unwrap();
    assert_eq!(history.config.name, "alice");
    assert_eq!(history.config_bytes, CONFIG.as_bytes());
    let got: Vec<_> = history
        .checkpoints
        .iter()
        .map(|c| c.rev.hex().to_string())
        .collect();
    assert_eq!(got, revs);
    assert!(matches!(
        history.checkpoints[1].batch.events.as_slice(),
        [Event::Observation { .. }]
    ));

    // Each digest is the one spelled from its parent's and its own objects.
    let mut parent = None;
    for c in &history.checkpoints {
        let payload = git(&repo, &["cat-file", "commit", c.rev.hex()]);
        let batch = git(
            &repo,
            &["show", &format!("{}:observations.eure", c.rev.hex())],
        );
        // `git` trims its output; the files end in a newline.
        let expected = checkpoint::digest(
            parent.as_ref(),
            &c.rev,
            format!("{payload}\n").as_bytes(),
            CONFIG.as_bytes(),
            format!("{batch}\n").as_bytes(),
        );
        assert_eq!(c.digest, expected, "{}", c.rev.short());
        parent = Some(c.digest);
    }
    assert_eq!(history.id(), history.checkpoints[0].digest);

    // A longer history keeps the earlier digests.
    commit(&repo, CONFIG, &batch(3, ""));
    let longer = read(&s, &repo, "mirror").unwrap();
    assert_eq!(longer.checkpoints.len(), 4);
    for (a, b) in history.checkpoints.iter().zip(&longer.checkpoints) {
        assert_eq!(a.digest, b.digest);
    }
}

#[test]
fn a_merge_is_refused() {
    tauto_messages::install();
    let s = Scratch::new("merge");
    let repo = s.0.join("repo");
    index(&repo);
    git(&repo, &["checkout", "--quiet", "-b", "side", "HEAD~1"]);
    commit(&repo, CONFIG, &batch(2, &observation()));
    git(&repo, &["checkout", "--quiet", "main"]);
    git(
        &repo,
        &[
            "merge", "--quiet", "--no-ff", "-X", "ours", "-m", "merge", "side",
        ],
    );
    let err = read(&s, &repo, "mirror").unwrap_err();
    assert!(err.contains("is a merge"), "{err}");
}

#[test]
fn the_config_does_not_change() {
    tauto_messages::install();
    let s = Scratch::new("config");
    let repo = s.0.join("repo");
    index(&repo);
    commit(&repo, &CONFIG.replace("alice", "mallory"), &batch(3, ""));
    let err = read(&s, &repo, "mirror").unwrap_err();
    assert!(err.contains("Index.eure changed"), "{err}");
}

#[test]
fn the_root_is_an_empty_batch_zero() {
    tauto_messages::install();
    let s = Scratch::new("root");
    let repo = s.0.join("repo");
    std::fs::create_dir_all(&repo).unwrap();
    git(&repo, &["init", "--quiet"]);
    commit(&repo, CONFIG, &batch(0, &observation()));
    let err = read(&s, &repo, "mirror").unwrap_err();
    assert!(err.contains("the root"), "{err}");
}

#[test]
fn a_bad_batch_or_a_missing_file_is_refused() {
    tauto_messages::install();
    let s = Scratch::new("bad");
    let repo = s.0.join("repo");
    index(&repo);
    commit(
        &repo,
        CONFIG,
        &batch(3, "").replace("format = 1", "format = 2"),
    );
    let err = read(&s, &repo, "a").unwrap_err();
    assert!(err.contains("format 2"), "{err}");

    let repo = s.0.join("other");
    index(&repo);
    git(&repo, &["rm", "--quiet", "observations.eure"]);
    git(&repo, &["commit", "--quiet", "-m", "gone"]);
    let err = read(&s, &repo, "b").unwrap_err();
    assert!(err.contains("has no observations.eure"), "{err}");

    #[cfg(unix)]
    {
        let repo = s.0.join("exec");
        index(&repo);
        git(&repo, &["update-index", "--chmod=+x", "observations.eure"]);
        git(&repo, &["commit", "--quiet", "-m", "exec"]);
        let err = read(&s, &repo, "c").unwrap_err();
        assert!(err.contains("not a regular file"), "{err}");
    }
}
