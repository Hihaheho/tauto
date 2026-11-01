//! A scratch directory and index repositories built with `git`.
#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

use totebag::index::ledger::Key;
use totebag::index::strict::hex_bytes;

pub struct Scratch(pub PathBuf);

impl Scratch {
    pub fn new(name: &str) -> Scratch {
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

pub fn git(dir: &Path, args: &[&str]) -> String {
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

pub const CONFIG: &str = "format = 1\nkind = \"index\"\nname = \"alice\"\nhistory = \"commit-batches\"\ngit_object_format = \"sha1\"\n";
pub const PROJECT: &str = "sha256:2222222222222222222222222222222222222222222222222222222222222222";
pub const SOURCE: &str = "sha256:3333333333333333333333333333333333333333333333333333333333333333";
pub const REV: &str = "0123456789abcdef0123456789abcdef01234567";

pub fn batch(sequence: u64, issued: &str, until: &str, events: &[String]) -> String {
    let events = if events.is_empty() {
        "events = []\n".to_string()
    } else {
        events.concat()
    };
    format!(
        "format = 1\nkind = \"batch\"\nsequence = {sequence}\nissued_at = \"{issued}\"\nvalid_until = \"{until}\"\n{events}"
    )
}

pub fn observation(first: &str) -> String {
    format!(
        "@ events[] {{\n  kind = \"observation\"\n  project = \"{PROJECT}\"\n  rev = \"{REV}\"\n  source_sha256 = \"{SOURCE}\"\n  first_seen_at = \"{first}\"\n}}\n"
    )
}

pub fn decision(verdict: &str) -> String {
    format!(
        "@ events[] {{\n  kind = \"decision\"\n  project = \"{PROJECT}\"\n  rev = \"{REV}\"\n  verdict = \"{verdict}\"\n  reason = \"reviewed\"\n}}\n"
    )
}

pub fn commit(repo: &Path, batch: &str) {
    std::fs::write(repo.join("Index.eure"), CONFIG).unwrap();
    std::fs::write(repo.join("observations.eure"), batch).unwrap();
    git(repo, &["add", "."]);
    git(repo, &["commit", "--quiet", "--allow-empty", "-m", "batch"]);
}

pub fn init(repo: &Path) {
    std::fs::create_dir_all(repo).unwrap();
    git(repo, &["init", "--quiet"]);
    commit(
        repo,
        &batch(0, "2026-10-01T00:00:00Z", "2026-10-02T00:00:00Z", &[]),
    );
}

pub fn url(repo: &Path) -> String {
    format!("file://{}", repo.display())
}

pub fn key() -> Key {
    Key {
        project: hex_bytes(&PROJECT["sha256:".len()..]),
        rev: REV.into(),
    }
}
