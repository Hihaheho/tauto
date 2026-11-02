//! Fetching from a repository on disk (`file:///`), as from a server.

use std::path::{Path, PathBuf};
use std::process::Command;

use totebag::cache::Cache;
use totebag::lock::Locked;
use totebag::source::{File, Tree};
use totebag::spec::{GitSource, SourceId};

struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Scratch {
        let dir = std::env::temp_dir().join(format!(
            "totebag-{name}-{}-{}",
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

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

/// A repository with a tote in `lib/` and a script beside it.
fn repository(at: &Path) -> String {
    git(at, &["init", "--quiet"]);
    write(
        &at.join("lib/Tauto.eure"),
        "package { name = \"lib\", version = \"0.1.0\", }\n",
    );
    write(&at.join("lib/src/lib.taut"), "fn one(): i64 { 1 }\n");
    write(&at.join("run.sh"), "#!/bin/sh\n");
    git(at, &["add", "."]);
    git(at, &["update-index", "--chmod=+x", "run.sh"]);
    git(at, &["commit", "--quiet", "-m", "first"]);
    git(at, &["rev-parse", "HEAD"])
}

fn source(repo: &Path) -> GitSource {
    GitSource {
        url: format!("file://{}", repo.display()),
        reference: "refs/heads/main".into(),
        dir: "lib".into(),
        project: None,
    }
}

#[test]
fn a_fetched_tree_is_the_commit_and_is_kept_under_its_id() {
    tauto_messages::install();
    let s = Scratch::new("fetch");
    let repo = s.0.join("repo");
    std::fs::create_dir_all(&repo).unwrap();
    let head = repository(&repo);
    let cache = Cache::at(s.0.join("cache"));
    let fetched = totebag::fetch_head(&cache, &source(&repo)).unwrap();
    assert_eq!(fetched.rev.hex(), head);
    let expected = Tree::new(vec![
        File {
            path: "lib/Tauto.eure".into(),
            executable: false,
            bytes: b"package { name = \"lib\", version = \"0.1.0\", }\n".to_vec(),
        },
        File {
            path: "lib/src/lib.taut".into(),
            executable: false,
            bytes: b"fn one(): i64 { 1 }\n".to_vec(),
        },
        File {
            path: "run.sh".into(),
            executable: true,
            bytes: b"#!/bin/sh\n".to_vec(),
        },
    ])
    .unwrap();
    assert_eq!(fetched.id, expected.id);
    assert_eq!(fetched.dir, cache.source_dir(&fetched.id).join("lib"));
    assert!(fetched.dir.join("src/lib.taut").is_file());
    cache.verify(&fetched.id).unwrap();

    // The same commit by its ID into another cache.
    let other = Cache::at(s.0.join("other"));
    let locked = Locked {
        name: "lib".into(),
        source: source(&repo),
        rev: fetched.rev.clone(),
        id: fetched.id.clone(),
    };
    // A new commit on the branch does not move what is locked.
    write(&repo.join("lib/src/lib.taut"), "fn one(): i64 { 2 }\n");
    git(&repo, &["commit", "--quiet", "-am", "second"]);
    let dir = totebag::fetch_locked(&other, &locked).unwrap();
    assert_eq!(
        std::fs::read_to_string(dir.join("src/lib.taut")).unwrap(),
        "fn one(): i64 { 1 }\n"
    );

    // A lock whose content does not match the commit.
    let wrong = Locked {
        id: SourceId::parse(&format!("sha256:{}", "0".repeat(64))).unwrap(),
        ..locked.clone()
    };
    let err = totebag::fetch_locked(&Cache::at(s.0.join("third")), &wrong).unwrap_err();
    assert!(err.contains("Tauto.lock says"), "{err}");

    // The head moved.
    let moved = totebag::fetch_head(&cache, &source(&repo)).unwrap();
    assert_ne!(moved.rev, fetched.rev);
    assert_ne!(moved.id, fetched.id);
}

#[test]
fn links_and_missing_directories_are_refused() {
    tauto_messages::install();
    let s = Scratch::new("refuse");
    let repo = s.0.join("repo");
    std::fs::create_dir_all(&repo).unwrap();
    repository(&repo);
    let cache = Cache::at(s.0.join("cache"));
    let missing = GitSource {
        dir: "nowhere".into(),
        ..source(&repo)
    };
    let err = totebag::fetch_head(&cache, &missing).unwrap_err();
    assert!(err.contains("no directory nowhere"), "{err}");

    #[cfg(unix)]
    {
        std::os::unix::fs::symlink("run.sh", repo.join("link")).unwrap();
        git(&repo, &["add", "link"]);
        git(&repo, &["commit", "--quiet", "-m", "link"]);
        let err = totebag::fetch_head(&cache, &source(&repo)).unwrap_err();
        assert!(err.contains("symbolic link"), "{err}");
    }
}
