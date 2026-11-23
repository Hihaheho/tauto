//! Fetching from a repository on disk (`file:///`), as from a server.

use std::path::{Path, PathBuf};
use tauto_test_support::{Scratch, git};

use totebag::cache::Cache;
use totebag::lock::Locked;
use totebag::source::{File, Tree};
use totebag::spec::{GitSource, SourceId};

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
        sparse: false,
        project: None,
    }
}

#[test]
fn a_fetched_tree_is_the_commit_and_is_kept_under_its_id() {
    tauto_messages::install();
    let s = Scratch::new("totebag-fetch");
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
    let s = Scratch::new("totebag-refuse");
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

/// A sparse source is the files under its `dir` and nothing else: the other
/// blobs of the commit are not in the cache's repository, and the tree
/// hashed is that directory's, with its paths in the repository.
#[test]
fn a_sparse_source_takes_only_its_directory() {
    tauto_messages::install();
    let s = Scratch::new("totebag-sparse");
    let repo = s.0.join("repo");
    std::fs::create_dir_all(&repo).unwrap();
    repository(&repo);
    write(
        &repo.join("other/Tauto.eure"),
        "package { name = \"other\" }\n",
    );
    write(&repo.join("other/big.txt"), "not for the lib\n");
    git(&repo, &["add", "."]);
    git(&repo, &["commit", "--quiet", "-m", "other"]);
    // A server that filters and gives objects by ID.
    git(&repo, &["config", "uploadpack.allowFilter", "true"]);
    git(&repo, &["config", "uploadpack.allowAnySHA1InWant", "true"]);
    let sparse = GitSource {
        sparse: true,
        ..source(&repo)
    };
    let cache = Cache::at(s.0.join("cache"));
    let fetched = totebag::fetch_head(&cache, &sparse).unwrap();
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
    ])
    .unwrap();
    assert_eq!(fetched.id, expected.id);
    assert!(fetched.dir.join("src/lib.taut").is_file());
    let root = cache.source_dir(&fetched.id);
    assert!(!root.join("run.sh").exists());
    assert!(!root.join("other").exists());
    cache.verify(&fetched.id).unwrap();

    // The whole repository hashes to another ID.
    let whole = totebag::fetch_head(&cache, &source(&repo)).unwrap();
    assert_ne!(whole.id, fetched.id);

    // What the sparse repository holds: the lib's blobs, not the others.
    let blob = git(&repo, &["rev-parse", "HEAD:other/big.txt"]);
    let mirror = cache.mirror_for(&sparse);
    // Asked with `rev-list`, which does not fetch what it finds missing.
    let listing = git(
        &mirror,
        &[
            "rev-list",
            "--objects",
            "--missing=print",
            "--no-object-names",
            fetched.rev.hex(),
        ],
    );
    let has = |oid: &str| !listing.lines().any(|l| l == format!("?{oid}"));
    assert!(!has(&blob));
    assert!(has(&git(&repo, &["rev-parse", "HEAD:lib/src/lib.taut"])));

    // The locked commit into another cache, by its ID.
    let locked = Locked {
        name: "lib".into(),
        source: sparse.clone(),
        rev: fetched.rev.clone(),
        id: fetched.id.clone(),
    };
    let other = Cache::at(s.0.join("other"));
    let dir = totebag::fetch_locked(&other, &locked).unwrap();
    assert!(dir.join("src/lib.taut").is_file());
    assert!(!other.source_dir(&fetched.id).join("other").exists());

    // Without a directory there is nothing to be sparse about.
    let bad = GitSource {
        dir: String::new(),
        ..sparse
    };
    assert!(totebag::fetch_head(&cache, &bad).is_err());
}

/// A server that does not filter, or does not give objects by ID, still
/// gives the directory.
#[test]
fn a_sparse_source_from_a_server_that_does_not_filter() {
    tauto_messages::install();
    let s = Scratch::new("totebag-sparse-plain");
    let repo = s.0.join("repo");
    std::fs::create_dir_all(&repo).unwrap();
    repository(&repo);
    let sparse = GitSource {
        sparse: true,
        ..source(&repo)
    };
    let cache = Cache::at(s.0.join("cache"));
    let fetched = totebag::fetch_head(&cache, &sparse).unwrap();
    let root = cache.source_dir(&fetched.id);
    assert!(root.join("lib/src/lib.taut").is_file());
    assert!(!root.join("run.sh").exists());
}
