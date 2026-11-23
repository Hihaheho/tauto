//! `totes/totebag-io`'s reading of a source tree and its ID (`source-v1`) against
//! `totebag::source::Tree::read_dir`.

use std::fs;
use std::path::Path;

use selfhost_harness::{assert_same_dump, root, run_tote_at, run_tote_at_with};

/// Reads the directories it is given and prints each one's ID, or `refused`.

/// `source` with its statements, those after its imports and functions, in
/// the body of the tote's `main`: a tote's main is a module.
fn entry(source: &str) -> String {
    let lines: Vec<&str> = source.lines().collect();
    let start = lines
        .iter()
        .position(|l| ["match ", "var ", "let ", "print(", "each("].iter().any(|p| l.starts_with(p)))
        .unwrap_or(lines.len());
    let mut out: String = lines[..start].iter().map(|l| format!("{l}\n")).collect();
    out.push_str("perform main(() => {\n");
    for l in &lines[start..] {
        out.push_str(&format!("  {l}\n"));
    }
    out.push_str("})\n");
    out
}

fn main_source() -> &'static str {
    r#"import totebag_io::source
import std::builtin::os
import std::text

fn each(dirs: List(Text)) {
  match dirs {
    Nil => #()
    Cons(d, rest) => {
      match tb_read_dir(d) {
        Ok(r) => print(Text::concat(r.snd, "\n"))
        Err(_) => print("refused\n")
      }
      each(rest)
    }
  }
}

each(perform argv())
"#
}

fn write(dir: &Path, path: &str, bytes: &[u8]) {
    let file = dir.join(path);
    fs::create_dir_all(file.parent().unwrap()).unwrap();
    fs::write(file, bytes).unwrap();
}

/// Trees of files, some executable.
fn trees(base: &Path) -> Vec<std::path::PathBuf> {
    let mut seed = 11u64;
    let mut bytes = |n: usize| -> Vec<u8> {
        (0..n)
            .map(|_| {
                seed = seed
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                (seed >> 56) as u8
            })
            .collect()
    };
    let cases: Vec<Vec<(&str, Vec<u8>)>> = vec![
        vec![],
        vec![("Tauto.eure", b"package {}\n".to_vec())],
        // Lengths around SHA-256's block and padding boundaries.
        vec![("a", bytes(0)), ("b", bytes(55)), ("c", bytes(56))],
        vec![("a", bytes(63)), ("b", bytes(64)), ("c", bytes(65)), ("d", bytes(119))],
        vec![("src/main.taut", bytes(300)), ("src/lib/x.taut", bytes(17)), ("README.md", bytes(4000))],
        // Byte order of paths, not component order.
        vec![("a-b", bytes(3)), ("a/b", bytes(3)), ("a.b", bytes(3)), ("B", bytes(1))],
        vec![("é/ü.taut", bytes(9)), ("z", bytes(2))],
        // One file without case.
        vec![("Readme", bytes(1)), ("README", bytes(1))],
        vec![("Ä", bytes(1)), ("ä", bytes(1))],
        // A name with a control character.
        vec![("a\u{7f}b", bytes(1))],
    ];
    let mut dirs = Vec::new();
    for (i, files) in cases.into_iter().enumerate() {
        let dir = base.join(format!("t{i}"));
        fs::create_dir_all(&dir).unwrap();
        for (path, b) in files {
            write(&dir, path, &b);
        }
        dirs.push(dir);
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let exec = base.join("exec");
        write(&exec, "run.sh", b"echo hi\n");
        write(&exec, "data", b"x");
        fs::set_permissions(exec.join("run.sh"), fs::Permissions::from_mode(0o755)).unwrap();
        fs::set_permissions(exec.join("data"), fs::Permissions::from_mode(0o444)).unwrap();
        dirs.push(exec);
    }
    let many = base.join("many");
    for i in 0..200 {
        write(&many, &format!("d{}/f{i}", i % 7), &bytes(i));
    }
    dirs.push(many);
    #[cfg(unix)]
    {
        let link = base.join("link");
        write(&link, "a", b"a");
        std::os::unix::fs::symlink("a", link.join("b")).unwrap();
        dirs.push(link);
    }
    dirs.push(base.join("missing"));
    dirs
}

#[test]
fn source_ids_match_rust() {
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let dirs = trees(&base.join("trees"));
    let probe = base.join("probe");
    fs::create_dir_all(probe.join("src")).unwrap();
    fs::write(
        probe.join("Tauto.eure"),
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            root().join("totes/totebag-io").canonicalize().unwrap().display()
        ),
    )
    .unwrap();
    fs::write(probe.join("src/main.taut"), entry(&main_source())).unwrap();
    let args: Vec<String> = dirs
        .iter()
        .map(|d| d.to_string_lossy().into_owned())
        .collect();
    let out = run_tote_at(&probe, &args, 4_000_000_000);
    assert_eq!(out.error, None, "{}", out.stderr);
    let rust: String = dirs
        .iter()
        .map(|d| match totebag::source::Tree::read_dir(d) {
            Ok(tree) => format!("{}\n", tree.id),
            Err(_) => "refused\n".to_string(),
        })
        .collect();
    let _ = fs::remove_dir_all(&base);
    assert_same_dump("totebag source ids", &rust, &out.stdout);
}

/// Reads the lock files it is given and prints each one written again, or
/// `refused`, each followed by `==`.
fn lock_main_source() -> &'static str {
    r#"import totebag_io::lock
import totebag::lock
import std::builtin::os
import std::text

fn each(paths: List(Text)) {
  match paths {
    Nil => #()
    Cons(p, rest) => {
      match read_file(p) {
        Ok(t) => match tb_parse_lock(t) {
          Ok(l) => print(tb_render(l))
          Err(_) => print("refused\n")
        }
        Err(_) => print("refused\n")
      }
      print("==\n")
      each(rest)
    }
  }
}

each(perform argv())
"#
}

fn sample_lock() -> String {
    let h = |c: &str, n| c.repeat(n);
    format!(
        "format = 1\n\n@ totes[] {{\n  name = \"text\"\n  git = \"https://example.org/text\"\n  ref = \"refs/heads/main\"\n  dir = \"\"\n  rev = \"sha1:{}\"\n  source = \"sha256:{}\"\n}}\n\n@ totes[] {{\n  name = \"semver\"\n  git = \"https://example.com/tauto/monorepo\"\n  ref = \"refs/tags/v1\"\n  dir = \"semver\"\n  sparse = true\n  project = \"sha256:{}\"\n  rev = \"sha1:{}\"\n  source = \"sha256:{}\"\n}}\n",
        h("1", 40),
        h("a", 64),
        h("c", 64),
        h("2", 40),
        h("b", 64)
    )
}

#[test]
fn locks_match_rust() {
    let text = sample_lock();
    let mut locks = vec![
        text.clone(),
        "format = 1\n".to_string(),
        String::new(),
        "// nothing\nformat = 1\ntotes = []\n".to_string(),
        totebag::lock::parse(&text).unwrap().render(),
    ];
    for (from, to) in [
        ("format = 1", "format = 2"),
        ("format = 1", "format = \"1\""),
        ("format = 1", ""),
        ("format = 1", "format = 1\nother = 1"),
        ("  dir = \"semver\"\n", "  dir = \"semver\"\n  extra = \"x\"\n"),
        ("name = \"text\"", "name = \"semver\""),
        ("name = \"text\"", "name = \"Text\""),
        ("name = \"text\"", "name = 3"),
        ("refs/heads/main", "main"),
        ("https://example.org/text", "http://example.org/text"),
        ("https://example.org/text", "https://user@example.org/text"),
        ("sha1:1111", "sha1:111"),
        ("sha256:aaaa", "sha256:aaa"),
        ("sha256:cccc", "sha256:ccc"),
        ("sparse = true", "sparse = false"),
        ("dir = \"semver\"", "dir = \"\""),
        ("dir = \"semver\"", "dir = \"../semver\""),
        ("  name = \"text\"\n", ""),
        ("@ totes[] {\n  name = \"text\"", "@ totes[] {\n  $note = \"x\"\n  name = \"text\""),
    ] {
        let bad = text.replacen(from, to, 1);
        assert_ne!(bad, text, "{from}");
        locks.push(bad);
    }
    locks.push(
        text.lines()
            .filter(|l| !l.trim_start().starts_with("rev"))
            .map(|l| format!("{l}\n"))
            .collect(),
    );
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-lock-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    fs::create_dir_all(base.join("probe/src")).unwrap();
    let mut args = Vec::new();
    for (i, l) in locks.iter().enumerate() {
        let p = base.join(format!("{i}.lock"));
        fs::write(&p, l).unwrap();
        args.push(p.to_string_lossy().into_owned());
    }
    let totes = root().join("totes").canonicalize().unwrap();
    fs::write(
        base.join("probe/Tauto.eure"),
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n  totebag {{ path = \"{}\" }}\n}}\n",
            totes.join("totebag-io").display(),
            totes.join("totebag").display()
        ),
    )
    .unwrap();
    fs::write(base.join("probe/src/main.taut"), entry(&lock_main_source())).unwrap();
    let out = run_tote_at(&base.join("probe"), &args, 4_000_000_000);
    let _ = fs::remove_dir_all(&base);
    assert_eq!(out.error, None, "{}", out.stderr);
    let rust: String = locks
        .iter()
        .map(|l| match totebag::lock::parse(l) {
            Ok(lock) => format!("{}==\n", lock.render()),
            Err(_) => "refused\n==\n".to_string(),
        })
        .collect();
    assert_same_dump("totebag locks", &rust, &out.stdout);
}

/// Reads the tree at the first argument, installs it in the cache at the
/// second, verifies it, and prints the tree's directory and the mirror
/// directories of the third argument, plain and sparse.
fn cache_main_source() -> &'static str {
    r#"import totebag_io::cache
import totebag_io::source
import std::builtin::os
import std::text

match perform argv() {
  Cons(tree, Cons(root, Cons(url, Nil))) => match tb_read_dir(tree) {
    Ok(r) => match tb_install(root, r.fst, r.snd) {
      Ok(dest) => {
        print(Text::concat(dest, "\n"))
        match tb_install(root, r.fst, r.snd) {
          Ok(again) => print(Text::concat(again, "\n"))
          Err(e) => print(Text::concat(e, "\n"))
        }
        match tb_verify(root, r.snd) {
          Ok(_) => print("verified\n")
          Err(e) => print(Text::concat(e, "\n"))
        }
        print(Text::concat(tb_mirror_dir(root, url, false), "\n"))
        print(Text::concat(tb_mirror_dir(root, url, true), "\n"))
      }
      Err(e) => print(Text::concat(e, "\n"))
    }
    Err(_) => print("refused\n")
  }
  _ => print("usage\n")
}
"#
}

#[test]
fn the_cache_matches_rust() {
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-cache-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let tree = base.join("tree");
    write(&tree, "Tauto.eure", b"package {}\n");
    write(&tree, "src/main.taut", b"print(\"hi\")\n");
    write(&tree, "src/deep/x.taut", &[0, 1, 2, 255]);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        write(&tree, "bin/run", b"#!/bin/sh\n");
        fs::set_permissions(tree.join("bin/run"), fs::Permissions::from_mode(0o755)).unwrap();
    }
    let root = base.join("cache");
    fs::create_dir_all(&root).unwrap();
    fs::create_dir_all(base.join("probe/src")).unwrap();
    fs::write(
        base.join("probe/Tauto.eure"),
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            root_totes().join("totebag-io").display()
        ),
    )
    .unwrap();
    fs::write(base.join("probe/src/main.taut"), entry(&cache_main_source())).unwrap();
    let url = "https://example.com/tauto/monorepo";
    let args = [
        tree.to_string_lossy().into_owned(),
        root.to_string_lossy().into_owned(),
        url.to_string(),
    ];
    let out = run_tote_at(&base.join("probe"), &args, 4_000_000_000);
    assert_eq!(out.error, None, "{}", out.stderr);
    let t = totebag::source::Tree::read_dir(&tree).unwrap();
    let cache = totebag::cache::Cache::at(root.clone());
    // Rust reads what the tote installed as the same tree.
    cache.verify(&t.id).unwrap();
    let dest = cache.source_dir(&t.id).display().to_string();
    let source = |sparse| totebag::spec::GitSource {
        url: url.into(),
        reference: "refs/heads/main".into(),
        dir: "x".into(),
        sparse,
        project: None,
    };
    let rust = format!(
        "{dest}\n{dest}\nverified\n{}\n{}\n",
        cache.mirror_for(&source(false)).display(),
        cache.mirror_for(&source(true)).display()
    );
    // The tote's files are read-only, and keep the executable bit, as Rust's.
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let dir = cache.source_dir(&t.id);
        let mode = |p: &str| fs::metadata(dir.join(p)).unwrap().permissions().mode() & 0o777;
        assert_eq!((mode("bin/run"), mode("Tauto.eure")), (0o555, 0o444));
    }
    let _ = make_writable(&base);
    let _ = fs::remove_dir_all(&base);
    assert_same_dump("totebag cache", &rust, &out.stdout);
}

fn root_totes() -> std::path::PathBuf {
    root().join("totes").canonicalize().unwrap()
}

/// Makes every file under `dir` writable again, so it can be removed where
/// the system refuses to remove read-only files.
fn make_writable(dir: &Path) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let p = entry?.path();
        if p.is_dir() {
            make_writable(&p)?;
        } else {
            let mut perm = fs::metadata(&p)?.permissions();
            #[allow(clippy::permissions_set_readonly_false)]
            perm.set_readonly(false);
            fs::set_permissions(&p, perm)?;
        }
    }
    Ok(())
}

/// Fetches the repository at the URL it is given into a mirror, as
/// `totebag::git` does, and prints the default branch, the fetched commit,
/// the tree's ID, sparse and whole, the commit payload's size, and the root
/// entry `Tauto.eure`.
fn git_main_source() -> &'static str {
    r#"import totebag_io::git
import totebag_io::source
import std::builtin::os
import std::text

fn line(r: Result(Text, Text)): Unit {
  match r {
    Ok(t) => print(Text::concat(t, "\n"))
    Err(e) => print(Text::concat("error ", Text::concat(e, "\n")))
  }
}

fn id(r: Result(List(TbFile) × Text, Text)): Result(Text, Text) {
  match r {
    Ok(t) => Ok(t.snd)
    Err(e) => Err(e)
  }
}

match perform argv() {
  Cons(url, Cons(mirror, Cons(sparse_mirror, Nil))) => {
    line(tb_default_branch(url))
    match tb_mirror_open(mirror, "sha1") {
      Ok(dir) => match tb_fetch_head(dir, url, "refs/heads/main", false) {
        Ok(rev) => {
          print(Text::concat(rev, "\n"))
          line(tb_resolve(dir, "FETCH_HEAD"))
          line(id(tb_git_tree(dir, rev, url, false, "")))
          match tb_commit(dir, rev) {
            Ok(p) => print(Text::concat(Text::of_u64(Bytes::len(p)), "\n"))
            Err(e) => print(Text::concat(e, "\n"))
          }
          match tb_keep(dir, "pkg", rev) {
            Ok(_) => print("kept\n")
            Err(e) => print(Text::concat(e, "\n"))
          }
          match tb_mirror_open(sparse_mirror, "sha1") {
            Ok(sdir) => match tb_fetch_rev(sdir, url, "refs/heads/main", true, rev) {
              Ok(_) => line(id(tb_git_tree(sdir, rev, url, true, "pkg")))
              Err(e) => print(Text::concat(e, "\n"))
            }
            Err(e) => print(Text::concat(e, "\n"))
          }
        }
        Err(e) => print(Text::concat(e, "\n"))
      }
      Err(e) => print(Text::concat(e, "\n"))
    }
  }
  _ => print("usage\n")
}
"#
}

#[test]
fn git_fetches_match_rust() {
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-git-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let repo = base.join("repo");
    write(&repo, "Tauto.eure", b"package {}\n");
    write(&repo, "pkg/src/main.taut", b"print(\"pkg\")\n");
    write(&repo, "other/a.txt", b"a");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        write(&repo, "pkg/run.sh", b"#!/bin/sh\n");
        fs::set_permissions(repo.join("pkg/run.sh"), fs::Permissions::from_mode(0o755)).unwrap();
    }
    let git = |args: &[&str]| {
        let out = std::process::Command::new("git")
            .arg("-C")
            .arg(&repo)
            .args(args)
            .env("GIT_AUTHOR_NAME", "t")
            .env("GIT_AUTHOR_EMAIL", "t@example.com")
            .env("GIT_COMMITTER_NAME", "t")
            .env("GIT_COMMITTER_EMAIL", "t@example.com")
            .output()
            .unwrap();
        assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    };
    git(&["init", "--quiet", "--initial-branch=main"]);
    git(&["config", "uploadpack.allowFilter", "true"]);
    git(&["config", "uploadpack.allowAnySHA1InWant", "true"]);
    git(&["add", "."]);
    git(&["commit", "--quiet", "-m", "one"]);
    let url = format!("file://{}", repo.display());
    fs::create_dir_all(base.join("probe/src")).unwrap();
    fs::write(
        base.join("probe/Tauto.eure"),
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            root_totes().join("totebag-io").display()
        ),
    )
    .unwrap();
    fs::write(base.join("probe/src/main.taut"), entry(&git_main_source())).unwrap();
    let args = [
        url.clone(),
        base.join("tote-mirror").to_string_lossy().into_owned(),
        base.join("tote-sparse").to_string_lossy().into_owned(),
    ];
    let out = run_tote_at_with(&base.join("probe"), &args, 4_000_000_000, &["git"]);
    assert_eq!(out.error, None, "{}", out.stderr);

    use totebag::git::{Mirror, default_branch};
    let source = |sparse: bool| totebag::spec::GitSource {
        url: url.clone(),
        reference: "refs/heads/main".into(),
        dir: "pkg".into(),
        sparse,
        project: None,
    };
    let mut rust = format!("{}\n", default_branch(&url).unwrap());
    let m = Mirror::open(base.join("rust-mirror"), "sha1").unwrap();
    let rev = m.fetch_head(&source(false)).unwrap();
    rust.push_str(&format!("{rev}\n{}\n", m.resolve("FETCH_HEAD").unwrap()));
    rust.push_str(&format!("{}\n", m.tree(&rev, &source(false)).unwrap().id));
    rust.push_str(&format!("{}\n", m.commit(&rev).unwrap().len()));
    m.keep("pkg", &rev).unwrap();
    rust.push_str("kept\n");
    let s = Mirror::open(base.join("rust-sparse"), "sha1").unwrap();
    s.fetch_rev(&source(true), &rev).unwrap();
    rust.push_str(&format!("{}\n", s.tree(&rev, &source(true)).unwrap().id));
    let _ = fs::remove_dir_all(&base);
    assert_same_dump("totebag git", &rust, &out.stdout);
}

/// Checks each argument as every kind of index value and as a strict
/// document, printing the value or the error's message ID.
fn strict_main_source() -> &'static str {
    r#"import totebag_io::strict
import std::builtin::os
import std::text

fn show(r: Result(Text, Text)): Text {
  match r {
    Ok(t) => Text::concat("ok ", t)
    Err(e) => e
  }
}

fn show_u64(r: Result(u64, Text)): Text {
  match r {
    Ok(n) => Text::concat("ok ", Text::of_u64(n))
    Err(e) => e
  }
}

fn doc(t: Text): Text {
  match tb_strict_parse(Bytes::of_text(t), 100) {
    Ok(d) => match tb_fields(d) {
      Ok(fs) => match tb_required(fs, "a") {
        Ok(p) => {
          let a := show_u64(tb_strict_integer(p.fst))
          match tb_finish(p.snd) {
            Ok(_) => a
            Err(e) => Text::concat(a, Text::concat(" ", e))
          }
        }
        Err(e) => match tb_finish(fs) {
          Ok(_) => e
          Err(e2) => Text::concat(e, Text::concat(" ", e2))
        }
      }
      Err(e) => e
    }
    Err(e) => e
  }
}

var rest := perform argv()
var going := true
while going {
  match rest {
    Cons(s, more) => {
      print(Text::concat(show_u64(tb_time(s)), "\n"))
      print(Text::concat(show(tb_sha256(s)), "\n"))
      print(Text::concat(show(tb_package_rev(s)), "\n"))
      print(Text::concat(show(tb_https_url(s)), "\n"))
      print(Text::concat(show(tb_branch(s)), "\n"))
      print(Text::concat(show(tb_alias(s)), "\n"))
      print(Text::concat(show(tb_reason(s)), "\n"))
      print(Text::concat(doc(s), "\n"))
      rest := more
    }
    Nil => {
      going := false
    }
  }
}
match perform argv() {
  Cons(_, _) => {
    print(Text::concat(tb_time_text(0), "\n"))
    print(Text::concat(tb_time_text(951868799), "\n"))
    print(Text::concat(tb_time_text(1790856000), "\n"))
    print(Text::concat(tb_time_text(253402300799), "\n"))
    print(Text::concat(show_u64(tb_seconds(315360000)), "\n"))
    print(Text::concat(show_u64(tb_seconds(315360001)), "\n"))
  }
  Nil => #()
}
"#
}

#[test]
fn strict_values_match_rust() {
    use totebag::index::strict as s;
    let inputs: Vec<String> = [
        "x".repeat(101),
    ]
    .into_iter()
    .chain([
        "1970-01-01T00:00:00Z",
        "2026-10-01T12:00:00Z",
        "2000-02-29T23:59:59Z",
        "9999-12-31T23:59:59Z",
        "1969-12-31T23:59:59Z",
        "2026-02-29T00:00:00Z",
        "2026-13-01T00:00:00Z",
        "2026-10-01T24:00:00Z",
        "2026-10-01T12:00:60Z",
        "2026-10-01T12:00:00.5Z",
        "2026-10-01T12:00:00+09:00",
        "+026-10-01T12:00:00Z",
        "0123abc",
        "v1.0.0+build",
        "a b",
        "refs/heads/main",
        "refs/tags/v1",
        "https://example.org/x",
        "file:///x",
        "http://example.org/x",
        "local",
        "Bad",
        "a = 1\n",
        "a = 1\nb = \"x\"\n",
        "a = !\n",
        "a = `x`\n",
        "a = 1.5\n",
        "a = -1\n",
        "a = true\n",
        "a = 1\na = 1\n",
        "a.$x = 1\n",
        "a = 18446744073709551616\n",
        "a = [1, 2]\n",
        "b = 1\n",
    ]
    .iter()
    .map(|t| t.to_string()))
    .chain([
        format!("sha256:{}", "ab".repeat(32)),
        format!("sha256:{}", "AB".repeat(32)),
        "x".repeat(257),
        "x".repeat(4097),
    ])
    .collect();
    // A check from `spec` gives its message already written out, under the
    // ID `text`; its own ID is what the text starts with.
    let id = |e: tauto_message::Message| {
        if e.id == "text" {
            e.to_string().split('(').next().unwrap_or("").to_string()
        } else {
            e.id.to_string()
        }
    };
    let show = |r: Result<String, tauto_message::Message>| match r {
        Ok(t) => format!("ok {t}"),
        Err(e) => id(e),
    };
    let show_u64 = |r: Result<u64, tauto_message::Message>| match r {
        Ok(n) => format!("ok {n}"),
        Err(e) => id(e),
    };
    let doc = |t: &str| -> String {
        let d = match s::Doc::parse(t.as_bytes(), "t", 100) {
            Ok(d) => d,
            Err(e) => return id(e),
        };
        let mut f = match d.fields(d.root(), "t") {
            Ok(f) => f,
            Err(e) => return id(e),
        };
        let a = match f.required("a") {
            Ok(n) => show_u64(d.integer(n)),
            Err(e) => id(e),
        };
        match f.finish() {
            Ok(()) => a,
            Err(e) => format!("{a} {}", id(e)),
        }
    };
    let mut rust = String::new();
    for t in &inputs {
        for line in [
            show_u64(s::time(t)),
            show(s::sha256(t).map(|_| t.clone())),
            show(s::package_rev(t)),
            show(s::https_url(t)),
            show(s::branch(t)),
            show(s::alias(t)),
            show(s::reason(t)),
            doc(t),
        ] {
            rust.push_str(&line);
            rust.push('\n');
        }
    }
    for t in [0, 951_868_799, 1_790_856_000, 253_402_300_799] {
        rust.push_str(&s::time_text(t));
        rust.push('\n');
    }
    rust.push_str(&format!("{}\n{}\n", show_u64(s::seconds(315_360_000)), show_u64(s::seconds(315_360_001))));
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-strict-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let totes = root_totes();
    write(
        &base,
        "Tauto.eure",
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            totes.join("totebag-io").display()
        )
        .as_bytes(),
    );
    write(&base, "src/main.taut", entry(&strict_main_source()).as_bytes());
    let out = run_tote_at(&base, &inputs, 4_000_000_000);
    let _ = fs::remove_dir_all(&base);
    assert_eq!(out.error, None, "{}", out.stderr);
    assert_same_dump("totebag strict values", &rust, &out.stdout);
}

/// Reads each argument as `Index.eure` and as `observations.eure` (SHA-1
/// commits), printing the config, or the batch written back, or the error's
/// first message ID.
fn ledger_main_source() -> &'static str {
    r#"import totebag_io::ledger
import totebag_io::strict
import totebag_io::git
import std::builtin::os
import std::text

fn first_word(e: Text): Text {
  match tb_split_once(e, 32) {
    Some(p) => p.fst
    None => e
  }
}

var rest := perform argv()
var going := true
while going {
  match rest {
    Cons(s, more) => {
      match tb_config(Bytes::of_text(s)) {
        Ok(c) => print(tb_cat(["config ", c.name, " ", c.git_object_format, "\n"]))
        Err(e) => print(Text::concat(first_word(e), "\n"))
      }
      match tb_batch(Bytes::of_text(s), "sha1") {
        Ok(b) => print(tb_render_batch(b))
        Err(e) => print(Text::concat(first_word(e), "\n"))
      }
      print("==\n")
      rest := more
    }
    Nil => {
      going := false
    }
  }
}
"#
}

#[test]
fn ledgers_match_rust() {
    use totebag::index::ledger;
    let h2 = format!("sha256:{}", "2".repeat(64));
    let h3 = format!("sha256:{}", "3".repeat(64));
    let rev = "0123456789abcdef0123456789abcdef01234567";
    let sample = format!(
        "format = 1\nkind = \"batch\"\nsequence = 1\nissued_at = \"2026-10-01T12:00:00Z\"\nvalid_until = \"2026-10-02T12:00:00Z\"\n\n\
         @ events[] {{\n  kind = \"observation\"\n  project = \"{h2}\"\n  rev = \"{rev}\"\n  source_sha256 = \"{h3}\"\n  first_seen_at = \"2026-10-01T11:59:00Z\"\n}}\n\
         @ events[] {{\n  kind = \"decision\"\n  project = \"{h2}\"\n  rev = \"{rev}\"\n  verdict = \"accept\"\n  reason = \"この内容を依存として採用する。\"\n}}\n\
         @ events[] {{\n  kind = \"withdrawal\"\n  project = \"{h2}\"\n  rev = \"v1.0\"\n  reason = \"a \\\"bad\\\" one\\nsecond\\tline\\u{{7f}}\\u{{85}}\"\n}}\n\
         @ events[] {{\n  kind = \"index-observation\"\n  index = \"{h3}\"\n  repository = \"https://example.org/bob/index\"\n  ref = \"refs/heads/main\"\n  rev = \"sha1:{rev}\"\n  sha256 = \"{h2}\"\n  first_seen_at = \"2026-10-01T11:00:00Z\"\n}}\n"
    );
    let config = "format = 1\nkind = \"index\"\nname = \"alice\"\nhistory = \"commit-batches\"\ngit_object_format = \"sha1\"\n";
    let mut docs = vec![
        sample.clone(),
        format!("{sample}@ events[] {{\n  kind = \"retirement\"\n  reason = \"closed\"\n}}\n"),
        format!("{sample}@ events[] {{\n  kind = \"retirement\"\n  reason = \"closed\"\n}}\n@ events[] {{\n  kind = \"retirement\"\n  reason = \"again\"\n}}\n"),
        "format = 1\nkind = \"batch\"\nsequence = 0\nissued_at = \"2026-10-01T12:00:00Z\"\nvalid_until = \"2026-10-02T12:00:00Z\"\nevents = []\n".to_string(),
        sample.split("\n\n@").next().unwrap().to_string(),
        config.to_string(),
        config.replace("sha1", "md5"),
        format!("{config}pin = \"x\"\n"),
        config.replace("name = \"alice\"\n", ""),
        config.replace("commit-batches", "other"),
        config.replace("\"alice\"", "\"\""),
        config.replace("format = 1", "format = 2"),
    ];
    for (from, to) in [
        ("format = 1", "format = 2"),
        ("kind = \"batch\"", "kind = \"index\""),
        ("sequence = 1", "sequence = -1"),
        ("valid_until = \"2026-10-02T12:00:00Z\"", "valid_until = \"2026-10-01T12:00:00Z\""),
        ("verdict = \"accept\"", "verdict = \"maybe\""),
        ("kind = \"observation\"", "kind = \"guess\""),
        ("  first_seen_at", "  extra = \"x\"\n  first_seen_at"),
        ("rev = \"0123", "rev = \"01 23"),
        ("source_sha256 = \"sha256:33", "source_sha256 = \"sha256:3"),
        ("first_seen_at = \"2026-10-01T11:59:00Z\"", "first_seen_at = \"2026-10-01T11:59:00+09:00\""),
        ("rev = \"sha1:", "rev = \"sha256:"),
        ("rev = \"sha1:", "rev = \""),
        ("refs/heads/main", "refs/tags/v1"),
        ("https://example.org/bob", "http://example.org/bob"),
        ("  reason = \"この", "  reason = \"\"\n  x = \"この"),
        ("  kind = \"decision\"\n", ""),
    ] {
        let bad = sample.replacen(from, to, 1);
        assert_ne!(bad, sample, "{from}");
        docs.push(bad);
    }
    let first = |e: String| e.split('(').next().unwrap_or("").to_string();
    let rust: String = docs
        .iter()
        .map(|d| {
            let c = match ledger::config(d.as_bytes()) {
                Ok(c) => format!("config {} {}\n", c.name, c.git_object_format),
                Err(e) => format!("{}\n", first(e)),
            };
            let b = match ledger::batch(d.as_bytes(), "sha1") {
                Ok(b) => b.render(),
                Err(e) => format!("{}\n", first(e)),
            };
            format!("{c}{b}==\n")
        })
        .collect();
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-ledger-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let totes = root_totes();
    write(
        &base,
        "Tauto.eure",
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            totes.join("totebag-io").display()
        )
        .as_bytes(),
    );
    write(&base, "src/main.taut", entry(&ledger_main_source()).as_bytes());
    let out = run_tote_at(&base, &docs, 8_000_000_000);
    let _ = fs::remove_dir_all(&base);
    assert_eq!(out.error, None, "{}", out.stderr);
    assert_same_dump("totebag ledgers", &rust, &out.stdout);
}

/// Reads each argument as a trust policy and prints what it says, or the
/// error's first message ID.
fn policy_main_source() -> &'static str {
    r#"import totebag_io::policy
import totebag_io::ledger
import totebag_io::git
import std::builtin::os
import std::text

fn first_word(e: Text): Text {
  match tb_split_once(e, 32) {
    Some(p) => p.fst
    None => e
  }
}

fn trusted(t: TbTrusted): Text {
  tb_cat(["index ", t.alias, " ", t.url, " ", t.reference, " ", t.index, " ", t.pin_rev, " ", t.pin_digest, "\n"])
}

fn names(l: List(TbTrusted)): Text {
  match l {
    Nil => ""
    Cons(t, rest) => tb_cat([" ", t.alias, names(rest)])
  }
}

fn witnesses(l: List(TbWitness)): Text {
  match l {
    Nil => ""
    Cons(w, rest) => match w {
      WitnessLocal => Text::concat(" local", witnesses(rest))
      WitnessRemote(t) => tb_cat([" ", t.alias, witnesses(rest)])
    }
  }
}

fn rule(r: TbRule): Text {
  tb_cat(["  observers", names(r.observers), "\n  witnesses", witnesses(r.witnesses), "\n  limits ", Text::of_u64(r.min_age), " ", Text::of_u64(r.max_checkpoint_lifetime), " ", Text::of_u64(r.max_source_check_age), "\n"])
}

fn policy(p: TbPolicy): Text {
  var out := ""
  var ix := p.indexes
  var going := true
  while going {
    match ix {
      Cons(t, more) => {
        out := Text::concat(out, trusted(t))
        ix := more
      }
      Nil => {
        going := false
      }
    }
  }
  out := tb_cat([out, "defaults\n", rule(p.defaults)])
  var rs := p.rules
  going := true
  while going {
    match rs {
      Cons(r, more) => {
        out := tb_cat([out, "rule ", r.fst, "\n", rule(r.snd)])
        rs := more
      }
      Nil => {
        going := false
      }
    }
  }
  out
}

var rest := perform argv()
var going := true
while going {
  match rest {
    Cons(s, more) => {
      match tb_parse_policy(Bytes::of_text(s)) {
        Ok(p) => print(policy(p))
        Err(e) => print(Text::concat(first_word(e), "\n"))
      }
      print("==\n")
      rest := more
    }
    Nil => {
      going := false
    }
  }
}
"#
}

fn policy_index(alias: &str, n: u8, transport: &str, repository: &str) -> String {
    format!(
        "@ indexes[] {{\n  alias = \"{alias}\"\n  id = \"sha256:{}\"\n  transport = \"{transport}\"\n  repository = \"{repository}\"\n  ref = \"refs/heads/main\"\n  pin_rev = \"sha1:{}\"\n  pin_sha256 = \"sha256:{}\"\n}}\n",
        format!("{n:02x}").repeat(32),
        "a".repeat(40),
        format!("{n:02x}").repeat(32),
    )
}

const POLICY_RULE: &str = "  require = \"all\"\n  observers = [\"alice\", \"bob\"]\n  age_witnesses = [\"carol\"]\n  min_age_seconds = 604800\n  max_checkpoint_lifetime_seconds = 86400\n  max_source_check_age_seconds = 3600\n";

fn sample_policy() -> String {
    format!(
        "format = 1\nkind = \"policy\"\ntrack = \"dependency-closure\"\n\n{}{}{}{}\n@ defaults {{\n{POLICY_RULE}}}\n\n@ rules[] {{\n  project = \"sha256:{}\"\n{}}}\n",
        policy_index("alice", 1, "https", "https://example.org/alice/index"),
        policy_index("bob", 2, "https", "https://example.org/bob/index"),
        policy_index("carol", 3, "https", "https://example.org/carol/index"),
        policy_index("me", 4, "local-owned", "file:///home/me/index"),
        "77".repeat(32),
        POLICY_RULE
            .replace("[\"alice\", \"bob\"]", "[\"me\"]")
            .replace("[\"carol\"]", "[\"local\", \"carol\"]"),
    )
}

#[test]
fn policies_match_rust() {
    use totebag::index::policy;
    let text = sample_policy();
    let mut docs = vec![text.clone()];
    for (from, to) in [
        ("format = 1", "format = 2"),
        ("kind = \"policy\"", "kind = \"index\""),
        ("track = \"dependency-closure\"", "track = \"all\""),
        ("require = \"all\"", "require = \"any\""),
        ("[\"carol\"]", "[\"alice\"]"),
        ("[\"carol\"]", "[\"me\"]"),
        ("[\"carol\"]", "[]"),
        ("[\"carol\"]", "[1]"),
        ("[\"alice\", \"bob\"]", "[\"alice\", \"alice\"]"),
        ("[\"alice\", \"bob\"]", "[\"dave\"]"),
        ("[\"alice\", \"bob\"]", "[\"local\"]"),
        ("alias = \"bob\"", "alias = \"alice\""),
        ("alias = \"bob\"", "alias = \"local\""),
        ("alias = \"bob\"", "alias = \"Bob\""),
        ("id = \"sha256:02", "id = \"sha256:01"),
        ("transport = \"https\"", "transport = \"ssh\""),
        ("https://example.org/alice/index", "http://example.org/alice/index"),
        ("file:///home/me/index", "https://example.org/me"),
        ("file:///home/me/index", "file://home/me/index"),
        ("refs/heads/main", "refs/tags/main"),
        ("pin_rev = \"sha1:", "pin_rev = \"sha2:"),
        ("max_source_check_age_seconds = 3600", "max_source_check_age_seconds = 0"),
        ("min_age_seconds = 604800", "min_age_seconds = 999999999999"),
        ("  min_age_seconds", "  extra = 1\n  min_age_seconds"),
        ("https://example.org/carol/index", "https://example.org/alice/index"),
        ("\n@ rules[] {", "\nother = 1\n@ rules[] {"),
        ("@ defaults {", "@ nothing {"),
    ] {
        let bad = text.replacen(from, to, 1);
        assert_ne!(bad, text, "{from}");
        docs.push(bad);
    }
    let last = text.rfind("  max_source_check_age_seconds = 3600\n").unwrap();
    let mut partial = text.clone();
    partial.replace_range(last..last + "  max_source_check_age_seconds = 3600\n".len(), "");
    docs.push(partial);
    let twice = text.replace(
        "\n@ rules[] {",
        &format!("\n@ rules[] {{\n  project = \"sha256:{}\"\n{POLICY_RULE}}}\n@ rules[] {{", "77".repeat(32)),
    );
    docs.push(twice);
    docs.push(text.split("\n@ rules[]").next().unwrap().to_string());
    let first = |e: String| e.split('(').next().unwrap_or("").to_string();
    let hex = |b: &[u8; 32]| format!("sha256:{}", totebag::index::strict::hex_of(b));
    let trusted = |t: &policy::Trusted| {
        format!(
            "index {} {} {} {} {} {}\n",
            t.alias,
            t.url,
            t.reference,
            hex(&t.index),
            t.pin.rev,
            hex(&t.pin.digest)
        )
    };
    let rule = |r: &policy::Rule| {
        let obs: String = r.observers.iter().map(|t| format!(" {}", t.alias)).collect();
        let wit: String = r
            .witnesses
            .iter()
            .map(|w| match w {
                policy::Witness::Local => " local".to_string(),
                policy::Witness::Remote(t) => format!(" {}", t.alias),
            })
            .collect();
        format!(
            "  observers{obs}\n  witnesses{wit}\n  limits {} {} {}\n",
            r.limits.min_age, r.limits.max_checkpoint_lifetime, r.limits.max_source_check_age
        )
    };
    let rust: String = docs
        .iter()
        .map(|d| {
            let body = match policy::parse(d.as_bytes(), "Trust.eure") {
                Ok(p) => {
                    let mut out: String = p.indexes.iter().map(trusted).collect();
                    out.push_str("defaults\n");
                    out.push_str(&rule(&p.defaults));
                    for (project, r) in &p.rules {
                        out.push_str(&format!("rule {}\n", hex(project)));
                        out.push_str(&rule(r));
                    }
                    out
                }
                Err(e) => format!("{}\n", first(e)),
            };
            format!("{body}==\n")
        })
        .collect();
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-policy-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let totes = root_totes();
    write(
        &base,
        "Tauto.eure",
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            totes.join("totebag-io").display()
        )
        .as_bytes(),
    );
    write(&base, "src/main.taut", entry(&policy_main_source()).as_bytes());
    let out = run_tote_at(&base, &docs, 8_000_000_000);
    let _ = fs::remove_dir_all(&base);
    assert_eq!(out.error, None, "{}", out.stderr);
    assert_same_dump("totebag policies", &rust, &out.stdout);
}

/// Reads each argument as `state.eure`, notes a receipt in it, and writes it
/// back, or prints the error's first message ID.
fn state_main_source() -> &'static str {
    r#"import totebag_io::state
import totebag_io::ledger
import totebag_io::git
import std::builtin::os
import std::text

fn first_word(e: Text): Text {
  match tb_split_once(e, 32) {
    Some(p) => p.fst
    None => e
  }
}

var rest := perform argv()
var going := true
while going {
  match rest {
    Cons(s, more) => {
      match tb_parse_state(Bytes::of_text(s)) {
        Ok(st) => {
          print(tb_render_state(st))
          let p := TbPoint { rev: "sha1:9999999999999999999999999999999999999999", digest: "sha256:9999999999999999999999999999999999999999999999999999999999999999" }
          let once := tb_receive(st, "sha256:0101010101010101010101010101010101010101010101010101010101010101", "https://example.org/alice/index", "refs/heads/main", p, 5)
          let twice := tb_receive(once, "sha256:0101010101010101010101010101010101010101010101010101010101010101", "https://example.org/alice/index", "refs/heads/main", p, 6)
          print(tb_render_state(twice))
        }
        Err(e) => print(Text::concat(first_word(e), "\n"))
      }
      print("==\n")
      rest := more
    }
    Nil => {
      going := false
    }
  }
}
"#
}

#[test]
fn states_match_rust() {
    use totebag::index::state::{self, Check, Ledger, Point, Receipt, State};
    use totebag::spec::Rev;
    let point = |c: char| Point {
        rev: Rev::from_git(&c.to_string().repeat(40)).unwrap(),
        digest: [c as u8; 32],
    };
    let sample = State {
        evaluated_at: 1_790_856_000,
        ledgers: vec![
            Ledger {
                index: [1; 32],
                url: "https://example.org/alice/index".into(),
                reference: "refs/heads/main".into(),
                pin: point('a'),
                prefix: point('b'),
                frozen: None,
                checked: Some(Check { head: point('b'), at: 1_790_855_940 }),
            },
            Ledger {
                index: [2; 32],
                url: "file:///home/me/index".into(),
                reference: "refs/heads/main".into(),
                pin: point('c'),
                prefix: point('c'),
                frozen: Some("the history at dddddddd is not \"an extension\"\n\u{1}".into()),
                checked: None,
            },
        ],
        receipts: vec![Receipt {
            index: [1; 32],
            url: "https://example.org/alice/index".into(),
            reference: "refs/heads/main".into(),
            point: point('b'),
            first_seen_at: 1_790_852_400,
        }],
    }
    .render();
    let mut docs = vec![sample.clone(), State::default().render()];
    for (from, to) in [
        ("format = 1", "format = 2"),
        ("kind = \"index-state\"", "kind = \"state\""),
        ("evaluated_at = \"2026", "evaluated_at = \"1926"),
        ("pin = \"sha1:", "pin = \"sha2:"),
        ("  prefix_digest", "  extra = 1\n  prefix_digest"),
        ("  first_seen_at", "  extra = 1\n  first_seen_at"),
        ("index = \"sha256:0202", "index = \"sha256:0101"),
        ("refs/heads/main", "refs/tags/v1"),
        ("https://example.org/alice/index", "http://user@example.org/alice/index"),
        ("  checked_at = ", "  late = "),
        ("  checked_digest", "  checked_digest_x"),
        ("frozen = \"", "frozen = `"),
        ("receipts[] {", "receipts[] {\n  x = 1"),
    ] {
        let bad = sample.replacen(from, to, 1);
        assert_ne!(bad, sample, "{from}");
        docs.push(bad);
    }
    docs.push(sample.replacen("frozen = \"the history at dddddddd is not \\\"an extension\\\"\\n\\u{1}\"", "frozen = 1", 1));
    let first = |e: String| e.split('(').next().unwrap_or("").to_string();
    let rust: String = docs
        .iter()
        .map(|d| {
            let body = match state::parse(d.as_bytes()) {
                Ok(mut s) => {
                    let once = s.render();
                    let p = point('9');
                    let p = Point { rev: p.rev, digest: [0x99; 32] };
                    s.receive([1; 32], "https://example.org/alice/index", "refs/heads/main", p.clone(), 5);
                    s.receive([1; 32], "https://example.org/alice/index", "refs/heads/main", p, 6);
                    format!("{once}{}", s.render())
                }
                Err(e) => format!("{}\n", first(e)),
            };
            format!("{body}==\n")
        })
        .collect();
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-state-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let totes = root_totes();
    write(
        &base,
        "Tauto.eure",
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            totes.join("totebag-io").display()
        )
        .as_bytes(),
    );
    write(&base, "src/main.taut", entry(&state_main_source()).as_bytes());
    let out = run_tote_at(&base, &docs, 8_000_000_000);
    let _ = fs::remove_dir_all(&base);
    assert_eq!(out.error, None, "{}", out.stderr);
    assert_same_dump("totebag states", &rust, &out.stdout);
}

/// Reads the first argument as a project's trust policy and each other as a
/// user's policy, and prints the project's policy strengthened by it, or the
/// error's first message ID.
fn user_main_source() -> String {
    let helpers = policy_main_source().split("var rest").next().unwrap();
    format!(
        "import totebag_io::user\n{helpers}{}",
        r#"match perform argv() {
  Cons(project, users) => match tb_parse_policy(Bytes::of_text(project)) {
    Ok(p) => {
      var rest := users
      var going := true
      while going {
        match rest {
          Cons(s, more) => {
            match tb_parse_user(Bytes::of_text(s)) {
              Ok(u) => match tb_strengthen(u, p) {
                Ok(q) => print(policy(q))
                Err(e) => print(Text::concat(first_word(e), "\n"))
              }
              Err(e) => print(Text::concat(first_word(e), "\n"))
            }
            print("==\n")
            rest := more
          }
          Nil => {
            going := false
          }
        }
      }
    }
    Err(e) => print(e)
  }
  Nil => print("usage\n")
}
"#
    )
}

#[test]
fn user_policies_match_rust() {
    use totebag::index::{policy, user};
    let project = sample_policy();
    let head = "format = 1\nkind = \"user-policy\"\ntrack = \"dependency-closure\"\n\n";
    let req = "@ require {\n  observers = [\"dave\"]\n  age_witnesses = [\"local\"]\n  min_age_seconds = 1209600\n  max_checkpoint_lifetime_seconds = 3600\n  max_source_check_age_seconds = 600000\n}\n";
    let dave = policy_index("dave", 5, "https", "https://example.org/dave/index");
    let mut users = vec![
        head.to_string(),
        format!("{head}{dave}{req}"),
        format!("{head}{dave}@ require {{\n  observers = [\"dave\"]\n}}\n"),
        format!("{head}@ require {{\n  min_age_seconds = 0\n}}\n"),
        format!("{head}@ require {{\n  min_age_seconds = 1\n  max_source_check_age_seconds = 10\n}}\n"),
        format!("{head}{}@ require {{\n  observers = [\"alice\"]\n  age_witnesses = [\"carol\"]\n}}\n", policy_index("alice", 1, "https", "https://example.org/alice/index")),
        format!("{head}{}", policy_index("alice", 1, "https", "https://example.org/other/index")),
        format!("{head}{}", policy_index("alice", 9, "https", "https://example.org/x/index")),
        format!("{head}{}@ require {{\n  age_witnesses = [\"zed\"]\n}}\n", policy_index("zed", 1, "https", "https://example.org/alice/index")),
        format!("{head}{}@ require {{\n  age_witnesses = [\"zed\"]\n}}\n", policy_index("zed", 8, "https", "https://example.org/alice/index")),
        format!("{head}{}@ require {{\n  observers = [\"zed\"]\n}}\n", policy_index("zed", 8, "https", "https://example.org/carol/index")),
        format!("{head}{dave}@ require {{\n  observers = [\"nobody\"]\n}}\n"),
        format!("{head}{dave}@ require {{\n  observers = []\n}}\n"),
        format!("{head}{dave}@ require {{\n  observers = [\"local\"]\n}}\n"),
        format!("{head}@ require {{\n  max_checkpoint_lifetime_seconds = 0\n}}\n"),
        format!("{head}@ require {{\n  extra = 1\n}}\n"),
        format!("{head}extra = 1\n"),
        head.replace("user-policy", "policy"),
        head.replace("format = 1", "format = 3"),
    ];
    users.push(format!("{head}{}", policy_index("me", 6, "local-owned", "file:///home/u/index")) + "@ require {\n  age_witnesses = [\"me\"]\n}\n");
    let first = |e: String| e.split('(').next().unwrap_or("").to_string();
    let hex = |b: &[u8; 32]| format!("sha256:{}", totebag::index::strict::hex_of(b));
    let trusted = |t: &policy::Trusted| {
        format!("index {} {} {} {} {} {}\n", t.alias, t.url, t.reference, hex(&t.index), t.pin.rev, hex(&t.pin.digest))
    };
    let rule = |r: &policy::Rule| {
        let obs: String = r.observers.iter().map(|t| format!(" {}", t.alias)).collect();
        let wit: String = r
            .witnesses
            .iter()
            .map(|w| match w {
                policy::Witness::Local => " local".to_string(),
                policy::Witness::Remote(t) => format!(" {}", t.alias),
            })
            .collect();
        format!(
            "  observers{obs}\n  witnesses{wit}\n  limits {} {} {}\n",
            r.limits.min_age, r.limits.max_checkpoint_lifetime, r.limits.max_source_check_age
        )
    };
    let p = policy::parse(project.as_bytes(), "Trust.eure").unwrap();
    let rust: String = users
        .iter()
        .map(|u| {
            let body = match user::parse(u.as_bytes(), "trust.eure").and_then(|u| u.strengthen(&p)) {
                Ok(q) => {
                    let mut out: String = q.indexes.iter().map(trusted).collect();
                    out.push_str("defaults\n");
                    out.push_str(&rule(&q.defaults));
                    for (project, r) in &q.rules {
                        out.push_str(&format!("rule {}\n", hex(project)));
                        out.push_str(&rule(r));
                    }
                    out
                }
                Err(e) => format!("{}\n", first(e)),
            };
            format!("{body}==\n")
        })
        .collect();
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-user-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let totes = root_totes();
    write(
        &base,
        "Tauto.eure",
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            totes.join("totebag-io").display()
        )
        .as_bytes(),
    );
    write(&base, "src/main.taut", entry(&user_main_source()).as_bytes());
    let mut args = vec![project];
    args.extend(users);
    let out = run_tote_at(&base, &args, 8_000_000_000);
    let _ = fs::remove_dir_all(&base);
    assert_eq!(out.error, None, "{}", out.stderr);
    assert_same_dump("totebag user policies", &rust, &out.stdout);
}

/// Fetches each branch named after the first two arguments (the index's URL
/// and the mirror) with its history, and prints each checkpoint of it, or
/// the error's first message ID.
fn history_main_source() -> &'static str {
    r#"import totebag_io::checkpoint
import totebag_io::ledger
import totebag_io::git
import std::builtin::os
import std::text

fn first_word(e: Text): Text {
  match tb_split_once(e, 32) {
    Some(p) => p.fst
    None => e
  }
}

fn checkpoints(l: List(TbCheckpoint)): Text {
  match l {
    Nil => ""
    Cons(c, rest) => tb_cat([c.rev, " ", c.digest, "\n", tb_render_batch(c.batch), checkpoints(rest)])
  }
}

match perform argv() {
  Cons(url, Cons(mirror, branches)) => match tb_mirror_open(mirror, "sha1") {
    Ok(dir) => {
      var rest := branches
      var going := true
      while going {
        match rest {
          Cons(b, more) => {
            match tb_fetch_history(dir, url, b) {
              Ok(head) => match tb_history(dir, head) {
                Ok(h) => print(tb_cat(["id ", tb_history_id(h), "\nconfig ", tb_config_id(h), " ", h.config.name, "\n", checkpoints(h.checkpoints)]))
                Err(e) => print(Text::concat(first_word(e), "\n"))
              }
              Err(e) => print(Text::concat(first_word(e), "\n"))
            }
            print("==\n")
            rest := more
          }
          Nil => {
            going := false
          }
        }
      }
    }
    Err(e) => print(e)
  }
  _ => print("usage\n")
}
"#
}

#[test]
fn index_histories_match_rust() {
    use totebag::index::{checkpoint, strict::hex_of};
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-history-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let repo = base.join("index");
    fs::create_dir_all(&repo).unwrap();
    let git = |args: &[&str]| {
        let out = std::process::Command::new("git")
            .arg("-C")
            .arg(&repo)
            .args(args)
            .env("GIT_AUTHOR_NAME", "t")
            .env("GIT_AUTHOR_EMAIL", "t@example.com")
            .env("GIT_COMMITTER_NAME", "t")
            .env("GIT_COMMITTER_EMAIL", "t@example.com")
            .env("GIT_AUTHOR_DATE", "2026-10-01T12:00:00Z")
            .env("GIT_COMMITTER_DATE", "2026-10-01T12:00:00Z")
            .output()
            .unwrap();
        assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    };
    let config = "format = 1\nkind = \"index\"\nname = \"alice\"\nhistory = \"commit-batches\"\ngit_object_format = \"sha1\"\n";
    let batch = |seq: u32, events: &str| {
        format!(
            "format = 1\nkind = \"batch\"\nsequence = {seq}\nissued_at = \"2026-10-01T12:00:00Z\"\nvalid_until = \"2026-10-02T12:00:00Z\"\n{events}"
        )
    };
    let event = format!(
        "\n@ events[] {{\n  kind = \"withdrawal\"\n  project = \"sha256:{}\"\n  rev = \"v1\"\n  reason = \"gone\"\n}}\n",
        "2".repeat(64)
    );
    let commit = |files: &[(&str, &str)], msg: &str| {
        for (p, t) in files {
            write(&repo, p, t.as_bytes());
        }
        git(&["add", "-A"]);
        git(&["commit", "--quiet", "--allow-empty", "-m", msg]);
    };
    git(&["init", "--quiet", "--initial-branch=main"]);
    commit(&[("Index.eure", config), ("observations.eure", &batch(0, "events = []\n"))], "root");
    git(&["branch", "nonempty-root-base"]);
    commit(&[("observations.eure", &batch(1, &event))], "one");
    commit(&[("observations.eure", &batch(2, "events = []\n"))], "two");
    git(&["checkout", "--quiet", "-b", "changed"]);
    commit(&[("Index.eure", &config.replace("alice", "bob"))], "changed");
    git(&["checkout", "--quiet", "-b", "bad-batch", "main"]);
    commit(&[("observations.eure", "format = 2\n")], "bad");
    git(&["checkout", "--quiet", "-b", "no-batch", "main"]);
    git(&["rm", "--quiet", "observations.eure"]);
    git(&["commit", "--quiet", "-m", "gone"]);
    git(&["checkout", "--quiet", "-b", "merged", "main"]);
    git(&["merge", "--quiet", "--no-ff", "-m", "merge", "changed"]);
    git(&["checkout", "--quiet", "--orphan", "full-root"]);
    commit(&[("Index.eure", config), ("observations.eure", &batch(0, &event))], "root");
    git(&["checkout", "--quiet", "--orphan", "sha256-config"]);
    commit(&[("Index.eure", &config.replace("\"sha1\"", "\"sha256\"")), ("observations.eure", &batch(0, "events = []\n"))], "root");
    git(&["checkout", "--quiet", "main"]);
    let branches = ["main", "changed", "bad-batch", "no-batch", "merged", "full-root", "sha256-config", "nonempty-root-base"];
    let url = format!("file://{}", repo.display());

    let first = |e: String| e.split('(').next().unwrap_or("").to_string();
    let m = totebag::git::Mirror::open(base.join("rust-mirror"), "sha1").unwrap();
    let mut rust = String::new();
    for b in branches {
        let reference = format!("refs/heads/{b}");
        let body = match m
            .fetch_history(&url, &reference)
            .and_then(|head| checkpoint::history(&m, &head))
        {
            Ok(h) => {
                let mut out = format!(
                    "id sha256:{}\nconfig sha256:{} {}\n",
                    hex_of(&h.id()),
                    hex_of(&h.config_id()),
                    h.config.name
                );
                for c in &h.checkpoints {
                    out.push_str(&format!("{} sha256:{}\n{}", c.rev, hex_of(&c.digest), c.batch.render()));
                }
                out
            }
            Err(e) => format!("{}\n", first(e)),
        };
        rust.push_str(&body);
        rust.push_str("==\n");
    }
    write(
        &base,
        "probe/Tauto.eure",
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            root_totes().join("totebag-io").display()
        )
        .as_bytes(),
    );
    write(&base, "probe/src/main.taut", entry(&history_main_source()).as_bytes());
    let mut args = vec![url.clone(), base.join("tote-mirror").to_string_lossy().into_owned()];
    args.extend(branches.iter().map(|b| format!("refs/heads/{b}")));
    let out = run_tote_at_with(&base.join("probe"), &args, 8_000_000_000, &["git"]);
    let _ = fs::remove_dir_all(&base);
    assert_eq!(out.error, None, "{}", out.stderr);
    assert!(rust.contains("id sha256:"), "{rust}");
    assert_same_dump("totebag index histories", &rust, &out.stdout);
}

/// Syncs the index the policy (the second argument) trusts, with its mirror
/// under the state directory in the first, from the state written in the
/// third (or none), at the times and for the keys that follow: `sync <now>` or
/// `evaluate <now> <project> <rev> <source>`. Prints what each step did and
/// the state after it.
fn engine_main_source() -> &'static str {
    r#"import totebag_io::engine
import totebag_io::state
import totebag_io::policy
import totebag_io::ledger
import totebag_io::git
import std::builtin::os
import std::text

fn first_word(e: Text): Text {
  match tb_split_once(e, 32) {
    Some(p) => p.fst
    None => e
  }
}

fn num(t: Text): u64 {
  match U64::of_text(t) {
    Some(n) => n
    None => 0
  }
}

match perform argv() {
  Cons(dir, Cons(policy_text, Cons(state_text, steps))) => match tb_parse_policy(Bytes::of_text(policy_text)) {
    Ok(p) => {
      var state := if state_text == "" {
        tb_empty_state()
      } else {
        match tb_parse_state(Bytes::of_text(state_text)) {
          Ok(s) => s
          Err(e) => {
            print(e)
            perform exit(1)
          }
        }
      }
      let t := match p.indexes {
        Cons(t, _) => t
        Nil => {
          perform exit(1)
        }
      }
      var rest := steps
      var going := true
      while going {
        match rest {
          Cons(s, more) => {
            let words := tb_split(Bytes::of_text(s), 32)
            match words {
              Cons("sync", Cons(now, Nil)) => match tb_sync(dir, state, t, num(now)) {
                Ok(r) => {
                  state := r.fst
                  match r.snd {
                    SyncOpen(head, taken) => print(tb_cat(["open ", head.rev, " ", head.digest, " ", Text::of_nat(taken), "\n"]))
                    SyncFrozen(prefix, why) => print(tb_cat(["frozen ", prefix.rev, " ", prefix.digest, " ", why, "\n"]))
                  }
                }
                Err(e) => print(Text::concat(first_word(e), "\n"))
              }
              Cons("evaluate", Cons(now, Cons(project, Cons(rev, Cons(source, Nil))))) => match tb_evaluate(dir, state, tb_rule_for(p, project), num(now), TbKey { project: project, rev: rev }, source) {
                Ok(r) => {
                  state := r.snd
                  print(if r.fst { "adopt\n" } else { "refuse\n" })
                }
                Err(e) => print(Text::concat(first_word(e), "\n"))
              }
              _ => print("bad step\n")
            }
            print(tb_render_state(state))
            print("==\n")
            rest := more
          }
          Nil => {
            going := false
          }
        }
      }
    }
    Err(e) => print(e)
  }
  _ => print("usage\n")
}
"#
}

#[test]
fn index_syncs_and_evaluations_match_rust() {
    use totebag::index::{checkpoint, ledger::Key, policy, state::Store, strict::hex_of};
    use totebag_index::engine;
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-engine-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    let repo = base.join("index");
    fs::create_dir_all(&repo).unwrap();
    let git = |args: &[&str]| {
        let out = std::process::Command::new("git")
            .arg("-C")
            .arg(&repo)
            .args(args)
            .env("GIT_AUTHOR_NAME", "t")
            .env("GIT_AUTHOR_EMAIL", "t@example.com")
            .env("GIT_COMMITTER_NAME", "t")
            .env("GIT_COMMITTER_EMAIL", "t@example.com")
            .env("GIT_AUTHOR_DATE", "2026-10-01T12:00:00Z")
            .env("GIT_COMMITTER_DATE", "2026-10-01T12:00:00Z")
            .output()
            .unwrap();
        assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    };
    let config = "format = 1\nkind = \"index\"\nname = \"alice\"\nhistory = \"commit-batches\"\ngit_object_format = \"sha1\"\n";
    let batch = |seq: u32, events: &str| {
        format!(
            "format = 1\nkind = \"batch\"\nsequence = {seq}\nissued_at = \"2026-10-01T12:00:00Z\"\nvalid_until = \"2026-10-02T12:00:00Z\"\n{events}"
        )
    };
    let project = format!("sha256:{}", "2".repeat(64));
    let source = format!("sha256:{}", "3".repeat(64));
    let other = format!("sha256:{}", "4".repeat(64));
    let observe = format!(
        "\n@ events[] {{\n  kind = \"observation\"\n  project = \"{project}\"\n  rev = \"v1\"\n  source_sha256 = \"{source}\"\n  first_seen_at = \"2026-10-01T11:00:00Z\"\n}}\n"
    );
    let decide = format!(
        "\n@ events[] {{\n  kind = \"decision\"\n  project = \"{project}\"\n  rev = \"v1\"\n  verdict = \"accept\"\n  reason = \"good\"\n}}\n"
    );
    let commit = |files: &[(&str, &str)], msg: &str| {
        for (p, t) in files {
            write(&repo, p, t.as_bytes());
        }
        git(&["add", "-A"]);
        git(&["commit", "--quiet", "--allow-empty", "-m", msg]);
    };
    git(&["init", "--quiet", "--initial-branch=main"]);
    commit(&[("Index.eure", config), ("observations.eure", &batch(0, "events = []\n"))], "root");
    let url = format!("file://{}", repo.display());
    let probe = totebag::git::Mirror::open(base.join("probe-mirror"), "sha1").unwrap();
    let head = probe.fetch_history(&url, "refs/heads/main").unwrap();
    let h = checkpoint::history(&probe, &head).unwrap();
    let id = format!("sha256:{}", hex_of(&h.id()));
    let trust = format!(
        "format = 1\nkind = \"policy\"\ntrack = \"dependency-closure\"\n\n@ indexes[] {{\n  alias = \"alice\"\n  id = \"{id}\"\n  transport = \"local-owned\"\n  repository = \"{url}\"\n  ref = \"refs/heads/main\"\n  pin_rev = \"{}\"\n  pin_sha256 = \"{id}\"\n}}\n\n@ defaults {{\n  require = \"all\"\n  observers = [\"alice\"]\n  age_witnesses = [\"local\"]\n  min_age_seconds = 0\n  max_checkpoint_lifetime_seconds = 86400\n  max_source_check_age_seconds = 3600\n}}\n",
        h.checkpoints[0].rev
    );
    let p = policy::parse(trust.as_bytes(), "Trust.eure").unwrap();
    let t = p.indexes[0].clone();
    let t0 = 1_790_856_000u64;
    let rust_store = Store::at(base.join("rust-state"));
    let mut rust = String::new();
    let mut held = rust_store.hold().unwrap();
    // The steps, each run by Rust here and by the tote below, with the
    // index's history changed between some of them.
    let mut steps: Vec<String> = Vec::new();
    let step = |s: &str, held: &mut totebag::index::state::Held, rust: &mut String, steps: &mut Vec<String>| {
        steps.push(s.to_string());
        let w: Vec<&str> = s.split(' ').collect();
        let line = match w.as_slice() {
            ["sync", now] => match engine::sync(&rust_store, held, &t, now.parse().unwrap()) {
                Ok(engine::Synced::Open { head, taken }) => {
                    format!("open {} sha256:{} {taken}\n", head.rev, hex_of(&head.digest))
                }
                Ok(engine::Synced::Frozen { prefix, why }) => {
                    format!("frozen {} sha256:{} {why}\n", prefix.rev, hex_of(&prefix.digest))
                }
                Err(e) => format!("{}\n", e.split('(').next().unwrap_or("")),
            },
            ["evaluate", now, project, rev, source] => {
                let pj = totebag::index::strict::sha256(project).unwrap();
                let key = Key { project: pj, rev: rev.to_string() };
                let src = totebag::index::strict::sha256(source).unwrap();
                match engine::evaluate(&rust_store, held, p.rule(&pj), now.parse().unwrap(), &key, &src) {
                    Ok(true) => "adopt\n".to_string(),
                    Ok(false) => "refuse\n".to_string(),
                    Err(e) => format!("{}\n", e.split('(').next().unwrap_or("")),
                }
            }
            _ => unreachable!(),
        };
        rust.push_str(&line);
        rust.push_str(&held.state.render());
        rust.push_str("==\n");
    };
    let mut log: Vec<(usize, Vec<(String, String)>)> = Vec::new();
    step(&format!("sync {}", t0 + 10), &mut held, &mut rust, &mut steps);
    step(&format!("evaluate {} {project} v1 {source}", t0 + 20), &mut held, &mut rust, &mut steps);
    log.push((steps.len(), vec![("observations.eure".into(), batch(1, &observe))]));
    commit(&[("observations.eure", &batch(1, &observe))], "one");
    step(&format!("sync {}", t0 + 30), &mut held, &mut rust, &mut steps);
    step(&format!("evaluate {} {project} v1 {source}", t0 + 40), &mut held, &mut rust, &mut steps);
    log.push((steps.len(), vec![("observations.eure".into(), batch(2, &decide))]));
    commit(&[("observations.eure", &batch(2, &decide))], "two");
    step(&format!("sync {}", t0 + 50), &mut held, &mut rust, &mut steps);
    step(&format!("evaluate {} {project} v1 {source}", t0 + 60), &mut held, &mut rust, &mut steps);
    step(&format!("evaluate {} {project} v1 {other}", t0 + 70), &mut held, &mut rust, &mut steps);
    step(&format!("evaluate {} {project} v2 {source}", t0 + 80), &mut held, &mut rust, &mut steps);
    step(&format!("evaluate {} {project} v1 {source}", t0 + 5), &mut held, &mut rust, &mut steps);
    step(&format!("evaluate {} {project} v1 {source}", t0 + 7200), &mut held, &mut rust, &mut steps);
    log.push((steps.len(), vec![("observations.eure".into(), batch(9, "events = []\n"))]));
    commit(&[("observations.eure", &batch(9, "events = []\n"))], "skip");
    step(&format!("sync {}", t0 + 7300), &mut held, &mut rust, &mut steps);
    step(&format!("sync {}", t0 + 7400), &mut held, &mut rust, &mut steps);
    step(&format!("evaluate {} {project} v1 {source}", t0 + 7500), &mut held, &mut rust, &mut steps);
    drop(held);
    assert!(rust.contains("adopt\n"), "{rust}");

    // The tote, on a copy of the index rebuilt the same way, step by step.
    git(&["checkout", "--quiet", "--detach"]);
    let full = String::from_utf8(
        std::process::Command::new("git")
            .arg("-C")
            .arg(&repo)
            .args(["rev-list", "--reverse", "main"])
            .output()
            .unwrap()
            .stdout,
    )
    .unwrap();
    let commits: Vec<&str> = full.lines().collect();
    write(
        &base,
        "probe/Tauto.eure",
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            root_totes().join("totebag-io").display()
        )
        .as_bytes(),
    );
    write(&base, "probe/src/main.taut", entry(&engine_main_source()).as_bytes());
    // The tote runs the steps in one go, so the index's history is moved
    // between them by running it once per stretch of steps, each time with
    // the state the last run printed.
    let mut tote = String::new();
    let mut start = 0;
    let mut stretches: Vec<usize> = log.iter().map(|(n, _)| *n).collect();
    stretches.push(steps.len());
    let tote_dir = base.join("tote-state").to_string_lossy().into_owned();
    let mut state_text = String::new();
    for (i, end) in stretches.iter().enumerate() {
        git(&["update-ref", "refs/heads/main", commits[i]]);
        let mut args = vec![tote_dir.clone(), trust.clone(), state_text.clone()];
        args.extend(steps[start..*end].iter().cloned());
        let out = run_tote_at_with(&base.join("probe"), &args, 20_000_000_000, &["git"]);
        assert_eq!(out.error, None, "{}", out.stderr);
        tote.push_str(&out.stdout);
        if let Some(last) = out.stdout.rsplit("==\n").nth(1) {
            state_text = last.split_once('\n').map(|(_, s)| s.to_string()).unwrap_or_default();
        }
        start = *end;
    }
    let _ = fs::remove_dir_all(&base);
    assert_same_dump("totebag index engine", &rust, &tote);
}

/// Holds the state in the directory it is given, notes a receipt in it,
/// saves it and lets go.
fn hold_main_source() -> &'static str {
    r#"import totebag_io::state
import std::builtin::os
import std::text

match perform argv() {
  Cons(dir, Nil) => match tb_hold(dir) {
    Ok(h) => {
      let p := TbPoint { rev: "sha1:9999999999999999999999999999999999999999", digest: "sha256:9999999999999999999999999999999999999999999999999999999999999999" }
      let s := tb_receive(h.state, "sha256:0101010101010101010101010101010101010101010101010101010101010101", "https://example.org/alice/index", "refs/heads/main", p, 5)
      match tb_save(dir, s) {
        Ok(_) => print("saved\n")
        Err(e) => print(Text::concat(e, "\n"))
      }
      tb_let_go(h)
    }
    Err(e) => print(Text::concat(e, "\n"))
  }
  _ => print("usage\n")
}
"#
}

#[test]
fn the_state_is_held_under_the_lock_rust_takes() {
    use totebag::index::state::Store;
    let base = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-totebag-hold-{}", std::process::id()));
    let _ = fs::remove_dir_all(&base);
    write(
        &base,
        "probe/Tauto.eure",
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  totebag-io {{ path = \"{}\" }}\n}}\n",
            root_totes().join("totebag-io").display()
        )
        .as_bytes(),
    );
    write(&base, "probe/src/main.taut", entry(&hold_main_source()).as_bytes());
    let dir = base.join("state");
    let store = Store::at(dir.clone());
    let held = store.hold().unwrap();
    // While Rust holds the lock, the tote waits for it.
    let (probe, arg) = (base.join("probe"), dir.to_string_lossy().into_owned());
    let tote = std::thread::spawn(move || run_tote_at(&probe, &[arg], 4_000_000_000));
    std::thread::sleep(std::time::Duration::from_secs(3));
    assert!(!tote.is_finished(), "the tote went on while Rust held the lock");
    assert!(!dir.join("state.eure").exists());
    drop(held);
    let out = tote.join().unwrap();
    assert_eq!(out.error, None, "{}", out.stderr);
    assert_eq!(out.stdout, "saved\n");
    // What the tote saved, Rust reads, and the tote has let go of the lock.
    let again = store.hold().unwrap();
    assert_eq!(again.state.receipts.len(), 1);
    assert_eq!(again.state.receipts[0].first_seen_at, 5);
    drop(again);
    let _ = fs::remove_dir_all(&base);
}
