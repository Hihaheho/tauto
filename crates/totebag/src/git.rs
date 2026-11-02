//! Fetching from Git with the `git` command: one bare repository per URL
//! under the cache, fetched into without a working tree, and read with
//! `ls-tree` and `cat-file`. No hook, checkout or filter runs.
//!
//! Each command is given the URL, never a remote name, and runs with
//! redirects off, terminal prompts off and only the `https` and `file`
//! protocols allowed. The user's own Git configuration still applies (a
//! credential helper, `url.<base>.insteadOf`): it is theirs to set.

use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use crate::source::{File, Tree};
use crate::spec::{GitSource, Rev};

/// The bare repository that holds what was fetched from one URL.
pub struct Mirror {
    dir: PathBuf,
}

fn git(dir: Option<&Path>) -> Command {
    let mut c = Command::new("git");
    if let Some(dir) = dir {
        c.arg("--git-dir").arg(dir);
    }
    c.args([
        "-c",
        "http.followRedirects=false",
        "-c",
        "protocol.allow=never",
        "-c",
        "protocol.https.allow=always",
        "-c",
        "protocol.file.allow=always",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "fetch.recurseSubmodules=false",
    ]);
    c.env("GIT_TERMINAL_PROMPT", "0");
    c.env_remove("GIT_DIR");
    c.env_remove("GIT_WORK_TREE");
    c.env_remove("GIT_OBJECT_DIRECTORY");
    c.env_remove("GIT_ALTERNATE_OBJECT_DIRECTORIES");
    c.stdin(Stdio::null());
    c
}

fn run(mut c: Command, what: &str) -> Result<Vec<u8>, String> {
    let out = c.output().map_err(|e| {
        say!(
            "totebag-git-could-not-run-for",
            what = what,
            error = e.to_string()
        )
    })?;
    if out.status.success() {
        Ok(out.stdout)
    } else {
        let err = String::from_utf8_lossy(&out.stderr);
        Err(say!("totebag-at", place = what, error = err.trim()))
    }
}

/// The branch `HEAD` of the repository at `url` points to, as a full ref.
pub fn default_branch(url: &str) -> Result<String, String> {
    crate::spec::check_url(url)?;
    let mut c = git(None);
    c.args(["ls-remote", "--symref", "--", url, "HEAD"]);
    let out = run(c, &say!("totebag-asking-default-branch", url = url))?;
    let text = String::from_utf8_lossy(&out);
    let found = text.lines().find_map(|l| {
        let (target, name) = l.strip_prefix("ref: ")?.split_once('\t')?;
        (name == "HEAD").then(|| target.to_string())
    });
    match found {
        Some(r) => {
            crate::spec::check_ref(&r)?;
            Ok(r)
        }
        None => Err(say!("totebag-no-default-branch", url = url)),
    }
}

impl Mirror {
    /// The bare repository for `url` in `dir`, made when it is not there.
    pub fn open(dir: PathBuf, object_format: &str) -> Result<Mirror, String> {
        if !dir.join("HEAD").is_file() {
            std::fs::create_dir_all(&dir).map_err(|e| {
                say!(
                    "totebag-at",
                    place = dir.display().to_string(),
                    error = e.to_string()
                )
            })?;
            let mut c = git(None);
            c.args(["init", "--bare", "--quiet"])
                .arg(format!("--object-format={object_format}"))
                .arg(&dir);
            run(c, "git init")?;
        }
        Ok(Mirror { dir })
    }

    fn has_commit(&self, rev: &Rev) -> bool {
        let mut c = git(Some(&self.dir));
        c.args(["cat-file", "-e", &format!("{}^{{commit}}", rev.hex())]);
        c.stderr(Stdio::null());
        c.status().is_ok_and(|s| s.success())
    }

    /// Fetches the commit `source.reference` names now, and gives its ID.
    pub fn fetch_head(&self, source: &GitSource) -> Result<Rev, String> {
        let mut c = git(Some(&self.dir));
        c.args(["fetch", "--quiet", "--no-tags", "--depth=1", "--"])
            .arg(&source.url)
            .arg(&source.reference);
        run(c, &say!("totebag-fetching", source = source.to_string()))?;
        let mut c = git(Some(&self.dir));
        c.args(["rev-parse", "--verify", "FETCH_HEAD^{commit}"]);
        let out = run(c, "git rev-parse")?;
        Rev::from_git(String::from_utf8_lossy(&out).trim())
    }

    /// Fetches the branch `reference` of `url` with all of its history, as an
    /// index is read, and gives the ID of its head.
    pub fn fetch_history(&self, url: &str, reference: &str) -> Result<Rev, String> {
        crate::spec::check_url(url)?;
        crate::spec::check_ref(reference)?;
        let mut c = git(Some(&self.dir));
        c.args(["fetch", "--quiet", "--no-tags"]);
        if self.dir.join("shallow").is_file() {
            c.arg("--unshallow");
        }
        c.arg("--").arg(url).arg(reference);
        run(
            c,
            &say!("totebag-fetching-from", reference = reference, url = url),
        )?;
        let mut c = git(Some(&self.dir));
        c.args(["rev-parse", "--verify", "FETCH_HEAD^{commit}"]);
        let out = run(c, "git rev-parse")?;
        Rev::from_git(String::from_utf8_lossy(&out).trim())
    }

    /// The commit `name` (a ref, or `HEAD`) names here.
    pub fn resolve(&self, name: &str) -> Result<Rev, String> {
        let mut c = git(Some(&self.dir));
        c.args(["rev-parse", "--verify", "--end-of-options"])
            .arg(format!("{name}^{{commit}}"));
        let out = run(c, &say!("totebag-finding", name = name))?;
        Rev::from_git(String::from_utf8_lossy(&out).trim())
    }

    /// Points `refs/totebag/<name>` at `rev`, so that the commit and what it
    /// reaches are kept here whatever the server's branch later says.
    pub fn keep(&self, name: &str, rev: &Rev) -> Result<(), String> {
        let mut c = git(Some(&self.dir));
        c.args(["update-ref", &format!("refs/totebag/{name}"), rev.hex()]);
        run(c, "git update-ref").map(|_| ())
    }

    /// Makes sure the commit `rev` is here: fetched by its ID, or else
    /// through `source.reference` when the server does not give a commit by ID.
    pub fn fetch_rev(&self, source: &GitSource, rev: &Rev) -> Result<(), String> {
        if self.has_commit(rev) {
            return Ok(());
        }
        let mut c = git(Some(&self.dir));
        c.args(["fetch", "--quiet", "--no-tags", "--depth=1", "--"])
            .arg(&source.url)
            .arg(rev.hex());
        let by_id = run(
            c,
            &say!(
                "totebag-fetching-from",
                reference = rev.short(),
                url = &source.url
            ),
        );
        if self.has_commit(rev) {
            return Ok(());
        }
        let mut c = git(Some(&self.dir));
        c.args(["fetch", "--quiet", "--no-tags", "--"])
            .arg(&source.url)
            .arg(&source.reference);
        run(c, &say!("totebag-fetching", source = source.to_string()))?;
        if self.has_commit(rev) {
            return Ok(());
        }
        Err(match by_id {
            Ok(_) => say!(
                "totebag-no-commit",
                url = &source.url,
                rev = rev.to_string()
            ),
            Err(e) => say!(
                "totebag-no-commit-because",
                url = &source.url,
                rev = rev.to_string(),
                error = e
            ),
        })
    }

    /// The files of the commit `rev`: the whole repository, not only the
    /// tote's directory, so that its paths to other totes in the same
    /// repository stay inside what was fetched.
    pub fn tree(&self, rev: &Rev) -> Result<Tree, String> {
        let mut c = git(Some(&self.dir));
        c.args(["ls-tree", "-r", "-z", "--full-tree", rev.hex()]);
        let listing = run(c, "git ls-tree")?;
        let mut entries = Vec::new();
        for record in listing.split(|b| *b == 0).filter(|r| !r.is_empty()) {
            let tab = record
                .iter()
                .position(|b| *b == b'\t')
                .ok_or_else(|| say!("totebag-ls-tree-no-path"))?;
            let head = std::str::from_utf8(&record[..tab]).map_err(|e| e.to_string())?;
            let path = std::str::from_utf8(&record[tab + 1..])
                .map_err(|_| say!("totebag-path-not-utf8", place = rev.short()))?;
            let mut parts = head.split(' ');
            let (Some(mode), Some(kind), Some(oid)) = (parts.next(), parts.next(), parts.next())
            else {
                return Err(say!(
                    "totebag-ls-tree-cannot-read",
                    head = format!("{head:?}")
                ));
            };
            let executable = match (mode, kind) {
                ("100644", "blob") => false,
                ("100755", "blob") => true,
                ("120000", _) => {
                    return Err(say!("totebag-symbolic-link", path = format!("{path:?}")));
                }
                ("160000", _) => {
                    return Err(say!("totebag-submodule", path = format!("{path:?}")));
                }
                _ => {
                    return Err(say!(
                        "totebag-not-regular-file",
                        path = format!("{path:?}"),
                        mode = mode
                    ));
                }
            };
            entries.push((path.to_string(), executable, oid.to_string()));
        }
        if entries.len() > crate::source::MAX_FILES {
            return Err(say!(
                "totebag-too-many-files",
                max = crate::source::MAX_FILES
            ));
        }
        let blobs = self.blobs(entries.iter().map(|(_, _, oid)| oid.as_str()))?;
        if blobs.len() != entries.len() {
            return Err(say!("totebag-cat-file-blob-missing"));
        }
        let files = entries
            .into_iter()
            .zip(blobs)
            .map(|((path, executable, _), bytes)| File {
                path,
                executable,
                bytes,
            })
            .collect();
        Tree::new(files)
    }

    /// The payload of the commit `rev`, checked to hash to `rev`.
    pub fn commit(&self, rev: &Rev) -> Result<Vec<u8>, String> {
        let mut c = git(Some(&self.dir));
        c.args(["cat-file", "commit", rev.hex()]);
        let payload = run(c, &say!("totebag-reading-commit", rev = rev.short()))?;
        if self.hash_object("commit", &payload)? != rev.hex() {
            return Err(say!("totebag-commit-hash-mismatch", rev = rev.short()));
        }
        Ok(payload)
    }

    /// The mode and ID of the entry `name` at the root of the tree `tree`.
    pub fn root_entry(&self, tree: &str, name: &str) -> Result<Option<(String, String)>, String> {
        let mut c = git(Some(&self.dir));
        c.args(["ls-tree", "-z", "--full-tree", tree, "--", name]);
        let out = run(c, "git ls-tree")?;
        for record in out.split(|b| *b == 0).filter(|r| !r.is_empty()) {
            let text = String::from_utf8_lossy(record);
            let Some((head, path)) = text.split_once('\t') else {
                continue;
            };
            if path != name {
                continue;
            }
            let mut parts = head.split(' ');
            if let (Some(mode), Some(_), Some(oid)) = (parts.next(), parts.next(), parts.next()) {
                return Ok(Some((mode.to_string(), oid.to_string())));
            }
        }
        Ok(None)
    }

    /// The bytes of the blob `oid`, checked to hash to `oid`.
    pub fn blob(&self, oid: &str, max: usize) -> Result<Vec<u8>, String> {
        let mut c = git(Some(&self.dir));
        c.args(["cat-file", "-s", oid]);
        let size: usize = String::from_utf8_lossy(&run(c, "git cat-file -s")?)
            .trim()
            .parse()
            .map_err(|_| say!("totebag-cat-file-not-a-size"))?;
        if size > max {
            return Err(say!("totebag-blob-too-large", oid = oid, max = max));
        }
        let mut c = git(Some(&self.dir));
        c.args(["cat-file", "blob", oid]);
        let bytes = run(c, "git cat-file blob")?;
        if self.hash_object("blob", &bytes)? != oid {
            return Err(say!("totebag-blob-hash-mismatch", oid = oid));
        }
        Ok(bytes)
    }

    /// The ID Git gives `bytes` as an object of `kind`, in this repository's format.
    fn hash_object(&self, kind: &str, bytes: &[u8]) -> Result<String, String> {
        let mut c = git(Some(&self.dir));
        c.args(["hash-object", "-t", kind, "--stdin"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let mut child = c
            .spawn()
            .map_err(|e| say!("totebag-git-could-not-run", error = e.to_string()))?;
        let mut stdin = child.stdin.take().expect("piped");
        let input = bytes.to_vec();
        let writer = std::thread::spawn(move || stdin.write_all(&input));
        let out = child.wait_with_output().map_err(|e| e.to_string())?;
        writer
            .join()
            .map_err(|_| say!("totebag-writer-panicked", command = "git hash-object"))?
            .map_err(|e| {
                say!(
                    "totebag-at",
                    place = "git hash-object",
                    error = e.to_string()
                )
            })?;
        if !out.status.success() {
            return Err(say!(
                "totebag-at",
                place = "git hash-object",
                error = String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
        Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
    }

    fn blobs<'a>(&self, oids: impl Iterator<Item = &'a str>) -> Result<Vec<Vec<u8>>, String> {
        let request: String = oids.map(|o| format!("{o}\n")).collect();
        let mut c = git(Some(&self.dir));
        c.args(["cat-file", "--batch"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let mut child = c
            .spawn()
            .map_err(|e| say!("totebag-git-could-not-run", error = e.to_string()))?;
        let mut stdin = child.stdin.take().expect("piped");
        let writer = std::thread::spawn(move || stdin.write_all(request.as_bytes()));
        let mut out = BufReader::new(child.stdout.take().expect("piped"));
        let mut blobs = Vec::new();
        let mut total = 0u64;
        let mut line = String::new();
        loop {
            line.clear();
            if out.read_line(&mut line).map_err(|e| e.to_string())? == 0 {
                break;
            }
            let mut parts = line.trim_end().split(' ');
            let (Some(_), Some(kind), Some(size)) = (parts.next(), parts.next(), parts.next())
            else {
                return Err(say!(
                    "totebag-at",
                    place = "git cat-file",
                    error = line.trim_end()
                ));
            };
            let size: u64 = size
                .parse()
                .map_err(|_| say!("totebag-at", place = "git cat-file", error = &line))?;
            total += size;
            if kind != "blob" || total > crate::source::MAX_BYTES {
                return Err(say!(
                    "totebag-cat-file-not-a-blob",
                    max = crate::source::MAX_BYTES
                ));
            }
            let mut bytes = vec![0; size as usize];
            out.read_exact(&mut bytes).map_err(|e| e.to_string())?;
            let mut newline = [0u8; 1];
            out.read_exact(&mut newline).map_err(|e| e.to_string())?;
            blobs.push(bytes);
        }
        writer
            .join()
            .map_err(|_| say!("totebag-writer-panicked", command = "git cat-file"))?
            .map_err(|e| say!("totebag-at", place = "git cat-file", error = e.to_string()))?;
        let status = child.wait().map_err(|e| e.to_string())?;
        if !status.success() {
            return Err(say!("totebag-cat-file-failed"));
        }
        Ok(blobs)
    }
}
