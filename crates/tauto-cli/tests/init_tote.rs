//! `tauto init` written in Tauto (`totes/initcmd`, run with `TAUTO_INIT=tote`) answers as the
//! Rust command does: the same output, the same exit status and the same files left behind.
use std::fs;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

struct Temp(PathBuf);
impl Temp {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "tauto-init-tote-{}-{}",
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

/// Everything under `dir` as a sorted listing, with the contents of files and the targets of links.
fn tree(dir: &Path) -> Vec<String> {
    fn walk(base: &Path, dir: &Path, out: &mut Vec<String>) {
        let mut entries: Vec<_> = fs::read_dir(dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect();
        entries.sort();
        for path in entries {
            let rel = path.strip_prefix(base).unwrap().display().to_string();
            let meta = fs::symlink_metadata(&path).unwrap();
            if meta.file_type().is_symlink() {
                out.push(format!(
                    "{rel} -> {}",
                    fs::read_link(&path).unwrap().display()
                ));
            } else if meta.is_dir() {
                out.push(format!("{rel}/"));
                walk(base, &path, out);
            } else {
                out.push(format!("{rel}: {:?}", fs::read_to_string(&path).unwrap()));
            }
        }
    }
    let mut out = Vec::new();
    walk(dir, dir, &mut out);
    out
}

/// Runs `tauto init ARGS` in a fresh directory prepared by `setup`, with the Rust command or the
/// tote, and returns what it printed (the directory's name made constant), its status and the files.
fn run(
    tote: bool,
    setup: &dyn Fn(&Path),
    args: &[&str],
) -> (String, String, Option<i32>, Vec<String>) {
    let temp = Temp::new();
    let root = temp.0.join("work");
    fs::create_dir(&root).unwrap();
    setup(&root);
    let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
    command
        .current_dir(&root)
        .env("TAUTO_LANG", "en")
        .arg("init")
        .args(args);
    if tote {
        command.env("TAUTO_INIT", "tote");
    }
    let output = command.output().unwrap();
    let clean =
        |bytes: &[u8]| String::from_utf8_lossy(bytes).replace(root.to_str().unwrap(), "<work>");
    (
        clean(&output.stdout),
        clean(&output.stderr),
        output.status.code(),
        tree(&root),
    )
}

fn same(setup: &dyn Fn(&Path), args: &[&str]) {
    let rust = run(false, setup, args);
    let tote = run(true, setup, args);
    assert_eq!(rust, tote, "tauto init {args:?}");
}

fn nothing(_: &Path) {}

#[test]
fn a_new_tote_in_the_current_directory_or_below_it() {
    same(&|d| fs::create_dir(d.join("hello-world")).unwrap(), &[]);
    same(&nothing, &["hello-world"]);
    same(
        &|d| fs::create_dir(d.join("日本語")).unwrap(),
        &["日本語/hello-world"],
    );
    same(&|d| fs::create_dir(d.join("pkg")).unwrap(), &["pkg/"]);
    same(&|d| fs::create_dir(d.join("pkg")).unwrap(), &["./pkg"]);
    same(&|d| fs::create_dir(d.join("pkg")).unwrap(), &["pkg/."]);
}

#[test]
fn an_absolute_path() {
    let temp = Temp::new();
    let target = temp.0.join("abs-pkg");
    let path = target.to_str().unwrap().to_string();
    let tote = run(true, &nothing, &[&path]);
    assert_eq!(tote.2, Some(0), "{}", tote.1);
    assert!(target.join("Tauto.eure").is_file() && target.join("src/main.taut").is_file());
    fs::remove_dir_all(&target).unwrap();
    let rust = run(false, &nothing, &[&path]);
    assert_eq!((rust.0, rust.2), (tote.0, tote.2));
}

#[test]
fn the_files_that_are_there_are_kept() {
    let create = |d: &Path| {
        fs::write(d.join("keep.txt"), "keep").unwrap();
        fs::create_dir(d.join("src")).unwrap();
        fs::write(d.join("src/other.taut"), "x").unwrap();
    };
    same(
        &|d| {
            create(d);
            fs::create_dir(d.join("pkg")).unwrap()
        },
        &["pkg"],
    );
    same(
        &|d| {
            fs::create_dir(d.join("pkg")).unwrap();
            fs::write(d.join("pkg/Tauto.eure"), "mine").unwrap()
        },
        &["pkg"],
    );
    same(
        &|d| {
            fs::create_dir_all(d.join("pkg/src")).unwrap();
            fs::write(d.join("pkg/src/main.taut"), "mine").unwrap()
        },
        &["pkg"],
    );
}

#[test]
fn links_are_refused_and_never_written_through() {
    same(
        &|d| {
            fs::create_dir(d.join("real")).unwrap();
            symlink("real", d.join("lnk")).unwrap()
        },
        &["lnk"],
    );
    same(
        &|d| {
            fs::create_dir(d.join("real")).unwrap();
            symlink("real", d.join("lnk")).unwrap()
        },
        &["lnk/pkg"],
    );
    same(&|d| symlink("nowhere", d.join("lnk")).unwrap(), &["lnk"]);
    same(
        &|d| {
            fs::create_dir(d.join("pkg")).unwrap();
            fs::create_dir(d.join("elsewhere")).unwrap();
            symlink("../elsewhere", d.join("pkg/src")).unwrap()
        },
        &["pkg"],
    );
    same(
        &|d| {
            fs::create_dir(d.join("pkg")).unwrap();
            symlink("nowhere", d.join("pkg/Tauto.eure")).unwrap()
        },
        &["pkg"],
    );
    same(
        &|d| {
            fs::create_dir_all(d.join("pkg/src")).unwrap();
            symlink("nowhere", d.join("pkg/src/main.taut")).unwrap()
        },
        &["pkg"],
    );
}

#[test]
fn what_cannot_be_a_tote() {
    same(&nothing, &["Bad"]);
    same(&nothing, &["1st"]);
    same(&nothing, &["has_underscore"]);
    same(&nothing, &["../x"]);
    same(&nothing, &["a/../x"]);
    same(&nothing, &["missing/pkg"]);
    same(&|d| fs::write(d.join("file"), "x").unwrap(), &["file"]);
    same(&|d| fs::write(d.join("file"), "x").unwrap(), &["file/pkg"]);
    same(&nothing, &[""]);
}

#[test]
fn the_arguments() {
    same(&nothing, &["--help"]);
    same(&nothing, &["-h"]);
    same(&nothing, &["--bogus"]);
    same(&nothing, &["a", "b"]);
}

#[test]
fn a_tote_made_by_the_command_checks_and_runs() {
    let temp = Temp::new();
    let output = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(&temp.0)
        .env("TAUTO_INIT", "tote")
        .args(["init", "hello-world"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let run = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(temp.0.join("hello-world"))
        .args(["run", "--tote", "."])
        .output()
        .unwrap();
    assert!(String::from_utf8_lossy(&run.stdout).contains("42"));
}
