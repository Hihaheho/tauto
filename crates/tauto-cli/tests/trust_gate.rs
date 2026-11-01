//! A run asks before it is trusted with anything not approved before: the
//! `trust` section of `Tauto.eure` and a `--permissions FILE`. Without a
//! terminal it does not start unless `--approve-trust` is given.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn temp(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tauto-trust-gate-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(d.join("app/src")).unwrap();
    fs::write(d.join("app/src/main.taut"), "perform show(\"n\", 1)\n").unwrap();
    d
}

fn manifest(root: &Path, trust: &str) {
    fs::write(
        root.join("app/Tauto.eure"),
        format!(
            "package {{\n  name = \"app\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}}\n{trust}"
        ),
    )
    .unwrap();
}

/// `tauto run …` in a session of its own, so it has no terminal to ask at.
fn run(root: &Path, args: &[&str]) -> Output {
    let mut c = Command::new(env!("CARGO_BIN_EXE_tauto"));
    c.arg("run")
        .args(args)
        .arg("--tote")
        .arg(root.join("app"))
        .env("TAUTO_HOME", root.join("home"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en");
    #[cfg(unix)]
    unsafe {
        use std::os::unix::process::CommandExt;
        c.pre_exec(|| {
            libc::setsid();
            Ok(())
        });
    }
    c.output().unwrap()
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

#[test]
fn a_new_or_changed_trust_needs_approval() {
    let root = temp("trust");
    manifest(&root, "trust {\n  extern = [\"a\"]\n}\n");
    let refused = run(&root, &[]);
    assert!(!refused.status.success());
    let e = stderr(&refused);
    assert!(e.contains("has not been approved before"), "{e}");
    assert!(e.contains("+ extern: a"), "{e}");
    assert!(e.contains("--approve-trust"), "{e}");

    assert!(run(&root, &["--approve-trust"]).status.success());
    // Approved once, the same trust runs without asking.
    let again = run(&root, &[]);
    assert!(again.status.success(), "{}", stderr(&again));

    manifest(&root, "trust {\n  extern = [\"a\", \"b\"]\n}\n");
    let changed = stderr(&run(&root, &[]));
    assert!(
        changed.contains("changed since it was approved"),
        "{changed}"
    );
    assert!(changed.contains("+ extern: a, b"), "{changed}");
    assert!(changed.contains("- extern: a"), "{changed}");
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn no_trust_asks_nothing() {
    let root = temp("none");
    manifest(&root, "");
    let o = run(&root, &[]);
    assert!(o.status.success(), "{}", stderr(&o));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn a_permissions_file_needs_approval() {
    let root = temp("file");
    manifest(&root, "");
    let file = root.join("perm.eure");
    fs::write(&file, "env = [\"HOME\"]\n").unwrap();
    let f = file.to_str().unwrap();
    let e = stderr(&run(&root, &["--permissions", f]));
    assert!(e.contains("The permissions file"), "{e}");
    assert!(e.contains("+ env: HOME"), "{e}");
    assert!(
        run(&root, &["--permissions", f, "--approve-trust"])
            .status
            .success()
    );
    assert!(run(&root, &["--permissions", f]).status.success());
    fs::write(&file, "env = [\"HOME\"]\nnet = true\n").unwrap();
    let e = stderr(&run(&root, &["--permissions", f]));
    assert!(e.contains("+ net: everything"), "{e}");
    let _ = fs::remove_dir_all(&root);
}
