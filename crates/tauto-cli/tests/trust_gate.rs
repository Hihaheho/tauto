//! A run asks before it is trusted with anything not approved before: the
//! `trust` section of `Tauto.eure`, and at its start the permissions its
//! effects need. Without a terminal it does not start unless
//! `--approve-trust` (the trust) or `--yes` (the permissions) is given.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn temp(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tauto-trust-gate-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(d.join("app/src")).unwrap();
    fs::write(d.join("app/src/main.taut"), "perform main(() => show(&1))\n").unwrap();
    d
}

fn manifest(root: &Path, trust: &str) {
    fs::write(
        root.join("app/Tauto.eure"),
        format!("package {{\n  name = \"app\"\n  version = \"0.1.0\"\n}}\n{trust}"),
    )
    .unwrap();
}

/// `tauto run …` in a session of its own, so it has no terminal to ask at.
fn run(root: &Path, args: &[&str]) -> Output {
    let mut c = Command::new(env!("CARGO_BIN_EXE_tauto"));
    c.current_dir(root.join("app"))
        .arg("run")
        .args(args)
        .arg(".")
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

/// The tote's program reads an environment variable: its rows need `env`.
fn reads_env(root: &Path) {
    fs::write(
        root.join("app/src/main.taut"),
        "import std::builtin::os\n\nperform main(() => show(&(perform env(\"HOME\"))))\n",
    )
    .unwrap();
}

#[test]
fn what_the_effects_need_is_asked_at_the_start() {
    let root = temp("ask");
    manifest(&root, "");
    reads_env(&root);
    let refused = run(&root, &[]);
    assert!(!refused.status.success());
    let e = stderr(&refused);
    assert!(e.contains("needs these permissions to run"), "{e}");
    assert!(e.contains("+ env: read environment variables"), "{e}");
    assert!(e.contains("--yes"), "{e}");
    let allowed = run(&root, &["--yes"]);
    assert!(allowed.status.success(), "{}", stderr(&allowed));
    // `--yes` keeps nothing: the next run asks again.
    assert!(!run(&root, &[]).status.success());
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn a_program_without_host_effects_is_asked_nothing() {
    let root = temp("quiet");
    manifest(&root, "");
    let o = run(&root, &[]);
    assert!(o.status.success(), "{}", stderr(&o));
    assert!(!stderr(&o).contains("needs these permissions"));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn trust_run_grants_a_kind_without_asking() {
    let root = temp("trust-run");
    manifest(&root, "trust {\n  run {\n    env = [\"HOME\"]\n  }\n}\n");
    reads_env(&root);
    let e = stderr(&run(&root, &[]));
    assert!(
        e.contains("+ run: { env = [\"HOME\"] }") || e.contains("+ run:"),
        "{e}"
    );
    let o = run(&root, &["--approve-trust"]);
    assert!(o.status.success(), "{}", stderr(&o));
    let o = run(&root, &[]);
    assert!(o.status.success(), "{}", stderr(&o));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn permission_flags_are_gone() {
    let root = temp("gone");
    manifest(&root, "");
    for flag in ["--allow-env", "--allow-read=x", "-A", "--permissions"] {
        let o = run(&root, &[flag]);
        assert_eq!(o.status.code(), Some(2));
        let e = stderr(&o);
        assert!(e.contains("is gone"), "{flag}: {e}");
    }
    let _ = fs::remove_dir_all(&root);
}
