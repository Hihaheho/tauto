use selfhost_harness::shared_cli::{Config, supervise, validate_worker_report, write_report};
use serde_json::json;
use std::{path::PathBuf, process::Command, time::Duration};

fn parse(args: &[&str]) -> Result<Config, String> {
    Config::parse(args.iter().map(|s| (*s).into()))
}
#[test]
fn options_require_values_and_reject_unknown_or_duplicate_selection() {
    for args in [
        vec!["--root"],
        vec!["--root", "cases", "--report"],
        vec!["--root", "cases", "--filter"],
        vec!["--root", "cases", "--filter", ""],
        vec!["--root", "cases", "--filter", "--report", "r.json"],
        vec!["--root", "cases", "--target", "other"],
        vec!["--root", "cases", "--component", "unknown"],
        vec![
            "--root",
            "cases",
            "--component",
            "syntax",
            "--component",
            "syntax",
        ],
        vec!["--root", "cases", "--root", "other"],
        vec!["--root", "cases", "--report", "a", "--report", "b"],
        vec!["--root", "cases", "--unknown", "x"],
        vec!["--root", "cases", "--timeout-seconds", "0"],
        vec!["--root", "cases", "--timeout-seconds", "86401"],
        vec!["--root", "cases", "--timeout-seconds", "1.5"],
    ] {
        assert!(parse(&args).is_err(), "{args:?}");
    }
}
#[test]
fn setup_and_execution_have_separate_limits_and_selection() {
    let setup = parse(&[
        "--root",
        "cases",
        "--prepare",
        "rustgen",
        "--setup-timeout-seconds",
        "900",
    ])
    .unwrap();
    assert_eq!(setup.setup_timeout, Duration::from_secs(900));
    assert_eq!(setup.prepare.as_deref(), Some("rustgen"));
    let execution = parse(&[
        "--root",
        "cases",
        "--timeout-seconds",
        "15",
        "--component",
        "syntax",
        "--filter",
        "one",
    ])
    .unwrap();
    assert_eq!(execution.timeout, Duration::from_secs(15));
    assert_eq!(execution.modes, ["syntax"]);
    for args in [
        vec!["--root", "cases", "--setup-timeout-seconds", "900"],
        vec!["--root", "cases", "--prepare", "kernel"],
        vec!["--root", "cases", "--prepare", "rustgen", "--filter", "one"],
        vec![
            "--root",
            "cases",
            "--prepare",
            "rustgen",
            "--target",
            "rust",
        ],
        vec![
            "--root",
            "cases",
            "--prepare",
            "rustgen",
            "--component",
            "syntax",
        ],
        vec![
            "--root",
            "cases",
            "--prepare",
            "rustgen",
            "--timeout-seconds",
            "10",
        ],
    ] {
        assert!(parse(&args).is_err(), "{args:?}");
    }
}
fn passed() -> serde_json::Value {
    json!({"invocation":"current","phase":"execution","status":"completed","semantic_execution_verified":true,"summary":{"passed":1,"failed":0,"incomplete":0,"host_harness":0,"explicitly_excluded":0},"cases":[{"case":"one","status":"passed"}]})
}
#[test]
fn stale_wrong_phase_missing_cases_signals_and_false_counts_are_rejected() {
    let report = passed();
    let names = vec!["one".to_string()];
    assert!(validate_worker_report(&report, "current", "execution", &names, Some(0)).unwrap());
    assert!(validate_worker_report(&report, "old", "execution", &names, Some(0)).is_err());
    assert!(validate_worker_report(&report, "current", "setup", &names, Some(0)).is_err());
    assert!(
        validate_worker_report(&report, "current", "execution", &["two".into()], Some(0)).is_err()
    );
    for exit in [None, Some(1), Some(2)] {
        assert!(validate_worker_report(&report, "current", "execution", &names, exit).is_err());
    }
    let mut wrong = report.clone();
    wrong["status"] = json!("running");
    assert!(validate_worker_report(&wrong, "current", "execution", &names, Some(0)).is_err());
    wrong["status"] = json!("failed");
    assert!(validate_worker_report(&wrong, "current", "execution", &names, Some(0)).is_err());
    let mut wrong = report;
    wrong["summary"]["passed"] = json!(2);
    assert!(validate_worker_report(&wrong, "current", "execution", &names, Some(0)).is_err());
}
#[test]
fn preparation_requires_an_artifact_and_never_claims_semantic_success() {
    let mut report = json!({"invocation":"current","phase":"setup","status":"prepared","semantic_execution_verified":false,"summary":{"passed":0,"failed":0,"incomplete":0,"host_harness":0,"explicitly_excluded":0},"cases":[],"prepared":{"artifact_sha256":"a".repeat(64)}});
    assert!(validate_worker_report(&report, "current", "setup", &[], Some(0)).unwrap());
    report["semantic_execution_verified"] = json!(true);
    assert!(validate_worker_report(&report, "current", "setup", &[], Some(0)).is_err());
    report["semantic_execution_verified"] = json!(false);
    report["prepared"]["artifact_sha256"] = json!("");
    assert!(validate_worker_report(&report, "current", "setup", &[], Some(0)).is_err());
}
struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let path = std::env::temp_dir().canonicalize().unwrap().join(format!(
            "selfhost-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
#[test]
fn fresh_report_replaces_previous_success_before_validation() {
    let dir = Scratch::new();
    let path = dir.0.join("report.json");
    write_report(&path, &passed()).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_shared-cases"))
        .arg("--root")
        .arg(dir.0.join("missing"))
        .arg("--report")
        .arg(&path)
        .output()
        .unwrap();
    assert!(!result.status.success());
    let current: serde_json::Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    assert_ne!(current["invocation"], "current");
    assert_eq!(current["status"], "failed");
    assert_eq!(current["semantic_execution_verified"], false);
    assert_eq!(current["summary"]["passed"], 0);
}
#[cfg(unix)]
#[test]
fn supervision_preserves_nonzero_status_and_both_streams() {
    let dir = Scratch::new();
    let result = supervise(
        Command::new("/bin/sh").args(["-c", "printf output; printf diagnostic >&2; exit 7"]),
        &dir.0,
        Duration::from_secs(5),
    )
    .unwrap();
    assert_eq!(result.code, Some(7));
    assert!(!result.timed_out);
    assert_eq!(result.stdout, b"output");
    assert_eq!(result.stderr, b"diagnostic");
}
#[cfg(unix)]
#[test]
fn supervision_preserves_signal_even_after_complete_looking_output() {
    let dir = Scratch::new();
    let result = supervise(
        Command::new("/bin/sh").args(["-c", "printf complete; kill -TERM $$"]),
        &dir.0,
        Duration::from_secs(5),
    )
    .unwrap();
    assert_eq!(result.code, None);
    assert!(!result.timed_out);
    assert_eq!(result.stdout, b"complete");
}
#[cfg(unix)]
#[test]
fn timeout_terminates_descendants_and_preserves_partial_streams() {
    let dir = Scratch::new();
    let marker = dir.0.join("descendant-survived");
    let result = supervise(
        Command::new("/bin/sh")
            .args([
                "-c",
                "printf partial; printf waiting >&2; (sleep 1; printf orphan > \"$1\") & wait",
                "worker",
            ])
            .arg(&marker),
        &dir.0,
        Duration::from_millis(100),
    )
    .unwrap();
    assert!(result.timed_out);
    assert_eq!(result.code, None);
    assert_eq!(result.stdout, b"partial");
    assert_eq!(result.stderr, b"waiting");
    std::thread::sleep(Duration::from_millis(1200));
    assert!(!marker.exists(), "descendant escaped worker process group");
}

#[test]
fn invalid_arguments_replace_an_unambiguous_requested_report() {
    let dir = Scratch::new();
    let path = dir.0.join("report.json");
    write_report(&path, &passed()).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_shared-cases"))
        .args(["--root", "cases", "--component", "unknown", "--report"])
        .arg(&path)
        .output()
        .unwrap();
    assert!(!result.status.success());
    let current: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
    assert_ne!(current["invocation"], "current");
    assert_eq!(current["phase"], "arguments");
    assert_eq!(current["status"], "failed");
    assert_eq!(current["summary"]["passed"], 0);
}
#[test]
fn ambiguous_report_arguments_do_not_choose_a_destination() {
    let dir = Scratch::new();
    let path = dir.0.join("report.json");
    write_report(&path, &passed()).unwrap();
    let before = std::fs::read(&path).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_shared-cases"))
        .args(["--root", "cases", "--report"])
        .arg(&path)
        .arg("--report")
        .arg(&path)
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert_eq!(std::fs::read(&path).unwrap(), before);
    assert!(String::from_utf8_lossy(&result.stderr).contains("no report destination selected"));
}

#[cfg(unix)]
#[test]
fn normal_worker_exit_also_cleans_up_background_descendants() {
    let dir = Scratch::new();
    let marker = dir.0.join("descendant-survived");
    let result = supervise(
        Command::new("/bin/sh")
            .args(["-c", "(sleep 1; printf orphan > \"$1\") & exit 0", "worker"])
            .arg(&marker),
        &dir.0,
        Duration::from_secs(5),
    )
    .unwrap();
    assert_eq!(result.code, Some(0));
    assert!(!result.timed_out);
    std::thread::sleep(Duration::from_millis(1200));
    assert!(
        !marker.exists(),
        "normal worker exit left a background descendant"
    );
}
