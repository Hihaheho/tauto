//! Timing reports preserve the build contract and describe only completed work.
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

use serde_json::Value;

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new(source: &str) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "tauto-build-timings-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("main.taut"), source).unwrap();
        Self(dir)
    }

    fn command(&self, flags: &[&str]) -> Command {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_tauto"));
        // The messages below are the English ones, whatever the language here.
        cmd.env("TAUTO_LANG", "en");
        cmd.arg("build")
            .args(flags)
            .arg(self.0.join("main.taut"))
            .arg("-o")
            .arg(self.0.join("out"))
            .env("TAUTO_TARGET_DIR", self.0.join("target"))
            .env("CARGO_BUILD_JOBS", "1")
            .env("CARGO_PROFILE_DEV_DEBUG", "0")
            .env("CARGO_INCREMENTAL", "0")
            .env("CARGO_NET_OFFLINE", "true");
        cmd
    }

    fn build(&self, flags: &[&str]) -> Output {
        self.command(flags).output().unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn report(out: &Output) -> Value {
    let stderr = String::from_utf8_lossy(&out.stderr);
    let json = stderr.lines().last().expect("timing report on stderr");
    let value: Value = serde_json::from_str(json).unwrap_or_else(|e| panic!("{e}: {stderr}"));
    assert_eq!(value["schema_version"], 1);
    assert_eq!(value["kind"], "tauto.build.timings");
    assert_eq!(
        value["status"],
        if out.status.success() { "ok" } else { "failed" }
    );
    let phases = value["phases"].as_array().unwrap();
    assert!(!phases.is_empty());
    assert_eq!(
        phases
            .iter()
            .map(|p| p["duration_ns"].as_u64().unwrap())
            .sum::<u64>(),
        value["duration_ns"].as_u64().unwrap()
    );
    for p in &phases[..phases.len() - 1] {
        assert_eq!(p["status"], "ok");
    }
    assert_eq!(phases.last().unwrap()["status"], value["status"]);
    // The report is metadata, not a source/host/environment dump.
    assert!(!json.contains("main.taut"));
    assert!(!json.contains("tauto-build-timings-"));
    value
}

fn names(value: &Value) -> Vec<&str> {
    value["phases"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| p["name"].as_str().unwrap())
        .collect()
}

#[test]
fn emit_preserves_stdout_and_observes_generated_source_reuse() {
    let f = Fixture::new(
        r#"perform show("answer", 42)
"#,
    );
    let first = f.build(&["--emit", "rust", "--timings=json"]);
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let first_report = report(&first);
    assert_eq!(
        names(&first_report),
        [
            "input",
            "tote_load_check_extract",
            "parse_expand",
            "check",
            "lower",
            "codegen",
            "write",
            "finish"
        ]
    );
    assert_eq!(first_report["cache"]["native"], "not_run");
    assert_eq!(first_report["cache"]["generated_sources"]["hits"], 0);
    let count = first_report["cache"]["generated_sources"]["misses"]
        .as_u64()
        .unwrap();
    assert!(count > 0);
    let ordinary = f.build(&["--emit", "rust"]);
    assert!(ordinary.status.success());
    assert_eq!(ordinary.stdout, first.stdout);
    assert!(ordinary.stderr.is_empty());
    let second = f.build(&["--emit", "rust", "--timings=json"]);
    assert_eq!(second.stdout, ordinary.stdout);
    let second_report = report(&second);
    assert_eq!(second_report["cache"]["generated_sources"]["hits"], count);
    assert_eq!(second_report["cache"]["generated_sources"]["misses"], 0);
    assert_eq!(
        second_report["cache"]["generated_sources"]["provenance"],
        "content_equality"
    );
    let human = f.build(&["--emit", "rust", "--timings"]);
    assert_eq!(human.stdout, ordinary.stdout);
    let text = String::from_utf8(human.stderr).unwrap();
    assert!(text.starts_with("build timings (ok; rust / host; wall time):"));
    assert!(text.contains("total"));
    assert!(text.contains("native cache: not_run"));
}

#[test]
fn failures_keep_exit_codes_and_diagnostics_before_final_json() {
    let f = Fixture::new(
        r#"fn broken(
"#,
    );
    for (source, expected_phase) in [
        (
            r#"fn broken(
"#,
            "tote_load_check_extract",
        ),
        (
            r#"let answer: Bool := 42
"#,
            "check",
        ),
    ] {
        fs::write(f.0.join("main.taut"), source).unwrap();
        let ordinary = f.build(&["--emit", "rust"]);
        let timed = f.build(&["--emit", "rust", "--timings=json"]);
        assert_eq!(ordinary.status.code(), Some(1));
        assert_eq!(timed.status.code(), ordinary.status.code());
        assert_eq!(timed.stdout, ordinary.stdout);
        assert!(timed.stderr.starts_with(&ordinary.stderr));
        let value = report(&timed);
        assert_eq!(names(&value).last(), Some(&expected_phase));
        assert_eq!(value["cache"]["native"], "not_run");
    }
    fs::remove_file(f.0.join("main.taut")).unwrap();
    let missing = f.build(&["--timings=json"]);
    assert_eq!(missing.status.code(), Some(2));
    assert_eq!(names(&report(&missing)), ["input"]);
}

#[test]
fn output_and_native_failures_are_not_successful_phases() {
    let f = Fixture::new(
        r#"perform show("answer", 42)
"#,
    );
    fs::write(f.0.join("out"), "not a directory").unwrap();
    let write = f.build(&["--emit", "rust", "--timings=json"]);
    assert_eq!(write.status.code(), Some(2));
    let value = report(&write);
    assert_eq!(names(&value).last(), Some(&"write"));
    assert!(value["cache"]["generated_sources"].is_null());
    fs::remove_file(f.0.join("out")).unwrap();
    let native = f
        .command(&["--timings=json"])
        .env("CARGO", f.0.join("absent-cargo"))
        // Without rustc too: a runtime kept from an earlier build would
        // otherwise let the build go on without Cargo.
        .env("RUSTC", f.0.join("absent-rustc"))
        .output()
        .unwrap();
    assert_eq!(native.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&native.stderr).starts_with("cannot run cargo:"));
    let value = report(&native);
    assert_eq!(names(&value).last(), Some(&"native_compile"));
    assert_eq!(value["cache"]["native"], "unknown");
}

#[test]
fn native_host_build_reports_cargo_without_changing_binary_path() {
    let f = Fixture::new(
        r#"perform show("answer", 42)
"#,
    );
    let out = f.build(&["--timings=json"]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let value = report(&out);
    assert!(names(&value).contains(&"native_compile"));
    assert_eq!(names(&value).last(), Some(&"finish"));
    assert_eq!(value["cache"]["native"], "unknown");
    let stdout = String::from_utf8(out.stdout).unwrap();
    let path = Path::new(stdout.trim());
    assert!(path.is_file(), "{}", path.display());
    let run = Command::new(path).output().unwrap();
    assert!(run.status.success());
    assert_eq!(run.stdout, b"answer = 42\n");
    let ordinary = f.build(&[]);
    assert!(ordinary.status.success());
    assert_eq!(ordinary.stdout, stdout.as_bytes());
    assert!(ordinary.stderr.is_empty());
}

#[test]
fn javascript_build_targets_do_not_run_the_program_or_claim_native_compilation() {
    let f = Fixture::new(
        r#"perform show("answer", 42)
"#,
    );
    for target in ["node", "browser"] {
        let out = f.build(&[
            "--backend",
            "javascript",
            "--target",
            target,
            "--declarations",
            "--timings=json",
        ]);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let value = report(&out);
        assert_eq!(value["backend"], "javascript");
        assert_eq!(value["target"], target);
        assert_eq!(value["cache"]["native"], "not_run");
        assert!(value["cache"]["generated_sources"].is_null());
        assert!(names(&value).contains(&"codegen_write"));
        assert_eq!(names(&value).last(), Some(&"finish"));
        assert!(!String::from_utf8_lossy(&out.stdout).contains("answer ="));
        assert!(f.0.join("out/main.mjs").is_file());
        assert!(f.0.join("out/program.d.mts").is_file());
    }
}

#[test]
fn timings_are_build_only_and_reject_invalid_or_duplicate_formats() {
    for args in [
        vec!["run", "--backend", "rust", "main.taut", "--timings"],
        vec!["build", "main.taut", "--timings=xml"],
        vec!["build", "main.taut", "--timings", "--timings=json"],
        vec!["build", "--timings=json"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .args(args)
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(2));
        assert!(out.stdout.is_empty());
        assert!(String::from_utf8_lossy(&out.stderr).starts_with("usage:"));
        assert!(!String::from_utf8_lossy(&out.stderr).contains("\"schema_version\""));
    }
}

#[test]
fn javascript_rust_extern_failure_reports_the_native_boundary() {
    let f = Fixture::new(
        r#"extern { fn absolute(n: i64): i64 }
perform show("abs", absolute(0 - 42))
"#,
    );
    fs::write(f.0.join("Tauto.eure"), "package { name = \"timed-extern\" sources = [\"main.taut\"] }\nrust { extern { absolute = \"i64::abs\" } }\n").unwrap();
    let empty_path = f.0.join("no-tools");
    fs::create_dir(&empty_path).unwrap();
    let out = f
        .command(&[
            "--backend",
            "javascript",
            "--target",
            "browser",
            "--timings=json",
        ])
        .env("PATH", &empty_path)
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).starts_with("cannot build Rust wasm externs:"));
    let value = report(&out);
    assert_eq!(value["target"], "browser");
    assert_eq!(names(&value).last(), Some(&"native_compile"));
    assert_eq!(value["cache"]["native"], "unknown");
    assert!(
        value["cache"]["generated_sources"]["misses"]
            .as_u64()
            .unwrap()
            > 0
    );
}

#[test]
fn tote_loading_reports_its_combined_proof_check_and_extraction_boundary() {
    let f = Fixture::new(
        r#"perform show("answer", 42)
"#,
    );
    fs::write(
        f.0.join("Tauto.eure"),
        "package { name = \"timed-tote\" sources = [\"main.taut\"] }\n",
    )
    .unwrap();
    for fail in [false, true] {
        if fail {
            fs::write(
                f.0.join("Tauto.eure"),
                "package { name = \"timed-tote\" sources = [\"missing.taut\"] }\n",
            )
            .unwrap();
        }
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .args(["build", "--emit", "rust", "--timings=json"])
            .arg(&f.0)
            .arg("-o")
            .arg(f.0.join("out"))
            .output()
            .unwrap();
        assert_eq!(
            out.status.success(),
            !fail,
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let value = report(&out);
        assert!(names(&value).contains(&"tote_load_check_extract"));
        assert_eq!(value["cache"]["proof"], "unknown");
        assert_eq!(value["cache"]["native"], "not_run");
        if fail {
            assert_eq!(names(&value).last(), Some(&"tote_load_check_extract"));
        } else {
            assert_eq!(names(&value).last(), Some(&"finish"));
        }
    }
}
