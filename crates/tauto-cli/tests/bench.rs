use std::fs;
use std::process::Command;

#[test]
fn help_and_invalid_options_do_not_build_or_run() {
    let binary = env!("CARGO_BIN_EXE_tauto");
    let help = Command::new(binary)
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(["bench", "--help"])
        .output()
        .unwrap();
    assert!(help.status.success());
    assert!(String::from_utf8_lossy(&help.stdout).contains("whole-process"));
    for args in [
        vec!["bench"],
        vec!["bench", "missing.taut", "--samples", "0"],
        vec!["bench", "missing.taut", "--warmup", "101"],
        vec!["bench", "missing.taut", "--timeout-ms", "0"],
        vec!["bench", "missing.taut", "--backend", "javascript"],
    ] {
        let output = Command::new(binary)
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .args(args)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn native_benchmark_builds_once_and_reports_real_samples() {
    let root = std::env::temp_dir().join(format!("tauto-bench-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let source = root.join("calc.taut");
    fs::write(
        &source,
        r#"perform show("sum", 2 + 3)
"#,
    )
    .unwrap();
    let target = root.join("target");
    let output = Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .arg("bench")
        .arg(&source)
        .args(["--warmup", "1", "--samples", "3", "--json"])
        .env("TAUTO_TARGET_DIR", &target)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["backend"], "rust");
    assert_eq!(report["profile"], "release");
    assert_eq!(report["measurement"], "whole_process_wall_time");
    assert_eq!(report["warmup"], 1);
    assert_eq!(report["exit_code"], 0);
    assert_eq!(report["output_consistent"], true);
    assert_eq!(report["poll_interval_ms"], 1);
    assert_eq!(report["includes_harness_overhead"], true);
    assert!(report["stdout_bytes"].as_u64().unwrap() > 0);
    let samples = report["samples"].as_array().unwrap();
    assert_eq!(samples.len(), 3);
    assert!(samples.iter().all(|n| n.as_f64().unwrap() > 0.0));
    assert!(
        report["statistics"]["min"].as_f64().unwrap()
            <= report["statistics"]["median"].as_f64().unwrap()
    );
    assert!(target.join("target/release/calc").exists());
    fs::write(
        &source,
        r#"perform exit(7)
"#,
    )
    .unwrap();
    let failed = Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .arg("bench")
        .arg(&source)
        .args(["--warmup", "0", "--samples", "1", "--json"])
        .env("TAUTO_TARGET_DIR", &target)
        .output()
        .unwrap();
    assert_eq!(failed.status.code(), Some(1));
    assert!(failed.stdout.is_empty());
    assert!(String::from_utf8_lossy(&failed.stderr).contains("program failed"));
    let _ = fs::remove_dir_all(&root);
}
