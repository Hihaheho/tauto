//! Diagnostic mode sees library entries without silently trusting ordinary Fn.
use std::{fs, path::Path, process::Command};

fn library_source() -> &'static str {
    r#"fn sum(&read: (u64) -> u64, size: u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size { total := total + read(index)
    index := index + 1 }
  total
}
fn run(&read: (u64) -> u64, size: u64): Result(u64, Text) {
  handle { budget(steps: 1000) { Ok(sum(&(index) => read(index), size)) } } with {
    exceeded(info), k => Err("exhausted")
  }
}
"#
}

fn directory(name: &str) -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "tauto-budget-explain-{}-{name}",
        std::process::id()
    ));
    fs::create_dir_all(&path).unwrap();
    fs::write(path.join("input.taut"), library_source()).unwrap();
    path
}

fn emit(dir: &Path, explain: bool) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
    command
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(["build", "--emit", "rust", "-o"])
        .arg(dir.join("out"));
    if explain {
        command.arg("--explain-budget");
    }
    command.arg(dir.join("input.taut")).output().unwrap()
}

#[test]
fn unused_library_callbacks_have_explicit_fallback_diagnostics() {
    let dir = directory("ordinary");
    let ordinary = emit(&dir, false);
    assert!(
        ordinary.status.success(),
        "{}",
        String::from_utf8_lossy(&ordinary.stderr)
    );
    assert!(!String::from_utf8_lossy(&ordinary.stderr).contains("[unknown-callback]"));
    let rust = fs::read_to_string(dir.join("out/src/lib.rs")).unwrap();
    // The program driver is named run.
    assert_eq!(rust.matches("pub fn run(").count(), 1);
    let explained = emit(&dir, true);
    assert!(
        explained.status.success(),
        "{}",
        String::from_utf8_lossy(&explained.stderr)
    );
    let diagnostic = String::from_utf8(explained.stderr).unwrap();
    assert!(
        diagnostic.contains("(ordinary): ordinary Future path"),
        "{diagnostic}"
    );
    assert!(diagnostic.contains("[unknown-callback]"), "{diagnostic}");
    assert!(!diagnostic.contains("[trusted-assumption]"), "{diagnostic}");
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn selected_qualified_library_entry_reports_assertions_separately() {
    let dir = directory("qualified");
    fs::write(
        dir.join("Tauto.eure"),
        r#"rust {
      exports = ["run"]
      nonresuming { entries { run_trusted = "run" } }
    }"#,
    )
    .unwrap();
    // Explicit entry configuration makes the library entry available even
    // without diagnostic mode; the unconfigured ordinary CLI remains pruned.
    assert!(emit(&dir, false).status.success());
    let output = emit(&dir, true);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let diagnostic = String::from_utf8(output.stderr).unwrap();
    assert!(
        diagnostic.contains("(ordinary): ordinary Future path"),
        "{diagnostic}"
    );
    assert!(
        diagnostic.contains("(run_trusted): statically eligible"),
        "{diagnostic}"
    );
    assert!(diagnostic.contains("[compiler-checks]"), "{diagnostic}");
    assert!(
        diagnostic.contains("[trusted-assumption] embedding run_trusted"),
        "{diagnostic}"
    );
    assert!(
        diagnostic.contains("not a compiler or kernel proof"),
        "{diagnostic}"
    );
    let rust = fs::read_to_string(dir.join("out/src/lib.rs")).unwrap();
    let facade = rust.split("pub mod api").nth(1).unwrap();
    assert!(facade.contains("pub fn run_trusted("));
    assert!(facade.contains("TrustedBudgetHost"));
    assert!(!facade.contains("pub fn sum("));
    fs::write(
        dir.join("Tauto.eure"),
        r#"rust { exports = [] nonresuming { entries { run_trusted = "run" } } }"#,
    )
    .unwrap();
    let rejected = emit(&dir, true);
    assert!(!rejected.status.success());
    assert!(String::from_utf8_lossy(&rejected.stderr).contains("unknown or unselected export run"));
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn ordinary_program_emission_keeps_its_runtime_guard() {
    let dir = directory("program");
    fs::write(
        dir.join("input.taut"),
        r#"let result := handle { budget(steps: 0) { 42 } } with { exceeded(info), k => -1 }
perform show("result", result)"#,
    )
    .unwrap();
    let ordinary = emit(&dir, false);
    assert!(
        ordinary.status.success(),
        "{}",
        String::from_utf8_lossy(&ordinary.stderr)
    );
    let original = fs::read_to_string(dir.join("out/src/lib.rs")).unwrap();
    assert!(original.contains("can_run_nonresuming"));
    assert!(emit(&dir, true).status.success());
    assert_eq!(
        original,
        fs::read_to_string(dir.join("out/src/lib.rs")).unwrap()
    );
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn library_diagnostics_compose_with_build_timing_observers() {
    let dir = directory("timings");
    fs::write(
        dir.join("Tauto.eure"),
        r#"rust { exports = ["run"] nonresuming { entries { run_trusted = "run" } } }"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args([
            "build",
            "--emit",
            "rust",
            "--explain-budget",
            "--timings=json",
            "-o",
        ])
        .arg(dir.join("out"))
        .arg(dir.join("input.taut"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("(run_trusted): statically eligible"));
    assert!(stderr.contains("[trusted-assumption]"));
    let report: serde_json::Value = serde_json::from_str(stderr.lines().last().unwrap()).unwrap();
    assert_eq!(report["kind"], "tauto.build.timings");
    assert_eq!(report["status"], "ok");
    let phases = report["phases"].as_array().unwrap();
    for name in ["parse_expand", "check", "lower", "codegen", "write"] {
        assert!(phases.iter().any(|phase| phase["name"] == name), "{report}");
    }
    fs::remove_dir_all(dir).unwrap();
}
