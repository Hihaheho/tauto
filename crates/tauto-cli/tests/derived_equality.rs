//! The decidable equality an inductive lists runs as what is written does: called, and passed
//! as a function value, under `tauto run` and `tauto test`, with no import.
use std::fs;
use std::path::PathBuf;
use std::process::Command;

const SOURCE: &str = r#"import std::prelude::Os

inductive Color: Type => fn Color::beq, theorem Color::beq_refl, theorem Color::beq_sound, theorem Color::deq {
  Red: Color
  Blue: Color
}

fn apply2(f: (Color, Color) -> Bool, a: Color, b: Color): Bool {
  f(a, b)
}

match Bool::and(not(Color::beq(Red, Blue)), apply2(Color::beq, Blue, Blue)) {
  true => perform stdout("ok\n")
  false => perform stdout("wrong\n")
}
"#;

fn fixture(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "tauto-derived-equality-{name}-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("main.taut");
    fs::write(&file, SOURCE).unwrap();
    file
}

fn tauto(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(args)
        .output()
        .unwrap()
}

#[test]
fn run_calls_and_passes_the_generated_equality() {
    let file = fixture("run");
    let out = tauto(&["run", file.to_str().unwrap()]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "{stderr}");
    assert_eq!(String::from_utf8_lossy(&out.stdout), "ok\n", "{stderr}");
}

#[test]
fn test_runs_the_generated_equality() {
    let file = fixture("test");
    let out = tauto(&["test", file.to_str().unwrap()]);
    assert!(
        out.status.success(),
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}
