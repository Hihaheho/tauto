use std::path::PathBuf;
use std::process::Command;

fn example(dir: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(dir)
}
fn audit(dir: &str, json: bool) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
    // The messages below are the English ones, whatever the language here.
    command.env("TAUTO_LANG", "en");
    command.args(["audit", "--tote"]).arg(example(dir));
    if json {
        command.arg("--json");
    }
    let out = command.output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn lists_externs_and_the_rust_bridge() {
    let text = audit("rust/files", false);
    assert!(
        text.starts_with("files-demo 0.1.0\n  externs:    count_chars, shout\n"),
        "{text}"
    );
    assert!(
        text.contains("  rust:       bridge bridge; crates: none\n"),
        "{text}"
    );
}

#[test]
fn covers_path_dependencies() {
    let text = audit("calc", true);
    assert!(text.contains(r#""name":"calc""#), "{text}");
    assert!(text.contains(r#""name":"compiler""#), "{text}");
    assert!(text.contains(r#""effects":["Div","stdout"]"#), "{text}");
}
