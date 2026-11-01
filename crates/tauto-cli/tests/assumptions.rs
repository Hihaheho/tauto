use std::path::PathBuf;
use std::process::{Command, Output};

const SOURCE: &str = "extern {
  fn shout(&t: Text): Text
}
fn loud(&t: Text): Text { shout(t) }
fn louder(&t: Text): Text { loud(t) }
fn quiet(n: Nat): Nat { n }
axiom em(P: Prop): P ∨ ¬P
theorem not_not(P: Prop, n: ¬¬P): P {
  ?h
}
theorem uses_em(P: Prop): P ∨ ¬P {
  em(P)
}
";

fn file() -> PathBuf {
    let path = std::env::temp_dir().join(format!("tauto-assumptions-{}.taut", std::process::id()));
    std::fs::write(&path, SOURCE).unwrap();
    path
}
fn cli(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(args)
        .output()
        .unwrap()
}

#[test]
fn lists_axioms_externs_and_holes() {
    let path = file();
    let out = cli(&["assumptions", path.to_str().unwrap()]);
    let text = String::from_utf8_lossy(&out.stdout);
    // Only a hole is left: 3, as `check`.
    assert_eq!(out.status.code(), Some(3), "{text}");
    assert!(
        text.contains("louder (skipped)\n  axioms:  none\n  externs: shout\n"),
        "{text}"
    );
    assert!(
        text.contains("quiet (ok)\n  axioms:  none\n  externs: none\n"),
        "{text}"
    );
    assert!(text.contains("uses_em (ok)\n  axioms:  em\n"), "{text}");
    assert!(text.contains("not_not (incomplete)"), "{text}");
    assert!(text.contains("  holes:   ?h\n"), "{text}");

    let out = cli(&["assumptions", path.to_str().unwrap(), "uses_em", "--json"]);
    assert!(out.status.success());
    assert_eq!(
        String::from_utf8_lossy(&out.stdout).trim(),
        r#"[{"name":"uses_em","status":"ok","axioms":["em"],"externs":[],"holes":[],"uses_incomplete":[]}]"#
    );

    let out = cli(&["assumptions", path.to_str().unwrap(), "missing"]);
    assert_eq!(out.status.code(), Some(1));
    let _ = std::fs::remove_file(path);
}
