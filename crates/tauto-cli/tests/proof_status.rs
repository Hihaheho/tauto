use std::process::Command;

#[test]
fn counts_the_declarations_holes_and_axioms() {
    let dir = std::env::temp_dir().join(format!("tauto-proof-status-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("a.taut"),
        "axiom em(P: Prop): P ∨ ¬P\ntheorem uses(P: Prop): P ∨ ¬P {\n  em(P)\n}\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("b.taut"),
        "extern {\n  fn shout(&t: Text): Text\n}\ntheorem t(P: Prop, p: P): P {\n  ?h\n}\n",
    )
    .unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["proof-status", dir.to_str().unwrap(), "--json"])
        .output()
        .unwrap();
    // A hole is left and nothing failed: 3, as `check`.
    assert_eq!(out.status.code(), Some(3));
    assert_eq!(
        String::from_utf8_lossy(&out.stdout).trim(),
        r#"{"files":2,"ok":2,"incomplete":1,"holes":1,"failed":0,"skipped":0,"axioms":["em"],"externs":1,"unread":[]}"#
    );
    std::fs::remove_dir_all(&dir).unwrap();
}
