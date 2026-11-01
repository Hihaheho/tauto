use std::path::PathBuf;
use std::process::Command;

fn proofs() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/proofs.taut")
}
fn elaborate(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        .arg("elaborate")
        .arg(proofs())
        .args(args)
        .output()
        .unwrap()
}

#[test]
fn shows_the_term_the_kernel_checks() {
    let out = elaborate(&["and_swap"]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    // The type arguments `And.right` and `And.left` leave implicit are written out.
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "and_swap := A => B => p => and_intro(B, A, And.right(A, B, p), And.left(A, B, p))\n"
    );
    let out = elaborate(&["compose", "--json"]);
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        text.starts_with(
            r#"[{"name":"compose","term":"A => B => C => f => g => a => g(f(a))","tree":"#
        ),
        "{text}"
    );
    assert!(!elaborate(&["missing"]).status.success());
}
