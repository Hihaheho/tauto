//! `tauto check FILE` for a file that only proves things: what it declares is checked as proofs,
//! and nothing in it is a program that has to extract.
use std::{fs, path::PathBuf, process::Command};

struct Fixture(PathBuf);
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn check(name: &str, source: &str) -> (bool, String) {
    let dir = std::env::temp_dir().join(format!("tauto-check-proof-{name}-{}", std::process::id()));
    let fixture = Fixture(dir.clone());
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("proof.taut"), source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["check", "proof.taut"])
        .current_dir(&fixture.0)
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&output.stdout).to_string()
        + &String::from_utf8_lossy(&output.stderr);
    (output.status.success(), text)
}

#[test]
fn a_proof_that_rests_on_an_axiom_checks() {
    let (ok, text) = check(
        "axiom",
        "axiom em(P: Prop): P ∨ ¬P\n\n\
         theorem not_not(P: Prop, n: ¬¬P): P {\n  \
           Or::elim(em(P), p => p, np => False::elim(n(np)))\n}\n",
    );
    assert!(ok, "{text}");
    assert!(!text.contains("uses axioms"), "{text}");
}

#[test]
fn an_inductive_over_universe_levels_checks() {
    let (ok, text) = check(
        "ubox",
        "inductive UBox(u: Level, A: Type(u)): Type(u) {\n  ubox(value: A): UBox(u, A)\n}\n\n\
         theorem small_box(): UBox(0, Nat) {\n  ubox(<u: 0, A: Nat>, 3)\n}\n",
    );
    assert!(ok, "{text}");
    assert!(!text.contains("did not check"), "{text}");
}

#[test]
fn a_wrong_proof_over_an_axiom_still_fails() {
    let (ok, text) = check(
        "wrong",
        "axiom em(P: Prop): P ∨ ¬P\n\ntheorem bad(): False { em(False) }\n",
    );
    assert!(!ok, "{text}");
}
