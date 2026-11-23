//! `tauto run` on a file with nothing to run says so and fails, instead of
//! ending with code 0 having done nothing.

use std::process::Command;

#[test]
fn run_without_entry_fails() {
    let dir = std::env::temp_dir().join(format!("tauto-no-entry-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("only_decls.taut");
    std::fs::write(&file, "fn f(x: nat): nat { x }\n").unwrap();
    for backend in ["vm"] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .env("TAUTO_LANG", "en")
            .args(["run", "--backend", backend])
            .arg(&file)
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(2), "{backend}");
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(err.contains("has nothing to run"), "{backend}: {err}");
    }
}
