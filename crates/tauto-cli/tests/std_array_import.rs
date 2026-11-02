//! A file that imports `std::Array` checks: the decidable equality the
//! standard library's `Array` lists after its sort is named with the type.
use std::fs;
use std::process::Command;

#[test]
fn importing_std_array_checks_its_listed_equality() {
    let root = std::env::temp_dir().join(format!("tauto-std-array-import-{}", std::process::id()));
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("Tauto.eure"), "package { name = \"rp\" }\n").unwrap();
    fs::write(
        root.join("src/a.taut"),
        "import std::Array\nfn f(a: Array(Nat)): Array(Nat) { a }\n",
    )
    .unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(&root)
        .args(["check", "src/a.taut"])
        .output()
        .unwrap();
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let _ = fs::remove_dir_all(&root);
    assert!(out.status.success(), "{text}");
    assert!(!text.contains("FAILED"), "{text}");
}
