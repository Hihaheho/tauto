//! The standard library keeps its import lists exact: `tauto check` of the library's tote
//! reports no listed name that a file does not use and no used name its list does not write.
//! It is run twice, so a list that one run accepts and another refuses fails as well.

use std::path::Path;
use std::process::Command;

#[test]
fn std_import_lists_are_exact() {
    let std_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
    for _ in 0..2 {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("check")
            .current_dir(&std_dir)
            .output()
            .expect("tauto runs");
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let wrong: Vec<&str> = text
            .lines()
            .filter(|l| {
                l.contains("but this file does not use it") || l.contains("whose list does not write it")
            })
            .collect();
        assert!(wrong.is_empty(), "import lists of std:\n{}", wrong.join("\n"));
    }
}
