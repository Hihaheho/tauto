//! `tauto run --backend niri` prints what the program writes to standard
//! output, as `tauto run` does: `show` writes there.

use std::fs;
use std::process::Command;

#[test]
fn niri_prints_what_show_writes() {
    let dir = std::env::temp_dir().join(format!("tauto-niri-stdout-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("main.taut");
    fs::write(&file, "show(&1)\nshow(&\"two\")\n").unwrap();
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("run")
            .args(args)
            .arg(&file)
            .output()
            .unwrap()
    };
    let niri = run(&["--backend", "niri"]);
    let default = run(&[]);
    fs::remove_dir_all(&dir).unwrap();
    assert!(niri.status.success(), "{}", String::from_utf8_lossy(&niri.stderr));
    assert_eq!(String::from_utf8_lossy(&niri.stdout), "1\n\"two\"\n");
    assert_eq!(niri.stdout, default.stdout);
}
