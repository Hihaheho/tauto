//! A program that holds a long constant starts running promptly.
use std::{fs, process::Command, time::Duration, time::Instant};

// Each constructor of a long list is visited from every enclosing one before
// the program runs. Its value is computed once, so this stays linear: 400
// items took about a minute when every visit followed the whole tail again.
//
// The first run after `tauto` is rebuilt also builds the machine the program
// runs on, which takes longer than the limit by itself. That is paid once, not
// by the program, so a short program runs first and only the second run is
// timed.
#[test]
fn a_long_constant_list_does_not_delay_the_run() {
    let dir = std::env::temp_dir().join(format!("tauto-constant-data-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let items: Vec<String> = (0..400).map(|i| format!("\"r{i}\"")).collect();
    let file = dir.join("main.taut");
    fs::write(
        &file,
        format!(
            "let rules := [{}]\nlet main := perform show(\"r\", \"x\")\n",
            items.join(", ")
        ),
    )
    .unwrap();
    let warm = dir.join("warm.taut");
    fs::write(&warm, "let main := perform show(\"w\", \"x\")\n").unwrap();
    let run = |file: &std::path::Path| {
        Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("run")
            .arg(file)
            .output()
            .unwrap()
    };
    let warmed = run(&warm);
    assert!(
        warmed.status.success(),
        "{}",
        String::from_utf8_lossy(&warmed.stderr)
    );
    let started = Instant::now();
    let out = run(&file);
    let elapsed = started.elapsed();
    fs::remove_dir_all(&dir).unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), "r = \"x\"\n");
    assert!(elapsed < Duration::from_secs(20), "took {elapsed:?}");
}
