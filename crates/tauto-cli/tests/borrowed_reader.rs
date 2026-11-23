//! A reader that walks borrowed lists runs in time that grows with the work it
//! does, not with how deep the borrows go or how large the program is.
use std::{fs, path::Path, process::Command, time::Duration, time::Instant};

// `fixtures/borrowed-reader/main.taut` reads 160 statements `kN = "..."` the
// way a hand-written parser does: each reader takes the length of what is left
// as its fuel, and that length is counted through a borrow of the list, one
// step deeper on each call. On the machine (`--backend vm`) a borrow named its
// place by the path from the cell and every read walked that path again, so
// the run took more than five minutes; it now reads each step at once. On
// JavaScript an environment was an object keyed by binding ids, which gave
// each call an element store as long as the largest id.
const SOURCE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/borrowed-reader/main.taut"
);

fn tauto(args: &[&str], file: &Path) -> std::process::Output {
    tauto_with(args, file, None)
}

fn tauto_with(args: &[&str], file: &Path, vm: Option<&str>) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
    if let Some(vm) = vm {
        command.env("TAUTO_VM", vm);
    }
    command.args(args).arg(file).output().unwrap()
}

fn work_dir(name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "tauto-borrowed-reader-{name}-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    dir
}

// The machine of `tauto-vm` (`TAUTO_VM=rust`) named a borrowed part the same
// way, copying the path at each step down and walking it at each read: the
// run took about two minutes.
#[test]
fn a_reader_over_borrowed_lists_runs_promptly_on_the_rust_machine() {
    let started = Instant::now();
    let out = tauto_with(&["run", "--backend", "vm"], Path::new(SOURCE), Some("rust"));
    let elapsed = started.elapsed();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), "2930");
    assert!(elapsed < Duration::from_secs(30), "took {elapsed:?}");
}

// The first run after `tauto` is rebuilt also builds the machine, which is not
// the program's time, so a short program runs first and only the second run
// is timed.
#[test]
fn a_reader_over_borrowed_lists_runs_promptly_on_the_machine() {
    let dir = work_dir("vm");
    let warm = dir.join("warm.taut");
    fs::write(&warm, "let main := show(&\"x\")\n").unwrap();
    let warmed = tauto(&["run", "--backend", "vm"], &warm);
    assert!(
        warmed.status.success(),
        "{}",
        String::from_utf8_lossy(&warmed.stderr)
    );
    let started = Instant::now();
    let out = tauto(&["run", "--backend", "vm"], Path::new(SOURCE));
    let elapsed = started.elapsed();
    fs::remove_dir_all(&dir).unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), "2930");
    assert!(elapsed < Duration::from_secs(60), "took {elapsed:?}");
}

#[test]
fn a_reader_over_borrowed_lists_runs_promptly_on_javascript() {
    let dir = work_dir("js");
    let built = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["build", "--backend", "javascript", "-o"])
        .arg(&dir)
        .arg(SOURCE)
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let started = Instant::now();
    let out = Command::new("node")
        .arg(dir.join("main.mjs"))
        .output()
        .unwrap();
    let elapsed = started.elapsed();
    fs::remove_dir_all(&dir).unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), "2930");
    assert!(elapsed < Duration::from_secs(30), "took {elapsed:?}");
}
