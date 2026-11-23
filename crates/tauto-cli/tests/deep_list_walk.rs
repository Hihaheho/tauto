//! Walking a long list by recursion that is not a tail call stays linear.
//!
//! A server reads a request body as a list of bytes and measures and joins it
//! with functions of this shape (a length, a join). When each
//! call deeper copied the path of the borrow it was handed, a body of 8 KiB
//! took 16 s and one of 1 MiB never got an answer. At 65536 cells the copying
//! machine needed several minutes; a linear one needs a few seconds.
use std::{fs, process::Command, time::Duration, time::Instant};

const CELLS: u64 = 65536;

fn program() -> String {
    program_of(CELLS)
}

fn program_of(cells: u64) -> String {
    format!(
        r#"import std::builtin::os

fn cells(n: u64, acc: List(Nat)): List(Nat) {{
  if n == 0 {{ acc }} else {{ cells(n - 1, Cons(97, acc)) }}
}}

fn len(l: List(Nat)): Nat {{
  match l {{
    Nil => Zero
    Cons(h, t) => Succ(len(t))
  }}
}}

fn join(l: List(Nat), m: List(Nat)): List(Nat) {{
  match l {{
    Nil => m
    Cons(h, t) => Cons(h, join(t, m))
  }}
}}

let joined := join(cells({cells}, Nil), Cons(98, Nil))
show(&len(joined))
"#
    )
}

// `tauto run` runs on the vm unless another backend is named.
fn run(file: &std::path::Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        .arg("run")
        .arg(file)
        .output()
        .unwrap()
}

#[test]
fn a_long_list_is_walked_in_linear_time() {
    let dir = std::env::temp_dir().join(format!("tauto-deep-list-walk-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("main.taut");
    fs::write(&file, program()).unwrap();
    // The first run after a rebuild also builds the machine; only later runs are timed.
    let warm = dir.join("warm.taut");
    fs::write(&warm, "import std::builtin::os\nshow(&0)\n").unwrap();
    let expected = format!("{}\n", CELLS + 1);
    let warmed = run(&warm);
    assert!(
        warmed.status.success(),
        "{}",
        String::from_utf8_lossy(&warmed.stderr)
    );
    let started = Instant::now();
    let out = run(&file);
    let elapsed = started.elapsed();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), expected);
    assert!(elapsed < Duration::from_secs(30), "took {elapsed:?}");
    fs::remove_dir_all(&dir).unwrap();
}

// niri runs a call as a frame of its own list, not on the Rust stack, so it
// has no limit on how deep calls nest: a program the vm runs, it runs too.
// It stopped at 4000 nested calls before. Its ownership check costs more per
// call than the vm, so the list is shorter here.
#[test]
fn niri_runs_calls_nested_deeper_than_4000() {
    let dir = std::env::temp_dir().join(format!("tauto-deep-niri-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("main.taut");
    fs::write(&file, program_of(5000)).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["run", "--backend", "niri"])
        .arg(&file)
        .output()
        .unwrap();
    fs::remove_dir_all(&dir).unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out.stdout), "5001\n");
}
