//! `std/uint.taut`'s and `std/sint.taut`'s arithmetic, and `nat`, run the same on every backend.
use std::{
    path::{Path, PathBuf},
    process::Command,
};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn run(args: &[&str], path: &Path, target: &Path) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_tauto"));
    if args.iter().any(|a| *a == "--tote") {
        let args: Vec<&str> = args.iter().copied().filter(|a| *a != "--tote").collect();
        command.current_dir(path).args(&args).arg(".");
    } else {
        command.args(args).arg(path);
    }
    let out = command.env("TAUTO_TARGET_DIR", target).output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

/// A number at or above 2^63 fits a `u64` and a `nat`: the kernel reads it as
/// one, and so do the checker and the evaluator of the program it runs.
#[test]
fn numbers_at_and_above_two_to_the_63_run_alike_on_every_backend() {
    let dir = std::env::temp_dir().join(format!("tauto-high-numbers-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("main.taut");
    std::fs::write(
        &file,
        "import std::nat\n\
         \n\
         fn half(): Nat {\n  9223372036854775808\n}\n\
         \n\
         fn top(): Nat {\n  18446744073709551615\n}\n\
         \n\
         show(&half())\n\
         show(&top())\n\
         show(&U64::of_nat(top()))\n",
    )
    .unwrap();
    let expected = "\
9223372036854775808
18446744073709551615
18446744073709551615
";
    let target = dir.join("target");
    assert_eq!(run(&["run"], &file, &target), expected);
    assert_eq!(run(&["run", "--backend", "rust"], &file, &target), expected);
    assert_eq!(
        run(&["run", "--backend", "javascript"], &file, &target),
        expected
    );
}
