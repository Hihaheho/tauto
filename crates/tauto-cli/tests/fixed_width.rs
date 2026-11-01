//! `std/UInt.taut`'s and `std/SInt.taut`'s arithmetic, and `nat`, run the same on every backend.
use std::{
    path::{Path, PathBuf},
    process::Command,
};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn run(args: &[&str], path: &Path, target: &Path) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(args)
        .arg(path)
        .env("TAUTO_TARGET_DIR", target)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

#[test]
fn fixed_width_example_runs_alike_on_every_backend() {
    let example = root().join("examples/fixed-width");
    let target = std::env::temp_dir().join(format!("tauto-fixed-width-{}", std::process::id()));
    let expected = "\
step = Some(255)
overflow = None
bump = 255
sub = None
mul = Some(4294967295)
mul_overflow = None
u64_add = Some(9223372036854775807)
u64_mul = Some(4611686018427387904)
u64_mul_overflow = None
caught = None
saturated = 255
fits = 255
wrap_add = 0
wrap_sub = 4294967295
wrap_mul = 0
nat = 73786976294838206464
i32_add_overflow = None
i32_mul = Some(-2147483648)
i32_mul_overflow = None
i64_sub = Some(-9223372036854775808)
i64_sub_overflow = None
signed_kept = 2147483647
signed_step = 2147483640
u64_top = 18446744073709551615
u64_high = 18446744073709551614
nat_literal = 36893488147419103233
";
    assert_eq!(run(&["run", "--tote"], &example, &target), expected);
    assert_eq!(
        run(&["run", "--backend", "rust"], &example, &target),
        expected
    );
    assert_eq!(
        run(&["run", "--backend", "javascript"], &example, &target),
        expected
    );
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
        "import std::Nat\n\
         \n\
         fn half(): Nat {\n  9223372036854775808\n}\n\
         \n\
         fn top(): Nat {\n  18446744073709551615\n}\n\
         \n\
         perform show(\"half\", half())\n\
         perform show(\"top\", top())\n\
         perform show(\"u64\", U64::of_nat(top()))\n",
    )
    .unwrap();
    let expected = "\
half = 9223372036854775808
top = 18446744073709551615
u64 = 18446744073709551615
";
    let target = dir.join("target");
    assert_eq!(run(&["run"], &file, &target), expected);
    assert_eq!(run(&["run", "--backend", "rust"], &file, &target), expected);
    assert_eq!(
        run(&["run", "--backend", "javascript"], &file, &target),
        expected
    );
}
