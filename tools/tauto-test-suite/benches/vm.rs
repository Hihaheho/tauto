//! Repeated execution of a prebuilt Tauto VM, checked against the evaluator.
//! `cargo bench -p tauto-test-suite --bench vm -- --machine PATH [--filter TEXT]
//! [--samples N] [--prepare-only]`. Inputs remain in target/vm-bench for profiling.

use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const INPUTS: &[&str] = &[
    "fib-27",
    "while-3e6",
    "vec-50000",
    "hashmap-5000",
    "list-2000",
    "direct-effect-2000",
    "resume-effect-2000",
];

fn main() {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap();
}

fn run() {
    let mut machine = None;
    let mut filter = String::new();
    let mut samples = 5;
    let mut prepare = false;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--machine" => machine = Some(PathBuf::from(args.next().expect("machine path"))),
            "--filter" => filter = args.next().expect("filter"),
            "--samples" => samples = args.next().expect("sample count").parse::<usize>().unwrap(),
            "--prepare-only" => prepare = true,
            "--bench" => {}
            _ => panic!("unknown argument: {arg}"),
        }
    }
    assert!(samples > 0);
    let machine = machine.expect("--machine PATH is required");
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let machine = if machine.is_absolute() {
        machine
    } else {
        root.join(machine)
    };
    let work = root.join("target/vm-bench");
    let work = if prepare {
        work
    } else {
        work.join(format!("run-{}", std::process::id()))
    };
    std::fs::create_dir_all(&work).unwrap();
    let selected: Vec<_> = INPUTS
        .iter()
        .filter(|name| name.contains(&filter))
        .collect();
    assert!(!selected.is_empty(), "no matching workload");
    for name in selected {
        let source = case_inputs::fixture_static("backend-bench-inputs.eure", name);
        let package = tauto_nir::compile_javascript(source).expect("compile input");
        let wire = tauto_vm::wire::write(&package).expect("encode input");
        let input = work.join(format!("{name}.cps"));
        std::fs::write(&input, wire).unwrap();
        let flags = vec!["--allow-div".to_owned()];
        let command_args = tauto_vm::wire::machine_args(&flags, &input, None, None, &[]);
        eprintln!("{name}: {} {}", machine.display(), command_args.join(" "));
        if prepare {
            continue;
        }
        let evaluated = tauto::eval::run_with_budget(source, u64::MAX / 4).expect("evaluate input");
        assert!(evaluated.stdout.is_empty() && evaluated.stderr.is_empty());
        assert_eq!(evaluated.exit.unwrap_or(0), 0);
        let expected = evaluated
            .outputs
            .iter()
            .map(|(n, v)| format!("{n} = {v}\n"))
            .collect::<String>();
        let mut times = Vec::new();
        for iteration in 0..=samples {
            let out_path = work.join(format!("{name}.stdout"));
            let err_path = work.join(format!("{name}.stderr"));
            let start = Instant::now();
            let mut child = Command::new(&machine)
                .args(&command_args)
                .stdin(Stdio::null())
                .stdout(std::fs::File::create(&out_path).unwrap())
                .stderr(std::fs::File::create(&err_path).unwrap())
                .spawn()
                .expect("start machine");
            let status = loop {
                if let Some(status) = child.try_wait().unwrap() {
                    break status;
                }
                if start.elapsed() > Duration::from_secs(180) {
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!("{name}: exceeded 180 seconds");
                }
                std::thread::sleep(Duration::from_millis(1));
            };
            let elapsed = start.elapsed();
            let stderr = std::fs::read_to_string(err_path).unwrap();
            assert!(status.success(), "{name}: {status}: {stderr}");
            assert!(stderr.is_empty(), "{name}: {stderr}");
            assert_eq!(
                std::fs::read_to_string(out_path).unwrap(),
                expected,
                "{name}"
            );
            if iteration > 0 {
                times.push(elapsed.as_secs_f64() * 1000.0);
            }
        }
        times.sort_by(f64::total_cmp);
        println!(
            "{name}: median_ms={:.3} samples_ms={times:?}",
            times[times.len() / 2]
        );
    }
}

/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn fixture_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
            ("backend-bench-inputs.eure", "vec-50000") => {
                r#"var v := Vec::new()
var i := 0
while i < 50000 {
  Vec::push(&mut v, i)
  i := i + 1
}
var s := 0
var j := 0
while j < 50000 {
  match Vec::get(&v, j) {
    Some(x) => { s := s + x }
    None => #()
  }
  j := j + 1
}
perform show("s", s)
"#
            }
            ("backend-bench-inputs.eure", "list-2000") => {
                r#"fn build(n: i64): List(i64) { if n == 0 { Nil } else { Cons(n, build(n - 1)) } }
fn sum(xs: List(i64)): i64 {
  match xs {
    Nil => 0
    Cons(x, r) => x + sum(r)
  }
}
var k := 0
var t := 0
while k < 20 {
  t := t + sum(build(2000))
  k := k + 1
}
perform show("t", t)
"#
            }
            ("backend-bench-inputs.eure", "while-3e6") => {
                r#"var i := 0
var s := 0
while i < 3000000 {
  s := s + mod(i, 7)
  i := i + 1
}
perform show("s", s)
"#
            }
            ("backend-bench-inputs.eure", "hashmap-5000") => {
                r#"var m := HashMap::new()
var i := 0
while i < 5000 {
  HashMap::insert(&mut m, Text::of_u64(i), i)
  i := i + 1
}
var s := 0
var j := 0
while j < 5000 {
  match HashMap::get(&m, &Text::of_u64(j)) {
    Some(x) => { s := s + x }
    None => #()
  }
  j := j + 1
}
perform show("s", s)
"#
            }
            ("backend-bench-inputs.eure", "fib-27") => {
                r#"fn fib(n: i64): i64 { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }
perform show("fib", fib(27))
"#
            }
            ("backend-bench-inputs.eure", "direct-effect-2000") => {
                r#"effect tick(n: i64): i64 direct
fn go(n: i64, acc: i64): i64 ! {tick, Div} {
  if n == 0 { acc } else {
    let v := perform tick(n)
    go(n - 1, acc + v)
  }
}
let r := handle { go(2000, 0) } with {
  tick(n), k => k(n)
}
perform show("r", r)
"#
            }
            ("backend-bench-inputs.eure", "resume-effect-2000") => {
                r#"effect tick(n: i64): i64
fn go(n: i64, acc: i64): i64 ! {tick, Div} {
  if n == 0 { acc } else {
    let v := perform tick(n)
    go(n - 1, acc + v)
  }
}
let r := handle { go(2000, 0) } with {
  tick(n), k => k(n)
}
perform show("r", r)
"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn fixture(file: &str, name: &str) -> String {
        fixture_static(file, name).to_string()
    }
}
