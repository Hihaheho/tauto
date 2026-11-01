//! The evaluator against the Rust backend on
//! every program of the test suite that says what it shows, and on a few
//! heavier programs of the bench's own.
//!
//! `cargo bench -p tauto-test-suite --bench backend [-- FILTER] [--debug]
//! [--no-suite] [--no-heavy]`
//!
//! For each program: the evaluator's time (parse, check and run), the time to
//! write the Rust crate (`tauto_nir::compile` and `tauto_rustgen`), the time
//! `cargo build` takes (the builds run side by side, so it is only
//! indicative), and the time the built program takes to run (the process, its
//! start included). The times of the evaluator and of the program are medians
//! of several runs taken one at a time, after all the builds.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::time::{Duration, Instant};

use tauto_rustgen::Sources;
use tauto_test_suite::rust_cases;

struct Program {
    name: String,
    source: String,
    shows: Vec<String>,
    heavy: bool,
}

struct Row {
    name: String,
    heavy: bool,
    eval: Duration,
    gen_: Duration,
    build: Duration,
    run: Duration,
}

/// The heavier programs: what the evaluator is slow at.
/// Each entry pairs a benchmark label with the ID of its shared fixture.
const HEAVY: &[(&str, &str)] = &[
    ("fib 27", "fib-27"),
    ("while 3e6", "while-3e6"),
    ("vec 50000", "vec-50000"),
    ("hashmap 5000", "hashmap-5000"),
    ("list 2000 (recursion)", "list-2000"),
    ("direct effect 2000", "direct-effect-2000"),
    ("resume effect 2000", "resume-effect-2000"),
];

fn median(mut v: Vec<Duration>) -> Duration {
    v.sort();
    v[v.len() / 2]
}

/// Runs `f` until it has taken about `budget` in all (at least `min` times
/// unless that takes four times the budget, at most `max`), and gives the
/// median.
fn timed(budget: Duration, min: usize, max: usize, mut f: impl FnMut()) -> Duration {
    let mut times = Vec::new();
    let start = Instant::now();
    while times.is_empty()
        || (times.len() < max
            && (times.len() < min || start.elapsed() < budget)
            && start.elapsed() < budget * 4)
    {
        let t = Instant::now();
        f();
        times.push(t.elapsed());
    }
    median(times)
}

fn ms(d: Duration) -> String {
    format!("{:.2}", d.as_secs_f64() * 1000.0)
}

/// A program built: its binary, and the times to write and to build it.
struct Built {
    bin: PathBuf,
    gen_: Duration,
    build: Duration,
}

fn build_one(p: &Program, work: &Path, target: &Path, release: bool) -> Result<Built, String> {
    let t = Instant::now();
    let package = tauto_nir::compile(&p.source).map_err(|e| format!("{e:?}"))?;
    let bindings = tauto_rustgen::Bindings::resolve(&package, None, None)?;
    let ws = tauto_rustgen::workspace(
        "bench",
        &package,
        &Sources {
            file: "input.taut",
            text: &p.source,
        },
        &bindings,
        &Default::default(),
    );
    let gen_ = t.elapsed();
    let t = Instant::now();
    let built = ws.build("bench", work, target, release)?;
    // The next build in this target overwrites the binary.
    let bin = work.join(format!("run-{}", p.name.replace(['/', ' ', '(', ')'], "_")));
    std::fs::copy(&built, &bin).map_err(|e| e.to_string())?;
    Ok(Built {
        bin,
        gen_,
        build: t.elapsed(),
    })
}

fn run_binary(bin: &Path) -> Result<Vec<String>, String> {
    let out = Command::new(bin).output().map_err(|e| e.to_string())?;
    if !out.status.success() {
        return Err(format!("exit {:?}", out.status.code()));
    }
    Ok(String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::to_string)
        .collect())
}

fn eval_shows(source: &str) -> Result<Vec<String>, String> {
    let outcome = tauto::eval::run_with_budget(source, u64::MAX / 4).map_err(|e| e.to_string())?;
    Ok(outcome
        .outputs
        .iter()
        .map(|(n, v)| format!("{n} = {v}"))
        .collect())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flag = |f: &str| args.iter().any(|a| a == f);
    let filter = args.iter().find(|a| !a.starts_with('-')).cloned();
    let release = !flag("--debug");

    let mut programs = Vec::new();
    if !flag("--no-suite") {
        let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let root = crate_dir.join("../../cases");
        for c in rust_cases(&root).expect("the cases") {
            if c.unimplemented || c.rust_shows.is_some() || c.rust_error.is_some() {
                continue;
            }
            if c.shows.is_none() || c.build.is_some() {
                continue;
            }
            let source = c
                .compilation_source()
                .expect("benchmark source")
                .into_owned();
            let shows = c.shows.expect("output expectation");
            programs.push(Program {
                name: c.name,
                source,
                shows,
                heavy: false,
            });
        }
    }
    if !flag("--no-heavy") {
        for (name, fixture) in HEAVY {
            programs.push(Program {
                name: format!("heavy/{name}"),
                source: case_inputs::fixture("backend-bench-inputs.eure", fixture),
                shows: Vec::new(),
                heavy: true,
            });
        }
    }
    programs.retain(|p| filter.as_ref().is_none_or(|f| p.name.contains(f.as_str())));

    // Builds, side by side.
    let base: PathBuf = std::env::var_os("CARGO_TARGET_TMPDIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
        .join("tauto-bench");
    let threads = std::thread::available_parallelism().map_or(2, |n| n.get().min(4));
    let queue = Mutex::new((0..programs.len()).collect::<Vec<_>>());
    let built: Mutex<Vec<(usize, Result<Built, String>)>> = Mutex::new(Vec::new());
    eprintln!(
        "building {} programs ({})",
        programs.len(),
        if release { "release" } else { "debug" }
    );
    std::thread::scope(|s| {
        for t in 0..threads {
            let (queue, built, base, programs) = (&queue, &built, &base, &programs);
            s.spawn(move || {
                let target = base.join(format!("target-{t}"));
                let work = base.join(format!("work-{t}"));
                loop {
                    let Some(i) = queue.lock().unwrap().pop() else {
                        break;
                    };
                    let _ = std::fs::remove_dir_all(work.join("src"));
                    let r = build_one(&programs[i], &work, &target, release);
                    built.lock().unwrap().push((i, r));
                }
            });
        }
    });
    let mut built = built.into_inner().unwrap();
    built.sort_by_key(|(i, _)| *i);

    // Timings, one at a time.
    let mut rows = Vec::new();
    let mut skipped = Vec::new();
    for (i, b) in built {
        let p = &programs[i];
        eprintln!("timing {}", p.name);
        let b = match b {
            Ok(b) => b,
            Err(e) => {
                skipped.push(format!("{}: {}", p.name, e.lines().next().unwrap_or("")));
                continue;
            }
        };
        let (reference, rust) = match (eval_shows(&p.source), run_binary(&b.bin)) {
            (Ok(a), Ok(b)) => (a, b),
            (Err(e), _) => {
                skipped.push(format!("{}: eval: {e}", p.name));
                continue;
            }
            (_, Err(e)) => {
                skipped.push(format!("{}: run: {e}", p.name));
                continue;
            }
        };
        if reference != rust || (!p.heavy && reference != p.shows) {
            skipped.push(format!(
                "{}: the outputs differ: {reference:?} vs {rust:?}",
                p.name
            ));
            continue;
        }
        let (budget, max) = if p.heavy {
            (Duration::from_secs(5), 5)
        } else {
            (Duration::from_millis(300), 30)
        };
        let eval = timed(budget, 3, max, || {
            let _ = eval_shows(&p.source);
        });
        let run = timed(budget, 5, max, || {
            let _ = run_binary(&b.bin);
        });
        rows.push(Row {
            name: p.name.clone(),
            heavy: p.heavy,
            eval,
            gen_: b.gen_,
            build: b.build,
            run,
        });
    }

    println!("| program | eval ms | rust run ms | speedup | gen ms | build ms |");
    println!("|---|---:|---:|---:|---:|---:|");
    let heavy: Vec<&Row> = rows.iter().filter(|r| r.heavy).collect();
    let suite: Vec<&Row> = rows.iter().filter(|r| !r.heavy).collect();
    let speed = |r: &Row| r.eval.as_secs_f64() / r.run.as_secs_f64().max(1e-9);
    for r in &heavy {
        println!(
            "| {} | {} | {} | {:.1}x | {} | {} |",
            r.name,
            ms(r.eval),
            ms(r.run),
            speed(r),
            ms(r.gen_),
            ms(r.build)
        );
    }
    if !suite.is_empty() {
        let total = |f: fn(&Row) -> Duration| suite.iter().map(|r| f(r)).sum::<Duration>();
        let (eval, run, gen_, build) = (
            total(|r| r.eval),
            total(|r| r.run),
            total(|r| r.gen_),
            total(|r| r.build),
        );
        println!(
            "| **suite total ({} programs)** | {} | {} | {:.1}x | {} | {} |",
            suite.len(),
            ms(eval),
            ms(run),
            eval.as_secs_f64() / run.as_secs_f64().max(1e-9),
            ms(gen_),
            ms(build)
        );
        let mut by_eval: Vec<&&Row> = suite.iter().collect();
        by_eval.sort_by_key(|r| std::cmp::Reverse(r.eval));
        println!("\nSlowest in the evaluator:\n");
        println!("| program | eval ms | rust run ms | speedup |");
        println!("|---|---:|---:|---:|");
        for r in by_eval.iter().take(10) {
            println!(
                "| {} | {} | {} | {:.1}x |",
                r.name,
                ms(r.eval),
                ms(r.run),
                speed(r)
            );
        }
        let faster = suite.iter().filter(|r| r.run < r.eval).count();
        println!(
            "\nThe built program is faster than the evaluator on {faster} of {} programs (a process start is about {} ms).",
            suite.len(),
            ms(median(suite.iter().map(|r| r.run).collect()))
        );
    }
    if !skipped.is_empty() {
        println!("\nLeft out ({}):", skipped.len());
        for s in &skipped {
            println!("- {s}");
        }
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
