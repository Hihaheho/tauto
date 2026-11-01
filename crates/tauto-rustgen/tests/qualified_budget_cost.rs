//! Native facade costs, with correctness counters separate from wall time.

use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::process::Command;

use tauto_rustgen::{Bindings, Options, Sources, Workspace, workspace};

const SIZE: u64 = 500_000;
const REPEATS: u64 = 4;
const SAMPLES: usize = 9;
const WORKLOADS: [&str; 3] = ["callback", "extern", "combined"];

fn source_source() -> &'static str {
    r#"
effect stop(total: u64): Never resume 0
extern { fn native(value: u64): u64 }
fn sum(&read: (u64) -> u64, size: u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size { total := total + read(index)
    index := index + 1 }
  total
}
fn ext_sum(size: u64): u64 ! {Div} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size { total := total + native(index)
    index := index + 1 }
  total
}
fn scan(&read: (u64) -> u64, size: u64, stop_at: u64): u64 ! {Div, stop} {
  var index: u64 := 0
  var total: u64 := 0
  while index < size {
    if index == stop_at { perform stop(total) }
    total := total + native(read(index))
    index := index + 1
  }
  total
}
fn callback_run(steps: i64, &read: (u64) -> u64, size: u64): Result(u64, Text) {
  handle { budget(steps: steps) { Ok(sum(&(index) => read(index), size)) } } with {
    exceeded(info), k => Err("exhausted")
  }
}
fn extern_run(steps: i64, size: u64): Result(u64, Text) {
  handle { budget(steps: steps) { Ok(ext_sum(size)) } } with {
    exceeded(info), k => Err("exhausted")
  }
}
fn combined_run(steps: i64, &read: (u64) -> u64, size: u64, stop_at: u64): Result(u64, Text) {
  handle { budget(steps: steps) { Ok(scan(&(index) => read(index), size, stop_at)) } } with {
    stop(total) => Ok(total)
    exceeded(info), k => Err("exhausted")
  }
}
"#
}

const MANIFEST: &str = r#"rust {
  extern { native = "host::native" }
  nonresuming {
    extern { native = "closed-host-v1" }
    entries {
      callback_trusted = "callback_run"
      extern_trusted = "extern_run"
      combined_trusted = "combined_run"
    }
  }
}"#;

const HOST: &str = r#"
pub mod host {
    #[inline(never)]
    pub fn native(value: u64) -> u64 {
        // EXTERN_COUNTER
        value + 1
    }
}
"#;

const MAIN: &str = r#"
use qualified_budget_cost::api;
use std::hint::black_box;
const QUALIFIED: bool = QUALIFIED_VALUE;
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let workload = args[1].as_str();
    let size: u64 = args[2].parse().unwrap();
    let repeats: u64 = args[3].parse().unwrap();
    assert!((2..=1_000_000).contains(&size));
    assert!((1..=16).contains(&repeats));
    let steps = black_box((size + 16) as i64);
    let stop_at = black_box(size - 1);
    let size = black_box(size);
    let token = tauto_rt::budget_contract::TrustedBudgetHost::assert_contract();
    let read = |value: u64| {
        // CALLBACK_COUNTER
        value + 1
    };
    let read = black_box(&read as &dyn Fn(u64) -> u64);
    let mut checksum = 0_u64;
    let started = std::time::Instant::now();
    for _ in 0..repeats {
        let answer = match (workload, QUALIFIED) {
            ("callback", false) => api::callback_run(steps, read, size),
            ("callback", true) => api::callback_trusted(&token, steps, read, size),
            ("extern", false) => api::extern_run(steps, size),
            ("extern", true) => api::extern_trusted(&token, steps, size),
            ("combined", false) => api::combined_run(steps, read, size, stop_at),
            ("combined", true) => api::combined_trusted(&token, steps, read, size, stop_at),
            _ => panic!("unknown workload"),
        };
        checksum += black_box(answer.unwrap());
    }
    let elapsed_ns = started.elapsed().as_nanos();
    println!("checksum={checksum} elapsed_ns={elapsed_ns}");
    // COUNTER_REPORT
}
"#;

#[test]
#[ignore = "builds native release executables and requires an isolated timing window"]
fn ordinary_and_qualified_facade_costs() {
    let package = tauto_nir::compile_with(source_source(), true).unwrap();
    let manifest = tauto::manifest::parse(MANIFEST, Path::new("Tauto.eure")).unwrap();
    let bindings = Bindings::resolve(&package, Some(&manifest), None).unwrap();
    let sources = Sources {
        file: "qualified-cost.taut",
        text: source_source(),
    };
    let reports = tauto_rustgen::budget_diagnostics(&package, &sources, &bindings);
    for workload in WORKLOADS {
        let qualified = format!("{workload}_trusted");
        assert!(
            reports
                .iter()
                .any(|r| r.variant == qualified && r.eligible())
        );
        let ordinary = format!("{workload}_run");
        assert!(
            reports
                .iter()
                .any(|r| { r.variant == "ordinary" && r.function == ordinary && !r.eligible() })
        );
    }
    let base = workspace(
        "qualified-budget-cost",
        &package,
        &sources,
        &bindings,
        &Options::default(),
    );
    let root = std::env::var_os("TAUTO_QUALIFIED_BENCH_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::env::temp_dir().join("tauto-qualified-budget-cost"));
    std::fs::create_dir_all(&root).unwrap();
    let targets = std::env::var_os("TAUTO_NATIVE_TEST_TARGET")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join("targets"));
    let timing_only = std::env::var_os("TAUTO_QUALIFIED_TIMING_ONLY").is_some();
    let build_only = std::env::var_os("TAUTO_NONRESUMING_BUILD_ONLY").is_some();
    assert!(!(timing_only && build_only));
    let mut timed = Vec::new();
    for instrument in [true, false] {
        for qualified in [false, true] {
            let name = format!(
                "{}-{}",
                if qualified { "qualified" } else { "ordinary" },
                if instrument { "counts" } else { "time" }
            );
            let mut variant = Workspace {
                files: base.files.clone(),
            };
            file(&mut variant, "src/lib.rs").push_str(HOST);
            *file(&mut variant, "src/main.rs") =
                MAIN.replace("QUALIFIED_VALUE", if qualified { "true" } else { "false" });
            if instrument {
                instrument_counts(&mut variant);
            }
            let package_name = format!("qualified-budget-cost-{name}");
            replace_once(
                file(&mut variant, "Cargo.toml"),
                "name = \"qualified-budget-cost\"",
                &format!("name = \"{package_name}\""),
            );
            replace_once(
                file(&mut variant, "src/main.rs"),
                "qualified_budget_cost::api",
                &format!("{}::api", package_name.replace('-', "_")),
            );
            let identity = format!("{:016x}", fingerprint(&variant.files));
            let directory = root.join(format!("{identity}-{name}"));
            let binary = directory.join("retained-bin");
            let hash_file = directory.join("binary.fingerprint");
            if timing_only {
                for (path, text) in &variant.files {
                    assert_eq!(
                        std::fs::read_to_string(directory.join(path)).unwrap(),
                        *text
                    );
                }
                let bytes = std::fs::read(&binary).unwrap();
                assert_eq!(
                    std::fs::read_to_string(&hash_file).unwrap(),
                    format!("{:016x}\n", fingerprint(&bytes)),
                    "prepared executable changed"
                );
            } else {
                let built = build_release(
                    &variant,
                    &package_name,
                    &directory,
                    &targets.join(format!("{identity}-{name}")),
                );
                std::fs::copy(built, &binary).unwrap();
                std::fs::write(
                    hash_file,
                    format!("{:016x}\n", fingerprint(&std::fs::read(&binary).unwrap())),
                )
                .unwrap();
            }
            println!("{name}: retained executable {}", binary.display());
            if instrument {
                for workload in WORKLOADS {
                    let (_, counts) = execute(&binary, workload, true);
                    let counts = counts.unwrap();
                    let calls = REPEATS
                        * if workload == "combined" {
                            SIZE - 1
                        } else {
                            SIZE
                        };
                    let expected = [
                        if qualified { REPEATS } else { 0 },
                        if qualified { 0 } else { REPEATS },
                        REPEATS * (SIZE + 1),
                        if qualified && workload == "combined" {
                            REPEATS
                        } else {
                            0
                        },
                        if workload == "extern" { 0 } else { calls },
                        if workload == "callback" { 0 } else { calls },
                    ];
                    assert_eq!(counts, expected, "{name}/{workload}");
                    println!(
                        "{name}/{workload}: fast,future,ticks,abort,callback,extern={counts:?}"
                    );
                }
            } else {
                timed.push(binary);
            }
        }
    }
    if build_only {
        println!("prepared; no wall-time samples collected");
        return;
    }
    let mut rows = String::from("phase\tworkload\tsample\torder\tvariant\telapsed_ns\tchecksum\n");
    for workload in WORKLOADS {
        let mut samples = [Vec::new(), Vec::new()];
        for (index, binary) in timed.iter().enumerate() {
            let (elapsed, _) = execute(binary, workload, false);
            let name = if index == 0 { "ordinary" } else { "qualified" };
            println!("warmup/{workload}/{name}: {elapsed} ns");
            rows.push_str(&format!(
                "warmup\t{workload}\t0\t{index}\t{name}\t{elapsed}\t{}\n",
                checksum(workload)
            ));
        }
        for sample in 0..SAMPLES {
            let order = if sample % 2 == 0 { [0, 1] } else { [1, 0] };
            for (position, index) in order.into_iter().enumerate() {
                let (elapsed, _) = execute(&timed[index], workload, false);
                samples[index].push(elapsed);
                let name = if index == 0 { "ordinary" } else { "qualified" };
                println!(
                    "sample {sample}/{position}/{workload}/{name}: {elapsed} ns checksum={}",
                    checksum(workload)
                );
                rows.push_str(&format!(
                    "sample\t{workload}\t{sample}\t{position}\t{name}\t{elapsed}\t{}\n",
                    checksum(workload)
                ));
            }
        }
        for values in &mut samples {
            values.sort_unstable();
        }
        let ordinary = samples[0][SAMPLES / 2];
        let qualified = samples[1][SAMPLES / 2];
        println!(
            "{workload}: ordinary median {ordinary} ns; qualified median {qualified} ns; ordinary/qualified {:.6}x; checksum={}",
            ordinary as f64 / qualified as f64,
            checksum(workload)
        );
        std::fs::write(root.join("samples.tsv"), &rows).unwrap();
    }
}

fn checksum(workload: &str) -> u64 {
    let value = if workload == "combined" {
        let count = SIZE - 1;
        count * (count + 3) / 2
    } else {
        SIZE * (SIZE + 1) / 2
    };
    value * REPEATS
}

fn execute(binary: &Path, workload: &str, instrumented: bool) -> (u128, Option<[u64; 6]>) {
    let output = Command::new(binary)
        .args([workload, &SIZE.to_string(), &REPEATS.to_string()])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    let fields: Vec<_> = stdout.split_whitespace().collect();
    assert_eq!(fields.len(), 2, "{stdout}");
    assert_eq!(fields[0], format!("checksum={}", checksum(workload)));
    let elapsed = fields[1]
        .strip_prefix("elapsed_ns=")
        .unwrap()
        .parse()
        .unwrap();
    let counts = if instrumented {
        let stderr = String::from_utf8(output.stderr).unwrap();
        let values: Vec<u64> = stderr
            .trim()
            .strip_prefix("COUNTS=")
            .unwrap()
            .split(',')
            .map(|value| value.parse().unwrap())
            .collect();
        Some(values.try_into().unwrap())
    } else {
        assert!(output.stderr.is_empty());
        None
    };
    (elapsed, counts)
}

fn fingerprint(value: &impl Hash) -> u64 {
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hash);
    hash.finish()
}

fn file<'a>(workspace: &'a mut Workspace, path: &str) -> &'a mut String {
    &mut workspace
        .files
        .iter_mut()
        .find(|(name, _)| name == path)
        .unwrap()
        .1
}

fn replace_once(text: &mut String, from: &str, to: &str) {
    assert_eq!(text.matches(from).count(), 1, "unique site: {from}");
    *text = text.replace(from, to);
}

fn instrument_counts(workspace: &mut Workspace) {
    let budget = file(workspace, "tauto-rt/src/budget.rs");
    for (from, to) in [
        (
            "    let result = {",
            "    FAST.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n    let result = {",
        ),
        (
            "    let left = Rc::new(Cell::new(",
            "    FUTURE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n    let left = Rc::new(Cell::new(",
        ),
        (
            "        let out = STACK.with",
            "        TICKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n        let out = STACK.with",
        ),
        (
            "        if self.left.get() == 0 {",
            "        TICKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);\n        if self.left.get() == 0 {",
        ),
        (
            "Err(Interrupted::Abort(abort)) => o::reraise(abort).await,",
            "Err(Interrupted::Abort(abort)) => { ABORT.fetch_add(1, std::sync::atomic::Ordering::Relaxed); o::reraise(abort).await },",
        ),
    ] {
        replace_once(budget, from, to);
    }
    for name in ["FAST", "FUTURE", "TICKS", "ABORT", "CALLBACK", "EXTERN"] {
        budget.push_str(&format!("\npub static {name}: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);\n"));
    }
    // Ghost counters characterize these test paths, not arbitrary host purity.
    replace_once(
        file(workspace, "src/lib.rs"),
        "// EXTERN_COUNTER",
        "tauto_rt::budget::EXTERN.fetch_add(1, std::sync::atomic::Ordering::Relaxed);",
    );
    replace_once(
        file(workspace, "src/main.rs"),
        "// CALLBACK_COUNTER",
        "tauto_rt::budget::CALLBACK.fetch_add(1, std::sync::atomic::Ordering::Relaxed);",
    );
    replace_once(
        file(workspace, "src/main.rs"),
        "// COUNTER_REPORT",
        r#"
    use tauto_rt::budget::{FAST, FUTURE, TICKS, ABORT, CALLBACK, EXTERN};
    use std::sync::atomic::Ordering::Relaxed;
    eprintln!("COUNTS={},{},{},{},{},{}", FAST.load(Relaxed), FUTURE.load(Relaxed), TICKS.load(Relaxed), ABORT.load(Relaxed), CALLBACK.load(Relaxed), EXTERN.load(Relaxed));
"#,
    );
}

fn build_release(workspace: &Workspace, name: &str, directory: &Path, target: &Path) -> PathBuf {
    workspace.write(directory).unwrap();
    let temporary = directory.join("tmp");
    std::fs::create_dir_all(&temporary).unwrap();
    for args in [
        &["generate-lockfile", "--offline"][..],
        &["build", "--release", "--locked", "--offline", "--jobs", "1"][..],
    ] {
        let output = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
            .args(args)
            .arg("--manifest-path")
            .arg(directory.join("Cargo.toml"))
            .current_dir(directory)
            .env("CARGO_TARGET_DIR", target)
            .env("CARGO_NET_OFFLINE", "true")
            .env("CARGO_INCREMENTAL", "0")
            .env("CARGO_PROFILE_RELEASE_DEBUG", "0")
            .env("CARGO_TERM_COLOR", "never")
            .env("TMPDIR", &temporary)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{name} {args:?}\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    target.join("release").join(name)
}
