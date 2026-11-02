//! Native checker comparison with matched process, file-I/O and output boundaries.
//! Match the generated crate's release settings with
//! `CARGO_PROFILE_BENCH_LTO=thin cargo bench --manifest-path tools/selfhost-harness/Cargo.toml --bench compiler -- [--samples N] [--filter TEXT]`.
//! `--native PATH` reuses an explicitly supplied native nibcheck executable.
//! Each measured sample is a fresh process. The first sample is reported separately;
//! subsequent samples warm filesystem caches, not process-local checker state.

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::time::{Duration, Instant};

use selfhost_harness::{assert_same_dump, corpus, materialize, root};

mod support;

fn report(mode: &str, source: &str) -> String {
    // Differential tests represent a rejected or unreadable input as `error`.
    std::panic::catch_unwind(|| {
        let program = tauto::surface::parse_program_as_written(source).ok()?;
        match mode {
            "--rows" => Some(tauto::rows::dump_rows(&tauto::rows::check_program_rows(
                &program,
            ))),
            "--types" => Some(tauto::types::dump_types(&tauto::types::check_program(
                &program,
            ))),
            "--lin" => tauto::lin::check_lin_program(&program)
                .ok()
                .map(|r| tauto::lin::dump_lin(&r)),
            _ => panic!("unknown analysis: {mode}"),
        }
    })
    .ok()
    .flatten()
    .unwrap_or_else(|| "error\n".into())
}

fn rust_worker(args: &[String]) {
    let [mode, prelude, paths @ ..] = args else {
        panic!("worker needs MODE PRELUDE FILE...")
    };
    // Rust embeds this prelude. Check the file supplied to the other implementation
    // rather than silently benchmarking different standard libraries.
    assert_eq!(
        std::fs::read_to_string(prelude).unwrap(),
        tauto::nibstd::PRELUDE
    );
    std::panic::set_hook(Box::new(|_| {}));
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for path in paths {
        let source = std::fs::read_to_string(path).unwrap();
        writeln!(out, "== {path}").unwrap();
        write!(out, "{}", report(mode, &source)).unwrap();
    }
}

fn build_tote() -> PathBuf {
    let out = Command::new(env!("CARGO"))
        .current_dir(root())
        .args([
            "run",
            "-q",
            "--release",
            "-p",
            "tauto-cli",
            "--",
            "build",
            "--release",
            "totes/nibcheck",
        ])
        .output()
        .expect("cargo");
    assert!(
        out.status.success(),
        "tauto build: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).unwrap();
    let path = PathBuf::from(stdout.lines().last().expect("binary path"));
    if path.is_absolute() {
        path
    } else {
        root().join(path)
    }
}

fn run(bin: &std::path::Path, worker: bool, flag: &str, paths: &[String]) -> (Duration, Output) {
    let mut command = Command::new(bin);
    if worker {
        command.arg("--rust-worker");
    }
    command
        .env("TAUTO_STEP_LIMIT", "1000000000000")
        .arg(flag)
        .args(paths);
    let start = Instant::now();
    let out = command.output().expect("checker process");
    let elapsed = start.elapsed();
    assert!(
        out.status.success(),
        "{flag}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        out.stderr.is_empty(),
        "{flag} stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    (elapsed, out)
}

fn option(args: &[String], name: &str) -> Option<String> {
    args.iter()
        .position(|a| a == name)
        .map(|i| args.get(i + 1).expect("missing option value").clone())
}

fn main() {
    // Match the generated runtime's default stack reservation.
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(real_main)
        .unwrap()
        .join()
        .unwrap();
}

fn real_main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.first().is_some_and(|a| a == "--rust-worker") {
        rust_worker(&args[1..]);
        return;
    }
    let mut index = 0;
    while index < args.len() {
        match args[index].as_str() {
            "--samples" | "--filter" | "--native" | "--analysis" => {
                assert!(index + 1 < args.len(), "missing value for {}", args[index]);
                index += 2;
            }
            "--bench" => index += 1,
            flag => panic!(
                "unknown option: {flag}; use --samples N, --filter TEXT, --native PATH, --analysis rows|types|lin"
            ),
        }
    }
    let samples: usize = option(&args, "--samples")
        .map(|s| s.parse().expect("sample count"))
        .unwrap_or(10);
    assert!(samples >= 2, "at least two warm-cache samples required");
    let filter = option(&args, "--filter").unwrap_or_default();
    let inputs: Vec<_> = corpus()
        .into_iter()
        .filter(|(name, _)| name.contains(&filter))
        .collect();
    assert!(!inputs.is_empty(), "empty corpus selection");
    let mut all = vec![("prelude".into(), tauto::nibstd::PRELUDE.into())];
    all.extend(inputs.iter().cloned());
    let m = materialize("bench", &all);
    let bin = option(&args, "--native")
        .map(PathBuf::from)
        .unwrap_or_else(build_tote);
    let host = std::env::current_exe().unwrap();
    println!(
        "{} inputs; {} bytes; filter={filter:?}; {samples} warm-filesystem samples; fresh process each time",
        inputs.len(),
        inputs.iter().map(|(_, s)| s.len()).sum::<usize>()
    );
    println!("Native Tauto: {}; Rust: {}", bin.display(), host.display());
    println!(
        "| analysis | Rust first s | Tauto first s | Rust median / p95 s | Tauto median / p95 s | median ratio |"
    );
    println!("|---|---:|---:|---:|---:|---:|");
    let analysis = option(&args, "--analysis");
    assert!(
        analysis
            .as_deref()
            .is_none_or(|a| matches!(a, "rows" | "types" | "lin")),
        "invalid analysis"
    );
    for flag in ["--rows", "--types", "--lin"]
        .into_iter()
        .filter(|flag| analysis.as_deref().is_none_or(|a| a == &flag[2..]))
    {
        let (first_r, expected) = run(&host, true, flag, &m.paths);
        let (first_t, actual) = run(&bin, false, flag, &m.paths);
        assert_same_dump(
            flag,
            std::str::from_utf8(&expected.stdout).unwrap(),
            std::str::from_utf8(&actual.stdout).unwrap(),
        );
        let mut rust = Vec::new();
        let mut tote = Vec::new();
        for sample in 0..samples {
            // Alternate order to avoid consistently favoring one implementation.
            for native in if sample % 2 == 0 {
                [true, false]
            } else {
                [false, true]
            } {
                let (time, out) = run(if native { &bin } else { &host }, !native, flag, &m.paths);
                assert_same_dump(
                    flag,
                    std::str::from_utf8(&expected.stdout).unwrap(),
                    std::str::from_utf8(&out.stdout).unwrap(),
                );
                if native {
                    tote.push(time)
                } else {
                    rust.push(time)
                }
            }
        }
        let rust_summary = support::summarize(&rust).unwrap();
        let tote_summary = support::summarize(&tote).unwrap();
        let r = rust_summary.median;
        let t = tote_summary.median;
        println!(
            "| {} | {:.6} | {:.6} | {:.6} / {:.6} | {:.6} / {:.6} | {:.3}x |",
            &flag[2..],
            first_r.as_secs_f64(),
            first_t.as_secs_f64(),
            r,
            rust_summary.p95,
            t,
            tote_summary.p95,
            t / r
        );
        println!(
            "samples {flag} rust={:?} tauto={:?}",
            rust.iter().map(Duration::as_secs_f64).collect::<Vec<_>>(),
            tote.iter().map(Duration::as_secs_f64).collect::<Vec<_>>()
        );
    }
}
