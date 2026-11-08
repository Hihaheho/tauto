//! Differential fuzzing of the evaluator, the Rust backend and the
//! JavaScript backend: each seed names a random well-typed program
//! (`tauto_test_suite::fuzz`), every backend runs it, and their observations
//! must be the same: the shows in order, and whether the run ends normally or
//! with which run-time error. Interaction programs also compare those events
//! against an independent scalar model, even when all backends agree.
//!
//! `cargo test -p tauto-test-suite --test fuzz -- [<count> [<first seed>]]
//! [eval,rust,javascript]` runs `count` seeds (default 300) from `first seed`
//! (default 0) on the listed backends (default all three). A disagreement is
//! printed with its program and makes the run fail; the seed reproduces it.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::{Duration, Instant};

use tauto_test_suite::fuzz;

/// The default corpus size; the quick profile is an explicit smoke run.
const DEFAULT_COUNT: u64 = 300;

/// What a run is seen to do.
#[derive(Debug, Clone, PartialEq)]
struct Observation {
    shows: Vec<String>,
    /// `None` for a run that ends normally, else the kind of its error.
    error: Option<String>,
}

/// The run-time errors the programs can raise, by the message every backend
/// gives; any other failure keeps its text, which no other backend matches.
fn error_kind(message: &str) -> String {
    for kind in ["the number is too large", "division by zero"] {
        if message.contains(kind) {
            return kind.into();
        }
    }
    format!("other: {}", message.trim())
}

/// The start of the error of a program the front end rejects: the generator
/// wrote a program it should not have.
const REJECTED: &str = "rejected: ";

/// Runs as `tauto run` does: from a file, through the row check.
fn eval_once(text: &str) -> Result<Vec<String>, String> {
    // One directory per call: the workers run at once.
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "tauto-fuzz-eval-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let path = dir.join("main.taut");
    std::fs::write(&path, text).map_err(|e| e.to_string())?;
    let loaded = tauto::program::load(&path);
    let _ = std::fs::remove_dir_all(&dir);
    let loaded = loaded.map_err(|e| format!("{REJECTED}{e}"))?;
    if let Some((error, _)) = loaded.program.errors.first() {
        return Err(format!("{REJECTED}{error}"));
    }
    let got = tauto::eval::run_loaded_with(
        &loaded,
        tauto::eval::DEFAULT_BUDGET,
        tauto::eval::RunOptions::default(),
    )
    .map_err(|e| match e {
        tauto::eval::RunError::Syntax(_)
        | tauto::eval::RunError::Type(_)
        | tauto::eval::RunError::Use(_) => format!("{REJECTED}{e}"),
        e => e.to_string(),
    })?;
    Ok(got
        .outputs
        .iter()
        .map(|(n, v)| format!("{n} = {v}"))
        .collect())
}

/// The evaluator does not return the shows of a run that fails, so the shows
/// before a failure are those of the longest prefix of show lines that runs.
fn eval(program: &fuzz::Program) -> Observation {
    match eval_once(&program.full()) {
        Ok(shows) => Observation { shows, error: None },
        Err(e) => {
            let shows = (0..program.shows.len())
                .rev()
                .find_map(|n| eval_once(&program.text(n)).ok())
                .unwrap_or_default();
            Observation {
                shows,
                error: Some(error_kind(&e)),
            }
        }
    }
}

fn wait(mut child: std::process::Child, limit: Duration) -> Option<std::process::ExitStatus> {
    let start = Instant::now();
    loop {
        if let Some(s) = child.try_wait().unwrap() {
            return Some(s);
        }
        if start.elapsed() > limit {
            let _ = child.kill();
            let _ = child.wait();
            return None;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

fn observed(
    status: Option<std::process::ExitStatus>,
    shows: Vec<String>,
    stderr: &str,
) -> Observation {
    let error = match status {
        None => Some("other: timed out".into()),
        Some(s) if s.success() => None,
        Some(_) => Some(error_kind(stderr)),
    };
    Observation { shows, error }
}

fn rust(text: &str, work: &Path, target: &Path) -> Observation {
    let failed = |e: String| Observation {
        shows: Vec::new(),
        error: Some(format!("other: {e}")),
    };
    let package = match tauto_nir::compile(text) {
        Ok(p) => p,
        Err(e) => return failed(format!("compile: {e:?}")),
    };
    let bindings = match tauto_rustgen::Bindings::resolve(&package, None, None) {
        Ok(b) => b,
        Err(e) => return failed(format!("bindings: {e}")),
    };
    let mut ws = tauto_rustgen::workspace(
        "fuzz",
        &package,
        &tauto_rustgen::Sources {
            file: "input.taut",
            text,
        },
        &bindings,
        &tauto_rustgen::Options::default(),
    );
    // Shows go to their own file, as in `tests/backends/rust.rs`.
    let lib = &mut ws
        .files
        .iter_mut()
        .find(|(p, _)| p == "src/lib.rs")
        .unwrap()
        .1;
    let needle = "\"{name} = {}\"";
    let Some(at) = lib.find(needle) else {
        return failed("cannot locate the generated show handler".into());
    };
    let start = lib[..at].rfind("println").unwrap();
    let end = at + lib[at..].find(';').unwrap() + 1;
    lib.replace_range(
        start..end,
        r#"{
        use std::io::Write;
        let mut output = std::fs::OpenOptions::new().create(true).append(true)
            .open(std::env::var_os("TAUTO_CASE_SHOWS").expect("case show path")).unwrap();
        writeln!(output, "{name} = {}", value.0).unwrap();
    }"#,
    );
    let _ = std::fs::remove_dir_all(work.join("src"));
    let bin = match ws.build("fuzz", work, target, false) {
        Ok(b) => b,
        Err(e) => return failed(format!("build: {e}")),
    };
    let show_path = work.join("shows");
    let err_path = work.join("stderr");
    std::fs::write(&show_path, "").unwrap();
    let child = Command::new(&bin)
        .env("TAUTO_CASE_SHOWS", &show_path)
        .stdout(std::process::Stdio::null())
        .stderr(std::fs::File::create(&err_path).unwrap())
        .spawn()
        .unwrap();
    let status = wait(child, Duration::from_secs(30));
    let shows = std::fs::read_to_string(&show_path)
        .unwrap()
        .lines()
        .map(str::to_string)
        .collect();
    observed(status, shows, &std::fs::read_to_string(&err_path).unwrap())
}

fn javascript(text: &str, dir: &Path) -> Observation {
    let failed = |e: String| Observation {
        shows: Vec::new(),
        error: Some(format!("other: {e}")),
    };
    let package = match tauto_nir::compile_javascript(text) {
        Ok(p) => p,
        Err(e) => return failed(format!("compile: {e:?}")),
    };
    let js = match tauto_jsgen::generate(&package) {
        Ok(js) => js,
        Err(e) => return failed(format!("generate: {e}")),
    };
    let module = dir.join("fuzz.mjs");
    let show_file = dir.join("shows.json");
    let err_file = dir.join("stderr");
    let show_path = serde_json::to_string(&show_file.to_string_lossy()).unwrap();
    let _ = std::fs::remove_file(&show_file);
    std::fs::write(&module, format!("import {{writeFileSync}} from 'node:fs';\n{js}\nconst shows=[]; try {{await run(text => shows.push(text), {{}}, {{args:[], permissions:{{}}, env:process.env, os_print:text => process.stdout.write(text), os_eprint:text => process.stderr.write(text)}});}} catch(e) {{console.error(e.message);process.exitCode=1;}} finally {{writeFileSync({show_path}, JSON.stringify(shows));}}\n")).unwrap();
    let child = Command::new("node")
        .arg(&module)
        .stdout(std::process::Stdio::null())
        .stderr(std::fs::File::create(&err_file).unwrap())
        .spawn()
        .unwrap();
    let status = wait(child, Duration::from_secs(60));
    let shows = std::fs::read_to_string(&show_file)
        .ok()
        .and_then(|t| serde_json::from_str(&t).ok())
        .unwrap_or_default();
    observed(status, shows, &std::fs::read_to_string(&err_file).unwrap())
}

fn observations(
    program: &fuzz::Program,
    backends: &[&str],
    work: &Path,
    target: &Path,
) -> Vec<(String, Observation)> {
    let text = program.full();
    backends
        .iter()
        .map(|&b| {
            let observed = match b {
                "eval" => eval(program),
                "rust" => rust(&text, work, target),
                "javascript" => javascript(&text, work),
                other => panic!("unknown backend {other}"),
            };
            (b.to_string(), observed)
        })
        .collect()
}

// Keep the failing backend set while shrinking; do not replace a semantic
// counterexample with a newly rejected program or a build/infrastructure error.
fn oracle_failures(seen: &[(String, Observation)], expected: &[String]) -> Option<Vec<String>> {
    if seen.iter().any(|(_, o)| o.error.is_some()) {
        return None;
    }
    Some(
        seen.iter()
            .filter(|(_, o)| o.shows != expected)
            .map(|(b, _)| b.clone())
            .collect(),
    )
}

fn main() -> ExitCode {
    tauto_test_suite::with_deep_stack(run)
}

fn run() -> ExitCode {
    let Some(args) = tauto_test_suite::harness_args("fuzz") else {
        return ExitCode::SUCCESS;
    };
    let mut numbers = args.iter().filter_map(|a| a.parse::<u64>().ok());
    let profile = std::env::var("TAUTO_FUZZ_PROFILE").unwrap_or_else(|_| "stress".into());
    let default_count = match profile.as_str() {
        "quick" => 9,
        "stress" => DEFAULT_COUNT,
        other => panic!("unknown TAUTO_FUZZ_PROFILE {other}; use quick or stress"),
    };
    let count = numbers.next().unwrap_or(default_count);
    let interactions = std::env::var_os("TAUTO_FUZZ_INTERACTIONS").is_some();
    let started = Instant::now();
    let first = numbers.next().unwrap_or(0);
    let backends: Vec<&str> = args
        .iter()
        .find(|a| a.parse::<u64>().is_err())
        .map(|a| a.split(',').collect())
        .unwrap_or_else(|| vec!["eval", "rust", "javascript"]);
    let base: PathBuf = std::env::var_os("CARGO_TARGET_TMPDIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
        .join("tauto-fuzz");
    let run_dir = base.join(format!("run-{}", std::process::id()));
    // `TAUTO_FUZZ_FILE=<path>` runs that program instead, to cut a
    // disagreement down by hand.
    let file = std::env::var_os("TAUTO_FUZZ_FILE").map(|p| std::fs::read_to_string(p).unwrap());
    // Explicit oracle input keeps a saved shared-backend bug reproducible.
    // Never infer expectations from an unrelated neighboring file.
    let replay_expected = std::env::var_os("TAUTO_FUZZ_EXPECTED").map(|path| {
        assert!(
            file.is_some(),
            "TAUTO_FUZZ_EXPECTED requires TAUTO_FUZZ_FILE"
        );
        std::fs::read_to_string(path)
            .expect("read TAUTO_FUZZ_EXPECTED")
            .lines()
            .map(str::to_string)
            .collect::<Vec<_>>()
    });
    let (first, count) = if file.is_some() {
        (0, 1)
    } else {
        (first, count)
    };
    let end = first.checked_add(count).expect("seed range overflows u64");
    assert!(count > 0, "count must be positive");
    assert!(!backends.is_empty(), "at least one backend is required");
    let seeds: Vec<u64> = (first..end).collect();
    // Seeds are independent. Each worker builds the generated crates in a work
    // and a target directory of its own (rustc's incremental cache and Cargo's
    // lock allow one build at a time), and the verdicts are printed in seed
    // order.
    let verdicts = tauto_test_suite::parallel_map(
        &seeds,
        |worker| {
            let work = run_dir.join(format!("work-{worker}"));
            std::fs::create_dir_all(&work).unwrap();
            (work, base.join(format!("target-{worker}")))
        },
        |(work, target), _, &seed| {
            let seed_started = Instant::now();
            let interaction = (interactions && file.is_none())
                .then(|| fuzz::interactions::Interaction::new(seed));
            let program = match (&file, &interaction) {
                (Some(text), _) => fuzz::Program::from_text(text),
                (_, Some(case)) => case.program(),
                _ => fuzz::program(seed),
            };
            let text = program.full();
            let seen = observations(&program, &backends, work, target);
            let rejected = seen.iter().any(|(b, o)| {
                b == "eval" && o.error.as_deref().is_some_and(|e| e.contains(REJECTED))
            });
            let expected = interaction
                .as_ref()
                .map(|case| case.expected())
                .or_else(|| replay_expected.clone());
            let oracle_ok = seen.iter().all(|(_, o)| {
                fuzz::matches_expected(&o.shows, o.error.is_none(), expected.as_deref())
            });
            let runtime_ok = seen.iter().all(|(_, o)| {
                o.error
                    .as_deref()
                    .is_none_or(|e| matches!(e, "the number is too large" | "division by zero"))
            });
            let agree =
                !rejected && runtime_ok && oracle_ok && seen.windows(2).all(|w| w[0].1 == w[1].1);
            let mut out = String::new();
            if rejected || !agree {
                out.push_str(&if rejected {
                    format!("seed {seed}: the generator wrote a program the checker rejects\n")
                } else {
                    format!("seed {seed}: DISAGREE\n")
                });
                for (b, o) in &seen {
                    out.push_str(&format!("  {b}: {o:?}\n"));
                }
                out.push_str(&format!("--- program ---\n{text}---\n"));
                let artifact = run_dir.join(format!("failure-{seed}"));
                std::fs::create_dir_all(&artifact).unwrap();
                std::fs::write(artifact.join("original.taut"), &text).unwrap();
                if let Some(want) = &expected {
                    std::fs::write(artifact.join("original-expected.txt"), want.join("\n"))
                        .unwrap();
                    out.push_str(&format!("  expected: {want:?}\n"));
                }
                if let (Some(mut case), Some(want)) = (interaction, expected.as_ref()) {
                    out.push_str(&format!("  family: {}\n", case.family()));
                    if let Some(failing) = oracle_failures(&seen, want).filter(|bs| !bs.is_empty())
                    {
                        // The scalar measure strictly decreases; a cap also bounds
                        // expensive backend recompilations on a failing smoke run.
                        let mut attempts = 0;
                        'shrink: while attempts < 20 {
                            for smaller in case.smaller() {
                                attempts += 1;
                                let trial =
                                    observations(&smaller.program(), &backends, work, target);
                                if oracle_failures(&trial, &smaller.expected()).as_ref()
                                    == Some(&failing)
                                {
                                    case = smaller;
                                    continue 'shrink;
                                }
                                if attempts >= 20 {
                                    break;
                                }
                            }
                            break;
                        }
                        std::fs::write(artifact.join("reduced.taut"), case.program().full())
                            .unwrap();
                        std::fs::write(artifact.join("expected.txt"), case.expected().join("\n"))
                            .unwrap();
                        out.push_str(&format!("  structural shrink attempts: {attempts}\n"));
                    }
                }
                std::fs::write(artifact.join("report.txt"), &out).unwrap();
                out.push_str(&format!("  artifacts: {}\n", artifact.display()));
            } else {
                out.push_str(&format!("seed {seed}: agree {:?}\n", seen[0].1));
            }
            out.push_str(&format!(
                "seed {seed}: elapsed {:.3}s\n",
                seed_started.elapsed().as_secs_f64()
            ));
            (agree, out)
        },
    );
    let mut disagreements = 0;
    for (agree, out) in verdicts {
        print!("{out}");
        if !agree {
            disagreements += 1;
        }
    }
    println!(
        "{disagreements} of {count} seeds failed; elapsed {:.3}s; profile {profile}",
        started.elapsed().as_secs_f64()
    );
    if disagreements == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
