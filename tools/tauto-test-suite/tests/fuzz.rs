//! Differential fuzzing of the evaluator, the Rust backend and the
//! JavaScript backend. The generator (`totes/fuzz`, through
//! `tauto_test_suite::fuzz`) turns a seed into a random well-typed program;
//! every backend runs it, and their observations must be the same: the shows
//! in order, and whether the run ends normally or with which run-time error.
//! Interaction programs also compare those events against an independent
//! scalar model, even when all backends agree.
//!
//! A failure is shrunk over the generator's choices while it keeps its
//! signature (the backends that are off, and each one's stage and normalized
//! message), then kept in `.fuzz/findings/<signature>/` with a case snippet
//! for `cases/`. A failure a case already declares (`<backend>.bug` or
//! `<backend>.unimplemented` with the same stage and message) is counted as
//! known, and its snippet is not written: a case goes in only when no case
//! fails for the same reason.
//!
//! Modes:
//!
//! - regression (default): seeds 0 to 299, as ten tests; `TAUTO_FUZZ_PROFILE=quick`
//!   runs 9. Arguments `[<count> [<first seed>]] [eval,rust,javascript]`.
//! - explore: `-- --minutes N` draws a fresh range of seeds and runs them until
//!   N minutes have passed. Run it when asked to; it is not part of a gate.
//!
//! `TAUTO_FUZZ_FILE=<path>` runs a program written by hand instead, and
//! `TAUTO_FUZZ_EXPECTED=<path>` gives the shows it must make.
//! `TAUTO_FUZZ_INTERACTIONS=1` runs the interaction families, and
//! `TAUTO_FUZZ_SHRINK_SECS` bounds how long one failure shrinks.
//! Every run prints how long each backend took per seed.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use tauto_test_suite::fuzz::{self, Failure, Observation, Signature};

/// The default corpus size; the quick profile is an explicit smoke run.
const DEFAULT_COUNT: u64 = 300;

/// The default corpus runs as this many tests.
const SHARDS: u64 = 10;

/// Seeds an explore run asks the generator for at once.
const EXPLORE_BATCH: u64 = 8;

/// How many smaller programs a failure may try while it shrinks.
const SHRINK_ATTEMPTS: usize = 200;

/// How long one failure may shrink: `TAUTO_FUZZ_SHRINK_SECS`, else five
/// minutes. A program the Rust backend builds takes seconds, so a failure
/// on it tries far fewer smaller programs in that time than one on the
/// evaluator.
fn shrink_time() -> Duration {
    Duration::from_secs(
        std::env::var("TAUTO_FUZZ_SHRINK_SECS")
            .ok()
            .and_then(|n| n.trim().parse().ok())
            .unwrap_or(300),
    )
}

/// Runs as `tauto run` does: from a file, through the row check.
fn eval_once(text: &str) -> Result<Vec<String>, Failure> {
    // One directory per call: the workers run at once.
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "tauto-fuzz-eval-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).map_err(|e| Failure::new("run", &e.to_string()))?;
    let path = dir.join("main.taut");
    std::fs::write(&path, text).map_err(|e| Failure::new("run", &e.to_string()))?;
    let loaded = tauto::program::load(&path);
    let _ = std::fs::remove_dir_all(&dir);
    let loaded = loaded.map_err(|e| Failure::new("check", &e.to_string()))?;
    if let Some((error, _)) = loaded.program.errors.first() {
        return Err(Failure::new("check", &error.to_string()));
    }
    let got = tauto::exec::run_loaded_with(
        &loaded,
        tauto::exec::DEFAULT_BUDGET,
        tauto::exec::RunOptions::default(),
    )
    .map_err(|e| match e {
        tauto::exec::RunError::Syntax(_)
        | tauto::exec::RunError::Type(_)
        | tauto::exec::RunError::Use(_)
        | tauto::exec::RunError::Row(_) => Failure::new("check", &e.to_string()),
        e => Failure::new("run", &e.to_string()),
    })?;
    Ok(got.stdout.lines().map(str::to_string).collect())
}

/// The evaluator does not return the shows of a run that fails, so the shows
/// before a failure are those of the longest prefix of show lines that runs.
fn eval(program: &fuzz::Program) -> Observation {
    match eval_once(&program.full()) {
        Ok(shows) => Observation { shows, error: None },
        Err(e) => {
            let shows = if e.stage == "run" {
                (0..program.shows.len())
                    .rev()
                    .find_map(|n| eval_once(&program.text(n)).ok())
                    .unwrap_or_default()
            } else {
                Vec::new()
            };
            Observation {
                shows,
                error: Some(e),
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
        None => Some(Failure::new("run", "timed out")),
        Some(s) if s.success() => None,
        Some(_) => Some(Failure::new("run", stderr)),
    };
    Observation { shows, error }
}

fn failed(stage: &str, e: String) -> Observation {
    Observation {
        shows: Vec::new(),
        error: Some(Failure::new(stage, &e)),
    }
}

fn rust(text: &str, work: &Path, target: &Path) -> Observation {
    let mut package = match tauto::nir::compile(text) {
        Ok(p) => p,
        Err(e) => return failed("compile", format!("{e:?}")),
    };
    let bindings = match tauto_rustgen::Bindings::resolve(&mut package, None, None) {
        Ok(b) => b,
        Err(e) => return failed("generate", e.to_string()),
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
    let _ = std::fs::remove_dir_all(work.join("src"));
    let bin = match ws.build("fuzz", work, target, false) {
        Ok(b) => b,
        Err(e) => return failed("build", e.to_string()),
    };
    let show_path = work.join("stdout");
    let err_path = work.join("stderr");
    let child = Command::new(&bin)
        .stdout(std::fs::File::create(&show_path).unwrap())
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
    let package = match tauto::nir::compile_javascript(text) {
        Ok(p) => p,
        Err(e) => return failed("compile", format!("{e:?}")),
    };
    let js = match tauto_jsgen::generate(&package) {
        Ok(js) => js,
        Err(e) => return failed("generate", e.to_string()),
    };
    let module = dir.join("fuzz.mjs");
    let show_file = dir.join("stdout");
    let err_file = dir.join("stderr");
    std::fs::write(&module, format!("{js}\ntry {{await run(console.log, {{}}, {{args:[], permissions:{{}}, env:process.env, os_print:text => process.stdout.write(text), os_eprint:text => process.stderr.write(text)}});}} catch(e) {{console.error(e.message);process.exitCode=1;}}\n")).unwrap();
    let child = Command::new("node")
        .arg(&module)
        .stdout(std::fs::File::create(&show_file).unwrap())
        .stderr(std::fs::File::create(&err_file).unwrap())
        .spawn()
        .unwrap();
    let status = wait(child, Duration::from_secs(60));
    let shows = std::fs::read_to_string(&show_file)
        .unwrap_or_default()
        .lines()
        .map(str::to_string)
        .collect();
    observed(status, shows, &std::fs::read_to_string(&err_file).unwrap())
}

/// Each backend's observation, and the time it took, added to `times`.
fn observations(
    program: &fuzz::Program,
    backends: &[&str],
    work: &Path,
    target: &Path,
    times: &Times,
) -> Vec<(String, Observation)> {
    let text = program.full();
    backends
        .iter()
        .map(|&b| {
            let started = Instant::now();
            let observed = match b {
                "eval" => eval(program),
                "rust" => rust(&text, work, target),
                "javascript" => javascript(&text, work),
                other => panic!("unknown backend {other}"),
            };
            times.add(b, started.elapsed());
            (b.to_string(), observed)
        })
        .collect()
}

/// Time spent per backend, over the programs run.
#[derive(Default)]
struct Times(Mutex<BTreeMap<String, (Duration, u64)>>);

impl Times {
    fn add(&self, backend: &str, d: Duration) {
        let mut t = self.0.lock().unwrap();
        let e = t.entry(backend.to_string()).or_default();
        e.0 += d;
        e.1 += 1;
    }

    fn report(&self) -> String {
        let t = self.0.lock().unwrap();
        t.iter()
            .map(|(b, (d, n))| {
                format!(
                    "{b} {:.3}s per program ({n} programs)",
                    d.as_secs_f64() / (*n).max(1) as f64
                )
            })
            .collect::<Vec<_>>()
            .join("; ")
    }
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

/// The signature of what the backends did, with an expectation when one is
/// known: a backend that does not show it is off even when all agree.
fn signature(seen: &[(String, Observation)], expected: Option<&[String]>) -> Option<Signature> {
    let mut sig = Signature::of(seen).map(|s| s.0).unwrap_or_default();
    for (b, o) in seen {
        if !fuzz::matches_expected(&o.shows, o.error.is_none(), expected) {
            sig.entry(b.clone())
                .or_insert_with(|| "output: differs from the expected shows".into());
        }
    }
    (!sig.is_empty()).then_some(Signature(sig))
}

/// What one seed came to.
enum Verdict {
    Agree,
    Known(String),
    Failed,
}

/// What every worker shares.
struct Run<'a> {
    backends: Vec<&'a str>,
    times: Times,
    known: fuzz::Known,
    deadline: Option<Instant>,
    /// The signatures this run has shrunk: a later failure of one is only
    /// counted, as it is the same bug.
    shrunk: Mutex<std::collections::BTreeSet<Signature>>,
}

impl Run<'_> {
    /// Shrink a generated failure over its choices while it keeps `sig`.
    fn shrink(
        &self,
        start: fuzz::Generated,
        sig: &Signature,
        work: &Path,
        target: &Path,
        out: &mut String,
    ) -> fuzz::Generated {
        let mut best = start;
        let mut attempts = 0;
        let until = Instant::now() + shrink_time();
        'step: while attempts < SHRINK_ATTEMPTS {
            if Instant::now() > until {
                out.push_str("  shrinking stopped: its time is up\n");
                break;
            }
            if self.deadline.is_some_and(|d| Instant::now() > d) {
                out.push_str("  shrinking stopped: the time is up\n");
                break;
            }
            let candidates = match fuzz::shrinks(&best.choices) {
                Ok(c) => c,
                Err(e) => {
                    out.push_str(&format!("  shrinking stopped: {e}\n"));
                    break;
                }
            };
            for smaller in candidates {
                if smaller.program.full().len() >= best.program.full().len() {
                    continue;
                }
                attempts += 1;
                let seen =
                    observations(&smaller.program, &self.backends, work, target, &self.times);
                if signature(&seen, None).as_ref() == Some(sig) {
                    best = smaller;
                    continue 'step;
                }
                if attempts >= SHRINK_ATTEMPTS {
                    break;
                }
            }
            break;
        }
        out.push_str(&format!("  shrink attempts: {attempts}\n"));
        best
    }

    /// Run one program and decide what it came to; a failure is shrunk and
    /// saved.
    #[allow(clippy::too_many_arguments)]
    fn judge(
        &self,
        label: &str,
        generated: Option<fuzz::Generated>,
        program: fuzz::Program,
        interaction: Option<fuzz::interactions::Interaction>,
        expected: Option<Vec<String>>,
        work: &Path,
        target: &Path,
    ) -> (Verdict, String) {
        let started = Instant::now();
        let mut out = String::new();
        let text = program.full();
        let seen = observations(&program, &self.backends, work, target, &self.times);
        let Some(sig) = signature(&seen, expected.as_deref()) else {
            out.push_str(&format!(
                "{label}: agree {:?}; elapsed {:.3}s\n",
                seen[0].1,
                started.elapsed().as_secs_f64()
            ));
            return (Verdict::Agree, out);
        };
        let rejected = seen.iter().any(|(b, o)| {
            b == "eval" && o.error.as_ref().is_some_and(|e| e.stage == "check")
        });
        out.push_str(&if rejected {
            format!("{label}: the generator wrote a program the checker rejects\n")
        } else {
            format!("{label}: DISAGREE\n")
        });
        for (b, o) in &seen {
            out.push_str(&format!("  {b}: {o:?}\n"));
        }
        out.push_str(&format!("  signature:\n    {}\n", sig.text().replace('\n', "\n    ")));
        if let Some(case) = self.known.declaring(&sig) {
            out.push_str(&format!("  known: the case {case} declares it\n"));
            return (Verdict::Known(case), out);
        }
        if !self.shrunk.lock().unwrap().insert(sig.clone()) {
            out.push_str("  the same signature as an earlier failure of this run\n");
            return (Verdict::Failed, out);
        }
        out.push_str(&format!("--- program ---\n{text}---\n"));
        let mut files: Vec<(&str, String)> = vec![
            ("original.taut", text.clone()),
            ("signature.txt", sig.text()),
        ];
        let (reduced, reduced_seen) = match generated {
            Some(g) if !rejected => {
                let g = self.shrink(g, &sig, work, target, &mut out);
                let seen = observations(&g.program, &self.backends, work, target, &self.times);
                files.push((
                    "choices.txt",
                    g.choices
                        .iter()
                        .map(u64::to_string)
                        .collect::<Vec<_>>()
                        .join(" "),
                ));
                (g.program.full(), seen)
            }
            _ => (text.clone(), seen.clone()),
        };
        if let (Some(want), Some(mut case)) = (&expected, interaction) {
            out.push_str(&format!("  expected: {want:?}\n  family: {}\n", case.family()));
            if let Some(failing) = oracle_failures(&seen, want).filter(|bs| !bs.is_empty()) {
                // The scalar measure strictly decreases; a cap also bounds
                // expensive backend recompilations on a failing smoke run.
                let mut attempts = 0;
                'shrink: while attempts < 20 {
                    for smaller in case.smaller() {
                        attempts += 1;
                        let trial = observations(
                            &smaller.program(),
                            &self.backends,
                            work,
                            target,
                            &self.times,
                        );
                        if oracle_failures(&trial, &smaller.expected()).as_ref() == Some(&failing) {
                            case = smaller;
                            continue 'shrink;
                        }
                        if attempts >= 20 {
                            break;
                        }
                    }
                    break;
                }
                files.push(("expected.txt", case.expected().join("\n")));
                out.push_str(&format!("  structural shrink attempts: {attempts}\n"));
            }
        }
        let name = format!("fuzz-{}", sig.key());
        let snippet = fuzz::case_snippet(&name, &sig, &reduced, &reduced_seen);
        out.push_str(&format!("--- reduced ---\n{reduced}---\n--- case ---\n{snippet}---\n"));
        files.push(("program.taut", reduced.clone()));
        files.push(("case.eure", snippet));
        files.push(("report.txt", out.clone()));
        let refs: Vec<(&str, &str)> = files.iter().map(|(n, t)| (*n, t.as_str())).collect();
        match fuzz::save(&sig, &refs, reduced.len()) {
            Ok((dir, true)) => out.push_str(&format!("  saved: {}\n", dir.display())),
            Ok((dir, false)) => out.push_str(&format!(
                "  a smaller program of this signature is kept in {}\n",
                dir.display()
            )),
            Err(e) => out.push_str(&format!("  not saved: {e}\n")),
        }
        out.push_str(&format!(
            "{label}: elapsed {:.3}s\n",
            started.elapsed().as_secs_f64()
        ));
        (Verdict::Failed, out)
    }
}

fn main() -> ExitCode {
    // An explore run may outlast the test binary's own time limit, which
    // it then sets above its budget.
    let raw: Vec<String> = std::env::args().collect();
    let minutes = raw
        .iter()
        .position(|a| a == "--minutes")
        .and_then(|i| raw.get(i + 1))
        .map(|n| n.parse::<u64>().expect("--minutes takes a whole number"));
    if let Some(m) = minutes {
        // SAFETY: no other thread runs yet.
        unsafe { std::env::set_var("TAUTO_TEST_TIMEOUT_SECS", (m * 60 + 900).to_string()) };
    }
    tauto_test_suite::with_deep_stack(|| run(minutes))
}

fn run(minutes: Option<u64>) -> ExitCode {
    // Messages are compared in English.
    tauto_messages::install();
    // The default corpus runs as `SHARDS` tests (`seeds-<k>`), so that the
    // runner gives each its own time limit.
    let mut args = match tauto_test_suite::harness_tests(|| {
        (0..SHARDS).map(|k| format!("seeds-{k}")).collect()
    }) {
        tauto_test_suite::Harness::Listed => return ExitCode::SUCCESS,
        tauto_test_suite::Harness::Run { positional, .. } => {
            positional.into_iter().filter(|a| a != "fuzz").collect::<Vec<_>>()
        }
    };
    if let Some(m) = minutes
        && let Some(i) = args.iter().position(|a| a == &m.to_string())
    {
        args.remove(i);
    }
    let shard = args
        .iter()
        .position(|a| a.starts_with("seeds-"))
        .and_then(|i| args.remove(i).strip_prefix("seeds-")?.parse::<u64>().ok());
    let mut numbers = args.iter().filter_map(|a| a.parse::<u64>().ok());
    let profile = std::env::var("TAUTO_FUZZ_PROFILE").unwrap_or_else(|_| "stress".into());
    let default_count = match profile.as_str() {
        "quick" => 9,
        "stress" => DEFAULT_COUNT,
        other => panic!("unknown TAUTO_FUZZ_PROFILE {other}; use quick or stress"),
    };
    let mut count = numbers.next().unwrap_or(default_count);
    let interactions = std::env::var_os("TAUTO_FUZZ_INTERACTIONS").is_some();
    let started = Instant::now();
    let mut first = numbers.next().unwrap_or(0);
    if let Some(k) = shard {
        let size = default_count.div_ceil(SHARDS);
        first = k * size;
        if first >= default_count {
            return ExitCode::SUCCESS;
        }
        count = size.min(default_count - first);
    }
    let backends: Vec<&str> = args
        .iter()
        .find(|a| a.parse::<u64>().is_err())
        .map(|a| a.split(',').collect())
        .unwrap_or_else(|| vec!["eval", "rust", "javascript"]);
    assert!(!backends.is_empty(), "at least one backend is required");
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
    let known = match fuzz::Known::read(&fuzz::repo_root().join("cases")) {
        Ok(k) => k,
        Err(e) => {
            println!("the cases do not read: {e}");
            return ExitCode::FAILURE;
        }
    };
    let deadline = minutes.map(|m| started + Duration::from_secs(m * 60));
    let run = Run {
        backends,
        times: Times::default(),
        known,
        deadline,
        shrunk: Mutex::default(),
    };
    let make = |worker: usize| {
        let work = run_dir.join(format!("work-{worker}"));
        std::fs::create_dir_all(&work).unwrap();
        (work, base.join(format!("target-{worker}")))
    };
    let mut tally = Tally::default();
    if let Some(deadline) = deadline {
        // A range of seeds no earlier run is likely to have drawn.
        let mut next = fuzz::Rng::new(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos() as u64)
                .unwrap_or(0),
        )
        .next()
            >> 16;
        let from = next;
        println!("explore: seeds from {from}, {} minutes", minutes.unwrap());
        while Instant::now() < deadline {
            let batch: Vec<u64> = (next..next + EXPLORE_BATCH).collect();
            next += EXPLORE_BATCH;
            if !run_seeds(&run, &batch, interactions, &make, &mut tally) {
                return ExitCode::FAILURE;
            }
        }
        println!("explore: ran seeds {from} to {}", next - 1);
    } else if let Some(text) = &file {
        let mut ws = make(0);
        let (verdict, out) = run.judge(
            "file",
            None,
            fuzz::Program::from_text(text),
            None,
            replay_expected,
            &ws.0,
            &ws.1,
        );
        let _ = &mut ws;
        print!("{out}");
        tally.add(&verdict);
    } else {
        assert!(count > 0, "count must be positive");
        let end = first.checked_add(count).expect("seed range overflows u64");
        let seeds: Vec<u64> = (first..end).collect();
        if !run_seeds(&run, &seeds, interactions, &make, &mut tally) {
            return ExitCode::FAILURE;
        }
    }
    println!(
        "{} programs: {} agree, {} known, {} failed; elapsed {:.3}s; profile {profile}",
        tally.total(),
        tally.agree,
        tally.known,
        tally.failed,
        started.elapsed().as_secs_f64()
    );
    println!("time: {}", run.times.report());
    if tally.failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

#[derive(Default)]
struct Tally {
    agree: u64,
    known: u64,
    failed: u64,
}

impl Tally {
    fn add(&mut self, v: &Verdict) {
        match v {
            Verdict::Agree => self.agree += 1,
            Verdict::Known(_) => self.known += 1,
            Verdict::Failed => self.failed += 1,
        }
    }

    fn total(&self) -> u64 {
        self.agree + self.known + self.failed
    }
}

/// Run `seeds`, print each verdict in seed order and count them. False when
/// the generator itself fails.
fn run_seeds(
    run: &Run,
    seeds: &[u64],
    interactions: bool,
    make: &(impl Fn(usize) -> (PathBuf, PathBuf) + Sync),
    tally: &mut Tally,
) -> bool {
    let generated = if interactions {
        None
    } else {
        let first = seeds[0];
        match fuzz::seeds(first, seeds.len() as u64) {
            Ok(g) => Some(Mutex::new(g.into_iter().map(Some).collect::<Vec<_>>())),
            Err(e) => {
                println!("the generator failed: {e}");
                return false;
            }
        }
    };
    // Seeds are independent. Each worker builds the generated crates in a work
    // and a target directory of its own (rustc's incremental cache and Cargo's
    // lock allow one build at a time), and the verdicts are printed in seed
    // order.
    let verdicts = tauto_test_suite::parallel_map(seeds, make, |(work, target), i, &seed| {
        let label = format!("seed {seed}");
        if let Some(g) = &generated {
            let g = g.lock().unwrap()[i].take().expect("each seed runs once");
            let program = fuzz::Program {
                declarations: g.program.declarations.clone(),
                shows: g.program.shows.clone(),
            };
            run.judge(&label, Some(g), program, None, None, work, target)
        } else {
            let case = fuzz::interactions::Interaction::new(seed);
            let expected = Some(case.expected());
            run.judge(&label, None, case.program(), Some(case), expected, work, target)
        }
    });
    for (verdict, out) in verdicts {
        print!("{out}");
        tally.add(&verdict);
    }
    true
}
