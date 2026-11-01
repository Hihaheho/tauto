//! Differential fuzzing of the evaluator, the Rust backend and the
//! JavaScript backend: each seed names a random well-typed program
//! (`tauto_test_suite::fuzz`), every backend runs it, and their observations
//! must be the same: the shows in order, and whether the run ends normally or
//! with which run-time error.
//!
//! `cargo test -p tauto-test-suite --test fuzz -- [<count> [<first seed>]]
//! [eval,rust,javascript]` runs `count` seeds (default 20) from `first seed`
//! (default 0) on the listed backends (default all three). A disagreement is
//! printed with its program and makes the run fail; the seed reproduces it.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::{Duration, Instant};

use tauto_test_suite::fuzz;

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
    let dir = std::env::temp_dir().join(format!("tauto-fuzz-eval-{}", std::process::id()));
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

fn main() -> ExitCode {
    tauto_test_suite::with_deep_stack(run)
}

fn run() -> ExitCode {
    let args: Vec<String> = std::env::args()
        .skip(1)
        .filter(|a| !a.starts_with('-'))
        .collect();
    let mut numbers = args.iter().filter_map(|a| a.parse::<u64>().ok());
    let count = numbers.next().unwrap_or(20);
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
    let work = base.join("work");
    let target = base.join("target");
    std::fs::create_dir_all(&work).unwrap();
    let mut disagreements = 0;
    // `TAUTO_FUZZ_FILE=<path>` runs that program instead, to cut a
    // disagreement down by hand.
    let file = std::env::var_os("TAUTO_FUZZ_FILE").map(|p| std::fs::read_to_string(p).unwrap());
    let (first, count) = if file.is_some() {
        (0, 1)
    } else {
        (first, count)
    };
    for seed in first..first + count {
        let program = match &file {
            Some(text) => fuzz::Program::from_text(text),
            None => fuzz::program(seed),
        };
        let text = program.full();
        let mut seen: Vec<(&str, Observation)> = Vec::new();
        for &b in &backends {
            let o = match b {
                "eval" => eval(&program),
                "rust" => rust(&text, &work, &target),
                "javascript" => javascript(&text, &work),
                other => panic!("unknown backend {other}"),
            };
            seen.push((b, o));
        }
        let rejected = seen
            .iter()
            .any(|(b, o)| *b == "eval" && o.error.as_deref().is_some_and(|e| e.contains(REJECTED)));
        let agree = !rejected && seen.windows(2).all(|w| w[0].1 == w[1].1);
        if rejected {
            disagreements += 1;
            println!("seed {seed}: the generator wrote a program the checker rejects");
            for (b, o) in &seen {
                println!("  {b}: {o:?}");
            }
            println!("--- program ---\n{text}---");
        } else if agree {
            println!("seed {seed}: agree {:?}", seen[0].1);
        } else {
            disagreements += 1;
            println!("seed {seed}: DISAGREE");
            for (b, o) in &seen {
                println!("  {b}: {o:?}");
            }
            println!("--- program ---\n{text}---");
        }
    }
    println!("{disagreements} of {count} seeds disagree");
    if disagreements == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
