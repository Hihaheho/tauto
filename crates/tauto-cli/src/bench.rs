//! Whole-process wall-time measurements of one release binary.

use std::io::Read;
use std::path::Path;
use std::process::{Command, ExitCode, Output, Stdio};
use std::time::{Duration, Instant};

use crate::i18n;

const USAGE: &str =
    "tauto bench FILE|DIR [--backend rust] [--warmup N] [--samples N] [--timeout-ms N] [--json]";

/// The help of `tauto bench`, in the user's language.
fn help() -> String {
    i18n::t!("bench-help", usage = USAGE)
}

#[derive(Debug, PartialEq)]
struct Options {
    path: String,
    warmup: usize,
    samples: usize,
    json: bool,
    timeout_ms: u64,
}

fn parse(args: &[String]) -> Result<Options, String> {
    let mut path = None;
    let mut warmup = 1;
    let mut samples = 10;
    let mut json = false;
    let mut timeout_ms = 30_000;
    let mut seen = std::collections::HashSet::new();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        if arg.starts_with('-') && !seen.insert(arg.as_str()) {
            return Err(i18n::t!("bench-duplicate-option", option = arg));
        }
        match arg.as_str() {
            "--backend" => {
                if args.next().map(String::as_str) != Some("rust") {
                    return Err(i18n::t!("bench-backend-rust-only"));
                }
            }
            "--warmup" | "--samples" => {
                let value = args
                    .next()
                    .and_then(|s| s.parse::<usize>().ok())
                    .ok_or_else(|| i18n::t!("bench-needs-integer", option = arg))?;
                if arg == "--warmup" && value <= 100 {
                    warmup = value;
                } else if arg == "--samples" && (1..=1000).contains(&value) {
                    samples = value;
                } else {
                    return Err(i18n::t!("bench-out-of-range", option = arg));
                }
            }
            "--timeout-ms" => {
                timeout_ms = args
                    .next()
                    .and_then(|s| s.parse().ok())
                    .filter(|n| (1..=3_600_000).contains(n))
                    .ok_or_else(|| i18n::t!("bench-timeout-range"))?;
            }
            "--json" => json = true,
            s if s.starts_with('-') => return Err(i18n::t!("bench-unknown-option", option = s)),
            s if path.is_none() => path = Some(s.to_owned()),
            _ => return Err(i18n::t!("bench-one-path")),
        }
    }
    Ok(Options {
        path: path.ok_or_else(|| i18n::t!("bench-needs-path"))?,
        warmup,
        samples,
        json,
        timeout_ms,
    })
}

#[derive(serde::Serialize)]
struct Statistics {
    min: f64,
    median: f64,
    mean: f64,
    max: f64,
    stddev: f64,
}

fn statistics(samples: &[f64]) -> Statistics {
    let mut sorted = samples.to_vec();
    sorted.sort_by(f64::total_cmp);
    let count = sorted.len();
    let mean = sorted.iter().sum::<f64>() / count as f64;
    let median = if count % 2 == 0 {
        (sorted[count / 2 - 1] + sorted[count / 2]) / 2.0
    } else {
        sorted[count / 2]
    };
    Statistics {
        min: sorted[0],
        median,
        mean,
        max: sorted[count - 1],
        stddev: (sorted.iter().map(|n| (n - mean).powi(2)).sum::<f64>() / count as f64).sqrt(),
    }
}

fn validate(output: &Output, reference: Option<&Output>) -> Result<(), String> {
    if !output.status.success() {
        return Err(i18n::t!(
            "bench-program-failed",
            status = output.status.to_string()
        ));
    }
    if reference.is_some_and(|r| r.stdout != output.stdout || r.stderr != output.stderr) {
        return Err(i18n::t!("bench-output-changed"));
    }
    Ok(())
}

const OUTPUT_LIMIT: usize = 1 << 20;

fn capture(mut reader: impl Read) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    let mut chunk = [0; 8192];
    let mut exceeded = false;
    loop {
        let count = reader
            .read(&mut chunk)
            .map_err(|e| i18n::t!("bench-cannot-read-output", error = e.to_string()))?;
        if count == 0 {
            break;
        }
        if bytes.len() + count <= OUTPUT_LIMIT && !exceeded {
            bytes.extend_from_slice(&chunk[..count]);
        } else {
            exceeded = true;
        }
    }
    if exceeded {
        Err(i18n::t!("bench-output-limit"))
    } else {
        Ok(bytes)
    }
}

fn execute(command: &mut Command, timeout: Duration) -> Result<Output, String> {
    let start = Instant::now();
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| i18n::t!("bench-cannot-start", error = e.to_string()))?;
    let stdout = child.stdout.take().expect("piped stdout");
    let stderr = child.stderr.take().expect("piped stderr");
    let stdout = std::thread::spawn(move || capture(stdout));
    let stderr = std::thread::spawn(move || capture(stderr));
    let mut status = None;
    loop {
        if status.is_none() {
            match child.try_wait() {
                Ok(found) => status = found,
                Err(error) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(i18n::t!("bench-cannot-wait", error = error.to_string()));
                }
            }
        }
        if start.elapsed() >= timeout {
            let _ = child.kill();
            let _ = child.wait();
            // Readers are detached on timeout; inherited pipes cannot delay return.
            return Err(i18n::t!(
                "bench-timeout",
                ms = timeout.as_millis().to_string()
            ));
        }
        if let Some(status) = status {
            if stdout.is_finished() && stderr.is_finished() {
                return Ok(Output {
                    status,
                    stdout: stdout
                        .join()
                        .map_err(|_| i18n::t!("bench-reader-failed", stream = "stdout"))??,
                    stderr: stderr
                        .join()
                        .map_err(|_| i18n::t!("bench-reader-failed", stream = "stderr"))??,
                });
            }
        }
        std::thread::sleep(Duration::from_millis(1));
    }
}

fn measure(binary: &Path, options: &Options) -> Result<(), String> {
    eprintln!(
        "{}",
        i18n::t!(
            "bench-running",
            warmup = options.warmup,
            samples = options.samples
        )
    );
    let mut reference = None;
    let mut samples = Vec::with_capacity(options.samples);
    for index in 0..options.warmup + options.samples {
        let start = Instant::now();
        let output = execute(
            &mut Command::new(binary),
            Duration::from_millis(options.timeout_ms),
        )
        .map_err(|e| i18n::t!("bench-run-error", run = index + 1, error = e))?;
        let elapsed = start.elapsed().as_secs_f64() * 1000.0;
        validate(&output, reference.as_ref())
            .map_err(|e| i18n::t!("bench-run-error", run = index + 1, error = e))?;
        if reference.is_none() {
            reference = Some(output);
        }
        if index >= options.warmup {
            samples.push(elapsed);
        }
    }
    let stats = statistics(&samples);
    let reference = reference.expect("at least one sample");
    if options.json {
        println!(
            "{}",
            serde_json::json!({
                "backend": "rust", "profile": "release", "measurement": "whole_process_wall_time",
                "unit": "ms", "warmup": options.warmup, "samples": samples,
                "timeout_ms": options.timeout_ms, "output_limit_bytes_per_stream": OUTPUT_LIMIT,
                "statistics": stats, "stdout_bytes": reference.stdout.len(), "stderr_bytes": reference.stderr.len(),
                "output_consistent": true, "exit_code": 0,
                "poll_interval_ms": 1, "includes_harness_overhead": true,
            })
        );
    } else {
        println!("{}", i18n::t!("bench-overhead-note"));
        println!(
            "{}",
            i18n::t!(
                "bench-heading",
                samples = options.samples,
                warmup = options.warmup
            )
        );
        println!(
            "min {:.3}  median {:.3}  mean {:.3}  max {:.3}  stddev {:.3}",
            stats.min, stats.median, stats.mean, stats.max, stats.stddev
        );
        println!(
            "{}",
            i18n::t!(
                "bench-consistent",
                stdout = reference.stdout.len(),
                stderr = reference.stderr.len()
            )
        );
    }
    Ok(())
}

pub fn command(args: &[String]) -> ExitCode {
    if args.len() == 1 && matches!(args[0].as_str(), "--help" | "-h") {
        println!("{}", help());
        return ExitCode::SUCCESS;
    }
    let options = match parse(args) {
        Ok(options) => options,
        Err(error) => {
            eprintln!("{error}\n{}", help());
            return ExitCode::from(2);
        }
    };
    let build_args = vec![
        "build".into(),
        "--backend".into(),
        "rust".into(),
        "--release".into(),
        options.path.clone(),
    ];
    super::rust::command_with(
        &build_args,
        Some(&mut |binary| match measure(binary, &options) {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("{}", i18n::t!("bench-error", error = error));
                ExitCode::FAILURE
            }
        }),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn child() {
        match std::env::var("TAUTO_BENCH_CHILD").as_deref() {
            Ok("fail") => std::process::exit(7),
            Ok("timeout") => std::thread::sleep(Duration::from_secs(60)),
            Ok("overflow") => print!("{}", "x".repeat(OUTPUT_LIMIT + 1)),
            _ => {}
        }
    }

    fn child_command(mode: &str) -> Command {
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args(["--exact", "bench::tests::child", "--nocapture"])
            .env("TAUTO_BENCH_CHILD", mode);
        command
    }

    #[test]
    fn failed_inconsistent_excessive_and_timed_out_runs_are_rejected() {
        let failed = execute(&mut child_command("fail"), Duration::from_secs(10)).unwrap();
        assert!(
            validate(&failed, None)
                .unwrap_err()
                .contains("program failed")
        );
        let mut normal = execute(&mut child_command("ok"), Duration::from_secs(10)).unwrap();
        assert!(validate(&normal, None).is_ok());
        let different = Output {
            status: normal.status,
            stdout: vec![0],
            stderr: vec![],
        };
        assert!(
            validate(&normal, Some(&different))
                .unwrap_err()
                .contains("changed")
        );
        normal.stdout = different.stdout.clone();
        normal.stderr = vec![1];
        assert!(
            validate(&normal, Some(&different))
                .unwrap_err()
                .contains("changed")
        );
        assert!(
            execute(&mut child_command("overflow"), Duration::from_secs(10))
                .unwrap_err()
                .contains("1 MiB")
        );
        assert!(
            execute(&mut child_command("timeout"), Duration::from_millis(50))
                .unwrap_err()
                .contains("timeout")
        );
    }

    #[test]
    fn summary_uses_population_standard_deviation_and_even_median() {
        let s = statistics(&[4.0, 1.0, 3.0, 2.0]);
        assert_eq!((s.min, s.median, s.mean, s.max), (1.0, 2.5, 2.5, 4.0));
        assert_eq!(s.stddev, 1.25_f64.sqrt());
        assert_eq!(statistics(&[2.0]).stddev, 0.0);
        assert_eq!(statistics(&[3.0, 1.0, 2.0]).median, 2.0);
    }

    #[test]
    fn bounded_options_reject_invalid_input() {
        for args in [
            vec![],
            vec!["a", "--samples", "0"],
            vec!["a", "--samples", "1001"],
            vec!["a", "--warmup", "101"],
            vec!["a", "--samples", "-1"],
            vec!["a", "--samples"],
            vec!["a", "--backend", "javascript"],
            vec!["a", "b"],
            vec!["a", "--json", "--json"],
        ] {
            assert!(parse(&args.into_iter().map(str::to_owned).collect::<Vec<_>>()).is_err());
        }
    }
}
