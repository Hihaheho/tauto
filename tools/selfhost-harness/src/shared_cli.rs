//! Supervised shared-case execution and cache preparation.
//!
//! Preparation produces an artifact identity, never a semantic case verdict.
//! Each invocation replaces its report before starting work; a worker's report
//! is accepted only with the current invocation identity and terminal status.
use serde_json::{Value, json};
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};
use tauto_test_suite::selfhost::{Backend, Verdict};

const MODES: &[&str] = &["syntax", "fmt", "types", "rows", "lin", "rustgen"];
const PREPARE: &[&str] = &["syntax", "fmt", "nibcheck", "rustgen"];
const WORKER_PREFIX: &str = "--internal-shared-worker";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    pub root: PathBuf,
    pub filter: String,
    pub modes: Vec<String>,
    pub target: Option<Backend>,
    pub report: Option<PathBuf>,
    pub prepare: Option<String>,
    pub timeout: Duration,
    pub setup_timeout: Duration,
}
impl Config {
    pub fn parse(args: impl IntoIterator<Item = String>) -> Result<Self, String> {
        let mut args = args.into_iter();
        let mut values = std::collections::BTreeMap::new();
        let mut modes = Vec::new();
        while let Some(flag) = args.next() {
            if ![
                "--root",
                "--filter",
                "--target",
                "--report",
                "--prepare",
                "--timeout-seconds",
                "--setup-timeout-seconds",
                "--component",
            ]
            .contains(&flag.as_str())
            {
                return Err(format!("unknown argument {flag}"));
            }
            let value = args
                .next()
                .filter(|v| !v.is_empty() && !v.starts_with("--"))
                .ok_or_else(|| format!("{flag} requires a value"))?;
            if flag == "--component" {
                if !MODES.contains(&value.as_str()) || modes.contains(&value) {
                    return Err(format!("unknown or duplicate component {value}"));
                }
                modes.push(value);
            } else if values.insert(flag.clone(), value).is_some() {
                return Err(format!("duplicate argument {flag}"));
            }
        }
        let root = values
            .remove("--root")
            .map(PathBuf::from)
            .ok_or("--root requires the cases directory")?;
        let target = match values.remove("--target").as_deref() {
            None => None,
            Some("rust") => Some(Backend::Rust),
            Some("javascript") => Some(Backend::Javascript),
            Some(_) => return Err("--target requires rust or javascript".into()),
        };
        let prepare = values.remove("--prepare");
        if prepare
            .as_ref()
            .is_some_and(|m| !PREPARE.contains(&m.as_str()))
        {
            return Err("--prepare requires syntax, fmt, nibcheck or rustgen".into());
        }
        if prepare.is_some()
            && (target.is_some()
                || values.contains_key("--filter")
                || !modes.is_empty()
                || values.contains_key("--timeout-seconds"))
        {
            return Err(
                "--prepare cannot select cases, a target, components, or an execution timeout"
                    .into(),
            );
        }
        if prepare.is_none() && values.contains_key("--setup-timeout-seconds") {
            return Err("--setup-timeout-seconds requires --prepare".into());
        }
        fn seconds(value: Option<String>, default: u64, name: &str) -> Result<Duration, String> {
            let n = match value {
                Some(v) => v
                    .parse::<u64>()
                    .map_err(|_| format!("{name} requires an integer"))?,
                None => default,
            };
            if !(1..=86_400).contains(&n) {
                return Err(format!("{name} must be between 1 and 86400"));
            }
            Ok(Duration::from_secs(n))
        }
        let timeout = seconds(values.remove("--timeout-seconds"), 120, "--timeout-seconds")?;
        let setup_timeout = seconds(
            values.remove("--setup-timeout-seconds"),
            1800,
            "--setup-timeout-seconds",
        )?;
        if modes.is_empty() {
            modes = MODES.iter().map(|m| (*m).to_string()).collect();
        }
        Ok(Self {
            root,
            filter: values.remove("--filter").unwrap_or_default(),
            modes,
            target,
            report: values.remove("--report").map(PathBuf::from),
            prepare,
            timeout,
            setup_timeout,
        })
    }
    fn phase(&self) -> &'static str {
        if self.prepare.is_some() {
            "setup"
        } else {
            "execution"
        }
    }
    fn deadline(&self) -> Duration {
        if self.prepare.is_some() {
            self.setup_timeout
        } else {
            self.timeout
        }
    }
}

/// An atomic replacement prevents a partial or previous report from looking like
/// the completed result of the current invocation.
pub fn write_report(path: &Path, value: &Value) -> Result<(), String> {
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    let temporary = parent.join(format!(".shared-report-{}.tmp", invocation_id()));
    let bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    fs::write(&temporary, bytes).map_err(|e| e.to_string())?;
    fs::rename(&temporary, path).map_err(|e| {
        let _ = fs::remove_file(&temporary);
        e.to_string()
    })
}
fn invocation_id() -> String {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    format!(
        "{}-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    )
}

#[derive(Debug)]
pub struct ProcessResult {
    pub code: Option<i32>,
    pub status: String,
    pub timed_out: bool,
    pub elapsed: Duration,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub stdout_path: PathBuf,
    pub stderr_path: PathBuf,
}

#[cfg(unix)]
fn stop_worker_group(group: u32) -> Result<(), String> {
    use std::ffi::c_int;
    unsafe extern "C" {
        fn kill(pid: c_int, signal: c_int) -> c_int;
    }
    let group = c_int::try_from(group).map_err(|_| "worker group identifier exceeds pid range")?;
    if group <= 1 {
        return Err("invalid worker process group".into());
    }
    // kill accepts a negative PID to address exactly that process group. The
    // group was allocated by Command::process_group(0), not by caller input.
    // SIGKILL and ESRCH are respectively 9 and 3 in the supported Unix ABI.
    let result = unsafe { kill(-group, 9) };
    cleanup_result(result, std::io::Error::last_os_error())
}
#[cfg(unix)]
fn cleanup_result(result: i32, error: std::io::Error) -> Result<(), String> {
    if result == 0 || error.raw_os_error() == Some(3) {
        Ok(()) // ESRCH: the worker group has already disappeared.
    } else {
        Err(format!("cannot terminate worker process group: {error}"))
    }
}

/// A private process group contains the worker and its compiler/build children.
/// Output goes to files so neither pipe backpressure nor a descendant holding a
/// pipe open can bypass the deadline. Unsupported platforms fail before spawn.
pub fn supervise(
    command: &mut Command,
    directory: &Path,
    deadline: Duration,
) -> Result<ProcessResult, String> {
    #[cfg(not(unix))]
    {
        let _ = (command, directory, deadline);
        return Err("process-tree supervision is unavailable on this platform".into());
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        fs::create_dir_all(directory).map_err(|e| e.to_string())?;
        let stdout_path = directory.join("worker.stdout");
        let stderr_path = directory.join("worker.stderr");
        command
            .process_group(0)
            .stdin(Stdio::null())
            .stdout(Stdio::from(
                fs::File::create(&stdout_path).map_err(|e| e.to_string())?,
            ))
            .stderr(Stdio::from(
                fs::File::create(&stderr_path).map_err(|e| e.to_string())?,
            ));
        let started = Instant::now();
        let mut child = command.spawn().map_err(|e| e.to_string())?;
        let group = child.id();
        let stop = || stop_worker_group(group);
        let (status, timed_out) = loop {
            match child.try_wait() {
                Ok(Some(status)) => {
                    stop()?;
                    break (status, false);
                }
                Ok(None) if started.elapsed() < deadline => {
                    std::thread::sleep(Duration::from_millis(10))
                }
                Ok(None) => {
                    let killed = stop();
                    let _ = child.kill();
                    let status = child.wait().map_err(|e| e.to_string())?;
                    killed?;
                    break (status, true);
                }
                Err(e) => {
                    let cleanup = stop();
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(format!(
                        "cannot wait for worker: {e}; group cleanup: {cleanup:?}"
                    ));
                }
            }
        };
        Ok(ProcessResult {
            code: status.code(),
            status: status.to_string(),
            timed_out,
            elapsed: started.elapsed(),
            stdout: fs::read(&stdout_path).map_err(|e| e.to_string())?,
            stderr: fs::read(&stderr_path).map_err(|e| e.to_string())?,
            stdout_path,
            stderr_path,
        })
    }
}

fn selected(config: &Config) -> Result<Vec<String>, String> {
    if config.prepare.is_some() {
        return Ok(Vec::new());
    }
    let names: Vec<_> = tauto_test_suite::selfhost::contracts(&config.root)?
        .into_iter()
        .filter(|c| c.name.contains(&config.filter))
        .map(|c| c.name)
        .collect();
    if names.is_empty() {
        return Err("no selected case contracts".into());
    }
    Ok(names)
}
fn pending(config: &Config, id: &str, names: &[String], status: &str, reason: &str) -> Value {
    json!({"invocation":id,"phase":config.phase(),"status":status,"semantic_execution_verified":false,"summary":{"passed":0,"failed":0,"incomplete":names.len(),"host_harness":0,"explicitly_excluded":0},"cases":names.iter().map(|n|json!({"case":n,"status":"incomplete","reasons":[reason],"observations":[]})).collect::<Vec<_>>(),"reason":reason})
}
fn backend() -> Result<Backend, String> {
    match std::env::var("TAUTO_SELFHOST_BACKEND").as_deref() {
        Ok("rust") | Err(_) => Ok(Backend::Rust),
        Ok("javascript") => Ok(Backend::Javascript),
        Ok(other) => Err(format!("unknown compiler backend {other}")),
    }
}
fn valid_root(config: &Config) -> Result<(), String> {
    let root = config.root.canonicalize().map_err(|e| e.to_string())?;
    let expected = crate::root()
        .canonicalize()
        .map_err(|e| e.to_string())?
        .join("cases");
    if root != expected {
        return Err(format!(
            "case root {} differs from compiled harness root {}; rebuild the path-sensitive harness",
            root.display(),
            expected.display()
        ));
    }
    Ok(())
}
fn worker(config: &Config, id: &str) -> Result<(Value, bool), String> {
    valid_root(config)?;
    let backend = backend()?;
    let identity = crate::shared_cases::input_identity(&config.root, &config.filter)?;
    let started = Instant::now();
    let (mut report, success) = if let Some(component) = &config.prepare {
        if backend != Backend::Rust {
            return Err("setup-only preparation exposes native artifacts only; JavaScript preparation is unavailable".into());
        }
        let path = crate::tote_binary(component)?;
        let bytes =
            fs::read(&path).map_err(|e| format!("prepared artifact {}: {e}", path.display()))?;
        (
            json!({"invocation":id,"phase":"setup","status":"prepared","semantic_execution_verified":false,"summary":{"passed":0,"failed":0,"incomplete":0,"host_harness":0,"explicitly_excluded":0},"cases":[],"prepared":{"component":component,"compiler_backend":backend.name(),"artifact_path":path,"artifact_sha256":tauto_syntax::sha256_hex(&bytes)}}),
            true,
        )
    } else {
        let target = config.target.unwrap_or(backend);
        let results =
            crate::shared_cases::run(&config.root, backend, target, &config.filter, &config.modes)?;
        let (mut passed, mut failed, mut incomplete, mut host, mut excluded) = (0, 0, 0, 0, 0);
        let records = results.into_iter().map(|result| {
            let (status, reasons) = match result.verdict {
                Verdict::Passed => { passed += 1; ("passed", vec![]) },
                Verdict::Failed(e) => { failed += 1; ("failed", e) },
                Verdict::Incomplete(e) => { incomplete += 1; ("incomplete", e) },
                Verdict::HostHarness => { host += 1; ("host-harness", vec![]) },
                Verdict::Excluded => { excluded += 1; ("explicitly-excluded", vec![]) },
            };
            println!("{}\t{status}\t{}", result.name, reasons.join("; "));
            json!({"case":result.name,"status":status,"reasons":reasons,"artifacts":result.artifacts,"observations":result.observations.iter().map(|o|json!({"requirement":o.requirement,"stage":o.stage,"implementation":format!("{:?}",o.implementation),"compiler_backend":o.compiler_backend.name(),"target_backend":o.target_backend.map(Backend::name),"actual":format!("{:?}",o.actual)})).collect::<Vec<_>>()})
        }).collect::<Vec<_>>();
        let success = failed == 0 && incomplete == 0 && passed > 0;
        (
            json!({"invocation":id,"phase":"execution","status":"completed","semantic_execution_verified":success,"summary":{"case_root":config.root.canonicalize().ok(),"compiler_root":crate::root().canonicalize().ok(),"compiler_backend":backend.name(),"target_backend":target.name(),"passed":passed,"failed":failed,"incomplete":incomplete,"host_harness":host,"explicitly_excluded":excluded},"cases":records}),
            success,
        )
    };
    if crate::shared_cases::input_identity(&config.root, &config.filter)? != identity {
        return Err("input files changed during execution".into());
    }
    report["input_identity"] = identity;
    report["elapsed_ms"] = json!(started.elapsed().as_millis());
    Ok((report, success))
}

/// Only a current worker report with consistent exit status can be published.
pub fn validate_worker_report(
    report: &Value,
    id: &str,
    phase: &str,
    names: &[String],
    exit: Option<i32>,
) -> Result<bool, String> {
    if report.get("invocation").and_then(Value::as_str) != Some(id)
        || report.get("phase").and_then(Value::as_str) != Some(phase)
    {
        return Err("worker report belongs to a different invocation or phase".into());
    }
    let cases = report
        .get("cases")
        .and_then(Value::as_array)
        .ok_or("worker report has no cases array")?;
    let reported = cases
        .iter()
        .map(|v| {
            v.get("case")
                .and_then(Value::as_str)
                .ok_or("worker case has no name")
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    let expected: BTreeSet<_> = names.iter().map(String::as_str).collect();
    if reported != expected || reported.len() != cases.len() {
        return Err("worker report does not contain exactly the selected cases".into());
    }
    let status = report.get("status").and_then(Value::as_str);
    if !matches!(
        (phase, status),
        ("setup", Some("prepared" | "failed")) | ("execution", Some("completed" | "failed"))
    ) {
        return Err("worker report is not terminal for this phase".into());
    }
    let summary = report
        .get("summary")
        .and_then(Value::as_object)
        .ok_or("worker report has no summary")?;
    let mut counts = [0u64; 5];
    for case in cases {
        let index = match case.get("status").and_then(Value::as_str) {
            Some("passed") => 0,
            Some("failed") => 1,
            Some("incomplete") => 2,
            Some("host-harness") => 3,
            Some("explicitly-excluded") => 4,
            _ => return Err("unknown worker case status".into()),
        };
        counts[index] += 1;
    }
    for (index, field) in [
        "passed",
        "failed",
        "incomplete",
        "host_harness",
        "explicitly_excluded",
    ]
    .iter()
    .enumerate()
    {
        if summary.get(*field).and_then(Value::as_u64) != Some(counts[index]) {
            return Err(format!(
                "worker summary disagrees with case records: {field}"
            ));
        }
    }
    if status == Some("failed") && counts[0] != 0 {
        return Err("failed worker cannot retain passed cases".into());
    }
    let success = if phase == "setup" {
        if report
            .get("semantic_execution_verified")
            .and_then(Value::as_bool)
            != Some(false)
            || !cases.is_empty()
        {
            return Err("preparation cannot verify semantic cases".into());
        }
        let prepared = report.get("status").and_then(Value::as_str) == Some("prepared");
        if prepared {
            let hash = report
                .pointer("/prepared/artifact_sha256")
                .and_then(Value::as_str)
                .ok_or("prepared artifact identity missing")?;
            if hash.len() != 64 || !hash.bytes().all(|b| b.is_ascii_hexdigit()) {
                return Err("malformed prepared artifact identity".into());
            }
        }
        prepared
    } else {
        let success = counts[0] > 0 && counts[1] == 0 && counts[2] == 0;
        if report
            .get("semantic_execution_verified")
            .and_then(Value::as_bool)
            != Some(success)
        {
            return Err("worker semantic status disagrees with case records".into());
        }
        success
    };
    if exit != Some(if success { 0 } else { 1 }) {
        return Err(format!(
            "worker report conflicts with process exit {exit:?}"
        ));
    }
    Ok(success)
}

fn worker_command(executable: &Path, id: &str, report: &Path, args: &[String]) -> Command {
    let mut command = Command::new(executable);
    command
        .arg(WORKER_PREFIX)
        .arg(id)
        .arg(report)
        .arg("--")
        .args(args);
    command
}

pub fn entry(mut args: Vec<String>) -> Result<bool, String> {
    // The invocation nonce and report path travel only in argv. The native
    // cache fingerprints the environment, so per-invocation environment values
    // would prevent setup from warming the subsequent execution's cache.
    let worker_request = if args.first().is_some_and(|s| s == WORKER_PREFIX) {
        if args.len() < 4 || args[1].is_empty() || args[2].is_empty() || args[3] != "--" {
            return Err("malformed internal worker arguments".into());
        }
        let request = (args[1].clone(), PathBuf::from(&args[2]));
        args.drain(..4);
        Some(request)
    } else {
        None
    };
    let config = match Config::parse(args.clone()) {
        Ok(config) => config,
        Err(error) => {
            if worker_request.is_none() {
                let destinations: Vec<_> = args
                    .iter()
                    .enumerate()
                    .filter(|(_, a)| a.as_str() == "--report")
                    .collect();
                if destinations.len() == 1 {
                    if let Some(path) = args
                        .get(destinations[0].0 + 1)
                        .filter(|p| !p.is_empty() && !p.starts_with("--"))
                    {
                        write_report(
                            Path::new(path),
                            &json!({"invocation":invocation_id(),"phase":"arguments","status":"failed","semantic_execution_verified":false,"summary":{"passed":0,"failed":0,"incomplete":0,"host_harness":0,"explicitly_excluded":0},"cases":[],"reason":error}),
                        )?;
                        return Err(error);
                    }
                }
                return Err(format!(
                    "{error}; no report destination selected: --report is absent, missing its value, or ambiguous"
                ));
            }
            return Err(error);
        }
    };
    if let Some((id, path)) = worker_request {
        let names = selected(&config)?;
        let (report, success) = match worker(&config, &id) {
            Ok(result) => result,
            Err(error) => (pending(&config, &id, &names, "failed", &error), false),
        };
        write_report(&path, &report)?;
        return Ok(success);
    }
    let id = invocation_id();
    let report_path = config
        .report
        .clone()
        .unwrap_or_else(|| crate::root().join("target/shared-cases/latest.json"));
    let mut report = pending(
        &config,
        &id,
        &[],
        "running",
        "input validation has not completed",
    );
    write_report(&report_path, &report)?;
    let started = Instant::now();
    let result: Result<bool, String> = (|| {
        valid_root(&config)?;
        backend()?;
        let names = selected(&config)?;
        let identity = crate::shared_cases::input_identity(&config.root, &config.filter)?;
        report = pending(&config, &id, &names, "running", "worker has not completed");
        report["input_identity"] = identity.clone();
        write_report(&report_path, &report)?;
        let directory = report_path
            .parent()
            .unwrap_or(Path::new("."))
            .join(".shared-cases-runs")
            .join(&id);
        fs::create_dir_all(&directory).map_err(|e| e.to_string())?;
        let worker_path = directory.join("result.json");
        let mut command = worker_command(
            &std::env::current_exe().map_err(|e| e.to_string())?,
            &id,
            &worker_path,
            &args,
        );
        let process = match supervise(&mut command, &directory, config.deadline()) {
            Ok(process) => process,
            Err(error) => {
                use std::io::Write;
                let stdout_path = directory.join("worker.stdout");
                let stderr_path = directory.join("worker.stderr");
                let stdout = fs::read(&stdout_path).unwrap_or_default();
                let stderr = fs::read(&stderr_path).unwrap_or_default();
                let _ = std::io::stdout().lock().write_all(&stdout);
                let _ = std::io::stderr().lock().write_all(&stderr);
                report["process"] = json!({"supervision_error":error,"stdout_path":stdout_path,"stderr_path":stderr_path,"stdout_sha256":tauto_syntax::sha256_hex(&stdout),"stderr_sha256":tauto_syntax::sha256_hex(&stderr),"stdout":String::from_utf8_lossy(&stdout),"stderr":String::from_utf8_lossy(&stderr)});
                return Err(error);
            }
        };
        use std::io::Write;
        let forwarded = std::io::stdout()
            .lock()
            .write_all(&process.stdout)
            .and_then(|_| std::io::stderr().lock().write_all(&process.stderr));
        let process_json = json!({"exit_code":process.code,"status":process.status,"timed_out":process.timed_out,"elapsed_ms":process.elapsed.as_millis(),"stdout_path":process.stdout_path,"stdout_sha256":tauto_syntax::sha256_hex(&process.stdout),"stderr_path":process.stderr_path,"stderr_sha256":tauto_syntax::sha256_hex(&process.stderr),"stdout":String::from_utf8_lossy(&process.stdout),"stderr":String::from_utf8_lossy(&process.stderr)});
        report["process"] = process_json.clone();
        forwarded.map_err(|e| format!("cannot forward worker output: {e}"))?;
        let success = if process.timed_out {
            report = pending(
                &config,
                &id,
                &names,
                "timeout",
                &format!(
                    "{} exceeded {} seconds; no selected case is verified by this invocation",
                    config.phase(),
                    config.deadline().as_secs()
                ),
            );
            false
        } else {
            let candidate: Value = serde_json::from_slice(
                &fs::read(&worker_path)
                    .map_err(|e| format!("worker report missing after {}: {e}", process.status))?,
            )
            .map_err(|e| format!("malformed worker report: {e}"))?;
            let success =
                validate_worker_report(&candidate, &id, config.phase(), &names, process.code)?;
            if candidate.get("input_identity") != Some(&identity)
                && candidate.get("status").and_then(Value::as_str) != Some("failed")
            {
                return Err("worker input identity differs from supervisor identity".into());
            }
            report = candidate;
            success
        };
        report["input_identity"] = identity;
        report["process"] = process_json;
        Ok(success)
    })();
    let success = match result {
        Ok(success) => success,
        Err(error) => {
            report["status"] = json!("failed");
            report["reason"] = json!(error);
            if let Some(cases) = report.get_mut("cases").and_then(Value::as_array_mut) {
                for case in cases {
                    case["reasons"] = json!([error]);
                }
            }
            report["semantic_execution_verified"] = json!(false);
            false
        }
    };
    report["elapsed_ms"] = json!(started.elapsed().as_millis());
    write_report(&report_path, &report)?;
    eprintln!(
        "{}",
        json!({"report":report_path,"phase":config.phase(),"status":report["status"],"summary":report["summary"]})
    );
    Ok(success)
}

#[cfg(all(test, unix))]
mod cleanup_tests {
    #[test]
    fn worker_identity_uses_argv_without_changing_cache_environment() {
        let args = vec!["--root".to_string(), "cases".to_string()];
        let command = super::worker_command(
            std::path::Path::new("runner"),
            "nonce",
            std::path::Path::new("report"),
            &args,
        );
        assert_eq!(command.get_envs().count(), 0);
        assert_eq!(
            command
                .get_args()
                .map(|a| a.to_str().unwrap())
                .collect::<Vec<_>>(),
            [
                "--internal-shared-worker",
                "nonce",
                "report",
                "--",
                "--root",
                "cases"
            ]
        );
    }
    #[test]
    fn only_success_and_already_gone_groups_are_successful_cleanup() {
        assert!(super::cleanup_result(0, std::io::Error::from_raw_os_error(1)).is_ok());
        assert!(super::cleanup_result(-1, std::io::Error::from_raw_os_error(3)).is_ok());
        for errno in [1, 22] {
            assert!(super::cleanup_result(-1, std::io::Error::from_raw_os_error(errno)).is_err());
        }
    }
}
