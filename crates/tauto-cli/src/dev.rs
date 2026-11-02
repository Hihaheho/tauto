//! `tauto dev`: runs a program and runs it again from the start whenever one
//! of its files changes (`docs/design/dev.md`). It runs on the machine
//! written in Tauto, as `tauto run` does; `--backend eval` runs it on the
//! evaluator.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, SystemTime};

use tauto::eval::{RunError, RunOptions};

use crate::{RunArgs, i18n, locate_in, parse_run_args};

const POLL: Duration = Duration::from_millis(250);

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Backend {
    Vm,
    Eval,
}

pub fn command(args: &[String], backend: Backend) -> ExitCode {
    let own = args.iter().position(|a| a == "--").unwrap_or(args.len());
    let without_backend: Vec<String> = match args[..own].iter().position(|a| a == "--backend") {
        Some(at) => [&args[..at], &args[(at + 2).min(args.len())..]].concat(),
        None => args.to_vec(),
    };
    let args = &without_backend[..];
    let run = match parse_run_args(args) {
        Ok(run) => run,
        Err(code) => return code,
    };
    let root = watched_root(&run);
    eprintln!(
        "{}",
        i18n::t!("dev-watching", path = root.display().to_string())
    );
    let stop = Arc::new(AtomicBool::new(false));
    tauto_rt::tcp::keep_listeners(stop.clone());
    if backend == Backend::Vm && run.check_ownership {
        eprintln!("{}", i18n::t!("vm-check-ownership"));
        return ExitCode::from(2);
    }
    let run = Arc::new((run, backend, args.to_vec()));
    let mut before = snapshot(&root);
    let mut worker = Some(spawn(&run, &stop));
    loop {
        std::thread::sleep(POLL);
        if worker.as_ref().is_some_and(|w| w.is_finished()) {
            let _ = worker.take().map(|w| w.join());
            eprintln!("{}", i18n::t!("dev-waiting"));
        }
        let now = snapshot(&root);
        if now == before {
            continue;
        }
        let changed = changes(&before, &now);
        before = now;
        eprintln!("{}", i18n::t!("dev-changed", files = changed.join(", ")));
        // The new version is checked before the running one is stopped: a
        // version that does not check leaves the running one as it is.
        let checks = {
            let run = run.clone();
            on_deep_stack(move || run.0.load().is_ok())
        };
        if !checks {
            if worker.is_some() {
                eprintln!("{}", i18n::t!("dev-keeps-running"));
            }
            continue;
        }
        if let Some(w) = worker.take() {
            stop.store(true, Ordering::Relaxed);
            // A read or write waiting on a stream ends when it is closed.
            tauto_rt::tcp::drop_streams();
            tauto_rt::tls_host::drop_sessions();
            let _ = w.join();
        }
        eprintln!("{}", i18n::t!("dev-running-again"));
        worker = Some(spawn(&run, &stop));
    }
}

fn on_deep_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .expect("a thread for the checker")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
}

fn spawn(
    run: &Arc<(RunArgs, Backend, Vec<String>)>,
    stop: &Arc<AtomicBool>,
) -> std::thread::JoinHandle<()> {
    stop.store(false, Ordering::Relaxed);
    let (run, stop) = (run.clone(), stop.clone());
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || match run.1 {
            Backend::Eval => run_once(&run.0, stop),
            Backend::Vm => run_once_on_vm(&run.2, stop),
        })
        .expect("a thread for the program")
}

/// Loads, checks and runs the program once: until it ends, fails or is
/// stopped. What it prints is written as it happens.
fn run_once(run: &RunArgs, stop: Arc<AtomicBool>) {
    let Ok(loaded) = run.load() else {
        return;
    };
    let options = RunOptions {
        check_ownership: run.check_ownership,
        args: run.program_args.clone(),
        permissions: run.permissions.clone(),
        live: true,
        cancel: Some(stop.clone()),
        ..RunOptions::default()
    };
    // Unlimited unless `--steps` is given: a server runs until a change.
    let steps = run.steps.unwrap_or(u64::MAX);
    match tauto::eval::run_loaded_with(&loaded, steps, options) {
        Ok(_) if stop.load(Ordering::Relaxed) => {}
        Ok(outcome) => match outcome.exit {
            Some(code) if code != 0 => {
                eprintln!("{}", i18n::t!("dev-exited", code = code.to_string()))
            }
            _ => eprintln!("{}", i18n::t!("dev-ended")),
        },
        Err(_) if stop.load(Ordering::Relaxed) => {}
        Err(error) => {
            let mut message = locate_in(&loaded, &run.entry(), &error.to_string());
            if matches!(error, RunError::Interrupted) {
                message.push(' ');
                message.push_str(&i18n::t!("dev-interrupted", steps = steps));
            }
            eprintln!("{message}");
        }
    }
}

/// Compiles the program and runs it once on the machine: until it ends,
/// fails or is stopped.
fn run_once_on_vm(args: &[String], stop: Arc<AtomicBool>) {
    // Unlimited unless `--steps` is given: a server runs until a change.
    let Ok(prepared) = crate::vm::prepare(args, u64::MAX, Some(u64::MAX)) else {
        return;
    };
    let mut child = match &prepared {
        crate::vm::Prepared::Machine { .. } => match prepared.spawn() {
            Ok(child) => child,
            Err(e) => {
                eprintln!("{}", crate::i18n::t!("dev-error", error = e.to_string()));
                prepared.finish();
                return;
            }
        },
        crate::vm::Prepared::InProcess { .. } => {
            eprintln!("{}", i18n::t!("dev-vm-in-process"));
            return;
        }
    };
    let status = loop {
        if stop.load(Ordering::Relaxed) {
            let _ = child.kill();
            let _ = child.wait();
            prepared.finish();
            return;
        }
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => std::thread::sleep(Duration::from_millis(20)),
            Err(e) => {
                eprintln!("{e}");
                prepared.finish();
                return;
            }
        }
    };
    prepared.finish();
    match status.code() {
        Some(0) => eprintln!("{}", i18n::t!("dev-ended")),
        Some(code) => eprintln!("{}", i18n::t!("dev-exited", code = code.to_string())),
        None => eprintln!("{}", i18n::t!("dev-exited", code = status.to_string())),
    }
}

/// The directory whose files are watched: the tote's, or the one the file
/// is in.
fn watched_root(run: &RunArgs) -> PathBuf {
    match (&run.file, &run.tote) {
        (_, Some(dir)) => PathBuf::from(dir),
        (Some(file), None) => match Path::new(file).parent() {
            Some(p) if !p.as_os_str().is_empty() => p.to_path_buf(),
            _ => PathBuf::from("."),
        },
        (None, None) => PathBuf::from("."),
    }
}

/// Each source and manifest file under `root` and when it was last
/// written. Hidden directories and `target` are passed over.
fn snapshot(root: &Path) -> BTreeMap<PathBuf, Option<SystemTime>> {
    let mut out = BTreeMap::new();
    walk(root, &mut out);
    out
}

fn walk(dir: &Path, out: &mut BTreeMap<PathBuf, Option<SystemTime>>) {
    let Ok(read) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in read.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        if kind.is_dir() {
            if !name.starts_with('.') && name != "target" {
                walk(&path, out);
            }
        } else if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("taut" | "tauto" | "eure")
        ) {
            let modified = entry.metadata().and_then(|m| m.modified()).ok();
            out.insert(path, modified);
        }
    }
}

fn changes(
    before: &BTreeMap<PathBuf, Option<SystemTime>>,
    now: &BTreeMap<PathBuf, Option<SystemTime>>,
) -> Vec<String> {
    let mut out: Vec<String> = now
        .iter()
        .filter(|(p, m)| before.get(*p) != Some(m))
        .map(|(p, _)| p.display().to_string())
        .collect();
    out.extend(
        before
            .keys()
            .filter(|p| !now.contains_key(*p))
            .map(|p| p.display().to_string()),
    );
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_written_file_is_a_change() {
        let dir = std::env::temp_dir().join(format!("tauto-dev-{}", std::process::id()));
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::create_dir_all(dir.join("target")).unwrap();
        let main = dir.join("src/main.taut");
        std::fs::write(&main, "a").unwrap();
        std::fs::write(dir.join("target/x.taut"), "a").unwrap();
        std::fs::write(dir.join("notes.txt"), "a").unwrap();
        let before = snapshot(&dir);
        assert_eq!(before.keys().collect::<Vec<_>>(), vec![&main]);
        std::fs::write(dir.join("notes.txt"), "b").unwrap();
        assert_eq!(snapshot(&dir), before);
        std::fs::write(dir.join("src/lib.taut"), "b").unwrap();
        let now = snapshot(&dir);
        assert_eq!(
            changes(&before, &now),
            vec![dir.join("src/lib.taut").display().to_string()]
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
