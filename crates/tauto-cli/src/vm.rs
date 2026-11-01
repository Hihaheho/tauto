//! `tauto run PATH` (and `--backend vm`), `tauto dev PATH`: the checked program, compiled to the
//! bytecode of the machine written in Tauto (`totes/vm`) and run on it. The
//! machine is compiled to Rust when `tauto` is built (`tauto-cli-totes`) and
//! is part of this executable: a run starts `tauto` again on it, and nothing
//! is compiled. `TAUTO_VM=rust` runs the program on the machine of `tauto-vm`
//! in this process instead, to compare the two.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use crate::tote_main::TOTE_FLAG;

use tauto_nir::CompileError;
use tauto_rt::permissions::{Grant, Permissions};

/// A checked program, compiled and ready to start on the machine.
pub(crate) enum Prepared {
    /// The bytecode, written to `dir`, and the machine's arguments.
    Machine { dir: PathBuf, args: Vec<String> },
    /// `TAUTO_VM=rust`: the machine of `tauto-vm` in this process.
    InProcess {
        path: String,
        package: Box<tauto_nir::Package>,
        program_args: Vec<String>,
        permissions: Permissions,
        steps: u64,
    },
}

impl Prepared {
    /// Starts the machine on the program as a process of its own, for `dev`,
    /// which stops it when a file changes (a run in this process cannot be
    /// stopped); the bytecode is removed by `finish`.
    pub(crate) fn spawn(&self) -> std::io::Result<std::process::Child> {
        match self {
            Prepared::Machine { args, .. } => std::process::Command::new(std::env::current_exe()?)
                .args([TOTE_FLAG, "vm"])
                .args(args)
                .spawn(),
            Prepared::InProcess { .. } => unreachable!("an in-process run is not a child"),
        }
    }

    /// Removes the bytecode.
    pub(crate) fn finish(&self) {
        if let Prepared::Machine { dir, .. } = self {
            let _ = std::fs::remove_dir_all(dir);
        }
    }
}

/// `tauto run [--backend vm] PATH`.
pub fn command(args: &[String]) -> ExitCode {
    let prepared = match prepare(&args[1..], u64::MAX, None) {
        Ok(p) => p,
        Err(code) => return code,
    };
    match &prepared {
        Prepared::InProcess {
            path,
            package,
            program_args,
            permissions,
            steps,
        } => in_process(
            path,
            package,
            program_args.clone(),
            permissions.clone(),
            *steps,
        ),
        // The machine is linked into this executable: `run` calls it here.
        Prepared::Machine { args, .. } => {
            let code = tauto_cli_totes::main("vm", args.clone()).unwrap_or(ExitCode::FAILURE);
            prepared.finish();
            code
        }
    }
}

/// Loads, checks and compiles the program `args` name (the arguments of
/// `run` after the command, `--backend vm` among them or not); an error is
/// printed. `unlimited` is the step limit of a run given `--allow-div`,
/// `default_steps` the one of a run without it (the host's when `None`).
pub(crate) fn prepare(
    args: &[String],
    unlimited: u64,
    default_steps: Option<u64>,
) -> Result<Prepared, ExitCode> {
    // `--backend vm` is this backend's; the rest are `run`'s own.
    let mut own = Vec::new();
    let mut rest = args.iter();
    while let Some(a) = rest.next() {
        match a.as_str() {
            "--backend" => {
                if rest.next().map(String::as_str) != Some("vm") {
                    return Err(super::usage());
                }
            }
            "--" => {
                own.push(a.clone());
                own.extend(rest.by_ref().cloned());
            }
            _ => own.push(a.clone()),
        }
    }
    let run = super::parse_run_args(&own)?;
    if run.check_ownership {
        eprintln!("{}", crate::i18n::t!("vm-check-ownership"));
        return Err(ExitCode::from(2));
    }
    let end = own.iter().position(|a| a == "--").unwrap_or(own.len());
    let flags: Vec<String> = own[..end]
        .iter()
        .filter(|a| *a == "-A" || a.starts_with("--allow-"))
        .cloned()
        .collect();
    let path = run.entry();
    let p = Path::new(&path);
    let tote = if run.tote.is_some() || p.is_dir() {
        Some(p.to_path_buf())
    } else if p.file_name().is_some_and(|n| n == "Tauto.eure") {
        Some(
            p.parent()
                .filter(|d| !d.as_os_str().is_empty())
                .unwrap_or(Path::new("."))
                .to_path_buf(),
        )
    } else {
        None
    };
    if let Some(dir) = &run.tote
        && !["src/main.taut", "src/main.tauto"]
            .iter()
            .any(|name| Path::new(dir).join(name).is_file())
    {
        let name = Path::new(dir)
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or(dir);
        eprintln!("{}", crate::i18n::t!("main-run-tote-no-main", name = name));
        return Err(ExitCode::from(2));
    }
    let loaded = match &tote {
        Some(d) => tauto::program::load_tote_for_build(d),
        None => tauto::program::load_extracted(p),
    };
    let loaded = match loaded {
        Ok(l) => l,
        Err(e) => {
            eprintln!("{e}");
            return Err(ExitCode::FAILURE);
        }
    };
    // The JavaScript backend's lowering: every function runs with explicit
    // continuations, as the machine runs them.
    let package = match tauto_nir::compile_loaded_with_observer(&loaded, false, true, |_| {}) {
        Ok(p) => p,
        Err(CompileError::Front(m)) => {
            eprintln!("{}", super::locate_in(&loaded, &path, &m));
            return Err(ExitCode::FAILURE);
        }
        Err(CompileError::Unsupported(u)) => {
            let place = u
                .span
                .and_then(|span| {
                    let (file, line, col) = loaded.locate(span.start)?;
                    Some(format!("{}:{line}:{col}", file.display()))
                })
                .unwrap_or_else(|| path.clone());
            eprintln!(
                "{}",
                crate::i18n::t!("vm-unsupported", place = place, what = &u.what)
            );
            return Err(ExitCode::FAILURE);
        }
        Err(e) => {
            eprintln!("{path}: {e}");
            return Err(ExitCode::FAILURE);
        }
    };
    // The permissions of the standard effects that reach the top level: a
    // run without one of them does not start.
    let permissions = run.permissions;
    let missing = permissions.missing(package.permissions.iter().map(String::as_str));
    if !missing.is_empty() {
        eprintln!("{}", tauto_rt::permissions::missing_message(&missing));
        return Err(ExitCode::from(2));
    }
    let steps = run.steps.unwrap_or(if permissions.div == Grant::All {
        unlimited
    } else {
        default_steps.unwrap_or(tauto_rt::DEFAULT_STEP_LIMIT)
    });
    if std::env::var_os("TAUTO_VM").is_some_and(|v| v == "rust") {
        return Ok(Prepared::InProcess {
            path,
            package: Box::new(package),
            program_args: run.program_args,
            permissions,
            steps,
        });
    }
    let bytecode = match tauto_vm::wire::write(&package) {
        Ok(b) => b,
        Err(what) => {
            eprintln!(
                "{}",
                crate::i18n::t!("vm-unsupported-yet", place = &path, what = &what)
            );
            return Err(ExitCode::FAILURE);
        }
    };
    static RUNS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "tauto-vm-{}-{}",
        std::process::id(),
        RUNS.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    let file = dir.join("program.bc");
    if let Err(e) = std::fs::create_dir_all(&dir).and_then(|()| std::fs::write(&file, bytecode)) {
        eprintln!("{}: {e}", file.display());
        return Err(ExitCode::FAILURE);
    }
    let limit = (steps != u64::MAX).then_some(steps);
    let args = tauto_vm::wire::machine_args(&flags, &file, limit, None, &run.program_args);
    Ok(Prepared::Machine { dir, args })
}

fn in_process(
    path: &str,
    package: &tauto_nir::Package,
    program_args: Vec<String>,
    permissions: Permissions,
    steps: u64,
) -> ExitCode {
    let program = match tauto_vm::compile(package) {
        Ok(p) => p,
        Err(what) => {
            eprintln!(
                "{}",
                crate::i18n::t!("vm-unsupported", place = path, what = &what)
            );
            return ExitCode::FAILURE;
        }
    };
    let mut host = tauto_vm::Process {
        args: program_args,
        permissions,
    };
    match tauto_vm::run(&program, &mut host, steps) {
        tauto_vm::End::Done => ExitCode::SUCCESS,
        tauto_vm::End::Exit(code) => ExitCode::from(code as u8),
        tauto_vm::End::Error(message) if message == tauto_rt::messages::STEP_LIMIT => {
            eprintln!(
                "{message} {}",
                crate::i18n::t!("main-run-interrupted", steps = steps)
            );
            ExitCode::FAILURE
        }
        tauto_vm::End::Error(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}
