//! `tauto run PATH` (and `--backend vm`), `tauto dev PATH`: the checked program, compiled to the
//! bytecode of the machine written in Tauto (`totes/vm`) and run on it. The
//! machine is compiled to Rust when `tauto` is built (`tauto-cli-totes`) and
//! is part of this executable: a run starts `tauto` again on it, and nothing
//! is compiled. `TAUTO_VM=rust` runs the program on the machine of `tauto-vm`
//! in this process instead, to compare the two.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use crate::tote_main::TOTE_FLAG;

use tauto_nibcheck::lower::CompileError;
use tauto_rt::permissions::{Grant, Permissions};

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

    pub(crate) fn finish(&self) {
        if let Prepared::Machine { dir, .. } = self {
            let _ = std::fs::remove_dir_all(dir);
        }
    }
}

pub fn command(args: &[String]) -> ExitCode {
    let prepared = match prepare(&args[1..], u64::MAX, None, "main-run-interrupted") {
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
/// `default_steps` the one of a run without it (the host's when `None`), and
/// `interrupted_hint` the id of what the message says after the steps run out.
pub(crate) fn prepare(
    args: &[String],
    unlimited: u64,
    default_steps: Option<u64>,
    interrupted_hint: &str,
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
    // `--tote NAME` resolves to a member directory; a bare file path stays as written.
    let path = if run.tote.is_some() {
        run.tote_dir()?.display().to_string()
    } else {
        run.file.clone().ok_or_else(super::usage)?
    };
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
    if run.tote.is_some()
        && !tauto::manifest::tote_entry(p).is_some_and(|entry| entry.is_file())
    {
        let name = run.tote.as_deref().unwrap_or(path.as_str());
        eprintln!("{}", crate::i18n::t!("main-run-tote-no-main", name = name));
        return Err(ExitCode::from(2));
    }
    // The bytecode of a tote's program and the permissions it needs are kept
    // with what it was read from (`rust_cache`), as the crate of `--backend
    // rust` is: while tauto itself, the arguments and every file the reading
    // depended on are unchanged, the run starts from the kept bytecode instead
    // of reading, checking and compiling the tote again. A run that lacks a
    // permission is refused before anything else.
    let kept = tote.as_ref().and_then(|d| {
        let key: Vec<String> = own[..end]
            .iter()
            .filter(|a| *a != "--yes")
            .cloned()
            .collect();
        super::rust_cache::lookup_outputs("vm-program", d, &key)
    });
    if let Some((_, Some(outputs))) = &kept
        && let Some(Ok(needed)) = outputs
            .get("permissions")
            .map(|b| String::from_utf8(b.clone()))
    {
        let permissions = run.grant(needed.split('\n').filter(|p| !p.is_empty()))?;
        if !in_process_vm()
            && let Some(Ok(bytecode)) = outputs
                .get("bytecode")
                .map(|b| String::from_utf8(b.clone()))
        {
            return machine(
                permissions,
                run,
                bytecode,
                unlimited,
                default_steps,
                interrupted_hint,
            );
        }
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
    super::require_entry(&loaded, &path)?;
    // The JavaScript backend's lowering: every function runs with explicit
    // continuations, as the machine runs them.
    let package = match tauto_nibcheck::lower::compile_loaded_with_observer(
        &loaded,
        false,
        tauto_nir::Target::JavaScript,
        |_| {},
    ) {
        Ok(p) => p,
        Err(CompileError::Front(m) | CompileError::Package(m)) => {
            eprintln!("{}", super::locate_front(&loaded, &path, &m));
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
                crate::i18n::t!("vm-unsupported", place = place, what = u.what.clone())
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
    // What is asked: the package's permissions, and `div` when the top level
    // may not stop; kept with the bytecode as the same list.
    let needed: Vec<String> = {
        let rows = loaded.check_rows(tauto::rows::Target::Rust);
        super::needed_permissions(&loaded, &rows)
    };
    let permissions = run.grant(needed.iter().map(String::as_str))?;
    if in_process_vm() {
        let steps = steps_of(&run, &permissions, unlimited, default_steps);
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
            let key = if tauto_vm::wire::refused(&what) {
                "vm-unsupported"
            } else {
                "vm-unsupported-yet"
            };
            eprintln!("{}", crate::i18n::t!(key, place = &path, what = &what));
            return Err(ExitCode::FAILURE);
        }
    };
    if let Some((lookup, _)) = &kept {
        let needed = needed.join("\n");
        super::rust_cache::keep_outputs(
            lookup,
            &loaded,
            &[
                ("permissions".to_string(), needed.as_bytes()),
                ("bytecode".to_string(), bytecode.as_bytes()),
            ],
        );
    }
    machine(
        permissions,
        run,
        bytecode,
        unlimited,
        default_steps,
        interrupted_hint,
    )
}

/// The step limit of `run`: `unlimited` with `div` allowed, otherwise
/// `--steps` or `default_steps` (the host's when `None`).
fn steps_of(
    run: &super::RunArgs,
    permissions: &Permissions,
    unlimited: u64,
    default_steps: Option<u64>,
) -> u64 {
    run.steps.unwrap_or(if permissions.div == Grant::All {
        unlimited
    } else {
        default_steps.unwrap_or(tauto_rt::DEFAULT_STEP_LIMIT)
    })
}

/// `TAUTO_VM=rust`: the program runs on the machine of `tauto-vm` in this process.
fn in_process_vm() -> bool {
    std::env::var_os("TAUTO_VM").is_some_and(|v| v == "rust")
}

/// Writes `bytecode` for the machine and gives its arguments.
fn machine(
    permissions: Permissions,
    run: super::RunArgs,
    bytecode: String,
    unlimited: u64,
    default_steps: Option<u64>,
    interrupted_hint: &str,
) -> Result<Prepared, ExitCode> {
    let steps = steps_of(&run, &permissions, unlimited, default_steps);
    let flags = crate::run_prompt::flags(&permissions);
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
    let interrupted = limit.map(|steps| {
        format!(
            "{} {}",
            crate::i18n::t!("eval-step-limit"),
            crate::i18n::t!(interrupted_hint, steps = steps)
        )
    });
    let args = tauto_vm::wire::machine_args(
        &flags,
        &file,
        limit,
        None,
        interrupted.as_deref(),
        Some(
            &crate::i18n::t!("eval-too-deep", depth = tauto_vm::wire::MACHINE_MAX_FRAMES)
                .to_string(),
        ),
        &run.program_args,
    );
    Ok(Prepared::Machine { dir, args })
}

fn in_process(
    path: &str,
    package: &tauto_nir::Package,
    program_args: Vec<String>,
    permissions: Permissions,
    steps: u64,
) -> ExitCode {
    let mut program = match tauto_vm::compile(package) {
        Ok(p) => p,
        Err(what) => {
            eprintln!(
                "{}",
                crate::i18n::t!("vm-unsupported", place = path, what = &what)
            );
            return ExitCode::FAILURE;
        }
    };
    if jit_on() {
        tauto_jit::attach(&mut program, package);
    }
    let mut host = tauto_vm::Process {
        args: program_args,
        permissions,
    };
    match tauto_vm::run(&program, &mut host, steps) {
        tauto_vm::End::Done => ExitCode::SUCCESS,
        tauto_vm::End::Exit(code) => ExitCode::from(code as u8),
        tauto_vm::End::Error(message) if message == tauto_rt::messages::STEP_LIMIT => {
            eprintln!(
                "{} {}",
                crate::i18n::t!("eval-step-limit"),
                crate::i18n::t!("main-run-interrupted", steps = steps)
            );
            ExitCode::FAILURE
        }
        tauto_vm::End::Error(message) if message == tauto_vm::machine::TOO_DEEP => {
            eprintln!(
                "{}",
                crate::i18n::t!("eval-too-deep", depth = tauto_vm::machine::MAX_FRAMES)
            );
            ExitCode::FAILURE
        }
        tauto_vm::End::Error(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

/// Whether the Rust machine (`TAUTO_VM=rust`) runs some functions as native
/// code (`docs/design/jit.md`): unless `TAUTO_JIT` is `0`. The machine of
/// `totes/vm` has no native code.
fn jit_on() -> bool {
    std::env::var_os("TAUTO_JIT").is_none_or(|v| v != "0")
}

/// Runs an already loaded and granted program on the machine, without a step
/// limit (a project's command, `commands.rs`); `path` names it in messages.
pub(crate) fn run_loaded(
    loaded: &tauto::program::Loaded,
    path: &str,
    permissions: Permissions,
    program_args: &[String],
) -> ExitCode {
    let package = match tauto_nibcheck::lower::compile_loaded_with_observer(
        loaded,
        false,
        tauto_nir::Target::JavaScript,
        |_| {},
    ) {
        Ok(p) => p,
        Err(CompileError::Front(m) | CompileError::Package(m)) => {
            eprintln!("{}", super::locate_front(loaded, path, &m));
            return ExitCode::FAILURE;
        }
        Err(CompileError::Unsupported(u)) => {
            eprintln!(
                "{}",
                crate::i18n::t!("vm-unsupported", place = path, what = u.what.clone())
            );
            return ExitCode::FAILURE;
        }
        Err(e) => {
            eprintln!("{path}: {e}");
            return ExitCode::FAILURE;
        }
    };
    if in_process_vm() {
        return in_process(path, &package, program_args.to_vec(), permissions, u64::MAX);
    }
    let bytecode = match tauto_vm::wire::write(&package) {
        Ok(b) => b,
        Err(what) => {
            let key = if tauto_vm::wire::refused(&what) {
                "vm-unsupported"
            } else {
                "vm-unsupported-yet"
            };
            eprintln!("{}", crate::i18n::t!(key, place = path, what = &what));
            return ExitCode::FAILURE;
        }
    };
    static RUNS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "tauto-vm-command-{}-{}",
        std::process::id(),
        RUNS.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    let file = dir.join("program.bc");
    if let Err(e) = std::fs::create_dir_all(&dir).and_then(|()| std::fs::write(&file, bytecode)) {
        eprintln!("{}: {e}", file.display());
        return ExitCode::FAILURE;
    }
    let flags = crate::run_prompt::flags(&permissions);
    let args = tauto_vm::wire::machine_args(&flags, &file, None, None, None, None, program_args);
    let code = tauto_cli_totes::main("vm", args).unwrap_or(ExitCode::FAILURE);
    let _ = std::fs::remove_dir_all(&dir);
    code
}
