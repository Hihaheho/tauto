//! Runs a program on the bytecode machine of `tauto-vm` in this process, as
//! a test or a tool reads the run: what it shows and writes, how it ends,
//! and the tests it called. `tauto run` runs the same bytecode on the
//! machine written in Tauto (`tauto-cli/src/vm.rs`).

use std::cell::RefCell;
use std::rc::Rc;

use tauto_message::{Message, msg};

use crate::program::Loaded;

pub use tauto_rt::permissions::{Grant, Permissions};

/// The step limit of a run that names none.
pub const DEFAULT_BUDGET: u64 = tauto_rt::DEFAULT_STEP_LIMIT;

/// What a program did: `perform show(name, v)` as `(name, v)`, in order,
/// what it wrote, the code it exited with, and the tests it called
/// (`tauto_rt::entry`): the name and the message of the `fail` that ended
/// the body, if one did.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Outcome {
    pub outputs: Vec<(String, String)>,
    /// The case host's probes (`Probe::new(name)`) dropped, by name, in order.
    pub probe_drops: Vec<String>,
    pub stdout: String,
    pub stderr: String,
    pub exit: Option<i32>,
    pub tests: Vec<(String, Option<String>)>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RunError {
    Syntax(String),
    /// The checker rejected the program; it did not run.
    Type(String),
    /// The use check rejected the program; it did not run.
    Use(String),
    /// The row check rejected the program; it did not run.
    Row(String),
    /// The program needs a permission the run was not given; it did not run.
    Denied(String),
    /// The machine cannot run the program.
    Unsupported(String),
    /// An error of the running program.
    Runtime(String),
    /// The step limit ran out.
    Interrupted,
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RunError::Syntax(m) => write!(f, "{}", msg!("eval-syntax-error", error = m)),
            RunError::Type(m) => write!(f, "{}", msg!("eval-type-error", error = m)),
            RunError::Use(m) => write!(f, "{}", msg!("eval-use-error", error = m)),
            RunError::Interrupted => write!(f, "{}", msg!("eval-step-limit")),
            RunError::Row(m)
            | RunError::Denied(m)
            | RunError::Unsupported(m)
            | RunError::Runtime(m) => write!(f, "{m}"),
        }
    }
}

/// What a run is given besides the program and its step limit.
#[derive(Debug, Clone, Default)]
pub struct RunOptions {
    pub args: Vec<String>,
    /// What the standard effects may ask of the host
    /// (`docs/design/host-effects.md`); nothing by default.
    pub permissions: Permissions,
}

/// Reads `source` as the one file it is, as `tauto run` reads a file, and
/// runs it with the default step limit.
pub fn run(source: &str) -> Result<Outcome, RunError> {
    run_with_budget(source, DEFAULT_BUDGET)
}

pub fn run_with_budget(source: &str, budget: u64) -> Result<Outcome, RunError> {
    run_source_with(source, budget, RunOptions::default())
}

pub fn run_source_with(
    source: &str,
    budget: u64,
    options: RunOptions,
) -> Result<Outcome, RunError> {
    tauto_parse::install();
    let entry = std::path::Path::new(crate::nir::TEXT_ENTRY);
    let loaded = crate::program::load_with_source(entry, &|path: &std::path::Path| {
        (path == entry).then(|| Ok(source.to_string()))
    })
    .map_err(|e| RunError::Syntax(e.to_string()))?;
    if let Some((message, _)) = loaded.program.errors.first() {
        return Err(RunError::Syntax(message.to_string()));
    }
    run_loaded_with(&loaded, budget, options)
}

/// Checks, compiles and runs a loaded program, with the evidence its loader
/// kept (a function the kernel accepted as total does not perform `div`).
pub fn run_loaded_with(
    loaded: &Loaded,
    budget: u64,
    options: RunOptions,
) -> Result<Outcome, RunError> {
    tauto_parse::install();
    let mut resolved = loaded.clone();
    resolved.resolve_runtime();
    // The imported files' top levels never run, and their types are checked
    // all the same, as `tauto check` checks them: a program `check` rejects
    // is not one `run` runs.
    if !resolved.imported_top.is_empty() {
        let report = crate::types::check_program(&resolved.program_with_imports());
        if let Some(error) = report.errors.first() {
            return Err(RunError::Type(error.to_string()));
        }
    }
    let rows = resolved.check_rows(crate::rows::Target::Rust);
    if let Some(e) = rows
        .errors
        .iter()
        .find(|e| !tauto_nibcheck::lower::in_macro_function(&resolved.program, e))
    {
        return Err(RunError::Type(e.to_string()));
    }
    if let Some((m, _)) = errors_before_run(&resolved.program, &rows)
        .into_iter()
        .next()
    {
        // A type error is the checker's; the rest are the use check's.
        let typed = crate::types::check_program(&resolved.program)
            .errors
            .is_empty();
        return Err(if typed {
            RunError::Use(m.to_string())
        } else {
            RunError::Type(m.to_string())
        });
    }
    let needed = crate::host::permissions(rows.host_effects.iter());
    let missing = options.permissions.missing(needed);
    if !missing.is_empty() {
        return Err(RunError::Denied(tauto_rt::permissions::missing_message(
            &missing,
        )));
    }
    let package = tauto_nibcheck::lower::compile_loaded_with_observer(
        loaded,
        false,
        tauto_nir::Target::JavaScript,
        |_| {},
    )
    .map_err(|e| match e {
        tauto_nibcheck::lower::CompileError::Front(m)
        | tauto_nibcheck::lower::CompileError::Package(m) => RunError::Type(m),
        tauto_nibcheck::lower::CompileError::Unsupported(u) => {
            RunError::Unsupported(u.what.to_string())
        }
        tauto_nibcheck::lower::CompileError::Build(m) => RunError::Unsupported(m),
    })?;
    run_package(&package, budget, options)
}

/// Runs a compiled package's top level on the machine.
pub fn run_package(
    package: &tauto_nir::Package,
    budget: u64,
    options: RunOptions,
) -> Result<Outcome, RunError> {
    let program = tauto_vm::compile(package).map_err(RunError::Unsupported)?;
    let dropped = Rc::new(RefCell::new(Vec::new()));
    let mut host = Kept {
        outcome: Outcome::default(),
        args: options.args,
        permissions: options.permissions,
        externs: program.externs.iter().map(|n| n.to_string()).collect(),
        dropped: dropped.clone(),
    };
    let end = tauto_vm::run(&program, &mut host, budget);
    let mut outcome = host.outcome;
    match end {
        tauto_vm::End::Done => {}
        tauto_vm::End::Exit(code) => outcome.exit = Some(code),
        tauto_vm::End::Error(m) if m == tauto_rt::messages::STEP_LIMIT => {
            return Err(RunError::Interrupted);
        }
        tauto_vm::End::Error(m) if m == tauto_vm::machine::TOO_DEEP => {
            return Err(RunError::Runtime(
                msg!("eval-too-deep", depth = tauto_vm::machine::MAX_FRAMES).to_string(),
            ));
        }
        tauto_vm::End::Error(m) => return Err(RunError::Runtime(m)),
    }
    outcome.probe_drops = dropped.borrow().clone();
    outcome.tests = tauto_rt::entry::report()
        .tests
        .into_iter()
        .filter_map(|(name, outcome)| match outcome {
            tauto_rt::entry::Outcome::Passed | tauto_rt::entry::Outcome::Retried(_) => {
                Some((name, None))
            }
            tauto_rt::entry::Outcome::Failed(why) => Some((name, Some(why))),
            tauto_rt::entry::Outcome::Stopped | tauto_rt::entry::Outcome::NotRun => None,
        })
        .collect();
    Ok(outcome)
}

/// What `program` with its `rows` is rejected for before anything runs: its
/// type errors, or else its use errors, each as a message and the byte it is
/// at. `tauto check` reports these, so that a program it accepts is not one
/// `run` rejects.
pub fn errors_before_run(
    program: &crate::surface::Program,
    rows: &crate::rows::RowReport,
) -> Vec<(Message, u32)> {
    if rows.entries
        && let Some(wrapped) = crate::host::wrap(program, rows.entries)
    {
        let mut rows = crate::rows::check_rewrapped_rows(rows, &wrapped);
        rows.host_effects.clear();
        rows.host_waits = false;
        rows.entries = false;
        return errors_before_run(&wrapped, &rows);
    }
    let report = crate::types::check_program(program);
    if !report.errors.is_empty() {
        return report
            .errors
            .into_iter()
            .map(|e| (e.message, e.span.start))
            .collect();
    }
    crate::lin::check(program, &report, rows)
        .into_iter()
        .map(|e| (e.message.into(), e.span.start))
        .collect()
}

/// The host of a run kept for the caller.
struct Kept {
    outcome: Outcome,
    args: Vec<String>,
    permissions: Permissions,
    externs: Vec<String>,
    dropped: Rc<RefCell<Vec<String>>>,
}

/// The case host's probe: its drop is written down by name.
struct Probe(String, Rc<RefCell<Vec<String>>>);

impl Drop for Probe {
    fn drop(&mut self) {
        self.1.borrow_mut().push(std::mem::take(&mut self.0));
    }
}

fn text_of(v: &tauto_vm::Value) -> Option<String> {
    match v {
        tauto_vm::Value::Text(t) => Some(t.to_string()),
        tauto_vm::Value::Buf(b) => Some(b.to_string()),
        tauto_vm::Value::Ref(p) => text_of(&p.get().ok()?),
        _ => None,
    }
}

impl tauto_vm::Host for Kept {
    fn show(&mut self, name: &str, value: &str) {
        self.outcome.outputs.push((name.into(), value.into()));
    }
    fn stdout(&mut self, text: &str) {
        self.outcome.stdout.push_str(text);
    }
    fn stderr(&mut self, text: &str) {
        self.outcome.stderr.push_str(text);
    }
    fn args(&self) -> Vec<String> {
        self.args.clone()
    }
    fn permissions(&mut self) -> &mut Permissions {
        &mut self.permissions
    }
    fn call_extern(
        &mut self,
        index: u32,
        args: Vec<tauto_vm::Value>,
    ) -> Result<tauto_vm::Value, String> {
        let name = self.externs.get(index as usize).map(String::as_str);
        match (name, args.first().and_then(text_of)) {
            (Some(n), Some(probe)) if n.ends_with("Probe::new") || n.ends_with("Probe.new") => Ok(
                tauto_vm::Value::Host("Probe".into(), Rc::new(Probe(probe, self.dropped.clone()))),
            ),
            _ => Err(msg!("eval-extern-is-not-runnable", name = name.unwrap_or("?")).to_string()),
        }
    }
}
