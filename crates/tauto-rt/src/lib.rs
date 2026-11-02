//! The run-time library of Rust code generated from tauto. No `unsafe`, and
//! no dependencies but the HTTP client of the `net` feature and rustls of
//! the `tls` feature.

#![forbid(unsafe_code)]

use std::any::Any;
use std::cell::Cell;
use std::fmt;
use std::sync::{Mutex, MutexGuard, TryLockError};

/// The shared pointer of generated code: `Rc`, or `Arc` when the program
/// starts tasks (the `sync` feature), so what a task holds may cross threads.
#[cfg(not(feature = "sync"))]
pub use std::rc::Rc;
#[cfg(feature = "sync")]
pub use std::sync::Arc as Rc;

pub mod a;
pub mod budget;
pub mod budget_contract;
pub mod child;
pub mod cps;
pub mod ct;
pub mod ev;
pub mod exec;
pub mod float;
mod float_math;
pub mod host;
pub mod int;
pub mod link;
pub use link::{Owned, Shared, Unlink};
pub mod messages;
pub mod nat;
pub use nat::Nat;
pub mod o;
pub mod permissions;
pub mod probe;
#[cfg(feature = "reactor")]
pub mod reactor;
pub mod show;
pub mod signal;
pub mod stdlib;
pub mod tcp;
#[cfg(feature = "tls")]
pub mod tls;
pub mod tls_host;

/// `Text`: immutable. A literal is a `&'static str` and costs no allocation;
/// anything built at run time is shared (`Rc<str>`).
#[derive(Clone)]
pub enum Text {
    Static(&'static str),
    Shared(Rc<str>),
}

impl Text {
    pub const fn lit(s: &'static str) -> Text {
        Text::Static(s)
    }
}

impl std::ops::Deref for Text {
    type Target = str;
    fn deref(&self) -> &str {
        match self {
            Text::Static(s) => s,
            Text::Shared(s) => s,
        }
    }
}

impl AsRef<str> for Text {
    fn as_ref(&self) -> &str {
        self
    }
}

impl From<String> for Text {
    fn from(s: String) -> Text {
        Text::Shared(Rc::from(s))
    }
}

impl From<&str> for Text {
    fn from(s: &str) -> Text {
        Text::Shared(Rc::from(s))
    }
}

impl PartialEq for Text {
    fn eq(&self, other: &Text) -> bool {
        **self == **other
    }
}

impl Eq for Text {}

impl PartialOrd for Text {
    fn partial_cmp(&self, other: &Text) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Text {
    fn cmp(&self, other: &Text) -> std::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl std::hash::Hash for Text {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

impl fmt::Debug for Text {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl fmt::Display for Text {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Never {}

/// A product `A × B × …`: its members in the order of the type, as a tuple.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Product<T>(pub T);

/// A name for an operation, and what is shown when nothing handles it.
pub type OpId = u32;
/// The arguments or the answer of an operation, boxed: the type is known to
/// the generated code that sends and receives it.
pub type Payload = Box<dyn Any>;

/// The operation `show`, which the host handles.
pub const OP_SHOW: Op = Op::new(0, "show");

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Op {
    pub id: OpId,
    pub name: &'static str,
}

impl Op {
    pub const fn new(id: OpId, name: &'static str) -> Op {
        Op { id, name }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Loc {
    pub file: &'static str,
    pub line: u32,
    pub col: u32,
}

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.col)
    }
}

/// A run-time error of the tauto program (the evaluator's `RunError`),
/// raised as a panic payload and reported by [`run_main`].
#[derive(Debug, Clone)]
pub struct TautoError {
    pub message: String,
    pub at: Option<Loc>,
}

pub fn error(message: impl Into<String>, at: Loc) -> ! {
    std::panic::panic_any(TautoError {
        message: message.into(),
        at: Some(at),
    })
}

pub fn error_here(message: impl Into<String>) -> ! {
    std::panic::panic_any(TautoError {
        message: message.into(),
        at: None,
    })
}

/// The same as `eval`'s default step limit.
pub const DEFAULT_STEP_LIMIT: u64 = 10_000_000;

thread_local! {
    static STEPS: Cell<u64> = const { Cell::new(0) };
}

/// `--allow-div` ([`permissions::Permissions::div`]): the host's limit is off.
static DIV_UNBOUNDED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub(crate) fn set_div_unbounded(on: bool) {
    DIV_UNBOUNDED.store(on, std::sync::atomic::Ordering::Relaxed);
}

/// The limit an embedder gave with [`set_step_limit`]; 0 is none given.
static STEP_LIMIT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Sets the host's step limit, over `TAUTO_STEP_LIMIT`: a host that is not a
/// process (a page, a UI on wasm32 with no environment) gives it here, before
/// [`run_embedded`]. 0 brings back `TAUTO_STEP_LIMIT`, else
/// [`DEFAULT_STEP_LIMIT`]. This process setting cannot change during a run.
pub fn set_step_limit(limit: u64) {
    with_config_lock("set_step_limit", || {
        STEP_LIMIT.store(limit, std::sync::atomic::Ordering::Relaxed);
    });
}

pub(crate) fn with_config_lock<T>(operation: &str, f: impl FnOnce() -> T) -> T {
    let _guard = match RUNNING.try_lock() {
        Ok(guard) => guard,
        Err(TryLockError::Poisoned(error)) => error.into_inner(),
        Err(TryLockError::WouldBlock) => {
            panic!("tauto: {operation} cannot change runtime configuration while it is in use")
        }
    };
    f()
}

fn reset_steps() -> (u64, u64) {
    let local = STEPS.with(|steps| steps.replace(0));
    let budget = budget::STEPS.swap(0, std::sync::atomic::Ordering::Relaxed);
    (local, budget)
}

fn restore_steps(previous: (u64, u64)) {
    STEPS.with(|steps| steps.set(previous.0));
    budget::STEPS.store(previous.1, std::sync::atomic::Ordering::Relaxed);
}

fn div_unbounded() -> bool {
    DIV_UNBOUNDED.load(std::sync::atomic::Ordering::Relaxed)
}

fn restore_div_unbounded(value: bool) {
    DIV_UNBOUNDED.store(value, std::sync::atomic::Ordering::Relaxed);
}

static RUNNING: Mutex<()> = Mutex::new(());

struct RunGuard {
    _lock: MutexGuard<'static, ()>,
}

fn enter_run() -> Result<RunGuard, ()> {
    match RUNNING.try_lock() {
        Ok(lock) => Ok(RunGuard { _lock: lock }),
        Err(TryLockError::Poisoned(error)) => Ok(RunGuard {
            _lock: error.into_inner(),
        }),
        Err(TryLockError::WouldBlock) => Err(()),
    }
}

/// The host's step limit: the one [`set_step_limit`] gave, else
/// `TAUTO_STEP_LIMIT`, else [`DEFAULT_STEP_LIMIT`].
fn step_limit() -> u64 {
    match STEP_LIMIT.load(std::sync::atomic::Ordering::Relaxed) {
        0 => env_step_limit(),
        set => set,
    }
}

fn env_step_limit() -> u64 {
    static LIMIT: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *LIMIT.get_or_init(|| {
        std::env::var("TAUTO_STEP_LIMIT")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(DEFAULT_STEP_LIMIT)
    })
}

/// The value in a shared cell that a `match` took apart: moved out when this
/// is the only owner, cloned otherwise.
pub fn unrc<P: link::Unrc>(rc: P) -> P::Target {
    rc.unrc()
}

/// The value in a shared field that a write goes through, unshared first.
pub fn unshare<P: link::Unshare>(rc: &mut P) -> &mut P::Target {
    rc.unshare()
}

pub fn unbox<P: link::Unbox>(b: P) -> P::Target {
    b.unbox()
}

/// The `clone` of a linear value, which the checker never lets two owners
/// share: reaching it is a bug in the generator.
pub fn linear_clone<T>(what: &'static str) -> T {
    panic!("tauto: a linear value was copied: {what}")
}

pub fn no_arm(at: Loc) -> ! {
    error(messages::NO_ARM, at)
}

pub fn nat_is<T: std::borrow::Borrow<Nat>>(t: &T, lit: u64) -> bool {
    *t.borrow() == Nat::from_u64(lit)
}

pub fn text_is<T: AsRef<str>>(t: &T, lit: &str) -> bool {
    t.as_ref() == lit
}

/// Puts `n` as this thread's count of steps outside any `budget` and gives
/// the count it replaces: a reactor keeps one count for each task it runs.
pub fn swap_steps(n: u64) -> u64 {
    STEPS.with(|s| s.replace(n))
}

/// Counts one step of a loop or a call that may not stop, outside any
/// `budget`. With `--allow-div` it counts nothing.
pub fn host_tick(at: Loc) {
    if DIV_UNBOUNDED.load(std::sync::atomic::Ordering::Relaxed) {
        return;
    }
    let n = STEPS.with(|s| {
        s.set(s.get() + 1);
        s.get()
    });
    if n > step_limit() {
        error(
            format!(
                "{} after {} steps; `TAUTO_STEP_LIMIT=N` raises it, `--allow-div` lifts it",
                messages::STEP_LIMIT,
                step_limit()
            ),
            at,
        );
    }
}

/// A linear value dropped: in a debug build, it is a bug in tauto's use
/// check or in the generator.
#[derive(Debug)]
pub struct Bomb {
    armed: bool,
    what: &'static str,
}

impl Bomb {
    pub fn new(what: &'static str) -> Bomb {
        Bomb { armed: true, what }
    }

    pub fn defuse(mut self) {
        self.armed = false;
    }
}

impl Drop for Bomb {
    fn drop(&mut self) {
        if cfg!(debug_assertions) && self.armed && !std::thread::panicking() {
            panic!("tauto: a linear value was dropped: {}", self.what);
        }
    }
}

/// The stack of the program's threads, its `main`'s, each task's and each
/// reactor worker's (`TAUTO_STACK_MB`, 1024 by default): a recursion that
/// ends on `main` ends in a task too.
pub fn stack_bytes() -> usize {
    static BYTES: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *BYTES.get_or_init(|| {
        let mb = std::env::var("TAUTO_STACK_MB")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(1024);
        mb << 20
    })
}

/// Runs the program's `main`: reports a [`TautoError`] as
/// `{file}:{line}:{col}: {message}` on the standard error and exits with 1;
/// any other panic (a Rust extern's) is `interrupted: …`.
///
/// The program runs on a thread with a large stack (`TAUTO_STACK_MB`, 1024 by
/// default; the memory is only used as it is touched): recursion over a long
/// list is how tauto walks it, and so is dropping one. A target without
/// threads (wasm32) runs it on the calling thread, whose stack the linker
/// sized.
pub fn run_main(main: impl FnOnce() + Send) -> std::process::ExitCode {
    run_main_with(std::env::args().skip(1).collect(), main)
}

/// [`run_main`] for a program that is not the process's own: `args` are what
/// the program's command line would be, after the executable's name.
pub fn run_main_with(args: Vec<String>, main: impl FnOnce() + Send) -> std::process::ExitCode {
    let Ok(_run) = enter_run() else {
        eprintln!("tauto: the runtime is already in use");
        return std::process::ExitCode::from(2);
    };
    // The leading `--allow-*` flags are the run's permissions; the program's
    // arguments are the rest (`permissions::Permissions::from_args`).
    match permissions::Permissions::from_args(&args) {
        Ok((granted, rest)) => {
            permissions::set_for_run(granted);
            stdlib::set_args_for_run(rest);
        }
        Err(e) => {
            eprintln!("{e}");
            return std::process::ExitCode::from(2);
        }
    }
    let code = match catch(main, Some(stack_bytes())) {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(text) => {
            eprintln!("{text}");
            std::process::ExitCode::from(1)
        }
    };
    // Diagnostics read by the test suite (`tools/tauto-test-suite`, Rust
    // backend): when set, these print the steps counted against the budget
    // and the dropped probes on stderr after the program ends. They only
    // read state and change neither what runs nor the exit code. They are
    // read at run time rather than behind a feature, because the test suite
    // runs generated programs built the same way as for users.
    if std::env::var_os("TAUTO_REPORT_BUDGET_STEPS").is_some() {
        let steps = budget::STEPS.load(std::sync::atomic::Ordering::Relaxed);
        eprintln!("tauto-budget-steps: {steps}");
    }
    if std::env::var_os("TAUTO_REPORT_PROBE_DROPS").is_some() {
        eprintln!("tauto-probe-drops: {}", probe::dropped().join(","));
    }
    code
}

/// Runs the program's `main` inside a host that is not a process: a page, a
/// UI, a test. The embedder gives the permissions and the arguments (the
/// default `Permissions` denies every kind) and has installed its
/// [`host::Host`] with [`host::set`] if the target has no system, and may
/// set the step limit with [`set_step_limit`]. `Err` is the
/// report [`run_main`] would print: a [`TautoError`] with its place, a panic
/// of a Rust extern, or `exit` with a code other than 0. Only one Tauto
/// program may run in a process at a time; concurrent and nested calls return
/// an error. The closure must finish or cancel every task it starts before it
/// returns. Permissions, arguments, division permission, and step counters
/// are restored on return or unwind. This function leaves the Rust panic hook
/// unchanged. With panic=abort, a panic aborts the process and cannot be
/// returned as an error.
pub fn run_embedded(
    granted: permissions::Permissions,
    args: Vec<String>,
    main: impl FnOnce() + Send,
) -> Result<(), String> {
    let _run = enter_run().map_err(|()| "the runtime is already in use".to_string())?;
    let state = EmbeddedState::save();
    permissions::set_for_run(granted);
    stdlib::set_args_for_run(args);
    let result = catch_unwind_report(main);
    drop(state);
    result
}

struct EmbeddedState {
    permissions: Option<permissions::Permissions>,
    args: Option<Vec<String>>,
    div_unbounded: bool,
    steps: (u64, u64),
}

impl EmbeddedState {
    fn save() -> Self {
        Self {
            permissions: permissions::snapshot(),
            args: stdlib::snapshot_args(),
            div_unbounded: div_unbounded(),
            steps: reset_steps(),
        }
    }
}

impl Drop for EmbeddedState {
    fn drop(&mut self) {
        permissions::restore(self.permissions.take());
        stdlib::restore_args(self.args.take());
        restore_div_unbounded(self.div_unbounded);
        restore_steps(self.steps);
    }
}

fn catch_unwind_report(main: impl FnOnce() + Send) -> Result<(), String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(main)) {
        Ok(()) => Ok(()),
        Err(payload) => catch_unwind_payload(payload),
    }
}

/// Runs `main`, on a thread of `stack` bytes where there are threads, and
/// turns what ends it into a report.
fn catch(main: impl FnOnce() + Send, stack: Option<usize>) -> Result<(), String> {
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|info| {
        let payload = info.payload();
        if cfg!(panic = "abort") {
            // Nothing unwinds to the report below (wasm32 aborts): the
            // report is made here, before the module traps.
            if payload.downcast_ref::<host::Exit>().is_none() {
                host::report(&format!("{}\n", report(payload)));
            }
        } else if payload.downcast_ref::<TautoError>().is_none()
            && payload.downcast_ref::<host::Exit>().is_none()
        {
            // A `TautoError` is reported below, and an `Exit` is no error; the
            // default report would repeat the one and misname the other.
            eprintln!("{info}");
        }
    }));
    let run = move || std::panic::catch_unwind(std::panic::AssertUnwindSafe(main));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match stack {
        Some(bytes) if THREADS => std::thread::scope(|s| {
            std::thread::Builder::new()
                .stack_size(bytes)
                .spawn_scoped(s, run)
                .expect("a thread for the program")
                .join()
                .unwrap_or_else(Err)
        }),
        _ => run(),
    }));
    std::panic::set_hook(previous);
    match result {
        Ok(result) => result.or_else(catch_unwind_payload),
        Err(payload) => catch_unwind_payload(payload),
    }
}

fn catch_unwind_payload(payload: Box<dyn Any + Send>) -> Result<(), String> {
    if let Some(host::Exit(code)) = payload.downcast_ref::<host::Exit>() {
        return if *code == 0 {
            Ok(())
        } else {
            Err(format!("exit {code}"))
        };
    }
    Err(report(&*payload))
}

fn report(payload: &(dyn Any + Send)) -> String {
    if let Some(e) = payload.downcast_ref::<TautoError>() {
        match e.at {
            Some(at) => format!("{at}: {}", e.message),
            None => e.message.clone(),
        }
    } else if let Some(s) = payload.downcast_ref::<&str>() {
        format!("interrupted: {s}")
    } else if let Some(s) = payload.downcast_ref::<String>() {
        format!("interrupted: {s}")
    } else {
        "interrupted: a panic".to_string()
    }
}

/// Whether the target can start threads: wasm32 without the `atomics`
/// target feature cannot.
pub const THREADS: bool = !cfg!(all(target_family = "wasm", not(target_feature = "atomics")));
