//! Where the bodies of tasks run (`perform spawn`). The host picks an
//! `Executor` once, before the program starts; a program that never picks
//! gets a thread for each task, or on a target without threads (wasm32)
//! runs each to its end at the `spawn`. Another pool plugs in by implementing
//! the trait. A program built with the `reactor` feature (`rust.executor =
//! "tokio"`, the default) installs a reactor instead (`crate::reactor`), which
//! runs many tasks on each of its threads.

use std::any::Any;
use std::sync::{Arc, Mutex, OnceLock, PoisonError};

use crate::signal::Signal;

use crate::Rc;
use crate::ev::Ev;
#[cfg(feature = "sync")]
use crate::o::Fut;

pub trait Executor: Send + Sync {
    fn execute(&self, job: Box<dyn FnOnce() + Send + 'static>);
}

/// A thread for each task, with the stack of `main` ([`crate::stack_bytes`]).
pub struct Threads;

impl Executor for Threads {
    fn execute(&self, job: Box<dyn FnOnce() + Send + 'static>) {
        std::thread::Builder::new()
            .name("tauto-task".into())
            .stack_size(crate::stack_bytes())
            .spawn(job)
            .expect("a thread for the task");
    }
}

/// Each task runs to its end at the `spawn`.
pub struct Inline;

impl Executor for Inline {
    fn execute(&self, job: Box<dyn FnOnce() + Send + 'static>) {
        job();
    }
}

static EXECUTOR: OnceLock<Box<dyn Executor>> = OnceLock::new();

/// Picks the executor of the program; `false` if one is already picked.
pub fn set_executor(e: Box<dyn Executor>) -> bool {
    EXECUTOR.set(e).is_ok()
}

#[cfg(feature = "sync")]
fn executor() -> &'static dyn Executor {
    EXECUTOR
        .get_or_init(|| {
            if crate::THREADS {
                Box::new(Threads)
            } else {
                Box::new(Inline)
            }
        })
        .as_ref()
}

type Outcome<A> = Result<A, Box<dyn Any + Send>>;

/// Where a running task leaves what ends it, and the signal it raises then.
pub struct Slot<A> {
    outcome: Mutex<Option<Outcome<A>>>,
    done: Signal,
}

/// What a running task holds that its failure poisons: the mutexes whose
/// content it took and has not put back.
pub trait Poison: Send + Sync {
    fn poison(&self, task: usize);
}

/// A running task, as the mutexes it takes from know it.
#[cfg(feature = "sync")]
#[derive(Default)]
pub struct TaskCtx {
    held: Mutex<Vec<std::sync::Weak<dyn Poison>>>,
}

#[cfg(feature = "sync")]
impl TaskCtx {
    fn id(self: &Arc<Self>) -> usize {
        Arc::as_ptr(self) as usize
    }

    /// The task failed: each mutex it holds the content of is poisoned.
    fn poison_all(self: &Arc<Self>) {
        let held = std::mem::take(&mut *self.held.lock().unwrap_or_else(PoisonError::into_inner));
        for h in held {
            if let Some(h) = h.upgrade() {
                h.poison(self.id());
            }
        }
    }
}

#[cfg(feature = "sync")]
thread_local! {
    static CURRENT: std::cell::RefCell<Option<Arc<TaskCtx>>> = const { std::cell::RefCell::new(None) };
}

/// Runs `f` as the task `ctx`. A panic that ends it poisons what it holds
/// and is reported to the host at once; whoever joins the task panics too.
#[cfg(feature = "sync")]
pub(crate) fn in_task<R>(ctx: &Arc<TaskCtx>, f: impl FnOnce() -> R) -> Outcome<R> {
    let outer = CURRENT.with(|c| c.replace(Some(ctx.clone())));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    CURRENT.with(|c| *c.borrow_mut() = outer);
    if let Err(payload) = &r {
        // The step limit is the host's, for the whole run: running out of it
        // in a task ends the run.
        if let Some(e) = payload.downcast_ref::<crate::TautoError>()
            && crate::messages::is_step_limit(&e.message)
        {
            crate::host::report(&format!("{}\n", crate::report(payload.as_ref())));
            crate::host::get().exit(1);
        }
        ctx.poison_all();
        crate::host::report(&format!(
            "a task failed: {}\n",
            crate::report(payload.as_ref())
        ));
    }
    r
}

/// The running task took the content of `m`: the id it is known by there,
/// or `None` on the program's main.
#[cfg(feature = "sync")]
pub fn note_taken(m: std::sync::Weak<dyn Poison>) -> Option<usize> {
    CURRENT.with(|c| {
        let c = c.borrow();
        let ctx = c.as_ref()?;
        ctx.held
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(m);
        Some(ctx.id())
    })
}

impl<A> Slot<A> {
    #[cfg(feature = "sync")]
    fn new() -> Arc<Slot<A>> {
        Arc::new(Slot {
            outcome: Mutex::new(None),
            done: Signal::new(),
        })
    }

    pub fn end(&self, outcome: Outcome<A>) {
        *self.outcome.lock().unwrap_or_else(PoisonError::into_inner) = Some(outcome);
        self.done.raise();
    }
}

/// The result of a task: ready, or on its way.
pub enum Pending<A> {
    Ready(A),
    Running(Arc<Slot<A>>),
}

pub fn pending_ready<A>(v: A) -> Pending<A> {
    Pending::Ready(v)
}

/// What the task `f` returns, or the panic that ends it, which poisons the
/// mutexes it holds.
#[cfg(feature = "sync")]
fn outcome<A>(f: impl FnOnce() -> A) -> Outcome<A> {
    in_task(&Arc::new(TaskCtx::default()), f)
}

/// Starts `body` on the executor. What it returns, or the panic that ends
/// it, is what `pending_take` gives back. A program that starts tasks is
/// built with the `sync` feature, where `Rc` is `Arc`. The body runs once,
/// so it may own what is moved into the task.
#[cfg(feature = "sync")]
pub fn pending_spawn<A: Send + 'static>(
    _ev: &Ev<'_>,
    body: Box<dyn FnOnce(&Ev<'_>) -> A + Send>,
) -> Pending<A> {
    let slot = Slot::new();
    let done = slot.clone();
    executor().execute(Box::new(move || {
        done.end(outcome(|| body(&Ev::empty())));
    }));
    Pending::Running(slot)
}

/// The body of a task that may wait (`perform wait`, or an answer of the host
/// that takes a while): a future that the host runs to its end. It is called
/// once.
#[cfg(feature = "sync")]
pub type OBody<A> = Box<dyn for<'a, 'ev> FnOnce(&'a Ev<'ev>) -> Fut<'ev, A> + Send>;

/// [`pending_spawn`] of a body that may wait: on the reactor when the program
/// installed one, else on the executor, which blocks the task's thread at
/// each wait.
#[cfg(feature = "sync")]
pub fn pending_spawn_o<A: Send + 'static>(_ev: &Ev<'_>, body: OBody<A>) -> Pending<A> {
    let slot = Slot::new();
    let done = slot.clone();
    #[cfg(feature = "reactor")]
    if crate::reactor::installed() {
        crate::reactor::spawn(body, done);
        return Pending::Running(slot);
    }
    executor().execute(Box::new(move || {
        done.end(outcome(|| {
            let ev = Ev::empty();
            crate::o::block_on(body(&ev))
        }));
    }));
    Pending::Running(slot)
}

/// Runs `f`, which may block its thread for a while (a request over the
/// network): on the reactor's pool of threads for blocking work, so no task
/// waits for it but the one that asked; else here, at once.
#[cfg(feature = "sync")]
pub fn os_offload<A: Send + 'static>(
    _ev: &Ev<'_>,
    f: Box<dyn FnOnce(&Ev<'_>) -> A + Send>,
) -> Pending<A> {
    #[cfg(feature = "reactor")]
    if crate::reactor::installed() {
        let slot = Slot::new();
        let done = slot.clone();
        crate::reactor::offload(Box::new(move || {
            done.end(outcome(|| f(&Ev::empty())));
        }));
        return Pending::Running(slot);
    }
    Pending::Ready(f(&Ev::empty()))
}

#[cfg(not(feature = "sync"))]
pub fn os_offload<A>(ev: &Ev<'_>, f: Box<dyn FnOnce(&Ev<'_>) -> A>) -> Pending<A> {
    Pending::Ready(f(ev))
}

/// There once `ms` milliseconds have passed: a timer of the reactor when the
/// program installed one, else a sleep of this thread.
pub fn os_sleep_pending(ms: u64) -> Pending<()> {
    #[cfg(feature = "reactor")]
    if crate::reactor::installed() {
        let slot = Slot::new();
        crate::reactor::sleep(ms, slot.clone());
        return Pending::Running(slot);
    }
    crate::stdlib::os_sleep(ms);
    Pending::Ready(())
}

/// There once the stream or listener `id` can be read (`write` 0: bytes, the
/// end of the stream or a connection have arrived) or written (`write` 1:
/// the socket has room), once it is closed, or once `deadline` passes. On
/// the reactor this waits on the system's poller and holds no thread, and
/// answers `true`: the read or accept that follows does not wait long, and a
/// write goes a piece at a time with `os_tcp_send`. Elsewhere it answers
/// `false` at once, and the operation waits where it runs.
pub fn os_tcp_ready(id: u64, write: u64, deadline: Option<i64>) -> Pending<bool> {
    #[cfg(all(unix, feature = "reactor"))]
    if crate::reactor::installed() {
        return match crate::tcp::ready(id, write != 0, deadline) {
            Some(wait) => polled(wait),
            None => Pending::Ready(true),
        };
    }
    let _ = (id, write, deadline);
    Pending::Ready(false)
}

/// `os_tcp_ready` for the TLS session `id`: there at once when the session
/// already holds decrypted bytes, else once its socket is ready. A write
/// goes a piece at a time with `os_tls_send`.
pub fn os_tls_ready(id: u64, write: u64, deadline: Option<i64>) -> Pending<bool> {
    #[cfg(all(unix, feature = "reactor", feature = "tls"))]
    if crate::reactor::installed() {
        return match crate::tls_host::ready(id, write != 0, deadline) {
            Some(wait) => polled(wait),
            None => Pending::Ready(true),
        };
    }
    let _ = (id, write, deadline);
    Pending::Ready(false)
}

#[cfg(all(unix, feature = "reactor"))]
fn polled(wait: crate::tcp::Wait) -> Pending<bool> {
    let slot = Slot::new();
    let done = slot.clone();
    crate::reactor::io_wait(wait, Arc::new(move || done.end(Ok(true))));
    Pending::Running(slot)
}

pub fn pending_is_ready<A>(p: &Pending<A>) -> bool {
    match p {
        Pending::Ready(_) => true,
        Pending::Running(slot) => slot.done.is_raised(),
    }
}

pub fn pending_signal<A>(p: &Pending<A>) -> Signal {
    match p {
        Pending::Ready(_) => Signal::raised(),
        Pending::Running(slot) => slot.done.clone(),
    }
}

/// The result, once its signal is raised (a host that runs a task to its
/// end waits here for one it has not); a task that panicked panics here,
/// in the task that joins it.
pub fn pending_take<A>(p: Pending<A>) -> A {
    match p {
        Pending::Ready(v) => v,
        Pending::Running(slot) => {
            slot.done.wait();
            match slot
                .outcome
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .take()
            {
                Some(Ok(v)) => v,
                Some(Err(payload)) => std::panic::resume_unwind(payload),
                None => panic!("tauto: a task's result taken twice"),
            }
        }
    }
}
