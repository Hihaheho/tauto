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

/// Runs a job, now or later, on this thread or another.
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

impl<A> Slot<A> {
    #[cfg(feature = "sync")]
    fn new() -> Arc<Slot<A>> {
        Arc::new(Slot {
            outcome: Mutex::new(None),
            done: Signal::new(),
        })
    }

    /// Leaves what ends the task and raises the signal.
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

/// What `f` returns, or the panic that ends it.
#[cfg(feature = "sync")]
fn outcome<A>(f: impl FnOnce() -> A) -> Outcome<A> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f))
}

/// Starts `body` on the executor. What it returns, or the panic that ends
/// it, is what `pending_take` gives back. A program that starts tasks is
/// built with the `sync` feature, where `Rc` is `Arc`.
#[cfg(feature = "sync")]
pub fn pending_spawn<A: Send + 'static>(
    _ev: &Ev<'_>,
    body: Rc<dyn Fn(&Ev<'_>) -> A + Send + Sync>,
) -> Pending<A> {
    let slot = Slot::new();
    let done = slot.clone();
    executor().execute(Box::new(move || {
        done.end(outcome(|| body(&Ev::empty())));
    }));
    Pending::Running(slot)
}

/// The body of a task that may wait (`perform wait`, or an answer of the host
/// that takes a while): a future that the host runs to its end.
#[cfg(feature = "sync")]
pub type OBody<A> = Rc<dyn for<'a, 'ev> Fn(&'a Ev<'ev>) -> Fut<'ev, A> + Send + Sync>;

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
    f: Rc<dyn Fn(&Ev<'_>) -> A + Send + Sync>,
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
pub fn os_offload<A>(ev: &Ev<'_>, f: Rc<dyn Fn(&Ev<'_>) -> A>) -> Pending<A> {
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

/// Whether the result is there, without waiting.
pub fn pending_is_ready<A>(p: &Pending<A>) -> bool {
    match p {
        Pending::Ready(_) => true,
        Pending::Running(slot) => slot.done.is_raised(),
    }
}

/// Raised when the result is there.
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
