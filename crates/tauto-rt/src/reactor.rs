//! The reactor: the host that runs many tasks on each of a few threads
//! (`rust.executor = "tokio"`, the default for a program that starts tasks).
//! Each thread is a tokio runtime of its own, with a `LocalSet` that holds
//! the tasks started on it, and a new task goes to the threads in turn. A
//! task that waits (`wait`, `std/prelude/Os.taut`) gives its thread to the
//! others until the signal is raised (`o::Hosted`); what the host answers
//! after a while is a timer of the runtime (`sleep`) or a job of its pool of
//! threads for blocking work (`offload`), which raise the signal when done.
//! On a target without threads there is no reactor: `installed` is `false`.

#[cfg(not(target_family = "wasm"))]
mod imp {
    use std::future::Future;
    use std::pin::Pin;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::{Arc, OnceLock};
    use std::task::{Context, Poll};
    use std::time::Duration;

    use tokio::sync::mpsc::{UnboundedSender, unbounded_channel};
    use tokio::task::LocalSet;

    use crate::ev::Ev;
    use crate::exec::{OBody, Slot};
    use crate::o::{Fut, Hosted};

    static INSTALLED: AtomicBool = AtomicBool::new(false);

    /// The program runs on the reactor: the generated `main` calls this
    /// before the program starts.
    pub fn install() {
        INSTALLED.store(true, Ordering::SeqCst);
    }

    pub fn installed() -> bool {
        INSTALLED.load(Ordering::Relaxed)
    }

    fn runtime() -> tokio::runtime::Runtime {
        tokio::runtime::Builder::new_current_thread()
            .enable_time()
            .build()
            .expect("tauto: a tokio runtime")
    }

    /// Runs the program's body to its end on this thread, as a task of the
    /// reactor.
    pub fn block_on<T>(f: Fut<'_, T>) -> T {
        LocalSet::new().block_on(&runtime(), Hosted::new(f))
    }

    /// A job a thread of the reactor runs: it starts a task there.
    type Job = Box<dyn FnOnce() + Send>;

    struct Workers {
        jobs: Vec<UnboundedSender<Job>>,
        next: AtomicUsize,
    }

    /// The threads of the reactor, one for each core, started with the first
    /// task. Each has the stack of the program's main thread: a task walks a
    /// long list by recursion as the program does.
    fn workers() -> &'static Workers {
        static WORKERS: OnceLock<Workers> = OnceLock::new();
        WORKERS.get_or_init(|| {
            let n = std::thread::available_parallelism().map_or(1, |n| n.get());
            let jobs = (0..n)
                .map(|i| {
                    let (send, mut receive) = unbounded_channel::<Job>();
                    std::thread::Builder::new()
                        .name(format!("tauto-reactor-{i}"))
                        .stack_size(crate::stack_bytes())
                        .spawn(move || {
                            LocalSet::new().block_on(&runtime(), async move {
                                while let Some(job) = receive.recv().await {
                                    job();
                                }
                            })
                        })
                        .expect("tauto: a thread for the reactor");
                    send
                })
                .collect();
            Workers {
                jobs,
                next: AtomicUsize::new(0),
            }
        })
    }

    /// A task: its body hosted, and the slot that takes what ends it.
    struct Task<A> {
        run: Hosted<'static, A>,
        done: Arc<Slot<A>>,
    }

    impl<A> Future for Task<A> {
        type Output = ();

        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
            let this = &mut *self;
            let polled = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                Pin::new(&mut this.run).poll(cx)
            }));
            match polled {
                Ok(Poll::Pending) => Poll::Pending,
                Ok(Poll::Ready(v)) => {
                    this.done.end(Ok(v));
                    Poll::Ready(())
                }
                Err(payload) => {
                    crate::o::clear_slot();
                    this.done.end(Err(payload));
                    Poll::Ready(())
                }
            }
        }
    }

    /// Starts `body` on a thread of the reactor; `done` takes what ends it.
    pub fn spawn<A: Send + 'static>(body: OBody<A>, done: Arc<Slot<A>>) {
        let w = workers();
        let i = w.next.fetch_add(1, Ordering::Relaxed) % w.jobs.len();
        let job: Job = Box::new(move || {
            let run = Hosted::new(body(&Ev::empty()));
            drop(tokio::task::spawn_local(Task { run, done }));
        });
        if w.jobs[i].send(job).is_err() {
            panic!("tauto: a thread of the reactor has stopped");
        }
    }

    /// Runs `job` on the runtime's pool of threads for blocking work.
    pub fn offload(job: Box<dyn FnOnce() + Send>) {
        match tokio::runtime::Handle::try_current() {
            Ok(h) => drop(h.spawn_blocking(job)),
            Err(_) => drop(std::thread::spawn(job)),
        }
    }

    /// Ends `done` once `ms` milliseconds have passed.
    pub fn sleep(ms: u64, done: Arc<Slot<()>>) {
        let wake = async move {
            tokio::time::sleep(Duration::from_millis(ms)).await;
            done.end(Ok(()));
        };
        match tokio::runtime::Handle::try_current() {
            Ok(h) => drop(h.spawn(wake)),
            Err(_) => drop(std::thread::spawn(move || runtime().block_on(wake))),
        }
    }
}

#[cfg(not(target_family = "wasm"))]
pub use imp::*;

#[cfg(target_family = "wasm")]
pub fn install() {}

#[cfg(target_family = "wasm")]
pub fn installed() -> bool {
    false
}

#[cfg(target_family = "wasm")]
pub fn block_on<T>(f: crate::o::Fut<'_, T>) -> T {
    crate::o::block_on(f)
}

#[cfg(target_family = "wasm")]
pub fn spawn<A>(_: crate::exec::OBody<A>, _: std::sync::Arc<crate::exec::Slot<A>>) {
    unreachable!("tauto: no reactor on this target")
}

#[cfg(target_family = "wasm")]
pub fn offload(_: Box<dyn FnOnce() + Send>) {
    unreachable!("tauto: no reactor on this target")
}

#[cfg(target_family = "wasm")]
pub fn sleep(_: u64, _: std::sync::Arc<crate::exec::Slot<()>>) {
    unreachable!("tauto: no reactor on this target")
}
