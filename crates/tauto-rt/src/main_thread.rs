//! Work that must run on the process's main thread.
//!
//! The program runs on a thread of its own, sized for deep recursion
//! ([`crate::stack_bytes`]); the main thread waits for it. Some host APIs only
//! work on the main thread (macOS's AppKit: `NSApplication`, `NSWindow`, the
//! event loop). A Rust extern hands such work to [`run`], which runs it on the
//! main thread while the caller waits for its result. A program built with
//! `rust.main-thread` (`crate::set_run_on_main_thread`) runs on the main
//! thread itself, and [`run`] runs the work at once.

use std::any::Any;
use std::sync::mpsc::{Receiver, Sender, channel};
use std::sync::{Mutex, OnceLock};
use std::thread::ThreadId;

type Job = Box<dyn FnOnce() + Send>;

/// What the main thread is sent while the program runs.
pub(crate) enum Message {
    /// Work to run on the main thread.
    Job(Job),
    /// The program has ended.
    Done,
}

static MAIN: OnceLock<ThreadId> = OnceLock::new();
static JOBS: Mutex<Option<Sender<Message>>> = Mutex::new(None);

/// Whether the caller is on the thread the runtime was entered from: the
/// process's main thread when the program is the process's own.
pub fn is_main() -> bool {
    MAIN.get() == Some(&std::thread::current().id())
}

/// Runs `job` on the main thread and returns what it returns; a panic in
/// `job` is resumed on the caller. On the main thread itself, `job` runs at
/// once.
///
/// The caller waits until `job` returns: a `job` that runs an event loop for
/// good (`NSApplication::run`) keeps the program waiting with it.
///
/// Panics outside a run of the program, where nothing on the main thread
/// takes the job.
pub fn run<R: Send + 'static>(job: impl FnOnce() -> R + Send + 'static) -> R {
    if is_main() {
        return job();
    }
    let send = JOBS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone()
        .expect("no main thread takes work outside a run of the program");
    let (answer, result) = channel::<Result<R, Box<dyn Any + Send>>>();
    let job: Job = Box::new(move || {
        let _ = answer.send(std::panic::catch_unwind(std::panic::AssertUnwindSafe(job)));
    });
    send.send(Message::Job(job))
        .expect("the main thread takes work while the program runs");
    match result.recv().expect("the main thread answers the work") {
        Ok(value) => value,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

/// Marks the calling thread as the main thread: the one the runtime was
/// entered from.
pub(crate) fn mark() {
    let _ = MAIN.set(std::thread::current().id());
}

/// Opens the main thread for work: returns the sender the program's thread
/// ends with [`Message::Done`], and the receiver [`serve`] reads.
pub(crate) fn open() -> (Sender<Message>, Receiver<Message>) {
    let (send, receive) = channel();
    *JOBS.lock().unwrap_or_else(|e| e.into_inner()) = Some(send.clone());
    (send, receive)
}

/// Runs the work sent to the main thread until the program ends.
pub(crate) fn serve(receive: Receiver<Message>) {
    while let Ok(Message::Job(job)) = receive.recv() {
        job();
    }
    *JOBS.lock().unwrap_or_else(|e| e.into_inner()) = None;
}
