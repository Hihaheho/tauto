//! `shutdown_token` (`std/prelude/Os.taut`): a request to end the run from
//! outside (SIGINT, SIGTERM) raises the signals the program asked for.
//!
//! The first `register` installs the handlers. A handler only sets a flag
//! (all it may do there); the flag is turned into raised signals by `poll`,
//! which the host calls at each step (`host_tick`) and while it waits
//! (`Signal::wait`), and, where tasks run on threads of their own, by a
//! watcher thread, so a task blocked in a `wait` is woken. A second request
//! ends the process at once with the status a shell gives a death by
//! that signal (`128 + n`). Without Unix signals (Windows, wasm) the
//! signals are never raised.

use crate::signal::Signal;
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};

/// Set by the handler; taken by `poll`.
static PENDING: AtomicBool = AtomicBool::new(false);
/// Set once a request has come: a signal registered afterwards is raised at once.
static FIRED: AtomicBool = AtomicBool::new(false);
/// The number of the first request's signal; 0 before one.
static FIRST: AtomicI32 = AtomicI32::new(0);

#[cfg(not(feature = "sync"))]
mod registry {
    use crate::signal::Signal;
    use std::cell::RefCell;

    thread_local! {
        static SIGNALS: RefCell<Vec<Signal>> = const { RefCell::new(Vec::new()) };
    }

    pub fn push(s: Signal) {
        SIGNALS.with(|r| r.borrow_mut().push(s));
    }
    pub fn take() -> Vec<Signal> {
        SIGNALS.with(|r| std::mem::take(&mut *r.borrow_mut()))
    }
    pub fn any() -> bool {
        SIGNALS.with(|r| !r.borrow().is_empty())
    }
}

#[cfg(feature = "sync")]
mod registry {
    use crate::signal::Signal;
    use std::sync::{Mutex, PoisonError};

    static SIGNALS: Mutex<Vec<Signal>> = Mutex::new(Vec::new());

    pub fn push(s: Signal) {
        SIGNALS.lock().unwrap_or_else(PoisonError::into_inner).push(s);
    }
    pub fn take() -> Vec<Signal> {
        std::mem::take(&mut *SIGNALS.lock().unwrap_or_else(PoisonError::into_inner))
    }
    pub fn any() -> bool {
        !SIGNALS.lock().unwrap_or_else(PoisonError::into_inner).is_empty()
    }
}

extern "C" fn on_signal(n: i32) {
    if FIRST
        .compare_exchange(0, n, Ordering::SeqCst, Ordering::SeqCst)
        .is_err()
    {
        tauto_rt_signal::exit_now(128 + n);
    }
    PENDING.store(true, Ordering::SeqCst);
}

fn install() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        if tauto_rt_signal::install(on_signal) {
            #[cfg(feature = "sync")]
            if crate::THREADS {
                std::thread::spawn(|| {
                    loop {
                        std::thread::sleep(std::time::Duration::from_millis(10));
                        poll();
                    }
                });
            }
        }
    });
}

/// Raises `s` when the run is asked to end; at once if it already was.
pub fn register(s: Signal) {
    install();
    if FIRED.load(Ordering::SeqCst) {
        s.raise();
    } else {
        registry::push(s);
        // A request between the load and the push.
        poll();
    }
}

/// Raises the registered signals if a request has come.
#[inline]
pub fn poll() {
    if PENDING.load(Ordering::Relaxed) {
        drain();
    }
}

#[cold]
fn drain() {
    if PENDING.swap(false, Ordering::SeqCst) {
        FIRED.store(true, Ordering::SeqCst);
    }
    if FIRED.load(Ordering::SeqCst) {
        for s in registry::take() {
            s.raise();
        }
    }
}

/// Whether a request to end the run would raise a signal still waiting for one.
pub fn waiting() -> bool {
    poll();
    registry::any()
}

/// Waits on this thread for `s` while a request could still raise it:
/// whether it is raised.
pub fn block_until(s: &Signal) -> bool {
    loop {
        poll();
        if s.is_raised() {
            return true;
        }
        if !registry::any() || !crate::THREADS {
            return false;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
}

/// For a test: as if a request had come.
#[doc(hidden)]
pub fn simulate() {
    let _ = FIRST.compare_exchange(0, 2, Ordering::SeqCst, Ordering::SeqCst);
    PENDING.store(true, Ordering::SeqCst);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_request_raises_signals_registered_before_and_after() {
        let before = Signal::new();
        register(before.clone());
        assert!(!before.is_raised());
        simulate();
        poll();
        assert!(before.is_raised());
        let after = Signal::new();
        register(after.clone());
        assert!(after.is_raised());
    }
}
