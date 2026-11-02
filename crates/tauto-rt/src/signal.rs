//! `Signal` (`std/prelude/Os.taut`): a flag raised once and never lowered.
//! A task's result, a mutex's content handed to a place in its line and the
//! answer of a host operation that takes a while each come with one; every
//! `wait` is a wait for one. The host answers `wait` where it runs the task
//! (`o::run_top`): on a thread of its own it blocks the thread, on a reactor
//! it goes on with the other tasks and is woken when the flag is raised.

use std::task::{Context, Waker};

#[derive(Default)]
struct State {
    raised: bool,
    wakers: Vec<Waker>,
}

impl State {
    /// Raised: `true`. Else the waker of `cx` is woken when it is.
    fn poll(&mut self, cx: &mut Context<'_>) -> bool {
        if !self.raised && !self.wakers.iter().any(|w| w.will_wake(cx.waker())) {
            self.wakers.push(cx.waker().clone());
        }
        self.raised
    }

    fn raise(&mut self) -> Vec<Waker> {
        self.raised = true;
        std::mem::take(&mut self.wakers)
    }
}

#[cfg(not(feature = "sync"))]
mod flag {
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::task::Context;

    use super::State;

    /// Without tasks nothing runs while the program waits, so a wait for a
    /// flag not raised never ends.
    #[derive(Clone, Default)]
    pub struct Signal(Rc<RefCell<State>>);

    impl Signal {
        pub fn new() -> Signal {
            Signal::default()
        }

        pub fn raise(&self) {
            let wakers = self.0.borrow_mut().raise();
            wakers.into_iter().for_each(|w| w.wake());
        }

        pub fn is_raised(&self) -> bool {
            self.0.borrow().raised
        }

        pub fn same(&self, other: &Signal) -> bool {
            Rc::ptr_eq(&self.0, &other.0)
        }

        /// Whether the flag is raised: there is nothing to wait for.
        pub fn wait(&self) -> bool {
            self.is_raised()
        }

        pub fn poll_raised(&self, cx: &mut Context<'_>) -> bool {
            self.0.borrow_mut().poll(cx)
        }
    }
}

#[cfg(feature = "sync")]
mod flag {
    use std::sync::{Arc, Condvar, Mutex, PoisonError};
    use std::task::Context;

    use super::State;

    #[derive(Clone, Default)]
    pub struct Signal(Arc<(Mutex<State>, Condvar)>);

    impl Signal {
        pub fn new() -> Signal {
            Signal::default()
        }

        fn state(&self) -> std::sync::MutexGuard<'_, State> {
            self.0.0.lock().unwrap_or_else(PoisonError::into_inner)
        }

        pub fn raise(&self) {
            let wakers = self.state().raise();
            self.0.1.notify_all();
            wakers.into_iter().for_each(|w| w.wake());
        }

        pub fn is_raised(&self) -> bool {
            self.state().raised
        }

        pub fn same(&self, other: &Signal) -> bool {
            Arc::ptr_eq(&self.0, &other.0)
        }

        /// Blocks this thread until the flag is raised. Where no thread but
        /// this one runs (wasm32 without atomics), a flag not raised is never
        /// raised: `false`.
        pub fn wait(&self) -> bool {
            if !crate::THREADS {
                return self.is_raised();
            }
            let mut state = self.state();
            while !state.raised {
                state = self.0.1.wait(state).unwrap_or_else(PoisonError::into_inner);
            }
            true
        }

        pub fn poll_raised(&self, cx: &mut Context<'_>) -> bool {
            self.state().poll(cx)
        }
    }
}

pub use flag::Signal;

impl Signal {
    pub fn raised() -> Signal {
        let s = Signal::new();
        s.raise();
        s
    }
}
