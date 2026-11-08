//! `Signal` (`std/prelude/Par.taut`): a flag raised once and never lowered.
//! A task's result, a mutex's content handed to a place in its line and the
//! answer of a host operation that takes a while each come with one; every
//! `wait` is a wait for one. The host answers `wait` where it runs the task
//! (`o::run_top`): on a thread of its own it blocks the thread, on a reactor
//! it goes on with the other tasks and is woken when the flag is raised.

use std::task::{Context, Waker};

#[derive(Default)]
struct State {
    raised: bool,
    wakers: Vec<(usize, Waker)>,
}

impl State {
    /// Raised: `true`. Else the waker of `cx` is woken when it is.
    fn poll(&mut self, cx: &mut Context<'_>, owner: usize) -> bool {
        if !self.raised
            && !self
                .wakers
                .iter()
                .any(|(id, w)| *id == owner && w.will_wake(cx.waker()))
        {
            self.wakers.push((owner, cx.waker().clone()));
        }
        self.raised
    }

    fn forget(&mut self, owner: usize, waker: &Waker) {
        self.wakers
            .retain(|(id, w)| *id != owner || !w.will_wake(waker));
    }

    fn forget_owner(&mut self, owner: usize) -> Vec<(usize, Waker)> {
        let (removed, retained) = std::mem::take(&mut self.wakers)
            .into_iter()
            .partition(|(id, _)| *id == owner);
        self.wakers = retained;
        removed
    }

    fn raise(&mut self) -> Vec<Waker> {
        self.raised = true;
        std::mem::take(&mut self.wakers)
            .into_iter()
            .map(|(_, w)| w)
            .collect()
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
    pub struct Flag(Rc<RefCell<State>>);

    impl Flag {
        pub fn raise(&self) {
            let wakers = self.0.borrow_mut().raise();
            wakers.into_iter().for_each(|w| w.wake());
        }

        pub fn key(&self) -> usize {
            Rc::as_ptr(&self.0) as usize
        }

        pub fn is_raised(&self) -> bool {
            self.0.borrow().raised
        }

        /// Whether the flag is raised: there is nothing to wait for.
        pub fn wait(&self) -> bool {
            self.is_raised()
        }

        pub fn poll_raised(&self, cx: &mut Context<'_>, owner: usize) -> bool {
            self.0.borrow_mut().poll(cx, owner)
        }
        pub fn forget_owner(&self, owner: usize) {
            let removed = self.0.borrow_mut().forget_owner(owner);
            drop(removed);
        }
        pub fn forget(&self, owner: usize, waker: &std::task::Waker) {
            self.0.borrow_mut().forget(owner, waker);
        }
    }
}

#[cfg(feature = "sync")]
mod flag {
    use std::sync::{Arc, Condvar, Mutex, PoisonError};
    use std::task::Context;

    use super::State;

    #[derive(Clone, Default)]
    pub struct Flag(Arc<(Mutex<State>, Condvar)>);

    impl Flag {
        fn state(&self) -> std::sync::MutexGuard<'_, State> {
            self.0.0.lock().unwrap_or_else(PoisonError::into_inner)
        }

        pub fn raise(&self) {
            let wakers = self.state().raise();
            self.0.1.notify_all();
            wakers.into_iter().for_each(|w| w.wake());
        }

        pub fn key(&self) -> usize {
            Arc::as_ptr(&self.0) as usize
        }

        pub fn is_raised(&self) -> bool {
            self.state().raised
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

        pub fn poll_raised(&self, cx: &mut Context<'_>, owner: usize) -> bool {
            self.state().poll(cx, owner)
        }
        pub fn forget_owner(&self, owner: usize) {
            let removed = self.state().forget_owner(owner);
            drop(removed);
        }
        pub fn forget(&self, owner: usize, waker: &std::task::Waker) {
            self.state().forget(owner, waker);
        }
    }
}

/// A wait observes its source flags directly; choices do not retain waiters.
#[derive(Clone)]
pub struct Signal(crate::Rc<Sources>);

struct Sources(Vec<flag::Flag>);

impl std::ops::Deref for Sources {
    type Target = Vec<flag::Flag>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Drop for Sources {
    fn drop(&mut self) {
        let owner = self as *const Self as usize;
        for source in &self.0 {
            source.forget_owner(owner);
        }
    }
}

impl Default for Signal {
    fn default() -> Self {
        Self(crate::Rc::new(Sources(vec![flag::Flag::default()])))
    }
}

impl Signal {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn raised() -> Self {
        let s = Self::new();
        s.raise();
        s
    }
    pub fn source_count(&self) -> usize {
        self.0.len()
    }
    pub fn either(a: Self, b: Self) -> Self {
        if a.same(&b) {
            return a;
        }
        let mut seen = std::collections::HashSet::new();
        Self(crate::Rc::new(Sources(
            a.0.iter()
                .chain(b.0.iter())
                .filter(|s| seen.insert(s.key()))
                .cloned()
                .collect(),
        )))
    }
    pub fn raise(&self) {
        assert_eq!(self.0.len(), 1, "only a source signal can be raised");
        self.0[0].raise();
    }
    pub fn same(&self, other: &Self) -> bool {
        crate::Rc::ptr_eq(&self.0, &other.0)
    }
    pub fn is_raised(&self) -> bool {
        self.0.iter().any(|s| s.is_raised())
    }
    pub fn poll_raised(&self, cx: &mut Context<'_>) -> bool {
        let owner = crate::Rc::as_ptr(&self.0) as usize;
        let ready = self.0.iter().any(|s| s.poll_raised(cx, owner));
        if ready {
            for s in self.0.iter() {
                s.forget(owner, cx.waker());
            }
        }
        ready
    }
    pub fn wait(&self) -> bool {
        // Without threads of its own nothing else raises a flag while this
        // one waits, but a request to end the run still may.
        #[cfg(not(feature = "sync"))]
        if !self.is_raised() {
            return crate::shutdown::block_until(self);
        }
        if self.0.len() == 1 {
            return self.0[0].wait();
        }
        #[cfg(feature = "sync")]
        if crate::THREADS {
            struct WakeThread(std::thread::Thread);
            impl std::task::Wake for WakeThread {
                fn wake(self: std::sync::Arc<Self>) {
                    self.0.unpark();
                }
                fn wake_by_ref(self: &std::sync::Arc<Self>) {
                    self.0.unpark();
                }
            }
            let waker = Waker::from(std::sync::Arc::new(WakeThread(std::thread::current())));
            let mut cx = Context::from_waker(&waker);
            while !self.poll_raised(&mut cx) {
                std::thread::park();
            }
            return true;
        }
        self.is_raised()
    }
}

pub fn signal_listen(s: Signal) -> Signal {
    s
}

pub fn signal_fresh() -> Signal {
    Signal::new()
}
pub fn signal_raise(s: Signal) {
    s.raise();
}
pub fn signal_is_raised(s: Signal) -> bool {
    s.is_raised()
}
pub fn signal_either(a: Signal, b: Signal) -> Signal {
    Signal::either(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };
    use std::task::Wake;

    struct Counter(AtomicUsize);
    impl Wake for Counter {
        fn wake(self: Arc<Self>) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
        fn wake_by_ref(self: &Arc<Self>) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn either_subscribes_to_both_inputs_and_observes_an_earlier_raise() {
        for right in [false, true] {
            let a = Signal::new();
            let b = Signal::new();
            let choice = Signal::either(a.clone(), b.clone());
            let counter = Arc::new(Counter(AtomicUsize::new(0)));
            let waker = Waker::from(counter.clone());
            assert!(!choice.poll_raised(&mut Context::from_waker(&waker)));
            if right {
                b.raise();
            } else {
                a.raise();
            }
            assert_eq!(counter.0.load(Ordering::SeqCst), 1);
            assert!(choice.poll_raised(&mut Context::from_waker(&waker)));
            if right {
                a.raise();
            } else {
                b.raise();
            }
            assert_eq!(counter.0.load(Ordering::SeqCst), 1);
            assert!(Signal::either(a, b).is_raised());
        }
    }

    #[test]
    fn completing_a_choice_keeps_other_choices_with_the_same_waker_subscribed() {
        let first = Signal::new();
        let shared = Signal::new();
        let a = Signal::either(first.clone(), shared.clone());
        let b = Signal::either(shared.clone(), Signal::new());
        let counter = Arc::new(Counter(AtomicUsize::new(0)));
        let waker = Waker::from(counter.clone());
        let mut cx = Context::from_waker(&waker);
        assert!(!a.poll_raised(&mut cx));
        assert!(!b.poll_raised(&mut cx));
        first.raise();
        assert!(a.poll_raised(&mut cx));
        shared.raise();
        assert_eq!(counter.0.load(Ordering::SeqCst), 2);
        assert!(b.poll_raised(&mut cx));
    }

    #[test]
    fn dropping_the_last_pending_choice_releases_only_its_waiters() {
        let source = Signal::new();
        let choice = Signal::either(source.clone(), Signal::new());
        let other = Signal::either(source.clone(), Signal::new());
        let counter = Arc::new(Counter(AtomicUsize::new(0)));
        let waker = Waker::from(counter.clone());
        let mut cx = Context::from_waker(&waker);
        assert!(!choice.poll_raised(&mut cx));
        assert!(!other.poll_raised(&mut cx));
        let clone = choice.clone();
        let before = Arc::strong_count(&counter);
        drop(choice);
        assert_eq!(Arc::strong_count(&counter), before);
        drop(clone);
        assert_eq!(Arc::strong_count(&counter), before - 2);
        source.raise();
        assert_eq!(counter.0.load(Ordering::SeqCst), 1);
        assert!(other.poll_raised(&mut cx));
        assert_eq!(Arc::strong_count(&counter), 2);
    }

    #[test]
    fn nested_choices_and_duplicate_inputs_remain_raised() {
        let a = Signal::new();
        let choice = Signal::either(Signal::new(), Signal::either(a.clone(), a.clone()));
        assert!(!choice.is_raised());
        a.raise();
        a.raise();
        assert!(choice.is_raised());
    }

    #[cfg(feature = "sync")]
    #[test]
    fn blocking_choice_wakes_when_either_input_changes() {
        for right in [false, true] {
            let a = Signal::new();
            let b = Signal::new();
            let choice = Signal::either(a.clone(), b.clone());
            let (tx, rx) = std::sync::mpsc::channel();
            let thread = std::thread::spawn(move || {
                tx.send(choice.wait()).unwrap();
            });
            if right {
                b.raise();
            } else {
                a.raise();
            }
            assert!(rx.recv_timeout(std::time::Duration::from_secs(5)).unwrap());
            thread.join().unwrap();
        }
    }
}
