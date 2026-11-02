//! How long the phases of reading a program take, for `--timings`. The clock is read only while
//! [`recorded`] runs; otherwise [`mark`] does nothing.

use std::cell::RefCell;
use std::time::{Duration, Instant};

thread_local! {
    static PHASES: RefCell<Option<(Instant, Vec<(&'static str, Duration)>)>> =
        const { RefCell::new(None) };
}

/// Runs `f`, with the phases it marks, each with the time since the mark before it (or since
/// the start).
pub fn recorded<R>(f: impl FnOnce() -> R) -> (R, Vec<(&'static str, Duration)>) {
    let outer = PHASES.with(|p| p.borrow_mut().replace((Instant::now(), Vec::new())));
    let r = f();
    let (_, phases) = PHASES
        .with(|p| std::mem::replace(&mut *p.borrow_mut(), outer))
        .unwrap_or((Instant::now(), Vec::new()));
    (r, phases)
}

/// Ends the phase `name`: the time since the mark before it is its.
pub fn mark(name: &'static str) {
    PHASES.with(|p| {
        if let Some((since, phases)) = p.borrow_mut().as_mut() {
            let now = Instant::now();
            phases.push((name, now - *since));
            *since = now;
        }
    });
}
