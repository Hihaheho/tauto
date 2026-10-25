//! The Rust a tauto program calls through `extern { … }`: a counter that
//! tasks on different threads add to. It is `Send + Sync`, which a program
//! that starts tasks requires of every extern type.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Clone)]
pub struct Counter(Arc<AtomicU64>);

pub fn counter_new() -> Counter {
    Counter(Arc::new(AtomicU64::new(0)))
}

pub fn counter_add(c: Counter, n: u64) {
    c.0.fetch_add(n, Ordering::SeqCst);
}

pub fn counter_get(c: Counter) -> u64 {
    c.0.load(Ordering::SeqCst)
}
