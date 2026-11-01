//! The case runner's host value: a program's `affine struct Probe {}` with
//! `module Probe { extern { fn new(&name: Text): Probe } }` makes one,
//! and its drop is written down by name. Every runner gives the same
//! extern, so the order a program drops its values in is a case
//! expectation (`probe_drops`) on every backend.

use std::sync::Mutex;

static DROPPED: Mutex<Vec<String>> = Mutex::new(Vec::new());

pub struct Probe(String);

pub fn probe(name: &str) -> Probe {
    Probe(name.to_string())
}

impl Drop for Probe {
    fn drop(&mut self) {
        DROPPED
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .push(std::mem::take(&mut self.0));
    }
}

/// The names of the probes dropped so far, in order.
pub fn dropped() -> Vec<String> {
    DROPPED.lock().unwrap_or_else(|p| p.into_inner()).clone()
}
