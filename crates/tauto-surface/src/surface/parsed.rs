//! The programs read from texts, kept for the thread when it asks for that ([`keep`]): a server
//! that reads the same files at every request reads each text once. A program is kept by its
//! text and the place it starts at, the whole of what reading it depends on.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use super::Program;

/// How many readings a kept program outlives unused.
const READINGS: u64 = 4;

type Key = (String, u32);

thread_local! {
    static KEEP: Cell<bool> = const { Cell::new(false) };
    static READING: Cell<u64> = const { Cell::new(0) };
    /// Each program with the reading it was last used in.
    static KEPT: RefCell<HashMap<Key, (Result<Program, String>, u64)>> =
        RefCell::new(HashMap::new());
}

/// Whether the programs this thread reads are kept; off by default.
pub fn keep(keep: bool) {
    KEEP.with(|k| k.set(keep));
    if !keep {
        KEPT.with(|k| k.borrow_mut().clear());
    }
}

pub(super) fn kept() -> bool {
    KEEP.with(Cell::get)
}

/// A reading of programs begins: the programs no reading used for the last few are let go.
pub fn begin_reading() {
    let now = READING.with(|r| {
        r.set(r.get() + 1);
        r.get()
    });
    KEPT.with(|k| {
        k.borrow_mut()
            .retain(|_, (_, used)| now.saturating_sub(*used) < READINGS)
    });
}

pub(super) fn get_or_read(
    source: &str,
    base: u32,
    read: impl FnOnce() -> Result<Program, String>,
) -> Result<Program, String> {
    let now = READING.with(Cell::get);
    let key = (source.to_string(), base);
    if let Some(found) = KEPT.with(|k| {
        k.borrow_mut().get_mut(&key).map(|(p, used)| {
            *used = now;
            p.clone()
        })
    }) {
        return found;
    }
    let program = read();
    KEPT.with(|k| k.borrow_mut().insert(key, (program.clone(), now)));
    program
}
