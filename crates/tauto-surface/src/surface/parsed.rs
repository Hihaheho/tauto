//! The programs read from texts, kept for the thread when it asks for that ([`keep`]): a server
//! that reads the same files at every request reads each text once. A program is kept by its
//! text and the place it starts at, the whole of what reading it depends on.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use super::Program;
use super::program::ParseError;

/// How many readings a kept program outlives unused.
const READINGS: u64 = 4;

type Key = (String, u32);

thread_local! {
    static KEEP: Cell<bool> = const { Cell::new(false) };
    static READING: Cell<u64> = const { Cell::new(0) };
    /// Each program with the reading it was last used in.
    static KEPT: RefCell<HashMap<Key, (Result<Program, ParseError>, u64)>> =
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
    read: impl FnOnce() -> Result<Program, ParseError>,
) -> Result<Program, ParseError> {
    let now = READING.with(Cell::get);
    let key = (source.to_string(), base);
    if let Some(mut found) = KEPT.with(|k| {
        k.borrow_mut().get_mut(&key).map(|(p, used)| {
            *used = now;
            p.clone()
        })
    }) {
        // A reading creates distinct lexical occurrences even when its syntax is reused.
        if let Ok(program) = &mut found {
            for stmt in &mut program.stmts {
                super::walk::stmt(stmt, &mut super::SurfaceTerm::freshen);
            }
        }
        return found;
    }
    let program = read();
    KEPT.with(|k| k.borrow_mut().insert(key, (program.clone(), now)));
    program
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn occurrences(program: &Program) -> HashSet<super::super::TermId> {
        let mut ids = HashSet::new();
        for stmt in &mut program.clone().stmts {
            super::super::walk::stmt(stmt, &mut |term| {
                ids.insert(term.id());
            });
        }
        ids
    }

    #[test]
    fn cached_readings_keep_syntax_but_have_distinct_occurrences() {
        let source = include_str!("../../../../std/prelude/Std.taut");
        keep(true);
        begin_reading();
        let first = super::super::parse_program_unresolved_at(source, 100).unwrap();
        let second = super::super::parse_program_unresolved_at(source, 100).unwrap();
        let third = super::super::parse_program_unresolved_at(source, 100).unwrap();
        keep(false);
        assert_eq!(first, second);
        assert_eq!(second, third);
        let ids = [
            occurrences(&first),
            occurrences(&second),
            occurrences(&third),
        ];
        assert!(!ids[0].is_empty());
        assert!(ids[0].is_disjoint(&ids[1]));
        assert!(ids[1].is_disjoint(&ids[2]));
        assert!(ids[0].is_disjoint(&ids[2]));
    }
}
