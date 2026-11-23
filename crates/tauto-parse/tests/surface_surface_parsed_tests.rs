//! Moved from `tauto_surface::surface::parsed`: these read the standard library, which takes the reader.
#![allow(unused_imports)]

use std::collections::HashSet;
use tauto_surface::surface::parsed::*;
use tauto_surface::surface::*;

fn occurrences(program: &Program) -> HashSet<tauto_surface::surface::TermId> {
    let mut ids = HashSet::new();
    for stmt in &mut program.clone().stmts {
        tauto_surface::surface::walk::stmt(stmt, &mut |term| {
            ids.insert(term.id());
        });
    }
    ids
}

#[test]
fn cached_readings_keep_syntax_but_have_distinct_occurrences() {
    tauto_parse::install();
    let source = include_str!("../../../std/prelude/std.taut");
    keep(true);
    begin_reading();
    let first = tauto_surface::surface::parse_program_unresolved_at(source, 100).unwrap();
    let second = tauto_surface::surface::parse_program_unresolved_at(source, 100).unwrap();
    let third = tauto_surface::surface::parse_program_unresolved_at(source, 100).unwrap();
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
