//! Moved from `tauto_surface::surface::shift`: these read the standard library, which takes the reader.
#![allow(unused_imports)]

use tauto_surface::surface::parse_program_unresolved_at;
use tauto_surface::surface::shift::*;
use tauto_surface::surface::*;

#[test]
fn a_statement_read_further_on_is_the_statement_moved() {
    tauto_parse::install();
    let text = "theorem t(c: Nat): Eq(Nat, c, c) {\n  by norm!(): Eq(Nat, c, c) {}\n}\n\
                fn f(x: Nat): Nat { match x { Zero => x, Succ(m) => m } }\n";
    let here = parse_program_unresolved_at(text, 10).expect("reads");
    let further = parse_program_unresolved_at(text, 25).expect("reads");
    assert!(!here.stmts.is_empty());
    for (a, b) in here.stmts.iter().zip(&further.stmts) {
        assert_ne!(a, b);
        assert!(moved_to(a, b, 15), "{a:#?}\n{b:#?}");
        assert!(!moved_to(a, b, 14));
    }
}
