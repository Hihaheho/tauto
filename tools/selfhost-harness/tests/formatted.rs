//! The totes' own code is laid out as `tauto fmt` lays it out.

use selfhost_harness::corpus;

#[test]
fn the_totes_are_formatted() {
    let mut unformatted = Vec::new();
    for (name, source) in corpus().iter().filter(|(n, _)| n.starts_with("totes/")) {
        match tauto::fmt::format(source) {
            Ok(out) if out == *source => {}
            Ok(_) => unformatted.push(name.clone()),
            Err(error) => panic!("{name}: {error}"),
        }
    }
    assert!(
        unformatted.is_empty(),
        "run `tauto fmt` on: {unformatted:?}"
    );
}
