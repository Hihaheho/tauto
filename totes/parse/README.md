# parse

The reader of the surface syntax: a port of `crates/tauto-parse`
(`docs/design/self-host.md`), in the proof language. `parse.taut` reads the tree
of `totes/syntax` into the syntax of `totes/surface`: terms, statements,
patterns and declarations. `main.taut` is the shell.
The readers call each other on nodes found below the one they read, not on
fields of it, so they share a number of steps: each takes the steps left as its
first argument and gives one fewer to the readers it calls, and the checker
reads the group as one function on the steps (`docs/design/self-host.md`「Termination」). The steps
are sixteen times the nodes of the tree, more than any walk takes.

    tauto run --tote totes/parse -- [--base N] FILE…

prints `== FILE` and the dump of each program, or `error` when it is not one.
`tools/selfhost-harness/tests/surface.rs` compares it with the Rust reader on
the whole corpus.
