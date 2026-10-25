# surface

The surface syntax of Tauto read from the tree of `totes/syntax`: a port of
`crates/tauto/src/surface.rs` and `surface/program.rs` (`docs/design/self-host.md`), in the proof language. `surface.taut` holds the
types, the text of a literal, the readers of terms, statements, patterns and
declarations, and the dump that writes a program as text, line for line what
`tauto::surface::dump::dump_program` writes. `main.taut` is the shell.

The readers call each other on nodes found below the one they read, not on
fields of it, so they share a number of steps: each takes the steps left as its
first argument and gives one fewer to the readers it calls, and the checker
reads the group as one function on the steps (`docs/design/self-host.md`「停止性の書き方」). The steps
are sixteen times the nodes of the tree, more than any walk takes.
The dump recurses on the fields of what it writes, one function per type.

    tauto run --tote totes/surface -- [--base N] FILE…

prints `== FILE` and the dump of each program, or `error` when it is not one.
`crates/tauto-selfhost/tests/surface.rs` compares it with the Rust reader on
the whole corpus.
