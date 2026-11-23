# surface

The surface syntax of Tauto: a port of `crates/tauto-surface` (`docs/design/self-host.md`),
in the proof language. `surface.taut` holds the types, the text of a literal and
what is computed on the syntax alone. `dump.taut` writes a program as text, line
for line what `tauto::surface::dump::dump_program` writes. Like `tauto-surface`,
it depends on no reader: `totes/parse` reads the tree of `totes/syntax` into it.
The dump recurses on the fields of what it writes, one function per type.
