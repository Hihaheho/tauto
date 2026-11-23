# `tauto check` output

`tauto check [FILE|DIR] [--json] [--verbose] [--summary]`.

- No path: the tote of the working directory. A directory: that tote (same as
  `--tote DIR`): its `sources` and other Tauto files in it; dependencies and
  imports are shown only when failed or incomplete. A file: it and its imports.

## Snippets

Each problem is one annotated source snippet, separated by blank lines; if
every declaration passes, the last line is `ok`.

1. Header `kind: message`, kind one of `error`, `incomplete` (holes `?h` and
   uses of incomplete declarations) and `warning[CODE]` (unused bindings,
   unused effects in rows, struct fields never read
   (`unused_field`), or unreachable code). An unused-marker `^` on a
   row effect that is performed is shown as `error` (`unused_marker_used`).
2. `--> path:line:col`, path relative to the working directory, column in
   characters.
3. The line with a `N |` gutter and `^` carets; failed declarations add
   ``in `name` ``. Whole-program errors (type, effect, ownership) have no label.
4. Notes ` = …`: `goal: ⊢ T` for holes, `help: …` for diagnostics with a fix.

A multi-line span shows its first and last lines, the middle line if there is
exactly one, else `...`. Carets are measured in terminal columns (tab = 4,
wide characters and emoji = 2, control and combining = 0). A declaration that
fails only because a declaration it uses failed is not shown. Colour is used
on a terminal unless `NO_COLOR` is set.

Snippets are rendered by the tote `totes/snippet`, compiled into `tauto` by
`crates/tauto-cli-totes`.

## Other forms

- `--summary`: `FAILED`/`INCOMPLETE` lines, counts and the axioms used.
- `--verbose`: one line per declaration, imports included.
- `--json`: machine-readable, independent of the above.

Exit status: 0 all pass, 3 only holes remain, 1 a declaration failed.
