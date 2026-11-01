# lr

The LALR(1) parser of a `syntax` grammar, in the proof language
(`src/lr.taut`, `docs/design/self-host.md`), reading the tables the LALR(1)
table generator writes (`totes/lalrgen`). It takes the tokens of
`totes/llk` and gives the same events and errors, so that what reads the
LL(k) parser's events reads these too.

## The tables

`lr_tables_read` reads five texts of numbers separated by single spaces;
`Tables::lr_texts` in `crates/tauto-syntax` writes them from a table file.

- `meta`: the start symbol, and the numbers of terminals, non-terminals and
  states.
- `skip`: the number of scanner modes, then for each the number of terminals
  the parser skips there and those.
- `actions`: a cell per state and terminal, run-length encoded (how many
  cells, then their value): 0 none, `s * 4 + 1` shift to state `s`,
  `p * 4 + 2` reduce by production `p`, `p * 4 + 3` accept by `p`.
- `gotos`: a cell per state and non-terminal, run-length encoded: 0 none,
  `s + 1` state `s`.
- `productions`: their number, then for each its left side, the length of
  its right side and the right side last first, each symbol 0 and a
  non-terminal or 1 and a terminal.

## The parse

The stack is three lists, top first: states (state 0 alone at the start),
symbols and the numbers of their nodes in the tree. A step looks up the
action of the state on top for the type of the next token:

- **None.** An error, at the next token, expecting the terminals the state
  has an action for.
- **Shift.** The token goes on the stack, with the state. The end of the
  input is never shifted.
- **Reduce by `p`.** The right side of `p` must be the symbols on top; they
  come off, with their states. The left side goes on, with the state the
  goto of the state now on top names for it. The node of `p` has the nodes
  that came off as its children.
- **Accept by `p`.** `p` must be a production of the start symbol, its right
  side all of the stack, and the next token the end of the input. Its node
  is the root of the tree.

A step that the tables cannot have asked for (a production that is not
there, a right side that is not on top, no goto) fails the parse; the
tables `totes/lalrgen` writes never do this. The parse runs on fuel, a step
each; far more than a parse takes is given, and a parse that runs out of it
fails.

## What it gives

`lr_parse` pushes the events of the tree in order, as `llk_parse` does: the
root (the node of the empty name, number `non_terminals`) opens, then each
node opens its left side, its children follow, and it closes; a token comes
after the skipped tokens before it; the skipped tokens before the end of the
input come last, and the root closes. It returns `LlkParsed`, or
`LlkFailed(error)` with where the error is and what was expected.

## What is proved

`src/derives.taut`: when the parse succeeds, the start symbol derives the
tokens before the end of the input by the tables' productions
(`lr_parse_sound`). Which actions and gotos the tables have does not matter
there; that a reduce pops the right side of its production, and that an
accept is by a production of the start symbol at the end of the input,
does.

## How it is tested

`tools/selfhost-harness/tests/lr.rs` runs `src/main.taut` on the LALR(1)
tables of `crates/tauto-syntax/tests/data` and compares its events and
errors with the parser of `crates/tauto-syntax`.
