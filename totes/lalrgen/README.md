# lalrgen

The LALR(1) table generator: the table file of a grammar written with
`%grammar_type 'lalr(1)'`. It makes the table parol makes, state for state:
parol calls the crate lalry 0.1.0, and `src/lr.taut` does what lalry does.

It is a library like `totes/llkgen`: `lalrgen_tables(grammar)` gives the
table file, and `lalrgen_lr_lines(grammar)` (for development) the lines
`terminals`, `non_terminals`, `start`, `productions` and `lr`; each takes a
text and gives `Result(Text, Text)`. `totes/syntaxgen` calls it for an LALR(1)
grammar (`--gen`), and `--lr FILE` gives the lines for development.

## What the grammar becomes

`totes/pargen` reads the grammar. For an LALR(1) grammar it differs from an
LL(k) one in two places, as parol does:

- A repetition `{ X }` is `XList: XList X | ;`, the list first (left
  recursion), where an LL(k) grammar has `XList: X XList | ;`.
- When the start symbol `S` has more than one production, a new start
  `S0: S;` comes first (parol's augmentation), so that one production starts
  the parse.

## The table

1. **The LR(0) states.** State 0 is the closure of the start production at
   position 0. An item is ordered by its production's left side, its symbols
   (terminals before non-terminals, each by number) and its position. From
   each state in turn, the items are moved over each symbol after the dot, in
   the order of the symbols. A set of items not seen before is the next state.
2. **The extended grammar.** For each state and each item there at
   position 0, a production whose left side is (state, non-terminal) and whose
   non-terminals are (the state they are read from, non-terminal). It ends in
   the state the item's production leads to.
3. **FIRST and FOLLOW** of the extended grammar. The end of the input follows
   (0, start).
4. **The actions.**
   - A state shifts on each terminal it has a transition for, and goes to
     the target on each non-terminal.
   - Each production of the extended grammar reduces, in the state where it
     ends, on each terminal of its left side's FOLLOW.
   - A state that would do two different things on a terminal (a shift and
     a reduce, or reduces by two productions) is an error, and so is a state
     that accepts and does something else at the end of the input. The
     message names the kind of conflict, the state, the terminal and the
     productions:
     `LALR(1) shift/reduce conflict in state 6 on Plus`, then one line for
     the shift (`shift to state 4`) or the production, and one line
     `reduce by production #1 of E`.
   - On the end of the input, a production of the start symbol accepts
     (the action names the production).

The `lr` line holds the number of states, then each state's:

- actions: their number, then for each the terminal, the kind (0 shift,
  1 reduce, 2 accept) and the state (shift) or the production (reduce,
  accept);
- gotos: their number, then for each the non-terminal and the state.

## How it is tested

The tables of a grammar without conflicts are compared with what parol makes
(parol settles a conflict by letting a shift win over a reduce and the
production written first win over a later one; this tote reports it). A small Rust program (not in
the repository) runs parol's own steps: reading, augmentation, then
`generate_parser_export_model_from_grammar`. It prints the productions and
the table in the form `--lr` has.

It was run on every grammar of parol's examples and tests and of this
repository (`tauto.par` too), with `%grammar_type 'lalr(1)'` put in. All 104
are the same, except:

- the one parol cannot read (`%state`);
- `examples/nat`, whose start symbol is used inside the grammar. There lalry
  stops on an internal error and this tote reports the conflict.
