# scan

The scanner of Tauto's syntax, in the proof language (`src/scan.taut`,
`docs/design/self-host.md`「構文（`totes/scan`、`totes/llk`、`totes/syntax`）」; extracted to Nib when
the tote is run). It cuts a text into tokens with the scanner tables of a
grammar (`crates/tauto-parol/tauto.par` and the `syntax` of a macro).

## What it decides

A scanner has modes (`INITIAL`, `InParen`, `InBrace`); each has an automaton
(DFA) whose states have transitions by *class* of character, and some states
accept a token.

1. **A character's class.** A table of runs of code points gives the class of
   each character (or none). Characters below 128 are looked up in a
   table of their own; the others by binary search over the runs.
2. **The longest token.** From the current byte, in the current mode's
   automaton, read characters while the state has a transition for the
   character's class. After each character, look at the state's accept
   entries in order; the first whose lookahead holds (an entry with no
   lookahead always holds) makes the text read so far the best token yet.
   The scanner stops at a character with no class or no transition, and the
   token is the best one. Every step reads one more character, so a later
   accept is always longer than an earlier one; within one state, the order
   of the entries decides which one holds first.
3. **A lookahead.** An entry's lookahead is another automaton, run from the
   byte after the token. A positive one holds if the run reaches a state
   that accepts (the first such state is enough), a negative one if it does
   not.
4. **No token.** If no entry ever held, the scanner skips one character and
   tries again from the next. (The grammar has a token for every character,
   `Error`, so this does not happen.)
5. **The mode.** After a token, the current mode's transitions are looked at
   for the token's terminal: *set* changes the mode, *push* remembers the
   current one and changes, *pop* goes back to the last remembered mode (and
   does nothing with none).

Positions are bytes. The scanner cuts the whole text at once: which mode
comes next depends on the tokens alone, never on the parser, so the parser
reading two tokens ahead does not change what is cut.

A token carries the mode it was cut in, which the parser needs to know which
tokens to skip.

## What is proved

`src/longest.taut` (`docs/design/self-host.md`「証明（`totes/*/src/`、`std/`）」): a token `scan_find` gives is
one a run of the automaton reaches (`scan_find_sound`), and no token a run
reaches is longer (`scan_find_longest`).

## The tables

`syntax_tables_scan_meta`, `_classes`, `_states` and `_rows` of
`totes/syntax/src/tables.taut` (see `totes/syntax/README.md`) are read by
`scan_tables_read`. All the automata, the modes' and the lookaheads', are
numbered together; `rows` is one long vector with a row of `classes` entries
for each state.

A table shorter than its counts say is not a scanner: `scan_tables_read`
gives `None`. (Every read is checked against the end of its table once,
after all of them; a read past the end reads 0 until then.)
