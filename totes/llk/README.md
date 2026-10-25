# llk

The LL(k) parser of Tauto's syntax, in the proof language (`src/llk.taut`,
`docs/design/self-host.md`), reading the tables the LL(k) table generator
writes (`totes/llkgen`). The parse runs on fuel
(a step reads a token, or opens or closes a node); far more than a parse
of the grammar takes is given, and a parse that runs out of it fails.

## The tokens

The scanner's tokens are split into those the parser reads and those it
skips. Terminals 1 to 4 (new line, white space, the comments) are always
skipped; so is a terminal the grammar skips in the mode the token was cut in
(the `skip` table). Each token the parser reads keeps the skipped ones
before it as its *trivia*. Two tokens of the end of input (terminal 0, at the
end of the text) follow the last; the skipped tokens at the end go with the
first of them.

## The parse

The parser has a stack of symbols, a non-terminal to expand, a terminal to
match or the end of a production, and the tokens ahead. It starts with the
start symbol on the stack and an event that opens the root, a node with the
name `""`. It repeats until the stack is empty:

- **A non-terminal.** The lookahead automaton of the non-terminal chooses a
  production (below). Pop the non-terminal; open the production's left side;
  push the end of the production, then the right side so that its first
  symbol is on top.
- **A terminal.** If the first token ahead has this terminal: emit its trivia
  and then the token, and take the token off. Otherwise it is an error.
- **The end of a production.** Close the node.

A production the automaton chooses must have the non-terminal as its left
side; if not, the tables are not a parser and the parse fails (the tables
`totes/llkgen` writes never do this).

When the stack is empty (or holds only the end of input), the trivia before
the end of input are emitted and the root is closed. The parse is a success if
the first token ahead is the end of input, and an error if it is not.

The trivia of a token are emitted just before the token, into whichever node
is open then, not where the scanner met them.

## Choosing a production

An automaton has `k` (0 to `max_k`) and states; state 0 is the start, and it
may have a production `prod0` already. For `i` from 0 to `k - 1`, with `ty`
the terminal of the `i`th token ahead: if the state has a transition for
`ty`, go to its state and take its production (if any, remember it); if not,
stay where it is and go on to the next `i`. At the end: the production the
last transition gave, or if that one has none, the last remembered one, and if
there is none, an error.

## What is not written

Recovery (going on after an error to report more of them) is not written:
the first error ends the parse, with where it is (the
start of the first token ahead) and, when a terminal was expected, which. The
production's flag that it only pushes a list element is not kept: it only
counts the depth of the parse, and no limit is set.

## What it gives

`llk_parsed()`, with the events left on the stack the parse was given: the
calls that build the tree, in order: open a non-terminal (by number; the root is the number after the last),
close, token (terminal, start, end). Or `llk_failed(error)`.

## What is proved

`src/derives.taut` (`docs/design/self-host.md`「証明（`totes/*/src/`、`std/`）」): when the parse succeeds, the
start symbol derives the tokens by the tables' productions
(`llk_parse_sound`).
