# synrun

The parse of a `syntax` at run time (`syn_parse`, which `math::parse` calls),
in Tauto: the machine (`totes/vm`) and the JavaScript backend run it, so that
a program reads a text as the Rust backend's does (`crates/tauto-syntax`:
`parse`, then `build_ast`), with the same tree, spans and diagnostics.

## The files

- `src/syntab.taut`: the parser (`SynParser`), and the values it makes
  (`SynVal`).
- `src/read.taut`: the parser read from the text `Tables::runtime_text`
  (`crates/tauto-syntax`) writes: numbers in decimal and texts, each its
  length in bytes and its bytes. The machine's programs are written in the
  same kind of text, and the machine reads its parsers with `w_syn_parser`.
- `src/syn.taut`: the parse. The scanner is `totes/scan`; an LL(k) grammar is
  parsed with its lookahead automata, an LALR(1) one with its states, and each
  production's node becomes a value as it closes, as the production's shape
  says (`tauto_syntax::Shape`).
- `src/answer.taut`: `syn_answer`, which the JavaScript backend calls. It
  reads the parser, parses, and writes the value or the diagnostic as a text
  of the same kind (the comment at the top says how).

## The constructors

The parse decides nothing about the schema of the syntax: each constructor of
its values (`SynSpan`, `SynCtx`, `SynToken`, `SynDiag`, `SynArg`, and the
constructor of each production's node) is a number the backend gave it in
the text of the parser, and the backend makes its own values of the numbers.
