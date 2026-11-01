# llkgen

The LL(k) table generator: the table file of a tauto `syntax`, written in Nib
(`docs/design/macro.md`「`tauto.par` との共通性と self-host」). Its output is
checked character by character against the reference tables committed in the
repository (`crates/tauto-syntax/tests/data`, the syntax fixtures, the
examples), so the numbering of the states of an automaton is fixed: it is the
numbering those tables have.

It is a library: every function it gives takes a text and gives a text, or
why there is none (`Result(Text, Text)`); it reads no file.

- `llkgen_tables(grammar)`: the table file of a grammar.
- For development, the parts of it: `llkgen_model_lines(grammar)` (the lines
  the reading of the grammar and the lookahead analysis decide),
  `llkgen_scan_lines(grammar)` (the `classes`, `modes` and `lookahead_dfas`
  lines, and the lines of the states of the scanner),
  `llkgen_rx_trees(lines)` (the regular expressions of the lines, read into
  the tree `rx.taut` builds) and `llkgen_lookahead_lines(table)` (the
  lookahead lines of a table file, made again from its grammar).

An error in the grammar is the effect `fail(Text)` inside the tote, caught by
these functions. The program that reads the grammar from a file and that
`tauto syntax gen` runs is `totes/syntaxgen`.

Every table file in the repository (`tauto.par`, the syntax fixtures, the
examples) is written byte for byte the same.

The grammar is read and its scanners are made by `totes/pargen`, which an
LR generator can share; this tote has the LL(k) lookahead analysis and the
table file.

| file | does |
|---|---|
| `ktuple.taut`, `analysis.taut`, `follow.taut`, `dfa.taut` | FIRST/FOLLOW, the least `k`, the lookahead automata and their minimal form |
| `tables.taut` | the lines of the file, in order, and the functions the tote gives |

The tests are in `tools/selfhost-harness/tests/llkgen.rs`: the lookahead
analysis, the grammars read, the regular expressions (a corpus of the patterns
of the repository's grammars and the cases of the syntax, in
`tools/selfhost-harness/tests/data/regexes.txt`), the scanners, the whole
files, and the program as a stand-in on standard input.

## What is not done

See `totes/pargen` for what the grammar reader and the scanners do not take.
