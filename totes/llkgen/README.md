# llkgen

The LL(k) table generator: the table file of a tauto `syntax`, written in Nib
(`docs/design/macro.md`「`tauto.par` との共通性と self-host」). Its output is
checked character by character against the reference tables committed in the
repository (`crates/tauto-syntax/tests/data`, the syntax fixtures, the
examples), so the numbering of the states of an automaton is fixed: it is the
numbering those tables have.

`llkgen` with no arguments reads a grammar on standard input and writes its
table file. It is the generator `tauto syntax gen` builds and runs;
`TAUTO_GRAMMAR_GEN=<a binary>` names another.
`llkgen --gen FILE` reads the grammar from a file. For development there are
the parts of it: `--par FILE` (the lines the reading of the grammar and the
lookahead analysis decide), `--scan FILE` (the `classes`, `modes` and
`lookahead_dfas` lines), `--rx FILE` (the regular expressions of the lines,
read into the tree `rx.taut` builds), and `llkgen TABLE…` (the lookahead lines
of a table file).

Every table file in the repository (`tauto.par`, the syntax fixtures, the
examples) is written byte for byte the same.

| file | does |
|---|---|
| `par.taut` | reads the grammar (the subset tauto allows) |
| `canon.taut` | EBNF into productions, the attributes of the productions |
| `model.taut` | terminals, names, non-terminals, productions, scanners |
| `ktuple.taut`, `analysis.taut`, `follow.taut`, `dfa.taut` | FIRST/FOLLOW, the least `k`, the lookahead automata and their minimal form |
| `rx.taut`, `uni.taut` | a regular expression into a tree of literals, classes, repetitions, concatenations and alternations, with its simplifications (`rx_concat`, `rx_alternation`, `rx_class`, `rx_repetition`); `\p{L}`, `\p{N}`, `\s` from tables written by `scripts/generate-unicode-tables.sh` |
| `nfa.taut` | the NFA of a mode, state for state |
| `cc.taut` | the disjoint character classes (a boundary after a range that ends before the surrogates is the greatest character, and the interval before the code points after the surrogates is one character long) |
| `sdfa.taut` | the DFA: subset construction and the partition refinement. The order of the states is the one the partition has, so it does not depend on how the subsets were found. |
| `scn.taut` | the patterns of each mode (newline, white space, comments, the terminals, the error token), the lookahead automata |
| `sch.taut` | the types of the grammar: which non-terminal is a struct, an enum or a token, and each production's type and constructor |
| `sha.taut` | SHA-256 of the grammar (there are no bitwise operations in Nib, so they are made of bits) |
| `emit.taut`, `main.taut` | the lines of the file, in order |

The tests are in `crates/tauto-selfhost/tests/llkgen.rs`: the lookahead
analysis, the grammars read, the regular expressions (a corpus of the patterns
of the repository's grammars and the cases of the syntax, in
`crates/tauto-selfhost/tests/data/regexes.txt`), the scanners, the whole
files, and the program as a stand-in on standard input.

## What is not done

- A grammar that uses a regular expression outside the subset the scanners of
  the repository use stops with `a regular expression: …` (word boundaries,
  anchors, `\d`, `\w`, `\p{…}` other than `L` and `N`, ASCII classes, flags,
  non-greedy repetitions). Of these, all but anchors and word boundaries are a
  matter of adding them to `rx.taut` with a case in `tests/data/regexes.txt`.
