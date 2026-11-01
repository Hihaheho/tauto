# pargen

What the table generators share (`totes/llkgen` and `totes/lalrgen`): reading
a grammar in parol's notation, turning its EBNF into productions, the types of
its tree, and its scanners (the work of scnr2): regular expressions, the NFA
and DFA of each mode, the character classes and the lookahead automata.

| file | does |
|---|---|
| `par.taut` | reads the grammar (the subset tauto allows) |
| `canon.taut` | EBNF into productions, the attributes of the productions |
| `model.taut` | terminals, names, non-terminals, productions, scanners |
| `rx.taut`, `uni.taut` | a regular expression into a tree of literals, classes, repetitions, concatenations and alternations, with its simplifications (`rx_concat`, `rx_alternation`, `rx_class`, `rx_repetition`); `\p{L}`, `\p{N}`, `\s` from tables written by `scripts/generate-unicode-tables.sh` |
| `nfa.taut` | the NFA of a mode, state for state |
| `cc.taut` | the disjoint character classes (exclusive integer bounds, 1114112 after the greatest Unicode scalar, surrogates left out) |
| `sdfa.taut` | the DFA: subset construction and the partition refinement. The order of the states is the one the partition has, so it does not depend on how the subsets were found. |
| `scn.taut` | the patterns of each mode (newline, white space, comments, the terminals, the error token), the lookahead automata |
| `sch.taut` | the types of the grammar: which non-terminal is a struct, an enum or a token, and each production's type and constructor |
| `sha.taut` | SHA-256 of the grammar (there are no bitwise operations in Nib, so they are made of bits) |
| `emit.taut` | the words of the lines of a table file |
| `list.taut`, `bytes.taut` | sorted lists of numbers; bytes and slices of a text at `u64` positions |

The tests are those of `totes/llkgen` (`tools/selfhost-harness/tests/llkgen.rs`).

## Beyond the syntaxes

The grammar reader also reads the notation of parol's own grammar
(`parol.par`): `%grammar_type 'll(k)'`, `%user_type`, `%nt_type`, `%t_type`,
`@member` names, `: Type` after a symbol, `^` on a non-terminal, and type
paths `a::b::C`. Names and types shape the generated tree, not the tables,
so they are read past.

`%grammar_type 'lalr(1)'` (or `'LALR(1)'`) marks a grammar for
`totes/lalrgen` (`pargen_is_lalr`). Its repetitions then become left
recursive (`XList: XList X | ;`, as parol makes them for LALR(1)), and a
start symbol of more than one production gets one above it (`S0: S`).
Another grammar type stops with `a grammar type that is not read yet`.

## The states of the scanner

A grammar may declare states of its scanner, as scnr2's dynamic state does,
and use them in terminals whose end depends on an earlier token (Rust's raw
strings, here-documents):

```
%state n: count(0..=16)
%state tag: str("[a-z]+")
%%
RawOpen: 'r' + %capture('#', n) + '"';
RawClose: <RAW>'"' + %validate('#', n);
RawQuote: <RAW>'"' + %validate('#', n, 0..n);
```

`count(MIN..=MAX)` (or `MIN..END`) holds how many times a unit was seen,
`str(PATTERN)` a text. A terminal is literals joined by `+` with one
`%capture` or `%validate`. `%capture(UNIT, n)` and `%capture(tag)` store
what they match when the terminal becomes the token; `%validate(UNIT, n)`
matches only as many units as the state holds, `%validate(UNIT, n, RANGE)`
a count in `RANGE` (`a..b`, `a..`, `..b`, with numbers, `n`, `+` and `-`),
and `%validate(tag)` only the text the state holds. The scanner tables get
the lines `dyn_states`, `dynamic` and `dynamic_dfas`, written only when a
state is declared; `crates/tauto-syntax` and `totes/scan` run them as
scnr2 does.

## What is not done

- A grammar that uses a regular expression outside the subset the scanners of
  the repository use stops with `a regular expression: …` (word boundaries,
  anchors, `\w`, `\p{…}` other than `L` and `N`, ASCII classes, flags,
  non-greedy repetitions). Of these, all but anchors and word boundaries are a
  matter of adding them to `rx.taut` with a case in
  `tools/selfhost-harness/tests/data/regexes.txt`.
