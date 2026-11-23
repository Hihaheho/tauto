# grammar

Tauto's grammar is the `syntax tauto` declaration in `src/grammar.taut`.
The explicit `=>` clause lists its generated types and `tauto::parse`.
The parser returns `Result(tauto::Program, SynDiag)`, including typed nodes,
not just an acceptance flag. `src/main.taut` calls this parser on each path
passed as an argument and prints `ok` or `error`.

```sh
tauto run --tote totes/grammar -- examples/effects.taut
```

The table in `.tauto-syntax/` is keyed by the exact grammar literal's SHA-256.
It is the same table as `crates/tauto-syntax/tests/data/tauto.tables`.
`tools/selfhost-harness/tests/grammar.rs` executes the generated parser on
Tauto, its own declaration, comments, Unicode, syntax literals and malformed
input, and compares acceptance with the bootstrap parser across the repository corpus.
Nested block comments are rejected by both entry points; ordinary block and
line comments are accepted. Parsing does not imply type checking or macro expansion.

## One grammar, two entry points

`tauto syntax source totes/grammar tauto` exports the grammar literal without
loading its generated types or requiring its table. This permits regeneration
when the grammar has changed and its old table no longer matches.
`scripts/generate-tauto-grammar.taut` writes that text verbatim to the bootstrap
`crates/tauto-parol/tauto.par` and the grammar-table fixture. Its `--check`
mode fails on drift without changing files. Both parser-generation scripts
call it, so the compiler and the declared parser derive from the same source.

After editing the declaration's grammar:

```sh
tauto gen-tauto-parol
tauto gen-grammar-tables
tauto lint --fix totes/grammar/src/grammar.taut
tauto gen-syntax-tables
```

The Rust compiler reads the declaration with committed bootstrap parser
tables. `tauto::parse` uses the existing `syn_parse` runtime
primitive; it is not a replacement for the compiler's CST recovery driver.
The `syntax` tote separately implements the scanner, LL(k) driver and CST
in Tauto. A shared declarative grammar is not a claim that those bootstrap
or runtime dependencies have disappeared. The generated typed AST and the
compiler's trivia-preserving CST are different representations.

The runtime parser has no input or stack limit: a program parses its own data,
of any length and depth. A syntax literal read while checking keeps the macro
limits (`docs/design/macro-security.md`).
