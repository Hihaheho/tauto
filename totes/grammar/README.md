# grammar

Tauto's grammar is the `syntax tauto` declaration in `src/grammar.taut`.
The explicit `=>` clause lists its generated types and `tauto_parse`.
The parser returns `Result(tauto_Program, SynDiag)`, including typed nodes,
not just an acceptance flag. `src/main.taut` calls this parser on each path
passed as an argument and prints `ok` or `error`.

```sh
tauto run --tote totes/grammar -- examples/effects.taut
```

The table in `.tauto-syntax/` is keyed by the exact grammar literal's SHA-256.
It is the same table as `crates/tauto-syntax/tests/data/tauto.tables`.
`crates/tauto-selfhost/tests/grammar.rs` executes the generated parser on
Tauto, its own declaration, comments, Unicode, syntax literals and malformed
input, and compares acceptance with the bootstrap parser across the repository corpus.
Nested block comments are rejected by both entry points; ordinary block and
line comments are accepted. Parsing does not imply type checking or macro expansion.

## One grammar, two entry points

`tauto syntax source totes/grammar tauto` exports the grammar literal without
loading its generated types or requiring its table. This permits regeneration
when the grammar has changed and its old table no longer matches.
`scripts/generate-tauto-grammar.sh` writes that text verbatim to the bootstrap
`crates/tauto-parol/tauto.par` and the grammar-table fixture. Its `--check`
mode fails on drift without changing files. Both parser-generation scripts
call it, so the compiler and the declared parser derive from the same source.

After editing the declaration's grammar:

```sh
bash scripts/generate-tauto-parol.sh
bash scripts/generate-grammar-tables.sh
tauto fmt --fill-generated totes/grammar/src/grammar.taut
bash scripts/generate-syntax-tables.sh
```

The Rust compiler reads the declaration with committed bootstrap parser
tables. `tauto_parse` uses the existing `syn_parse` runtime
primitive; it is not a replacement for the compiler's CST recovery driver.
The `syntax` tote separately implements the scanner, LL(k) driver and CST
in Tauto. A shared declarative grammar is not a claim that those bootstrap
or runtime dependencies have disappeared. The generated typed AST and the
compiler's trivia-preserving CST are different representations.

The runtime parser retains `syn_parse`'s limits (1 MiB input and 65,536 parse
stack entries). Exceeding a limit returns a diagnostic, not a partial CST.
