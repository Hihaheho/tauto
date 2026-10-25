# JavaScript backend

`tauto-jsgen` generates a standalone ES module from the checked NIR used by
`tauto-rustgen`. Parsing, type checking, effect checking, and ownership checking
remain shared. No kernel rules or language syntax are added.

```sh
tauto run --backend javascript program.taut
tauto build --emit javascript program.taut -o target/javascript
node target/javascript/main.mjs
```

`build --backend javascript` also writes the modules. Generation needs no
JavaScript runtime or package installation. `run` invokes `node` from PATH.
`--release` is specific to the Rust backend and is rejected for JavaScript.
The output directory defaults to `$TAUTO_TARGET_DIR/javascript/<name>` or
`target/tauto/javascript/<name>`. As with the Rust command, a tote directory
or its `Tauto.eure` may be used instead of a single source file.

The output contains `program.mjs` and `main.mjs`. Importing `program.mjs` does
not run the program. Its `run(show = console.log)` export executes the top
level, sending each complete display line to `show`. It can be imported into
another module or a browser. `main.mjs` calls it and turns an execution error
into a diagnostic and a failing process exit status.

## Initial supported subset

- Integers of all five widths, checked arithmetic and integer division,
  booleans, text, equality, and short-circuit boolean operators.
- Functions, recursion, function values, noncapturing closures, `if`, local
  variables, whole-variable assignment, loops, blocks, and early return.
- Constructors, records, field access, and matching with guards.
- Direct effects, aborting effects (`resume 0`), nested handlers, return arms,
  forwarding, and `show`.
- Builtins `concat`, `text_len`, `text_compare`, `text_of_i64`,
  `text_of_u64`, `div`, and `mod`.

Integers use `BigInt`, with checks against the declared width. Constructor
fields retain source evaluation order and are stored in declaration order.
Function and variable identifiers use NIR numeric identities. Source strings
are encoded as string literals rather than interpolated into executable code.
The generated module includes its runtime and has no package dependencies.

Suspending effects (`resume <=1`, `1`, `ω`), budgets, unions, borrows,
mutable captured cells, capturing closures, field assignment, other builtins,
and extern bindings are not implemented. Encountering one fails generation;
the CLI writes no output files until generation succeeds. NIR's existing
lowering restrictions also apply. This is not yet feature parity with the Rust
backend. The runtime does not provide Rust's independent ownership recheck.

Calls and loops marked by NIR consume a per-run host limit of ten million
steps. Recursion also remains subject to the host's call-stack limit. Runtime
errors currently report messages without Tauto source locations.

## Validation

`cargo test --locked -p tauto-cli --test javascript` runs emitted modules with
`node`, compares their output with the reference evaluator, exercises the CLI,
and checks rejection of unsupported features. The tests require `node` in PATH.
