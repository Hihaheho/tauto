# examples

Run these from the repository root; `tauto` is `cargo run -p tauto-cli --bin tauto --`.

## Start here

| File | What it shows | Command |
|---|---|---|
| `proofs.taut` | Theorems the kernel checks, one that uses an axiom, and a false claim shown by its negation | `tauto check examples/proofs.taut` |
| `handlers.taut` | Algebraic effects and `budget` in a few lines | `tauto run examples/handlers.taut` |
| `effects.taut` | An exception (the handler does not resume) and a choice (it resumes twice) | `tauto run examples/effects.taut` |
| `streams.taut` | A generator (`emit`) and a lazy stream whose items come from an effect (`fetch`), as effects instead of Future and Stream types | `tauto run examples/streams.taut` |
| `handler-proofs.taut` | Theorems about functions with effects and the handlers that run them, as written: a counter kept in a `var` (by induction), a handler that resumes twice, out-of-order completions | `tauto check examples/handler-proofs.taut` |
| `ownership.taut` | Moves, borrows, a view function, and writing through a borrow | `tauto run --check-ownership examples/ownership.taut` |
| `lean-migration/Simp.taut` | What to write where a Lean 4 proof uses `simp`: `Refl`, `match`, `rewrite!`, `calc`, `nat_norm!` ([guide](../docs/guide/from-lean.md)) | `tauto check examples/lean-migration/Simp.taut` |

`handlers.taut`, `effects.taut` and `ownership.taut` also run through the Rust backend
(`tauto run --backend rust FILE`) and print the same lines; `crates/tauto-cli/tests/examples.rs`
checks it.

## Programs with their proofs

Each is a tote: `src/` is the program, and proofs live in `proof/` or alongside the pure
implementation in `src/`. `tauto check` checks those sources; `tauto run --tote DIR` runs the
program. Axiom-free checking is covered by `cases/check/verified-examples.eure` and
`cases/check/effect-proofs.eure` and `cases/check/stack-check.eure`.

- `sort/`: insertion sort for **any type with an order** (`Ord`, `std/prelude/Ord.taut`), proved ordered
  and a rearrangement. `main.taut` sorts numbers and words with the same `sort`.
- `bst/`: a binary search tree (a set) for any `Ord` keys, proved ordered and a set.
- `compiler/`: arithmetic to a stack machine, proved correct.
- `stack-check/`: `mode!` generates a stack-language checker with derivations, unique output types, and refutations; a separate theorem connects accepted programs to safe execution, including both branches and their shared continuation. See its Japanese README.
- `regex/`: a derivative-based matcher that decides its language.
- `effect-proofs/`: algebraic completion effects whose handler calls the same proved transition; stale responses leave the state unchanged, while current responses update it. Its Japanese README states the handler and extraction trust boundary.
- `calc/`: reads arithmetic from text with an `inductive_syntax!` and compiles it with `compiler/`; the step from the tree to the code is proved.
- `typed-lang/`: a small typed expression language. `inductive_syntax!` makes the parser and tree from a grammar, `mode!` makes the type checker from the typing rules (sound, complete, unique), and the type safety of the evaluator is proved by hand. See its Japanese README.
- `bounded-batch/`: a queue snapshot split into a bounded batch and the remaining jobs, with
  proofs of order/duplicate preservation and size, source-bundle replay, and four-backend comparison.
- `certified-state/`: state transitions with `std/State.taut`; each command is proved to keep the
  invariant, and the program writes the checked transition's result into a mutable cell.
- `wf/`: functions by well-founded recursion (`decreasing_by`), with proofs from their unfolding equations.
- `fixed-width/`: steps on `U8` and `I32` from `std/UInt.taut` and `std/SInt.taut`, proved in the
  kernel and run on Nib's fixed-width integers.
- `float/` and `float32/`: `Float` and `Float32` code whose theorems the kernel checks by
  computing with `std/Float.taut` and `std/Float32.taut`.

`sort/` and `bst/` are where to see type classes: `where Ord(A)` on a function, `Ord::compare` as
its one comparison, and the laws of `Ord` (`equal_iff`, `swap`, `trans`) as the only facts the
proofs use about the elements.

## Proofs

- `nat/`: arithmetic on ℕ, stated with the `nat!` macro. Two induction steps use the proof step
  `by rewrite!(e): G { ⊢ G' from … }`, which writes the goal before and after each rewrite; the
  equations of the semiring use `by nat_norm!(): G {}`; the other steps use `Eq::trans` and typed `let`s. Both are checked by the same kernel.
- `lambda/`: the simply typed lambda calculus, type safety and strong normalization, with macros
  that write the typing and reduction proofs. The macros read syntax trees, so they use `_ =>`
  arms that `tauto lint` would reject in `std/` and `meta/`.
- `universes.taut`: an inductive type whose universe level is a parameter, and a recursor whose motive
  lives in a higher universe.

## Rust interop

`rust/` has five tote directories:

- `rust/files/`: a bridge crate written by hand.
- `rust/tasks/`: tasks on threads sharing a host counter from a hand-written bridge.
- `rust/threads/`: the `threads` executor, with a producer and a consumer over a `Channel`.
- `rust/regex_demo/` and `rust/json_demo/`: bindings generated by `tauto bind` for the `regex`
  and `serde_json` crates.

The files under `bind/` are generated: change `bind/*.config.eure` and run `tauto bind` again.
A `Buf` (an owned text buffer) is shown with its type, as in `replace = Buf("<> aab")`.

## JavaScript

`javascript/` is a tote for the JavaScript backend (`docs/design/javascript-backend.md`):
`tauto run --backend javascript examples/javascript/src/main.taut` runs it with `node`. It calls
asynchronous host functions in `host/http.mjs`, one of them through an `http_get` effect, and
Rust externs (the functions in `bridge/` and `i64::abs`) compiled to Wasm, with callbacks that perform effects.
