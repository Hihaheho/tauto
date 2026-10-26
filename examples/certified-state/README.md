# Certified state commands

`std/State.taut` describes explicit, total state transitions. `StateHoare`
connects a command's precondition to a postcondition of the **actual** returned
state. `StatePreserves` is the invariant-preservation obligation for every
command. `state_run_preserves` proves preservation for every finite command
list, by induction over that list.

`state_certified_run` requires that obligation and a valid initial state. The
proof language checks both arguments. Extraction removes these certificates,
not the executable transition: it retains the same `state_run`. This is not a
runtime validity check and does not restrict callers of the erased API.

The example tracks a revocable permission and a natural-number balance.
`gate_step` both executes and specifies each command. Its proofs establish:

- spending while closed leaves the entire state unchanged;
- spending while open uses saturating predecessor, including at zero;
- no command increases the balance;
- every command list preserves the bound given by the initial capacity.

`gate_advance_safe` covers resuming from any state satisfying the invariant.
The runtime's `gate_commit` borrows an actual mutable cell and assigns the
result of that same `gate_advance` to it. The executable updates one cell across
separate authorize, spend, and revoke calls; it does not compute a second,
unverified implementation of the transition.

## Trust boundary

The pure transitions and their universal properties are kernel checked without
axioms. The one-assignment mutable adapter, borrow implementation, extraction,
and evaluator/native backend are trusted, not proved by these theorems.
`tauto check` is not a verifier of arbitrary imperative function bodies. The
integration test exercises this adapter on both backends and compares each
update against the same pure runner; this is regression evidence, not a proof
of the backend. A native caller can bypass the adapter or call erased APIs
without a proof. Such calls are outside the certified source-level contract.

This library models one explicitly threaded state and a finite list of total
commands. It does not verify general algebraic handlers, continuation capture,
multi-shot resumptions, concurrency, IO, failures, external authorization, or
aliasing outside the adapter. `gate_authorize` is a synthetic input command,
not authentication. Natural numbers extract to bounded `u64`; this example
only decrements a supplied representable balance and performs no growth.
Resource exhaustion and native stack limits remain runtime concerns.

## Checks

- `tauto check examples/certified-state/src/state.taut --fresh`
- `tauto run --tote examples/certified-state`
- `tauto run --backend rust examples/certified-state`
- `cargo test --locked -p tauto --test certified_state`
- `cargo test --locked -p tauto-cli --test certified_state`

`rejected/forged.taut` is deliberately outside `package.sources`. Its
increasing transition supplies an invalid invariant certificate and must fail
both checking and extraction. Mutation tests also change the real transition
and require the affected permission/balance proof to fail. A separate adapter
mutation leaves the pure proofs valid but changes runtime output; it makes
the trusted boundary observable rather than treating the adapter as proved.

## Source trust manifest

From the repository root, using a locally trusted Tauto CLI:

```sh
bundle=$(mktemp)
target/debug/tauto trust bundle . examples/certified-state/src/state.taut > "$bundle"
target/debug/tauto trust verify "$bundle" --axiom-free
```

The bundle contains the **unchanged** `src/state.taut` and its five
standard-library imports, their hashes and the declaration/axiom report. Keep
that JSON file to inspect or recheck it later. Verification needs only the
bundle and trusted CLI, not the original source tree. These commands do not
run mutation tests or remove source files.

The Rust integration test exercises the same example without another scripting
runtime:

```sh
cargo test --locked -p tauto-cli --test trust_bundle
```

It exports a temporary copy of the six-file source closure, checks the report,
removes only that temporary source copy, and verifies the saved bundle with
`--axiom-free`. It also requires rejection of changed bytes, an invalid
transition with its hash recomputed, a forged declaration report and a missing
import. Repository sources are never edited or removed. No machine-specific
bundle is committed.

The receiver must use the **same executable bytes** to match the recorded
checker identity, and must trust that executable independently. A different
build requires generating a fresh bundle; no machine-specific checker hash is
committed as a universal certificate. Hashes establish consistency, not
identity, authorship or authenticated distribution. An independently rechecked,
valid alternative source/report is not a forgery.

The entry is the existing pure proof file, **not the package**. Its report has
18 checked example declarations, including `gate_step_preserves`,
`gate_run_safe` and `gate_advance_safe`, with no transitive user axioms. The
receiver's `--axiom-free` policy also rejects unused explicit axioms.
`src/main.taut`, `gate_commit`, `perform` calls and the package manifest are
outside this source closure; a missing declaration is not a claim that it was
verified. The report does not certify the mutable adapter, erased Rust API,
backend, generated binary or runtime/resource behavior. Trust replay uses the
normal fresh Rust kernel path, not two independently implemented checkers.

The source protocol rejects executable top-level statements, syntax/macros and
resource loads. It does not package parser tables or fetch dependencies. Export
requires Unix; verification itself reads the bundle without the original source
root. Hostile proof normalization still needs receiver-managed resource limits.
See `docs/design/trust-bundles.md` for the protocol and boundaries.
