# examples/wf: functions by well-founded recursion

A tote (`Tauto.eure`): `src/wf.taut` is the program (`half`, `pair_up`, `count_up`, each with `decreasing_by`),
`src/main.taut` runs it, and `proof/wf.taut` states what the functions do from their unfolding equations.
No axioms.

- `half(k, ...)` and `pair_up(t, ...)` recur on a value that is not a field of the argument, so structural
  recursion cannot define them; `decreasing_by measure(f)` compares the numbers `f` gives, and each recursive call
  ends with the proof that its first argument is below the one the function was called with.
- The kernel gets no rule for this (`crates/tauto-kernel/src/check/wf.rs`): `half` becomes `half@step`, `half`
  (`wf_fix` over `half@step`) and `half::eq`. `half` itself does not compute on a number; `half::eq` unfolds it once.
- `tauto run` and the Rust backend read the functions as plain recursion, the proofs left out of the calls.

```bash
tauto check examples/wf/proof/wf.taut
tauto run --tote examples/wf                 # the interpreter
tauto run --backend rust examples/wf         # the same program through the Rust backend
```
