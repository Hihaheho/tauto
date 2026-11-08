# Coming from Lean 4: replacing `simp`

This guide is for people who write proofs in Lean 4 and want to know how Tauto handles common uses of `simp`. Tauto has no general simplifier or lemma search. The checked examples linked below show the corresponding proofs in context; the test suite checks them through `cases/check/lean-migration.eure`.

## Why there is no `simp`

`simp` rewrites a goal with a set of lemmas in an order and to a depth the proof does not state. Tauto proofs make each transformation visible: a rewrite step writes its goal before and after the rewrite, and the kernel checks both goals and the term built by the tactic ([`macro-steps.md`](../design/macro-steps.md)).

There is no `sorry` or inference hole that asks the machine to guess a term. An unfinished proof is a named hole and is never accepted. A proposition can be proved by computation, by an explicit term, by a `calc` chain, or by a step that states both goals.

The examples in [`Simp.taut`](../../examples/lean-migration/Simp.taut) correspond to the following situations:

- `add_zero_right`: computation closes an equality, so the proof uses `Refl`.
- `zero_add`: structural induction uses `match`; the recursive call supplies the induction hypothesis.
- `add_comm_steps`: a rewrite step states the original and rewritten goals, then uses the induction hypothesis.
- `length_map_append`: a `calc!` chain names each equality used in the argument.
- `add_left_comm`: `nat_norm!` decides polynomial equalities over `Nat`.
- `swap_hyp`: rewrite the goal into the form of a hypothesis; hypotheses are not rewritten in place.

## Cheat sheet

| Lean 4 use | Tauto approach | Checked example |
|---|---|---|
| `simp` closes an equality by computation | Use `Refl`; the kernel checks conversion. | `add_zero_right` |
| `induction n <;> simp [*]` | Write `match` with every constructor and use recursive calls explicitly. | `zero_add` |
| `simp [h₁, h₂]` for equations | Use one goal-stating rewrite step per equation, a `calc!` chain, or a term. | `add_comm_steps`, `length_map_append` |
| Reorder natural number sums and products | Use `nat_norm!` for polynomial equalities and `nat_le!` for supported natural number inequalities. | `add_left_comm` |
| `simp at h`, `simpa using h` | Rewrite the goal to the statement of `h` and provide `h`. | `swap_hyp` |
| `simp?` | Inspect a named goal with `tauto goals`; `tauto expand` can scaffold a rewrite step. | — |

## Rewriting and calculation

A rewrite step names the expression being rewritten, the goal before the rewrite, and the goal afterward. The tactic does not infer a motive. The reader can compare the written goals, and the kernel rejects a step when either goal is wrong. The `add_comm_steps` theorem in the checked example file demonstrates this pattern.

For a chain of equalities, `calc!` (`std/Calc.taut`) names the intermediate expressions and the proof of each transition, with each expression written after a `$` (see `docs/design/syntax.md`, "証明の構文"). The `length_map_append` theorem shows how this replaces a simplifier that rewrites both sides.

There is no rewriting of hypotheses in place. To use a hypothesis, rewrite the goal until it matches the hypothesis, as in `swap_hyp`. To change the proposition available as a hypothesis, bind a new, typed `let` with an explicit proof term.

## Arithmetic automation

`nat_norm!` handles equations whose sides are polynomials over `Nat`, built from addition, multiplication, successors, numerals, and variables. Its correctness is proved in `std/NatNorm.taut`; the kernel checks the resulting term. It does not prove inequalities.

`nat_le!` handles the supported natural number propositions for `<` and `<=` described in `std/Tactic.taut`. For natural number facts outside those forms, use explicit lemmas and proof terms. Tauto has no counterparts for Lean's `omega`, `linarith`, `ring`, `norm_num`, or `decide` tactics.

## What the tools report

- `tauto goals FILE --hole h` reports the hypotheses and goal at a named hole.
- `tauto expand FILE --hole h --by 'rewrite!(e)'` creates a rewrite step with an arm to fill; `--write` edits the file.
- `tauto try FILE --hole h --with TERM` checks a candidate term without editing; `tauto fill` writes it.
- `tauto suggest FILE --hole h` lists lemmas whose conclusions fit the goal by shape. It does not search using function names in the goal. Inspect the relevant standard library file (`tauto doc` writes it as linked pages) to find lemmas.

A written goal that differs from the actual goal is an error. `tauto check --json` reports the same error in JSON, and a step whose arm differs from the goal produced by its tactic can be repaired using the edit described in [`macro-steps.md`](../design/macro-steps.md).

## Differences to expect

- A file sees names it imports. Files using `calc!` import `std/Calc.taut`; files using `rewrite!` import `std/Rewrite.taut`; files using `nat_norm!` or `nat_le!` import `std/Tactic.taut`.
- Every constructor must be listed in a `match`.
- `tauto suggest` is shape-based lemma assistance, not a replacement for a simplifier's rewrite set.

## Related

- [`docs/design/macro-steps.md`](../design/macro-steps.md): how a step is checked.
- [`examples/nat/`](../../examples/nat/): checked arithmetic proofs using rewrite steps and natural number tactics.
- [`docs/design/lemma-search.md`](../design/lemma-search.md): what `tauto suggest` does.
