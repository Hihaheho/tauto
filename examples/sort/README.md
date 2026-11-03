# examples/sort: insertion sort for any ordered type, proved ordered and a rearrangement

A tote (`Tauto.eure`): `src/sort.taut` is the program (`insert`, `sort`, both `where Ord(A)`), `src/main.taut` is the shell
that sorts numbers and words with it, and `proof/sort.taut` is the proof, which `tauto check` checks and `tauto run` does
not read. No axioms.

- The order is the class `Ord` of `std/prelude/Ord.taut`, which programs and proofs both read. The program has one
  comparison, `Ord::compare(x, y)`, matched on `Less`, `Equal` and `Greater`. `List`, `Option` and `Pair` have an instance
  there, with its laws proved; `i64`, `u64`, `Text` and the like have one in `std/prelude/Classes.taut`, and `Nat` in
  `std/Ord.taut`.
- `sorted(l)` is a function to a proposition (each element is `le` the next one, `le(a, b)` meaning `a` is not after `b`);
  `Perm(A, l, m)` is the usual inductive permutation (`PermNil`, `PermSkip`, `PermSwap`, `PermTrans`).
- `le_of_less`, `le_of_equal` and `le_of_greater` turn the answer of `Ord::compare` into `le`; with `ord_swap_greater`
  they are the only uses of the laws.
- `insert_after` inserts into a sorted list that starts with a smaller key; that keeps the induction free of any equation
  on the result of `insert`.
- `sort_correct`: `sorted(sort(l)) ∧ Perm(A, l, sort(l))`, for every `A` with an `Ord`.

`std/Sort.taut` also sorts, by a comparator argument, and proves the output has the same elements (`Equiv`, which ignores
repeats). This example is the one that proves a permutation (the same number of each element).

```bash
tauto check examples/sort/proof/sort.taut
tauto run --tote examples/sort              # the interpreter
tauto run --backend rust examples/sort      # the same program through the Rust backend
```
