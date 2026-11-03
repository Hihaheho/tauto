# examples/bst: a binary search tree (a set of any ordered keys), proved ordered and a set

A tote. `src/bst.taut` has `Tree(A)`, `tree_insert`, `tree_member`, `tree_delete` (with `tree_min`, `tree_remove_min`
and `tree_join` for a node with two children). The keys are any type with an order: the functions that compare say
`where Ord(A)` (`std/prelude/Ord.taut`) and use one three-way `Ord::compare`, so each operation has one `match` on an `Ordering`.
`proof/bst.taut` proves, for every such `A` and with no axioms:

- `bst(t)`: at every node the left keys are smaller (`all_less`) and the right ones larger (`all_greater`);
  `In(x, t)` is the membership.
- `insert_bst`, `delete_bst`: the operations keep the tree ordered.
- `in_insert_inv`, `in_insert_intro`: the keys after `tree_insert(x, t)` are `x` and the keys of `t`.
- `delete_sub`, `delete_gone`, `delete_keeps`: the keys after `tree_delete(x, t)` are the keys of `t` other than `x`.
- `member_sound`, `member_complete`, `member_correct`: in an ordered tree `tree_member(x, t)` is `true` iff `In(x, t)`.

Each operation's behaviour at a node is stated once as an equation (`insert_less`, `delete_equal`, …) and the proofs rewrite with it.

The proofs use the laws of `Ord` and nothing else about the keys (`cmp_equal`, `cmp_greater`, `lt_trans`, `less_irrefl`,
`less_asym`). `lt(a, b)` is `Ord::compare(a, b) = Less`. `Bst` is an inductive family over any "smaller" relation `R`, because
a constructor cannot ask for an `Ord`; `bst(t)` is `Bst` at `lt`, and `bst_left`, `bst_right`, `bst_all_less`,
`bst_all_greater` and `bst_build` take it apart and put it together, so no proof has to mention `R`.
`main.taut` builds a tree of numbers and a tree of words with the same functions.

```bash
tauto check examples/bst/proof/bst.taut
tauto run --tote examples/bst
tauto run --backend rust examples/bst
```
