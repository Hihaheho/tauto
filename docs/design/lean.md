# The Lean formalization

What `lean/` proves and assumes. Building it: [`lean/README.md`](../../lean/README.md).
Everything builds with the pinned Lean 4.34.1, with no `sorry`, no axiom beyond
Lean's `propext`, `Classical.choice` and `Quot::sound`, and no third-party
dependency.

## Trust

- The kernel's consistency and normalization cannot be proved in Tauto itself
  (Gödel's second theorem), so its model is proved in Lean. No axiom may be
  added to Tauto for kernel soundness before a Lean proof of `Consistent`
  exists.
- That `check/core.rs` implements the model is trusted and only tested
  (`crates/tauto/tests/kernel_diff.rs` fails if the Rust kernel accepts what the
  model rejects).
- Statements about Tauto's object languages are also proved in Tauto (`std/`,
  `meta/`), axiom-free except `Quot::sound` where `check.axioms` allows it.

## The kernel calculus

The kernel's pure stratum (`Γ ⊢ A : Sort u`, `Γ ⊢ t : A`): conversion and
proof erasure depend only on total, effect-free computation, and `Prop` is
proof-irrelevant with controlled elimination. The calculus must keep:

- proof and type equivalence independent of ambient effects;
- totality of `ε = ∅` by the rules, even with multi-shot handlers;
- effect keys not judged distinct merely because they are not yet
  definitionally equal;
- user axioms never introducing runtime reductions.

## Modules

| Module | Proves |
|---|---|
| `Proto/ListSet.lean` | lists as finite sets; shared by rows and tags |
| `Proto/Effects.lean`, `Tags.lean` | effect-instance equivalence and row laws |
| `Proto/Budget.lean`, `Choice.lean` | shared fuel composes (`advance_add`); a captured continuation queues branches in one machine |
| `Proto/Cycle.lean`, `Collect.lean`, `Analysis.lean`, `Memory.lean` | strong references form no cycle, reference counting frees exactly the unreachable objects, and the cycle analysis is sound ([`shared-levels.md`](shared-levels.md)) |
| `Proto/Core.lean` | type safety of a small pure core |
| `Proto/Nib/Typing.lean`, `Safety.lean` | Nib core typing, preservation, progress, `budget_bounded` ([`semantics.md`](semantics.md)) |
| `Proto/Nib/Div.lean`, `Halt.lean`, `Good.lean`, `Unfold.lean` | a row without `div` halts, by a logical relation |
| `Proto/Nib/Kind.lean`, `Lin.lean`, `Own.lean`, `Duplicate.lean` | ownership ([`ownership.md`](ownership.md)「Lean proofs」) |
| `Proto/Kernel/*` | the kernel model: confluence, subject reduction, normalization, consistency, quotients, the bidirectional checker, numerals and `+ * -` |
| `Proto/Handlers.lean` | adequacy of the computation-tree reading of handlers ([`effect-proofs.md`](effect-proofs.md)); `&mut` as one state per name agrees with a store when names do not alias |
| `Proto/Macro/*` | hygiene and expansion ([`macro-semantics.md`](macro-semantics.md)「Lean modules and obligations」) |

## The kernel's own model

The core (de Bruijn terms, impredicative `Prop`, cumulative sorts, `Pi`, `Nat`
with a dependent eliminator) is modelled in Lean (`Proto/Kernel/`) and again in
Tauto (`meta/Kernel*.taut`), proving the same substitution algebra, confluence,
`Pi` injectivity, weakening and subject reduction. `meta/kernel.taut` adds a
checker that returns its typing derivation, so it is sound by construction.
The Rust `Nat::ind` eliminates only into `Prop`, while the model's `natRec`
also eliminates into `Type`.

Numerals and `+`, `*`, `-` on `Nat` (`Lit`, a number below `2^256`, and the primitive operators of
`core.rs`) are abbreviations in the model (`Literals.lean`): `lit k` is
`succ^k zero`, and each operator is `natRec` with the motive `λ_. Nat` by
recursion on its second operand. On two numerals each reduces to the numeral
of the result (`add_lit`, `mul_lit`, `sub_lit`), which is what the kernel
writes at once, and each is typed `Nat`. A result of `2^256` or more is left
unreduced by the kernel, which only makes it convertible to less.
`kernel_diff.rs` generates numerals and the three operators and gives the
model their expansion.

### Rules of `core.rs` outside the model

What the kernel decides with these is trusted on the Rust code and its unit
tests alone; neither Lean nor `kernel_diff.rs` covers it.

| Rule in `core.rs` | Where | What would bring it in |
|---|---|---|
| Inductive families other than `Nat`, their eliminators and iota | `add_inductive`, `Core::iota` | a model of a general inductive schema |
| Unfolding of declared names and `let` values (delta) | `Core::unfold_head`, `Core::def` | a context of definitions in `Typing` |
| η for functions in conversion | `Core::conv_nodes` | an η rule in `Conv` |
| Proof irrelevance in conversion | `Core::conv` | `Prop` irrelevance in `Conv` (the model's `Conv` is untyped) |
| Universe level variables and polymorphic constants | `level.rs`, `universe.rs` | levels as terms in `sort` |
| `Nat::eq`, `Nat::lt`, `Nat::sub`, `Nat::div_nz`, `Nat::rem_nz` computed on numerals | `Core::numeric` | the prelude definitions in the model, as in `Literals.lean` |
| `Nat::divmod` and comparisons taken past a large offset `x + n` at once | `Core::divmod_offset`, `Core::offset_view` | an equation of the unfolding over `x + n`, `n ≥ 2^12` |
| Turns of a loop over a number taken at once | `Core::repeat` | the same, for the eliminator applied again |
| `Quot` and its constants | `Core::quot_iota` | modelled apart (below), not in `kernel_diff.rs` |

## Normalization and consistency

- **K** is the kernel core; **K_pred** is K with predicative `Π` (embedding
  into K, but not the Rust kernel, whose `Prop` is impredicative).
- Proved: strong normalization of K_pred (`typedP_sn`), its consistency
  (`consistent_pred`), and for full K consistency given normalization
  (`consistent_of_sn`) plus canonical forms.
- Missing: normalization of K. Reducibility candidates fail at the
  impredicative `Π` (the model graph is not well-founded), candidate valuations
  need domain-annotated λ, set models need ω inaccessibles, and no
  step-preserving translation to Church λ was found. A possible route is to
  erase proofs first, normalize the predicative remainder, then normalize
  proofs.
- Porting the proof to Tauto needs `Acc`, function-indexed families, choice
  and `propext`, which Tauto lacks.

## The quotient constants

`Quot`, `Quot::mk`, `Quot::lift` and `Quot::ind` with their computation rules
are conservative over K and K_pred (`Quotient.lean`): erasure maps each to the
carrier or an application. `Quot::sound` cannot be justified by erasure; it
holds in a realizability model reading types as partial equivalence relations
(`QuotEq.lean`, `PerModel.lean`, `QuotSound.lean`), proving consistency with
`Eq`, `Eq::rec` and `Quot::sound` over the predicative core. The model puts
`Eq(A, x, y)` in the sort of `A`, where the kernel puts it in `Prop`.

## The bidirectional checker

The checker is modelled as relations (`Bidir.lean` and neighbours). Proved:
soundness of the relation (not of the running checker), completeness of
conversion and subtyping for strongly normalizing terms, uniqueness of normal
forms, and completeness of checking for normal terms given normalization.

What the Rust kernel must match: impredicative `Prop` only at `imax`;
conversion compares needed subterms recursively after weak-head reduction; a
β-redex's argument is typed before reduction (otherwise `(λx. 0) Ω` would be
typed by its reduct). Call-by-need sharing and the memo of nodes found
different add no rule: reused forms are `Red1` steps already taken, and the memo
can only reject.

## Ported to tauto

`meta/` and `std/` re-prove the object-language results: `core.taut` (type
safety), `renaming.taut`, `row.taut` (lists as sets), `effects.taut`,
`budget.taut`, `identity.taut`, `typing.taut`, `syntax.taut`, `memory.taut`,
`Kernel*.taut` and `macro_scope.taut`. Inversion uses a `match` that unifies
indices through generated no-confusion.

## Open questions

- Normalization and consistency of K with impredicative `Prop`.
- Consistency with `Quot::sound` when `Eq` over `Type` lives in `Prop`.
- That the running checkers (`tc`, `check.rs`) implement the relation `Bi`.
- The `natRec` motive differs between the three checkers.
- Numerals of `2^256` or more in the kernel: the model's literals (`Literals.lean`)
  have no bound, so arithmetic past `2^256` would follow them, but the core
  does not compute it.
- Using the VM (`totes/vm`) during checking first needs a proof that it agrees
  with the Rust VM (`crates/tauto-vm`) on every program.
- For macros: the use-check half of T5 and the implementation's hygiene.
