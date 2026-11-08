# The Lean formalization

What `lean/` proves, what it assumes, and how it relates to the Rust
implementation and to the proofs tauto checks about itself (`std/`, `meta/`).
How to install the pinned Lean and build is in [`lean/README.md`](../../lean/README.md).

Everything in `lean/` builds with Lean 4.34.1 (pinned by SHA-256), with no
`sorry` and no axiom beyond Lean's own `propext`, `Classical.choice` and
`Quot::sound`. The package has no third-party Lean dependency.

The languages the theorems are about are specified elsewhere: Nib in
[`nib.md`](nib.md), [`semantics.md`](semantics.md) and
[`ownership.md`](ownership.md); macros in [`macro-semantics.md`](macro-semantics.md).
This document says which module proves what, and what is still open.

## Trust and what stays in Lean

* **Consistency and normalization of tauto itself** (the kernel in
  `crates/tauto-kernel/src/check.rs`: strong normalization, the soundness of the
  generated eliminators, the universe rules). By Gödel's second theorem a
  theory cannot prove its own consistency, so the model of the kernel is
  proved in Lean, in a stronger setting.
* **The Rust implementation** (that `check/core.rs` implements that model)
  is trusted; only tests relate them. Every declaration is checked by
  `check/core.rs`, which reads names by their binders. The named checker
  (`check.rs`) elaborates the surface syntax into the terms it checks, and
  asks it every question of typing, reduction and conversion on the way.
* Statements about tauto's *object* languages are proved in tauto as well
  (`std/` and `meta/`, checked by tauto's own kernel, axiom-free except for
  the quotient's `Quot::sound` in the files `check.axioms` of `Tauto.eure`
  lists, which `tauto check` enforces; see "Ported to tauto"). No axiom may be added to
  tauto for kernel soundness before a Lean proof of `Consistent` exists.

## The kernel calculus

The kernel's pure stratum: `Γ ⊢ A : Sort u` and pure `Γ ⊢ t : A`. Type
conversion and proof erasure depend only on total, effect-free computation.
`Prop` is proof-irrelevant with controlled elimination. The computational
strata (computations, operations, handlers, divergence, budgets) and the rules
for tags and handler results are Nib's ([`semantics.md`](semantics.md)).
Tauto adds operations with dependent signatures and pure term keys, and
recursive handler result types only when they elaborate to well-formed,
strictly positive, terminating recursive data definitions.

```text
Γ ⊢ A sort                         type formation
Γ ⊢ v : A                          pure value typing
Γ ⊢ c : A ! ε                      computation typing
Γ ⊢ A ≡ B                          definitional equality
Γ ⊢ ε ≈ δ                          extensional row equality
H ⊢ ⟨c, σ, κ⟩ ↦ ⟨c', σ', κ'⟩          machine transition
```

Constraints the calculus must keep:

- **Dependent effects vs conversion**: proof and type equivalence are not
  contingent on ambient effects. The soundness theorem reflects the
  operational semantics, not equality by effect execution.
- **Multi-shot plus totality**: handlers can duplicate and reinvoke
  continuations. `ε = ∅` implies totality by the rules, not by the shape of
  the syntax.
- **Key equivalence under substitution**: an open key term's identity may
  change as variables are instantiated. Constraint solving does not decide two
  keys are distinct merely because they are not yet definitionally equal.
- **Proof irrelevance and elimination**: erased proofs are distinguished from
  computational data, and user-declared axioms cannot introduce runtime
  reductions.

## Modules

| Module | What it proves |
|---|---|
| `Proto/ListSet.lean` | Lists read as finite sets (`Sub`, `Equiv`): reflexivity, symmetry, transitivity, order and repeats do not matter. The one development the rows of `Nib/Row.lean` and `Effects.lean` and the tags of `Tags.lean` share. |
| `Proto/Renaming.lean` | `upR`, the renaming of de Bruijn indices under a binder, and its algebra; shared by `Core.lean` and `Kernel/Syntax.lean`. |
| `Proto/Tags.lean` | Tag sets modeled by extensional membership: `TagEq` is `ListSet.Equiv`. |
| `Proto/Effects.lean` | Closed pure key terms (`1 + 1 ≡ 2`), effect-instance equivalence, row membership modulo equivalence, effect-row laws (from those of `ListSet.lean`). |
| `Proto/Syntax.lean` | De Bruijn abstract syntax including universes, Pi, handlers, unions, folds. Syntax only. |
| `Proto/Choice.lean` | A small computation-tree model with resumptions; `choose` captures the remainder as a continuation. |
| `Proto/Budget.lean` | Executable shared-fuel machine; resumable suspended states. `advance_add` (`advance (n + m) s = advance m (advance n s)`): replenishing a globally shared budget composes, and capturing a continuation queues two branches in one machine, not two separately funded runs. |
| `Proto/Cycle.lean` | Strong references form no cycle (`heap_invariant_implies_acyclic`): a graph whose edges between immutable nodes go to older nodes, and whose segments between mutable nodes (inner nodes immutable) raise the level, has no cycle. A statement about graphs only; the checker that establishes the two conditions, reference counts and the machine are not modelled. `sites_acyclic_implies_acyclic`: the same when the storages are abstracted to sites whose graph has no cycle. See [`shared-levels.md`](shared-levels.md). |
| `Proto/Collect.lean` | Reference counting on a finite heap: a free (count zero) never takes an object reachable from a root (`drain_keeps_reachable`), and when the strong edges have no cycle some sequence of frees ends with exactly the reachable objects (`drain_collects`). Weak references and destructors are not modelled. |
| `Proto/Analysis.lean` | The cycle check's analysis over its constraint language (copies, joins, allocations, stores, loads, `Weak`, frees): a solution of the constraints describes every state a run reaches, so when the graph on sites has no cycle no reachable heap has a strong reference cycle (`analysis_sound`). A `Weak` is no edge and never upgrades to a freed storage. That the translation of Nib emits a constraint for every run-time copy is not proved. |
| `Proto/Memory.lean` | Axiom-free counterpart of `meta/Memory.taut`: strong-path abstraction, reachability preservation and reflection during zero-count collection, and exact reachability after a terminal drain with well-founded incoming edges. A natural-number rank supplies well-foundedness. Existence of a terminal drain and correspondence to the implementation are not proved here. |
| `Proto/Core.lean` | A small pure core (functions, `Bool`, `Nat` with `natRec` at a constant motive): renaming and substitution preserve typing, preservation, progress, `type_safety`. |
| `Proto/Nib/Row.lean` | Nib's types (with type variables, tags, `Text`/`Decimal`/`Float`, and `struct`/`enum` types with type arguments), effects (a declaration with its type arguments) and rows read as sets with row variables, with their laws and types and rows put for the variables. |
| `Proto/Nib/Typing.lean` | Typing of Nib's core: functions, calls, `if`, `var` cells, generic functions over types and rows, tags, `struct`/`enum` values, fields and constructor patterns (also on unions), `Text`/`Decimal`/`Float`, `perform` and `handle` with patterns, guards and exhaustive arms, `match`, `budget`, arithmetic at a width, functions in place of functions (covariant results, contravariant parameters, smaller rows), and the exit from a union. |
| `Proto/Nib/Safety.lean` | Small-step semantics with cells of the core and its **preservation**, **progress**, `type_safety` and `budget_bounded`; exhaustive `match` (`HasType.mtch`, `HasType.mtch_exhaustive`) and tags not added (`HasType.var_tags`). See [`semantics.md`](semantics.md)「Proved: the core (`lean/Proto/Nib/Safety.lean`, no `sorry`)」. |
| `Proto/Nib/Div.lean` | The rules that give `Div` to every way to recur: what a `var` holds (`DivClosed`), definitions in order (`DefsOrdered`), operations in a well-founded order (`EffOk`), `struct`/`enum` fields that take their own type (`DataOk`), and what leaves a `budget` (`BudgetOk`). |
| `Proto/Nib/Subst.lean` | Substitution after substitution (and after renaming), and the identity: what a call and a continuation need. |
| `Proto/Nib/Halt.lean` | **A row without `Div` stops** (`halts`), for the whole core, by a Kripke logical relation (`Comp`, `Sem`) over worlds of cell types, assuming a `Good` interpretation. See [`semantics.md`](semantics.md)「Proved: a row without `Div` stops (`lean/Proto/Nib/Halt.lean`, no `sorry`)」. |
| `Proto/Nib/Good.lean` | A `Good` interpretation, level by level: least fixed points over a well-founded order of levels (`strat_fix`), `Sem` keeping the order of the interpretation by polarity (`Sem.interp_mono`), so one exists when the parts have levels (`Strat.good`). |
| `Proto/Nib/Unfold.lean` | **Rules 3 and 4 give levels**, for finitely many `struct`s/`enum`s, with type variables too (`Strat.of_rules`, so `halts_of_rules`). |
| `Proto/Nib/Kind.lean` | Ownership's kinds (`copy`/`shared`/`affine`/`linear` with their join), resume quantities, `OwnSig` (kinds of declarations and type variables, quantities of operations and row variables, and `strict` for the second rule of control-flow linearity), `Ty.kind`, `Ty.Mv` and the quantities of a row. |
| `Proto/Nib/Lin.lean` | The use check `Lin`, and that it holds in a bigger state, under renaming, substitution and types put for type variables. |
| `Proto/Nib/Own.lean` | Uniqueness of owned values (T1 `lin_preservation`, T2 `unique`, T3 `linear_kept`, T5 `captured_noOwned`, and `captured_noLin` under `strict`). |
| `Proto/Nib/Borrow.lean` | Borrows: `Tm.bor`, `Ty.Bv`, the borrow check `BLin` (with `Frozen` for arms that pin `k`), kept in a bigger state and under renaming, substitution and type instantiation. |
| `Proto/Nib/BorrowStep.lean` | The invariant of T4 (`StoreB`, `Lent`); frames, calls, arms and the steps on cells keep the borrow check. |
| `Proto/Nib/BorrowSafety.lean` | **T4** `borrow_safety`, `borrow_safety_run`: no step touches a cell moved out of, and an owned cell is moved out of only while nothing borrows it. |
| `Proto/Nib/Duplicate.lean` | The copy of a suspended state: what an operation that resumes `ω` captures is duplicable and holds no `&mut` (`captured_dup`, `Held.not_mbrw`). |
| `Proto/Nib/Free.lean` | Freeing at the end of a block (`Tm.scoped`, `scoped_lin`, `scoped_blin`, `scoped_borrow_rejected`). |
| `Proto/Nib/View.lean`, `ViewExample.lean` | Calls that return a view (`reborrow`, `reborrowMut`) and declared view functions (`ViewDecl`, `Prim.vcall`), with examples. |
| `Proto/Nib/Examples.lean` | Programs the rules accept or reject; a declaration (`askSig`) that meets the assumptions of the safety proof and the rules for `Div`; five loops without `Div`, each rejected by one rule; `halts` on `askSig`, a `Stream` and a generic `List<T>`; an `OwnSig` for `askSig` and arms the use check accepts or rejects. |
| `Proto/Kernel/Syntax.lean`, `Reduction.lean`, `Typing.lean`, `Safety.lean` | The kernel's core K: renaming and substitution algebra; parallel reduction, complete development, confluence, `Conv` as joinability, `Pi` injectivity and `Pi`/sort disjointness; `Sub`, `Typing`, weakening, substitution; generation, validity, `iota_typing`, subject reduction. |
| `Proto/Kernel/LR*.lean`, `CandOps.lean`, `SNBase.lean`, `SNCand.lean`, `Fund*.lean`, `NatRec.lean`, `StrongNorm.lean`, `Consistency.lean`, `Normalization.lean` | Normalization and consistency (see "Normalization and consistency of K"). |
| `Proto/Kernel/Quotient.lean` | The kernel's quotient constants are conservative (see "The quotient constants"). |
| `Proto/Kernel/QuotEq.lean`, `PerModel.lean`, `QuotSound.lean` | `Quot::sound` is consistent with the predicative core, `Eq` and `Eq::rec` (see "The quotient constants"). |
| `Proto/Kernel/Bidir.lean`, `WhNorm.lean`, `ConvComplete.lean`, `BidirComplete.lean` | The bidirectional checker as a relation (see "The bidirectional checker"). |
| `Proto/Handlers.lean` | Adequacy of the computation-tree reading of handlers (`adequate`): on a frame machine with bind and handler frames, where `perform` captures the continuation up to the nearest handler (multi-shot), a program that runs to a value has the tree `pure v` under the fold of [`effect-proofs.md`](effect-proofs.md). Operations, values and handler arms are abstract (HOAS); `var`, rows and the elaborator itself are not modelled. |
| `Proto/Macro/*.lean` | Hygiene and expansion of macros (see "Macro hygiene and expansion"). |

The ownership modules are described with their rules in
[`ownership.md`](ownership.md)「Lean での証明」.

## The kernel's own model

The kernel's core (de Bruijn terms, impredicative `Prop`, cumulative sorts,
`Pi`, `Nat` with a dependent eliminator) is modelled twice, and the two
developments prove the same things:

| Lean (`lean/Proto/Kernel/`) | tauto (`meta/`) |
|---|---|
| `Syntax.lean`: the renaming and substitution algebra | `KernelAlg.taut`: the same lemmas, up to pointwise equal renamings and substitutions (`meta/` does not assume function extensionality) |
| `Reduction.lean`: parallel reduction, `develop`, confluence, `Conv` as joinability, `Pi` injectivity, `Pi`/sort disjointness | `KernelPar.taut`: `Par`, `develop`, `par_dev`, strip lemma, `confluent`; `KConv` (the equivalence closure of `Red1`) equals joinability; `pi_inj`, `sort_inj`, `pi_ne_sort` |
| `Typing.lean`: `Sub`, `Typing`, weakening, substitution | `KernelSafe.taut`: `sub_trans`, `sub_pi_inv`, `sub_ren`, `sub_subst`, `ktyping_ren`, `ktyping_subst`, `ty_inst` |
| `Safety.lean`: generation, validity, `iota_typing`, subject reduction | `KernelSafe.taut`: `lam_inv`, `pi_gen`, `succ_inv`, `valid`, `iota_typing`, `conv_ctx`, `subject_reduction` |
| (not written) | `Kernel.taut`: a checker that returns its verdict together with the typing derivation, so its soundness holds by construction |

In the tauto port, conversion is an equivalence closure, and the
Church-Rosser proof is what makes it joinability. Inversion is a `match` that
unifies the indices (`lam_inv(h: KTyping(G, Klam(b), T))` lists only `ty_lam`
and `ty_sub`), and `subject_reduction` inverts `Red1` on `Kapp` and `KnatRec`
in its own arms; a `match` can only be on a variable, so a value computed by
another lemma is taken apart in a helper. A recursive call from inside a helper
is passed in as a function (`ih`), because only the function that does the
`match` may recurse structurally.

`crates/tauto/tests/kernel_diff.rs` is the differential test: it generates
closed `(term, type)` pairs, runs the model checker (inside the Rust kernel)
and the Rust kernel's own check on the translated program, and fails if the
Rust kernel accepts anything the model rejects. The one deliberate difference
it reports: the Rust `Nat::ind` eliminates into `Prop` only, whereas the
model's `natRec` also eliminates into `Type`.

## Normalization and consistency of K

**Target systems.**

* **K**: `Typing`/`WF`/`Red1` of `Typing.lean`, `Reduction.lean` (de Bruijn, Π/λ/app, impredicative
  `Prop` via `imax`, cumulative sorts, Nat/zero/succ/dependent `natRec`, full-congruence β/ι).
  No general inductives, definitional proof irrelevance, unions, effects, Div, budget.
* **K_pred**: K with `Π` at `sort (max s₁ s₂)` (`TypingP`, `Fund.lean`). Embeds into K
  (`TypingP.toTyping`). Not the Rust kernel: Rust's `Prop` is impredicative.

**Checked theorems.**

| Theorem | Statement | File |
|---|---|---|
| `typedP_sn` | `WFP Γ → TypingP Γ t A → SN t`, `SN t := Acc (fun next cur => Red1 cur next) t` | StrongNorm |
| `TypingP.toTyping` | `TypingP Γ t A → Typing Γ t A` | StrongNorm |
| `consistent_pred` | `¬ ∃ t, TypingP [] t FalseCode` | Consistency |
| `consistent_of_sn` | `SN t → Typing [] t FalseCode → False` (full K) | Consistency |
| `canon` | typable `Red1`-normal term is `Ne`, λ, zero, succ, sort, Π or nat | Consistency |
| `exists_nf` | `SN t → ∃ u, Reds t u ∧ normal u` | Consistency |

`Normalization.lean` pins down the statements (`SN`, `Consistent`,
`FalseCode`), proves that `FalseCode` (`∀ P : Prop, P`) is a well-formed
`Prop` and that strong normalization transfers along a step-simulating
translation.

**Rule correspondence** of the direct reducibility proof:

| Rule | Direct reducibility |
|---|---|
| var, sort, cumulativity | `Rall`/`R m`; `Sub` is semantic inclusion (`sub_sem`) |
| Π, λ, app | `LRB.pi` graph; `Cand.beta`; no weakening needed (`SN.of_subst`) |
| Nat, zero, succ, natRec (large elim.) | `RNat`, `natRec_main` (induction on `RNat`) |
| impredicative Prop | **missing** (see "Open questions") |

**Why SN of K is harder than K_pred.** K has, at once, an impredicative
`Prop`; a Curry-style λ (it carries no domain, so a term does not determine its
type); sorts cumulative over every level; and `natRec` eliminating into every
sort. Each standard route stops at a concrete point:

* **Reducibility candidates with a model graph (`LRB`).** At `Prop`, the `Π`
  clause quantifies over the candidates of a larger universe. The graph is then
  defined in terms of itself and is not well-founded. That is why only K_pred
  is proved.
* **Candidate valuations.** These interpret a type by a candidate given a
  valuation of its type variables, which needs convertible types to get the
  same candidate under every valuation. With Curry λ, a type variable can stand
  for a type constructor of any kind, and impredicative quantification ranges
  over all of them, so this coherence has to be proved for higher-kinded atoms;
  the usual proof relies on the term recording its domain.
* **Set-theoretic models** interpret `Type_i` for every `i` at once. That needs
  ω inaccessibles or induction-recursion, which Lean cannot state uniformly in
  one universe. Truncating to finitely many levels proves SN only for terms
  below a fixed level: weaker than `typed_sn`, though it covers every given term.
* **Translation to a calculus with Church λ.** A step-preserving translation
  would need domain annotations on λ. Adding them changes `Red1`, and none was
  found that keeps the steps one-to-one with Curry β.

A route that might work, unproved: erase proofs first, so that the
computational part is predicative and is normalized by the K_pred argument;
then normalize proofs by candidates over the erased types. The open lemma is
that erasure commutes with `Red1` up to the steps the erasure removes.

**A port to tauto** of the SN proof needs `Acc`, an inductive family with
function-valued indices (`LRB`), `Prop`-valued choice (`fun_choice`) and
`propext`/`funext` (`LRB.unique`). Tauto's function extensionality
(`std/Quot.taut`) rests on the axiom `Quot::sound`, which `meta/` does not
use, and tauto has no `propext` or choice, so a port needs sets restated as
setoid-predicates and `propext`/choice removed. Consistency of tauto itself is not claimed (K is data
inside Lean), and adding `typed_sn` as a tauto axiom is excluded.

## The quotient constants

The kernel's `Quot`, `Quot::mk`, `Quot::lift` and `Quot::ind` (`check/core.rs`,
declared in the prelude) with their computation rules
`Quot::lift(A, r, B, f, h, Quot::mk(A', r', a)) ⟶ f(a)` and
`Quot::ind(A, r, P, m, Quot::mk(A', r', a)) ⟶ m(a)` are added to K and K_pred
in `Quotient.lean` (`TmQ`, `Red1Q`, `TypingQ ρ` with `ρ = imax` for K and
`ρ = max` for K_pred). The model has no `Eq`, so the respect proof `h` may
have any type; erasure drops it, so the theorems hold for the kernel's
respect type too.

`erase` reads `Quot(A, r)` as `A`, `Quot::mk(A, r, a)` as `a`, and a lift or an
induction as an application. A step goes to steps (a computation rule to
none), and a typing to a typing.

| Theorem | Statement |
|---|---|
| `TypingQ.erase`, `TypingQ.eraseP` | `TypingQ imax Γ t A → Typing (eraseCtx Γ) (erase t) (erase A)`, the same for `max` and `TypingP` |
| `consistent_pred_quot` | `¬ ∃ t, TypingQ max [] t (embed FalseCode)` |
| `consistent_quot` | `Consistent → ¬ ∃ t, TypingQ imax [] t (embed FalseCode)` |
| `conservative`, `conservative_pred` | a closed type of K (K_pred) inhabited with the quotient constants is inhabited without them |

`Quot::sound` (`Eq(Quot(A, r), Quot::mk(A, r, a), Quot::mk(A, r, b))` from
`r(a, b)`) states an `Eq`, which erasure cannot justify: it would make
related values of the carrier equal, for every relation, and a large
elimination then tells them apart. It holds in the model that reads a
quotient as its set of equivalence classes, which `QuotSound.lean`
formalizes for the predicative core.

**The system** (`QuotEq.lean`, `TmE`, `TypingE`) is K_pred (`Π` at
`max s₁ s₂`) with the quotient constants, the kernel's respect type for
`Quot::lift` (`∀ a b, r(a, b) → Eq(B, f(a), f(b))`), `Eq`, `Refl`, the
dependent eliminator `Eq::rec` with its computation rule, and `Quot::sound`.
One rule differs from the kernel: `Eq(A, x, y)` lives in the sort of `A`,
as `Π` does in K_pred, where the kernel puts it in `Prop` for every
`A : Type`. A predicative `Prop` already cannot quantify over `Nat`; an
`Eq` of `Type` data in `Prop` is the same kind of step (see "Open questions").

**The model** (`PerModel.lean`) is a realizability model. A term is read as
a term of the core by `TmE.erase`: a proof of an equation (`Refl`,
`Quot::sound`) as `zero`, `Eq::rec` as its case `d`, a quotient value as its
representative, `Quot::lift` and `Quot::ind` as application, and `Eq` and
`Quot` as two codes that no other type reduces to (`eqc`, `qc`). A type is
read as a partial equivalence relation on terms, through the inductive
graph `G m L A A' S` ("`A` and `A'` are equal types whose equal elements
`S` relates"), built like `LRB` but on pairs of types, so that the domain
of a function type fixes its family up to equality:

| Type | Equal elements |
|---|---|
| `Nat` | reduce to the same numeral |
| `sort i` | equal types of the universe `i`; at `i = 0` their relation is also proof irrelevant |
| `Π` | send equal arguments to equal results |
| `Eq(X, x, y)` | any two terms when `x` and `y` are equal in `X`, none otherwise |
| `Quot(X, r)` | elements of `X` joined by a chain of equalities of `X` and of pairs `r` relates by an element |

| Theorem | Statement |
|---|---|
| `G.good`, `G.symm`, `G.trans`, `G.uniq`, `G.conv`, `G.mono` | each relation is a PER closed under conversion; type equality is symmetric, transitive, closed under conversion and determines the relation |
| `fundE` | a typed term, under two substitutions that send each variable to equal elements of equal types, gives equal elements of equal types |
| `consistent_quot_sound` | `¬ ∃ t, TypingE [] t (embed FalseCode)` |
| `no_eq_zero_one` | `¬ ∃ t, TypingE [] t (Eq(Nat, 0, 1))` |

`Quot::sound` holds because `zero` is an element of
`Eq(Quot(A, r), a, b)` exactly when `a` and `b` are in one class, which
`r(a, b)` having an element makes them. `Quot::lift` respects classes
because its respect proof, read through `Eq`, says that `f` sends each step
of a chain to equal results; `Quot::ind` does because its motive is a
proposition, whose relation is proof irrelevant. `FalseCode` is empty
because `Eq(Nat, 0, 1)` is a proposition with no elements.

## The bidirectional checker

The checker of `crates/tauto-kernel/src/check.rs` and `meta/Kernel.taut` (`tc`) is modelled as
inductive relations (`WhnfOf`, `ConvA`, `SubA`, `Bi inf|chk`), one constructor per case
(`Bidir.lean`, `WhNorm.lean`, `ConvComplete.lean`, `BidirComplete.lean`).

| Theorem | Statement | Assumes |
|---|---|---|
| `bi_infer_sound`, `bi_check_sound` (of the relation `Bi`, not of the running checker) | `Bi inf Γ t A → WF Γ → Typing Γ t A`; same for `chk` given `Γ ⊢ A : sort s` | nothing |
| `convA_complete` | `SN t → SN u → Conv t u → ConvA t u` (a derivation of the relation exists; not termination of an executable `conv`) | nothing |
| `subA_complete` | `Sub A B → SN A → SN B → SubA A B` | nothing |
| `normal_unique` | `Normal n → Normal m → Conv n m → n = m` | nothing (no SN) |
| `bi_complete` | `Γ ⊢ t : A`, `t` Red1-normal, `Γ ⊢ T : sort s`, `A ≤ T` ⟹ `Bi chk Γ t T` | `TypedSN` (hypothesis) |

`bi_complete` is conditional on `TypedSN` (strong normalization of K), which is proved only for K_pred.
Terms with a β-redex whose head is a λ are outside it: λ has no domain, so such a head cannot be
synthesized (`Kernel.taut`'s `redex_case` infers the argument first).

Differences between the three checkers:
* natRec motive: the Lean `Typing` allows any sort; `Kernel.taut` checks the motive against `Π nat (sort 2)`
  (incomplete); Rust eliminates only into `Prop`.
* β-redex head: see above.

**What the Rust kernel must match.** Impredicative `Prop` only at `imax`. SN is about the
full-congruence β/ι relation `Red1`; the checker may use weak-head reduction to expose a head
constructor, but its conversion must then compare the needed subterms recursively (the relations
`ConvA`/`SubA`). A β-redex `(λ b) a` has its argument typed before it is reduced: otherwise
`(λx. 0) Ω` with `Ω = (λx. x x)(λx. x x)` would be typed by its reduct `0`, although `t → t` makes it
non-SN and `Typing` requires `Ω : A`. Differential tests are not verification.

**Sharing in the Rust kernel adds no rule.** Reduction there is call by need: an argument
substituted for a variable, a field of a constructor and the value of a name are each one node
wherever they occur, and the weak head normal form found for a node is used again wherever that
node is met (`Core::whnf_node`, `Core::recall`). Each kept form was reached from its node by the
kernel's own β/δ/ι steps, so using it is a run of `Red1` steps already taken, and the joinability
`Conv` of the model is unchanged; nothing in the Lean development needs to change. Conversion also
remembers pairs of nodes it found different (`Core::conv_node`): that can only make it answer
"different", which rejects a proof and never accepts one. Entries hold their nodes weakly, so an
address is never reused while it is a key, and every table is emptied after each declaration.

## Ported to tauto

Proofs about tauto's object languages are also checked by tauto's own kernel:

| Lean | tauto |
| --- | --- |
| `Proto/Memory.lean`: path abstraction and exact reachability after terminal zero-count collection under a well-founded edge relation | `meta/Memory.taut`: the same model and theorems, without axioms; terminal-drain existence and implementation correspondence remain separate obligations |
| `Proto/Core.lean`: `Ty`, `Tm`, `ren`, `up`, `subst`, `single` | `meta/Core.taut`: same names; structural recursion compiled to eliminators |
| `upR` (`Proto/Renaming.lean`, shared with `Proto/Kernel/Syntax.lean`) | `upR` (`meta/Renaming.taut`, shared with `meta/Kernel.taut`) |
| `HasType` | `HasType` (indexed inductive in `Prop`), contexts as `List(Ty)` with `nth` |
| `RenOk`, `HasType.ren` | `RenOk`, `RenOk_up`, `ren_typing` |
| `SubstOk`, `HasType.subst`, `subst_single` | `SubstOk`, `SubstOk_up`, `subst_typing`, `subst_single_typing` |
| `Value`, `Step` | `Value`, `Step` |
| `preservation` | `preservation` (inversion by computation: `Inv`, `inversion`) |
| `canonical_*`, `progress` | `canon_arr/nat/bool`, `progress` (closedness as `G = nil`) |
| `type_safety` | `type_safety` |
| `Proto/ListSet.lean` (`Sub`, `Equiv`, `append_comm`, `append_idem`, `append_assoc`, `append_sub`, …), which `Proto/Nib/Row.lean` and `Proto/Tags.lean` (`TagEq`) use | `std/Row.taut`: one development over `List(A)`, with `Mem` an indexed inductive and `Mem::append_inv` proved by a `match` that unifies the index `cons(h, append(t, ys))` |
| `Proto/Nib/Row.lean` (`Ty`, `Eff`, `divEff`, `exceededEff`) | `meta/Effects.taut`: `Ty` and `Eff` are mutual and nest `List`; the rows of effects reuse the `Row.taut` lemmas; `Div` is not `Exceeded(T)` |
| `Proto/Choice.lean`, `Proto/Budget.lean` (`ChoiceTree`, `SearchMachine`, `step`, `advance`, `advance_add`, `advance_complete`, the three sample runs) | `meta/Budget.taut`: `ChoiceTree` has a function-typed field, `advance_add` is induction on the fuel with the machine changing |
| `Proto/Effects.lean` (`TypeCode`, `KeyTerm`, `KeyEq`, `EffectId`, `EffectEq`, `RowContains`, `RowEq`, `row_union_comm`, `row_union_idempotent`, `tag_order_does_not_change_effect`) | `meta/Identity.taut`: names are numbers, `∃` is the inductive `RowContains`, `∀ e. ↔` is `Iff` under a `∀`; in both, the laws of `RowEq` come from those of the rows as sets (`rowEq_of_equiv`) |
| `Proto/Nib/Typing.lean` and `Proto/Nib/Examples.lean` (`Width`, `Prim` with `div`, `Tm`/`Clause`, `HasType`/`HasTypes`/`ClauseOk`, `Fits`, `perform_mem`, `unhandled_perform`, the `ask`, handle and `budget` examples. Not ported: `Fits.no_widening`, whose `match` would have to unify the index of `fits_refl(a): Fits(a, a)` twice; the `div` and union examples) | `meta/Typing.taut`, `meta/TypingExamples.taut`: `Tm` and `Clause` are mutual and nest `List`/`Option`; the typing judgment is a mutual family of three indexed `Prop`s with a premise under `∀`; the two inversion lemmas are `match`es that unify the index `tperform(e, args)` against every constructor, by the no-confusion generated for the mutual group |
| `Proto/Syntax.lean` (`CoreUniv`, `CoreSort`, `CoreTerm`) | `meta/Syntax.taut`: `CoreTerm` nests `List` and `List(Pair(_, CoreTerm))`; a mutual `term_size` recurses through the lists |
| `Proto/Kernel/` | `meta/Kernel*.taut` (see "The kernel's own model") |
| `Proto/Macro/Scope.lean` | `meta/MacroScope.taut` (see "Macro hygiene and expansion") |

`Core.taut` states inversion of an indexed family as a continuation-passing
proposition computed from the term (`Inv`); the later ports use the `match`
that unifies indices (generated no-confusion).

## Macro hygiene and expansion (`Proto/Macro/`)

The modules, the statements they prove (hygiene H1 to H4, expansion E1, E2,
E4, determinism D2, `Judgement` C1, acceptance of typed macros T1, T2, T4, E5, and
both halves of the substitution lemma T5), their tauto port
(`meta/MacroScope.taut`) and what is not formalized are listed in
[`macro-semantics.md`](macro-semantics.md)「Lean のモジュールと証明義務」.

## Open questions

* `typed_sn` and `Consistent` for **K** (impredicative `Prop`). Only the
  conditional `consistent_of_sn` holds; the missing step is the `Π` clause of
  the reducibility model at `Prop` (see "Why SN of K is harder than K_pred").
* Consistency with `Quot::sound` with `Eq` in `Prop` for data of `Type`
  (the kernel's rule), and with an impredicative `Prop`. In the model of
  `QuotSound.lean` a proposition's relation is fixed by the graph of the
  universe below, so `Prop` cannot contain an `Eq` over `Type`, whose
  relation `Prop : Type` makes depend on `Prop`; reading `Prop` as truth
  values needs a model of the universes as sets (see "Why SN of K is harder
  than K_pred").
* "Normal forms of convertible SN terms coincide" follows from confluence and
  `exists_nf` but is not stated as a separate theorem.
* That the *running* checker (`tc` in tauto, `check.rs` in Rust) implements the
  relation `Bi`.
* The natRec motive differs between the three checkers (see "The bidirectional
  checker").
* Numerals past `u128` in the kernel. The core's literal arithmetic stops at
  `u128` and leaves a sum or product past it unreduced. Numbers of any size are
  to be handled by the kernel, and the representation and its arithmetic are
  backed by a correspondence with the Lean model of the literals (the same
  numeral as `Succ` applied to `Zero`, and each operation agreeing with the one
  on the unary form), before the core relies on them.
* Evaluation on the VM (`totes/vm`) during checking. The kernel does not use the
  VM's results. Before a result of the VM is taken in place of reduction, it is
  to be proved that the VM and the evaluator give the same meaning to every
  program they both run (the same value, the same unanswered operation, or both
  out of steps), so that the VM adds nothing to what is trusted beyond that
  proof.
* For macros: the use-check half of T5, and that the implementation's hygiene
  (`crates/tauto-surface/src/macros/scope.rs`) agrees with the inclusion rule
  ([`macro-semantics.md`](macro-semantics.md)「Lean のモジュールと証明義務」).
