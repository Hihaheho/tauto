# examples/lambda: the simply typed lambda calculus, with proofs and no axioms

Terms use de Bruijn indices (`Lib.taut`): `Ty = Tunit | Arr`, `Tm = Tvar | Lam(A, b) | App | Tstar`. Typing is an
inductive family over a context (`Has` for variables, `Typing`), reduction is full beta (`Step`, also under binders),
`Steps` is its reflexive transitive closure.

Files, each importing the previous one:

- `Lib.taut`: the definitions and the notation (below). `infer` and `Inferred` are made by `mode!` from the rules of
  `Typing` (`std/Mode.taut`): `infer(t, G)` returns a type with its typing derivation and a proof of uniqueness, or a refutation of every typing derivation.
  The answer carries its derivation, so there is no soundness theorem to prove. `lookup` and `Looked` are made the
  same way from `Has`; `ty_dec` (for the type a rule asks to be the same twice) is written by hand.
- `Typing.taut`: weakening and substitution lemmas (`ren_typing`, `subst_typing`), inversion, `preservation`,
  `progress` for closed terms, `type_safety` (a well-typed closed term never gets stuck).
- `Alg.taut`: the algebra of renaming and substitution, up to pointwise equality of the maps (there is no function
  extensionality): `ren_ren`, `ren_subst`, `subst_ren`, `subst_subst` and the two instances used for beta,
  `subst_up_single` and `subst_single_subst`.
- `SN.taut`: strong normalization by a logical relation (`Red`, computed by recursion on the type; the candidate
  conditions `cr` by the same recursion; `red_beta`, the fundamental lemma `fundamental`, then `strong_normalization`).
  `SN` is an accessibility predicate; `sn_induction` is its induction principle, a structural recursion whose call is on `k(u, s)`
  for the function-typed field `k`.
- `Examples.taut`: typing derivations, reductions (Church 2 + 2 = 4), `SN` of a closed term, and Omega, which
  steps to itself and so has no type. `tauto check examples/lambda/Examples.taut` checks all of it.

## Notation

`lc!` is a syntax macro (grammar `lc.par`, which must stay byte-for-byte equal to the `par` block of `Lib.taut`;
the table is `.tauto-syntax/<sha256 of lc.par>.tables`):

- ``lc!(`x: unit |- fun y: unit. x : unit -> unit`)`` is `Typing(Cons(Tunit, Nil), Lam(Tunit, Tvar(Succ(Zero))), Arr(Tunit, Tunit))`.
  Names become indices; the last binding of a context is index 0.
- `$e` embeds a tauto term, context or type; `t[u]` is `subst(t, single(u))`; `t ~> u` is `Step`, `t ~>* u` is `Steps`;
  a bare term is that term.

Two more macros write proofs; the kernel checks what they write:

- `steps!(then(s1, s2, s3))` is an untyped macro (it reads a tauto expression): `StepsStep(s1, StepsStep(s2, ...))`.
- ``reduce!(`t`)`` is a syntax macro that reduces the closed term `t` in normal order and writes the `Steps` proof.
  A wrong normal form in the theorem's statement is rejected by the kernel, not by the macro.
- `by reduce_goal!(): Steps(t, nf) {}` is a step whose tactic reads the term from the goal written
  (`docs/design/macro-steps.md`), so the proof is found from the claim.

A macro's own functions (executable code) and the terms it writes (inside `quote`) spell `List` and `Option` the same way
(`Nil`/`Cons`, `None`/`Some`), and they are one type: the prelude's `enum`, which proofs read as an inductive family. A macro that reads what a call in its argument
makes, such as `lc!(…)`, asks for it with `syn_expand`.
