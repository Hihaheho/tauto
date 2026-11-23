# Proof steps (tactics)

A proof is written as **steps stating the goal before and the goals after**.
Tactics are untrusted macros; the terms they build are checked, with the
written goals, by both kernels. No kernel rule is added. Implementation:
`crates/tauto-macro/src/macros/expand/step.rs`, `std/rewrite.taut`,
`std/tactic.taut`; cases: `cases/check/steps.eure`.

## Syntax

```
by TACTIC!(arg): goal_before {
  x: A, h: P ⊢ goal_1 from proof_1
  ⊢ goal_2 from proof_2
}
```

- Allowed wherever a term is, in kernel-checked declarations (`theorem`,
  `def`, kernel `fn`); not in `mutual` or executed code (`step.fragment`).
- `by` is a keyword only before `name!(`. The argument is one unchecked
  expression (`t!(())` when there is none; the tactic may `elab_check` it).
- Arms are `Δ ⊢ G from p` (`⊢` always written), in the tactic's order, without
  labels; `{}` when nothing remains. Proofs are any terms, including holes,
  steps and annotated `let`s.
- `: goal_before` is required (`step.before`), except when the step is itself
  an arm's proof, where it must be omitted. So every goal is written exactly
  once.
- Goals are compared by conversion, so a computed, more readable form may be
  written:

```
Succ(k) => by rewrite!(Nat::add_comm(a, k)): Succ(Nat::add(a, k)) = Nat::add(Succ(k), a) {
  ⊢ Succ(Nat::add(k, a)) = Nat::add(Succ(k), a) from by rewrite!(Nat::add_succ_left(k, a)) {
    ⊢ Succ(Nat::add(k, a)) = Succ(Nat::add(k, a)) from Refl
  }
}
```

`match` arm goals and `calc!` are in [`syntax.md`](syntax.md).

## Defining tactics

A tactic is a function whose input type is `ProofStep`, registered with
`macro`; there is no tactic language. From `std/builtin/macro.taut`:

```
struct ProofStep { before: Judgement, arg: SynExpr, after: List(StepGoal), span: SynSpan }
struct StepGoal { binders: List(Judgement::Binder), ty: Judgement }
ExHole(Text, SynSpan)                         // ?name
fn syn_hole(k: u64, at: SynSpan): SynExpr     // ?armK
```

- `before` is the goal in the position's context; `after` the written arms,
  whose binders are atoms usable with `BAtom`. `after` is `Nil` for an armless
  step (e.g. from `tauto expand --by`), where the tactic uses its default
  (all occurrences for `rewrite!`).
- The tactic returns a `SynExpr` containing exactly the holes
  `?arm1 … ?armN`. Helpers `syn_same`, `syn_replace`, `syn_abstract`,
  `syn_diff`, `syn_app_parts` are in `macro.taut`.
- `ProofStep` macros are called only via `by`, and only they can be
  (`macro.argument` / `step.tactic`). Combinators are ordinary functions.

## Expansion and checking (`step.rs`)

Per declaration, steps from the outside in:

1. Check the declaration with the step as a hole to get its context and goal
   (`HoleGoal`, as `tauto goals`). A step appearing as a remaining hole of the
   previous step's check reuses it, so k steps cost about k + 1 checks.
2. Compare `G0` with that goal (`step.before_mismatch`).
3. Run the tactic; the holes must be exactly `?arm1 … ?armN` (`step.holes`).
4. Check `the(G0, S)` in place to get each hole's goal and context. Added
   variables must match `Δ` by name and, by conversion, type
   (`step.context_mismatch`); goals are compared by conversion
   (`step.goal_mismatch`, showing the tactic's goal); an ill-typed term is
   `step.output_ill_typed`.
5. Place `the(G0, S[?armK := the(Gk, pk)])` (no `the` around a step arm).

Comparisons are the kernel checking
`step'check(Γ…, step'v: found): written { step'v }` (`'` cannot be written by
users). After an error, all steps of the declaration become holes `?step`,
`?step'2`, … so later diagnostics don't overlap.

| Guarantee | Checked by |
|---|---|
| the theorem is true | both kernels; the expanded term is like a hand-written one |
| the written goal before is the goal | step 2 and `the(G0, …)` |
| the written goals after are the goals | step 4 and `the(Gk, pk)` |
| the written contexts are right | step 4 (soundness does not depend on it) |
| the tactic is correct | never needed |

`tauto macro expand` shows expansions (record kind `step`).

## Steps in macro output

Output may contain `ExStep(tactic, arg, before, arms, span)` with
`SynStepArm { binders: List(SynBinder), goal: SynExpr, body: SynExpr }`
(`quote { by t!(e): G0 { … } }` builds one). They are expanded exactly like
written steps.

- Steps inside a typed macro's argument are expanded first, in place, and the
  expanded argument is the macro's input.
- The tactic is looked up by name: the file calling the producing macro must
  import it (`macro.unknown`), and that import counts as used. The tactic's own
  names resolve in its file.
- `before` cannot be omitted except for arm proofs. Tactic output may not
  contain steps (`step.nested`); arm proofs in macro output may.
- In position-macro output, if a position macro call remains in the
  declaration, steps expand first with that place left as a hole.
- A tactic call inside an unexpanded macro's argument is left for that macro
  (e.g. `$t!(e)` in `proof!`); elsewhere it is `macro.argument`.
- The `step-tactic` lint also covers steps stated by syntax literals.

## Tools

- `tauto goals`, `try`, `fill` work on holes inside arms as elsewhere.
- `tauto expand FILE --hole h --by 'rewrite!(e)'` turns a hole into a step:
  run armless, read the arms from `step.arms`, write them with `?h_1 …`
  (`assist::expand_step`), omitting `: G0` for arm proofs.
- Goal and context mismatches carry a `fix` rewriting the arm head to what the
  tactic produced (kept names when the count matches), returned by
  `tauto check --json` and as LSP quickfixes.
- `tauto lint` `step-tactic`: `std/` and `meta/` may only use `rewrite!`,
  `nat_norm!`, `nat_le!`, `int_norm!`.
- `tauto macro expand --write` writes steps back as terms.

## Standard tactics

Only tactics that do what terms cannot say briefly. Tactics mirroring term
syntax (`intro!`, `exact!`, `apply!`, `cases!`, `induction!`) would be a second
way to write the same thing; tactics searching all lemmas would make proofs
change when lemmas are added. Neither is in std.

**`rewrite!(e)`** with `e: Eq(A, l, r)`: goal before `M(l)`, arm goal `M(r)`,
term `Eq::subst(z => M(z), Eq::sym(e), ?arm1)`. The motive is never inferred:
it is fixed by the difference of the two written goals. `l` and `r` come from
`e`'s type, or, if unreadable (an induction hypothesis's recursive call) or
spelled differently, from the smallest differing part of the goals. The arm
decides which occurrences change (all, without an arm). Goals differing
beyond one equation are rejected.

**`nat_norm!(())`**: reflection for `Eq(Nat, l, r)`. Both sides are read as
`NatExpr` (`NeConst`, `NeVar`, `NeAdd`, `NeMul`) over `Nat::add`, `Nat::mul`,
`Succ`, `Zero` and numerals, other subterms becoming variables (equal by
`syn_same`); term `Nat::norm_eq(vars, l', r', Refl)` (`std/nat_norm.taut`).
Only `Nat::norm_eq` is trusted; `ne_norm` (sorted sum of sorted monomials) is
proved sound (`ne_norm_sound`), so a misreading only fails to check, and
differing normal forms are shown by `step.output_ill_typed`. No arms. Numerals
expand to sums, so it is poor for large numbers.

**`nat_le!(())`**: the same reading for `l <= r = true`, `l < r = true`
(`l < r` as `Succ(l) <= r`; also `Nat::le`, `Nat::lt`, not `Eq(Bool, …)`);
term `Nat::norm_le(vars, l', r', Refl)`, which checks iff
`Np::le_chk(Ne::norm(l'), Ne::norm(r')) = true`: every monomial of the left has
one on the right with no smaller coefficient (`Np::le_chk_sound`). Incomplete:
no hypotheses, subtraction or monomial-vs-monomial comparisons. No arms.

**`int_norm!(())`**: like `nat_norm!` for `Eq(Int, l, r)` over `Int::add`,
`Int::sub`, `Int::mul`, `Int::neg` and `int_of_nat` numerals; trusts only
`Int::norm_eq`. No arms.

The Lean formalization has nothing for tactics: no kernel rule is added, so
there is nothing to prove about them.
