# Nib's semantics and calculus

How a Nib program runs, as an abstract machine, and the judgments of its
calculus. The rules of the language are in [`nib.md`](nib.md). The Lean typing rules in
`lean/Proto/Nib/Typing.lean` are sound with respect to a small-step version
of it (`lean/Proto/Nib/Safety.lean`, see "Proved" below). An implementation may run
programs any way it likes as long as what can be observed is the same.

## Calculus

The judgments and the strata the model is built from (`lean/Proto/Nib/`,
`lean/Proto/Tags.lean`, `lean/Proto/Effects.lean`, `lean/Proto/Budget.lean`,
`lean/Proto/Choice.lean`, `lean/Proto/Core.lean`). Tauto's kernel, which adds
dependent types and proofs on top, is in [`lean.md`](lean.md).

### Semantic strata

1. **Computations**: `Γ ⊢ c : A ! ε`. A function may have a latent effect row,
   but merely referring to the function as a value does not perform it.
2. **Operations**: each has a declaration identity, an operation signature,
   type args, and an independent outer tag set.
   Equality for row matching is *definitional equivalence*, never subtyping.
3. **Handlers**: deep, multi-shot; the resumed continuation re-enters the
   corresponding handler; arm bodies run outside their handler. Unmatched
   operations forward outward, reconstructing the suspended context.
4. **Divergence**: a potentially diverging computation has `Div`. General
   recursive control (including handler-induced recursion) must not be able
   to evade this marker ("What has `Div`" below). Explicitly declared
   redundant `Div` emits lint; removing it triggers rechecking rather than a
   trust-based cast.
5. **Execution budgets**: symbolic step fuel is **global** across all
   branches. `budget n` converts `Div` to a resumable interruption via
   `Exceeded`, retaining the entire machine state. Repeated replenishment may
   itself diverge. A separate host mechanism may place a wall-clock bound; it
   is not the same theorem as a step-count bound.

### Judgments

```text
Γ ⊢ A type                         type formation
Γ ⊢ c : A ! ε                      computation typing
Γ ⊢ A ≡ B                          type equivalence
Γ ⊢ A <: B                         subtyping
Γ ⊢ ε ≈ δ                          extensional row equality
H ⊢ ⟨c, σ, κ⟩ ↦ ⟨c', σ', κ'⟩          machine transition
```

### Tagged types

Type equivalence satisfies:

```text
Tagged<∅, T> ≡ T
Tagged<S, Tagged<U, T>> ≡ Tagged<S ∪ U, T>
Tagged<{a}, Vector<T, n>> ≢ Vector<Tagged<{a}, T>, n>
```

For subtyping/tag forgetting, `Tagged<S1,T1> <: Tagged<S2,T2>` if
`S2 ⊆ S1` and `T1 <: T2`. This forgetful coercion never changes the
matching identity of an effect. The row and tag equivalence laws
(reflexive, symmetric, transitive; union commutative and idempotent; tag
order does not change an effect) are in `lean/Proto/Effects.lean` and
`lean/Proto/Tags.lean`.

### Handler result

A handler with result arms `R0`, ..., `Rn` has a *non-simplifying union*
`Union(R0, ..., Rn)` modulo associative/commutative/idempotent type
**equivalence**, but **not** subtyping elimination. A continuation `k`
returns this handler-result type.

## Machine

A CEK-style machine: a control (`Eval term env` or `Ret value`), an
environment, and a continuation that is a persistent list of frames.

* Values: integers, booleans, text, unit, closures `⟨ps, body, env⟩`, and
  captured continuations.
* `var x = e` makes a mutable cell; `x := e` writes it. Closures share cells.
* A call evaluates the callee, then the arguments left to right, then runs
  the body with the parameters bound.
* `return` unwinds to the nearest function frame.

## Effects (deep, multi-shot handlers)

`handle { body } with { op(p…), k => arm … ; return v => r }` pushes a
`Handle` frame and evaluates `body`.

* `perform op(vs)` walks the continuation outward, collecting frames, until
  it meets a `Handle` frame that has an arm for `op` whose patterns match
  `vs`. The captured frames, **including that `Handle` frame**, become the
  value of `k`. This is what makes the handler deep: `k(v)` re-enters the
  same handler.
* The arm then runs **outside** the handler (the continuation below the
  `Handle` frame), with the pattern variables and `k` bound.
* `k(v)` pushes a copy of the captured frames onto the *current*
  continuation and returns `v` into them. A continuation is a cloned frame
  list, so it can be resumed any number of times (multi-shot) when the
  operation is declared `resume ω`; otherwise at most once (see
  "Ownership" below). Cells are shared between resumptions.
* When the body returns a value `v`, `return v => r` runs `r`; without a
  `return` arm the handle's value is `v`.
* An effect nobody handles is a run-time error here; the checker is meant to
  rule it out through rows.

## Budget and `Div`

`budget(steps: n) { body }` pushes a `BudgetSteps` frame and counts steps.
When the count since the frame was pushed passes `n`, the body is suspended
and the machine performs `exceeded(info)` **at the budget expression**. The
arm receives `info` and `k : T -> …`:

* `k(v)` continues from the budget expression with `v` as its value; the
  suspended body is dropped.
* `info.more(m)` goes back into the suspended body with `m` more steps, and
  `info.unbounded()` goes back with no limit. Either way the body's value
  then continues from the budget expression, through the handler as `k`
  would, so both have the handle's result type.

What counts as one step is up to the implementation, and two
implementations need not agree; a body that does not stop must reach
`exceeded` for every `n`, and the steps of a nested budget count towards the
budgets around it. A host's limit outside any budget stops the run with
`Interrupted`, which is not an effect.

`Div` is the effect of a computation that may not terminate or keeps a
continuation alive; `budget` removes it from the row and adds `Exceeded(T)`
(`Proto/Nib/Typing.lean`, `Prim.ty`).

### What has `Div`

Besides `while` and `unbounded()`, the checker gives `Div` to every way to
recur. Five rules see them (`Proto/Nib/Div.lean`):

1. **`var`**: every function type in a `var`'s type has `Div` in its row
   (also inside unions, tags, and the fields of a `struct` or `enum`), and the
   type has no type variable. A function kept in a `var` may call what the
   `var` holds; a call of it then performs `Div`.
2. **Definitions**: a definition sees the ones before it as they are; it
   may use itself and the ones after it only as functions with `Div` in
   their rows.
3. **Operations**: the operations are in a well-founded order (Nib's is the
   order of declaration). A function in an operation's parameters or result
   that performs the operation itself or a later one has `Div` in its row.
   `effect Fix: () -> (() -> i64 ! {Fix})` is rejected;
   `() -> (() -> i64 ! {Fix, Div})` is fine.
4. **`struct` and `enum`**: a function in the fields of `D` that takes a `D`
   in a parameter or in an effect of its row has `Div` in its row, also when
   the `D` is inside another type (`Box(D) -> i64`). A `D` in a result is
   fine: `enum Stream { Cons(i64, () -> Stream) }`.
5. **`budget`**: what leaves a budget has `Div` on its functions and no
   type variable: its result, and the parameters of the operations its body
   performs outwards. Each budget counts afresh, so a function made inside
   one that runs another budget, given out and called again, would loop with
   no `Div` in its type.

## Ownership ([`ownership.md`](ownership.md)「実行時の意味論」)

The ownership rules are almost all static; the machine changes in three
places.

* **Drop.** When a block or a function body ends, the names it bound are
  dropped, the last bound first, unless their value was moved out. A value
  of a type defined in Nib has no observable drop; an `extern` type would
  run Rust's `Drop` there.
* **Borrows** are values: `&x` of a duplicable value is the value itself,
  otherwise a reference to the owner's place (a cell or a field), which a
  `&mut` writes through. No new value is made.
* **The dynamic ownership check** (`tauto run --check-ownership`, for
  tests). Every affine or linear value made at run time carries a token,
  and the machine stops when (a) a moved name is used again, (b) a linear
  token disappears without being consumed, (c) a continuation of an
  operation that resumes `ω` is captured while it holds a token, or (d) a
  continuation of an operation that resumes at most once is resumed twice.
  A program the static check accepts never stops so; every `shows` case in
  `cases/` runs both ways and must show the same.

The prelude (`std/prelude/Std.taut`, `Shared.taut`, `Affine.taut`) is loaded
before the program. Its `extern` functions (`Buf`, `Vec`,
`HashMap`, `replace`, …) are the machine's own; calling an
program's `extern` function is the error "extern is not runnable".

## Output

A program's results are observed through an operation the host declares
everywhere, `effect show<A>: (name: Text, value: A) -> ()`. A
`perform show("x", v)` that no handler answers is answered by the host: it
records the name and the value's display and resumes with `()`. What a run
shows is the list of those records, in order.

## Proved (`lean/Proto/Core.lean`, no `sorry`)

A small pure core: functions, `Bool`, `Nat` with `natRec` at a constant
motive, de Bruijn variables, call-by-value small steps. Proved: renaming
and substitution preserve typing, **preservation**, **progress** for closed
terms, and their combination `type_safety`. Preservation and progress do not imply
termination.

## Proved: the core (`lean/Proto/Nib/Safety.lean`, no `sorry`)

The core of `Proto/Nib/Typing.lean` has a small-step semantics that follows
the machine above. A state is a term together with the cells' values.

The core covers:
* functions and calls;
* `if`;
* `var` cells;
* generic functions over type variables and row variables;
* tags (`@a T`, `@a e`);
* `perform`;
* `handle` with and without `return`, and arms with patterns and guards;
* `struct` and `enum`: building a value, reading a field of a `struct`, and
  constructor patterns (nested, also in `match`);
* `match`, with exhaustive arms, also on a union (`Shape | i64` with
  `Circle(r)` and `-1` arms);
* `budget`, with `more` and `unbounded`;
* `+ - * div mod` at a width;
* `Text`, `Decimal` and `Float`: literals, `decimal(x)`, `+ - * /` of
  `Decimal` and of `Float`, joining `Text` with a function, and `Text`
  literal patterns;
* unions and `Never`, into a union (`A <: A | B`) and out of one
  (`A | B <: C` when `A <: C` and `B <: C`);
* functions in place of functions: results covariant, parameters
  contravariant, and a function may perform less than its type allows.

How it runs:
* Evaluation is call by value, left to right.
* A generic function used at types and rows is its body with those types and
  rows put for its variables.
* `@a v` is `v`: a tag does not change the value.
* A `perform` under frames that have no handler for its effect steps, in the
  innermost `handle` that has an arm for it, to trying those arms in order.
  The arm gets `k := (x) => handle { frames[x] } with { same arms }`.
  * The handler is deep, because `k` puts the same handler back around the
    frames.
  * It is multi-shot, because `k` is an ordinary function value.
  * Cells live in the state and are not copied, so resumptions share them.
* An arm's patterns are matched against the operation's values and then `k`
  (`op(p₁, …, pₙ), k`). A name takes any value and binds it, `_` takes any
  value, and a literal (`0`, `true`) takes that value. A constructor pattern
  `C(p₁, …, pₙ)` takes a value built by `C` whose fields the `pᵢ` take.
* A value of a `struct` or `enum` is its constructor with field values;
  `s.f` of a `struct` value is that field.
* An arm whose patterns do not match, or whose guard is `false`, is passed
  over. If no arm takes the operation, it goes on outwards, and its answer
  resumes `k`.
* `match t { p if g => b, … }` on a value of type `A` is a handler of an
  operation `Match(A)` that only `match` performs, on `t`. Its arms are
  `Match(p), _ if g => b`, so they are tried as a handler's are.
* `budget(n, f)` runs `f()` under a counter that every step inside it
  decrements. At `0`, it performs `Exceeded(T)` at the budget expression,
  with the `info` of the suspended body.
* `more(info, m)` runs the body on with `m` steps, and `unbounded(info)` runs
  it on with no limit. Nib's `info.more(m)` and `info.unbounded()` are
  `k(more(info, m))` and `k(unbounded(info))`: the body's value continues
  from the budget expression, through the handler, as the section on budget
  above says.
* Arithmetic that overflows its width, `div` or `mod` by zero, and `/` by
  zero of `Decimal` or `Float`, is a run-time error. Literals are in their
  width's range. `Decimal` arithmetic is exact.

Proved:
* **Preservation** (`preservation`): a step keeps the type and the row, and
  the cells keep their types (cells may be added).
* **Progress** (`progress`): a closed well-typed term is one of these:
  * a value;
  * a term that steps;
  * a term waiting on a `perform` of an effect **in its row** that no
    handler around it answers;
  * a term that fails at run time (overflow, or `div`/`mod` by zero).
* `type_safety` combines the two over any number of steps from no cells. A
  closed term with the empty row therefore never waits on an effect.
* **Exhaustive arms.** A handler takes an effect out of its row when its arms
  without a guard take every value the operation may get (`Covers`); with a
  guard or a pattern that may not match, the effect stays. A `match` has no
  `Match(A)` in its row exactly when its arms without a guard take every
  value of type `A` (`HasType.mtch`, `HasType.mtch_exhaustive`). So a closed
  program whose row is empty never runs a `match` that takes no arm.
* **Functions** fit a function type when their result fits its result, its
  parameters fit theirs, and their row is in its row. A call of a function
  value given at a wider type still has arguments its body accepts (`Chain.fn`,
  `Value.fn_inv`), and what a `fn` value does is in the row its type says.
* **Unions**: a value's type is read through the cases of the type it is
  given (`Atom`, `Fits.atom`): each case it starts from is below a case of
  the type it ends at, with no more tags. So the exit from a union keeps
  canonical forms (`Chain.eq`, `Chain.fn`), and a constructor pattern on a
  union binds its fields at the right types (`Owns.value`).
* **Tags** are forgotten, never added: a variable has no tag that its type
  does not have (`HasType.var_tags`).
* **Budget** (`budget_bounded`): `run n` takes at most `n + 1` steps of its
  own before it gives its body's value or performs `Exceeded(T)`. A body
  waiting on an effect handled outside does not step meanwhile, and keeps its
  count when resumed.

The proof rests on three assumptions about the declarations:
* `Builtins`: `Div` is never performed, `Exceeded(T)` takes the `info` and
  answers a `T`, and `Match(A)` takes an `A`.
* `SigOk`: a row variable is not an operation, and an effect's signature
  respects the types and rows put for its variables.
* `DefsOk`: generic functions have their declared types.

`Proto/Nib/Examples.lean` has a declaration with two effects, two generic
functions, a `struct Point` and an `enum Option<T>` that meets all three (`askSig_builtins`, `askSig_sigOk`,
`askSig_defsOk`), so the theorems are not about an empty set of programs.
It also meets the rules for `Div` (`askSig_divOk`).

The `var` and `budget` rules for `Div` (rules 1 and 5 above) are part of
the typing, and the proof covers them: a type with no type variable stays
such when variables are filled in (`DivClosed.inst`, `BudgetOk.inst`).

The typing rules gained what preservation needs:
* injection into a union and forgetting a tag (`fits`, the `A <: A | B` and
  `@a T <: T` of [`nib.md`](nib.md)), and `Never <: A`;
* a value may be given a tag (`tagged`), because `@a v` steps to `v`;
* a guarded arm, or one whose patterns may not match, does not take its
  effect out of the handle's row;
* run-time forms for a budget under way (`run`), its `info`, a cell (`loc`),
  and the arms being tried (`select`).

Places where the model is looser than Nib:
* `Exceeded(T)` also records the row of the suspended body, so that `more`
  can be typed.
* A cell is a value of type `cell(A)`, which Nib does not let programs name.
  `var` carries its type (`Tm.cell A t`), and the cells' values are stored
  with their types, so the types of the cells are read off the state.
* A value, such as a literal, may be given a tag (`tagged`); Nib's checker
  never adds one. A variable still cannot gain a tag (`HasType.var_tags`).
* A literal pattern is allowed at any type that holds its value, also under
  a tag.
* A constructor pattern of `d` is allowed at a type that holds `d` at one
  type argument list and has no type variable among its cases (`Owns`), so
  that it stays right when the variables are filled in. `Some(x)` on
  `Option(i64) | Option(Bool)` or on `Option(i64) | T` is rejected.
* Reading a field is only modeled for a `struct` (one constructor).
* `Decimal` is any exact rational: Nib does not say what `1 / 3` is (the
  representation of `Decimal` is open, [`ownership.md`](ownership.md)「未決定」).

And stricter: a `var` whose type has a type variable is rejected (rule 1 of
"What has `Div`"), since the variable could be a function type without
`Div`.

The model is therefore more permissive than Nib in the places listed above
and stricter in this one, and it is safe in all of them.

## Proved: a row without `Div` stops (`lean/Proto/Nib/Halt.lean`, no `sorry`)

Without the rules of "What has `Div`", five loops are typed without `Div`
(`Proto/Nib/Examples.lean`, at the end):
* a function kept in a `var` that calls what the `var` holds;
* a definition that calls itself;
* an effect whose operation answers a function that performs it again
  (`effect Fix: () -> (() -> i64 ! {Fix})`), resumed by its arm;
* an `enum` holding functions on itself (`enum D { D(D -> i64) }`),
  applied to itself;
* a function made in a budget and given out of it, that runs a budget again.

Each is rejected by its rule: the `var` rule rejects the `var` at
`() -> i64` (and at `() -> i64 ! {Div}` the program's row has `Div`), the
`budget` rule rejects a budget whose result or an operation outwards is
`() -> i64`, and the declarations of the other three break rules 2, 3 and 4
(`loopSig_not_defsOrdered`, `loopSig_not_effOk`, `loopSig_not_dataOk`).

`halts`: a closed program whose row has no `Div` reaches a value, an
operation of its row that no handler answers, or a run-time failure. It
covers the whole core above: functions, deep multi-shot handlers with
patterns and guards, `match`, `struct`/`enum`, generic definitions (rule 2
is used and proved there), tags and unions, `var`, and `budget` with `more`
and `unbounded`.
* The relation is over worlds (the types of the cells allocated so far). A
  value that `Sem` accepts is well typed (`Sem.wt`), and a well-typed value
  whose type has `Div` on its functions and no type variable is accepted
  (`HasType.sem_closed`). A good store is a well-typed one (`StoreSem`), so
  the store does not refer back to `Sem`.
* A budget runs its body by type safety, not by `Sem`: inside it every
  step keeps the type, and each `perform` that leaves it is answered with a
  value of a type with `Div` on its functions (rule 5), which `Sem` accepts.
  The count is the number of `perform`s left in the body (`run_sem`); its
  result is accepted the same way. The `Exceeded` handler is ordinary code
  of the program, and stops when its row has no `Div`.

It assumes a `Good` interpretation of the operations and types: what each
operation takes and answers, and what a value of each `struct`/`enum`
holds, read so that the function types in them run as they say. `loopSig`
has none (the proof would otherwise show its loops stop).
`Proto/Nib/Good.lean` builds one from levels (`Strat.good`): what each part
uses the same way is at its level or below, and what it uses the other way
(under a function's parameter, or what an operation answers) strictly
below; each level is a least fixed point over the ones below. Rules 3 and 4
give the levels for finitely many `struct`s and `enum`s, with type
variables too (`Proto/Nib/Unfold.lean`, `Strat.of_rules`, so
`halts_of_rules`). A chain of uses is followed by a machine whose state is
a type and a stack of the type arguments of the `struct`s it is in: it goes
into a declared field with the type arguments on top, and back to one at a
type variable. Rule 3 bounds its jumps to operations; if it comes back to
one height infinitely often, the type shrinks each time; if its height
rises for good, the last visit of each height goes into a field, so some
`struct` `G` is gone into at two heights with a parameter of a function
without `Div` between, and over `G`'s type variables that is a function in
`G`'s fields taking a `G`, which rule 4 rejects. So a chain of uses with
infinitely many the other way does not exist, and the level of a part is
how far such chains go below it (compared without ordinals: for
`struct X<T> { h: T -> i64 }` and `struct D<T> { f: T -> i64, g:
D<X<T>> }`, `D<i64>` is above `X<i64>`, `X<X<i64>>`, ...).
`Stream { head: i64, tail: () -> Stream }` (`streamSig_halts`) and
`enum List<T> { Nil, Cons(T, List<T>) }` (`listSig_halts`) are such cases;
`askSig`, with the generic `Option<T>`, has levels by size
(`askSig_halts`).

With `budget_bounded`, a budget's own steps are bounded by its count, and
the `Exceeded` handler's by `halts` when its row has no `Div`.

## Open (metatheory)

Nothing is open for the core of `Proto/Nib/Typing.lean`. What is left is
where the model differs from Nib (above).
