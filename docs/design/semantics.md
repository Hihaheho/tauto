# Nib's semantics

How a Nib program runs, as an abstract machine. The language rules are in
[`nib.md`](nib.md); the kernel built on top is in [`lean.md`](lean.md). Any
implementation may run programs differently as long as what can be observed is
the same. The Lean typing rules (`lean/Proto/Nib/Typing.lean`) are sound with
respect to a small-step version of this machine ([Proved](#proved)).

## Calculus

- **Computations** `Γ ⊢ c : A ! ε`: referring to a function does not perform
  its latent row.
- **Operations** have a declaration identity, type arguments and a tag set;
  rows match operations by definitional equivalence, never subtyping.
- **Handlers** are deep and multi-shot, and arms run outside their handler.
- **Divergence** is the effect `div`, which no form of recursion can evade
  ([What has `div`](#what-has-div)).
- **Budgets** count global step fuel across all branches and turn `div` into a
  resumable `exceeded`.

Tags satisfy `Tagged<∅, T> ≡ T` and `Tagged<S, Tagged<U, T>> ≡ Tagged<S ∪ U, T>`,
and do not distribute into type arguments. `Tagged<S1, T1> <: Tagged<S2, T2>`
when `S2 ⊆ S1` and `T1 <: T2`; forgetting tags never changes an effect's
identity. A handler's result type is the union of its arms' results, modulo
associativity, commutativity and idempotence, without subtyping elimination.

## Machine

A CEK machine: a control, an environment, and a continuation that is a
persistent list of frames. `var x := e` binds a local that later statements
and borrowed closures may reassign. Calls
evaluate the callee, then arguments left to right. `return` unwinds to the
nearest function frame.

## Effects (deep, multi-shot handlers)

- `perform op(vs)` walks outward to the first `Handle` frame with an arm whose
  patterns match. The frames up to and including that `Handle` become `k`, so
  `k(v)` re-enters the same handler (deep).
- The arm runs outside the handler, with its pattern variables and `k`.
- `k(v)` pushes a copy of the captured frames onto the current continuation,
  so it can be resumed many times when the operation is `resume ω`.
- `return v => r` runs on the body's value; without it the value is `v`.
- An unhandled effect is a run-time error that rows rule out.

### Effects indexed by type

A row or arm writes which instance of a generic operation it means:
`res(Pos)` and `res<Pos>()` name one instance; `∀ A. res(A)` and
`∀ A. res<A>()` name all of them, the arm treating `A` as a type equal to no
other. When any row writes an instance with type arguments, or an arm answers
one, each instance is a separate effect, and a handler of `res(Pos)` never sees
a `perform` of `res(Vel)`.

Before the other checks, once types are known, each such `perform`, arm and
row is renamed after its type arguments (`res@Pos`) and functions whose generic
is an index are copied per type. The instance at a `perform` or call comes from
what its types fix, else from the instance of the same effect in the
surrounding row, else from what the arguments perform. Only instances the
program writes are used; two candidates are an error asking for the type to be
written. Rows may index effects too (`effect cur<!e>()`), instantiated by
unification ([`row-parameters.md`](row-parameters.md)). After renaming, rows,
types, the machine and every backend see ordinary named effects.

### Variables across resumptions

Every implementation must agree on this. A continuation captures frames and
environments, and a `var` is a value of its environment: each resumption of a
copy of `k` starts from the value the `var` had when `k` was captured, and a
write in one resumption is not seen by another. A body whose operation may
resume more than once cannot use a `var` declared outside its `handle`: the
copies of `k` would each have their own value of it, and none would reach the
code after the `handle`. Sharing a state between resumptions is written with
an effect handled outside. `each-resumption-copies-a-var-made-in-the-body` in
`cases/eval/m_tier.eure` checks every backend.

## Budget and `div`

`perform budget(n, f)` runs the function `f` of no parameter and counts
its steps (`n: u64`); `f` is usually written in place, `() => { body }`. It is
an ordinary `perform` of an operation the host declares, so the arguments are
positional, as every call's are. When
the count passes `n`, the body is suspended and `exceeded(info)` is performed
at the budget expression:

- `k(v)` continues from the budget expression with `v`, dropping the body;
- `info.more(m)` resumes the body with `m` more steps, `info.unbounded()`
  without a limit; the body's value then continues as `k` would.

A step is a call of a function whose row has `div` or a round of a `while`
loop, the places where a run may go on without end; every implementation
counts the same steps, so the same `n` gives the same answer. A step of a call
is charged after the call's arguments are evaluated and before the callee runs
(`tick budget` in NIR marks the call; the order is the same on every backend), so
a budget that runs out at a call leaves the effects of its arguments in place
and does not run the callee. A body that
does not stop reaches `exceeded` for every `n`. Steps of a nested budget count
towards the budgets around it. Each budget keeps its own count; when one step
exhausts several, the innermost performs `exceeded` first, and `more` gives
steps only to it. A host limit outside any budget stops the run with
`Interrupted`, which is not an effect (lifted by `--allow-div`). The host limit
counts calls and loop rounds on every backend, so the same limit stops the same
programs.

`budget` removes `div` from the body's row and adds `exceeded` and `budget`.
What else the body performs is performed where the budget is written, so the
handlers around the budget answer it.

### The effect `budget`

`budget` is an operation of the host: the host counts. Where a body stops is
part of what a program does, and it rests on the host that runs it (cells are
not the same on every implementation, and a host may hold a stack or a count
only for a program that runs a budget), so running a budget is an effect and
the row says so: a function that runs a budget has `budget` in its row, and so
do its callers. A row names it as it names any operation, in lower case, and
so with `exceeded`. Like `div` and `exceeded`, `budget` is declared by the
language rather than by a source file, since its type depends on the body's
row; it is listed with what the host answers in `effect Host`
(`std/builtin/par.taut`). No `handle` has an arm for it, as none has one for
`wait`: an arm for `budget` is an error, and the host answers it at the top
level, in a task and in a macro without a permission. A function without
`budget` in its row runs no budget, whatever it calls.

`budget` resumes exactly once and does not suspend its caller: what stops a
body is `exceeded`, which the row shows apart.

`budget` is a word of the grammar only right before a number, in a
declaration's kernel budget (`fn f(): T budget 100_000 { … }`); anywhere else
it is a name.

### Memory budgets

`perform budget_memory(n, f)` counts allocated cells cumulatively instead of steps (a
value and each of its fields, text per 8 bytes, `Vec` elements, `HashMap`
entries). Cells are not bytes and may differ between implementations, but
unbounded allocation must reach `exceeded` for every `n`. Backends count values
made under the budget tier, not by functions without `div` or by externs. A
memory budget does not remove `div`, since a body may loop without allocating.
It is the host's operation `budget_memory`, and the row of a function that runs
one has `budget_memory`. Both limits are two budgets, one in the body of the
other: `perform budget(a, () => perform budget_memory(b, f))`.

### What has `div`

Besides `while` and `unbounded()`, every way to recur gets `div`
(`Proto/Nib/Div.lean`):

1. **`var`**: every function type in a `var`'s type has `div`, and the type
   has no type variable, since a stored function may call the `var` again.
2. **Definitions** see earlier definitions as they are, and themselves and
   later ones only as functions with `div`.
3. **Operations** are ordered by declaration; a function in an operation's
   signature that performs it or a later one has `div`.
4. **Data**: a function in `D`'s fields that takes a `D` (also nested, or in
   its row) has `div`; a `D` in a result is fine
   (`enum Stream { Cons(i64, () -> Stream) }`).
5. **`budget`**: functions leaving a budget (its result, and parameters of
   operations it performs outwards) have `div` and no type variable, since each
   budget counts afresh.

### Finite iteration

`FiniteStep(I, S, n)` either ends a traversal or yields an item and a new
state with a rank strictly below `n`. `Iterator(A, I, S)` prepares the initial
rank and state from an owned source and supplies a step for a given rank and
state. `SharedIterator(A, I, S)` takes the source by shared borrow. Its step
returns the successor state by value and lends the item from the source.
`ExclusiveStep(I, S, n)` is the exclusive counterpart of `FiniteStep`: it yields
a mutable item from the source with a rank strictly below `n`. Extraction keeps
the `&mut` place. `ExclusiveIterator(A, I, S)` takes the source by exclusive
borrow and steps with `ExclusiveStep`. A live item freezes the source under the
ordinary borrow rules, so the next acquire waits until the item is dropped.

The finite folds in `std::finite_iteration` recur by the rank, preserving
their callback row. A break returns its value without acquiring another
item. The decrease proof is checked before extraction and erased at runtime.

`for pat in e { B }` is a surface form for an owned `Iterator` traversal. Where
the program is read it becomes `iterator_ready(e)` and `for_ready` (which calls
`fold_finite`) with a step that binds `pat` and turns `break` / `continue` into
`IterationControl`. A file with a `for` reads `std::iterator` and
`std::finite_iteration` as if it had imported them, so the author writes no
import for the expansion. `std::iterator` implements `Iterator` for a `List`
itself, and the standard library owns the types of its prelude for the
inference rule of an instance. The loop itself does not add `div`. Shared and exclusive
`for` and conversion into an iterator are separate forms.

## Ownership ([`ownership.md`](ownership.md)「Runtime semantics」)

Names bound by a block drop in reverse at its end unless moved; only extern
types observe it. Borrows are values: the value itself when duplicable,
otherwise a reference to the owner's place. `tauto run --check-ownership` stops
when a moved name is reused, a linear value is lost, an `ω` continuation is
captured holding an owned value, or a one-shot continuation is resumed twice.
Programs the static check accepts never stop so. The check runs on niri, which
interprets NIR and counts a token for every owned value; the machine runs the
same NIR, which restates `lin.rs`'s decisions. A program's own externs are not
runnable on niri.

## Output

`show` is a function over the class `Debug` ([`debug.md`](debug.md)); `show(&v)`
writes the text of `v` to `stdout`. Standard effects (`std/builtin/os.taut`)
are answered by the host within the run's permissions
([`host-effects.md`](host-effects.md)).

## Proved

All in `lean/Proto/Nib/`, without `sorry`.

**Type safety** (`Safety.lean`). The model covers functions, `if`, `var` (a `scope` term holding its place),
type and row generics, tags, `perform` and `handle` with patterns and guards,
`struct`/`enum`, `match` (on a union by typed arms, which test the head of the
value), `budget` with `more` and
`unbounded`, width arithmetic, `Text`/`Decimal`/`Float`, unions, `Never` and
function subtyping. `match` is a handler of an internal operation `Match(A)`,
and `k` is `(x) => handle { frames[x] } with { same arms }`.

- `preservation`: a step keeps the type and row.
- `progress`: a closed well-typed term is a value, steps, or waits on an
  effect in its row. An operator without a result steps to performing
  `overflow` or `divzero`, which never answer, so nothing fails at run time.
- So a closed term with the empty row never waits on an effect, and with
  exhaustive arms never runs a `match` without a matching arm.
- `budget_bounded`: a budget takes at most `n + 1` steps of its own before
  returning or performing `exceeded`.

The proof assumes well-behaved built-ins, operation signatures and generic
definitions; `Examples.lean` exhibits declarations meeting them. The model is
looser than Nib in places that are safe (the model's `Exceeded` records the body's row,
literals may be tagged, `Decimal` is any
exact rational, `budget` is a built-in function of the steps and the body that
counts as the machine above does, so its row has no `budget`: a row of Nib is
the model's row with `budget` added) and stricter in one (a `var` whose type has a type variable).

**Termination** (`Halt.lean`): a closed program whose row has no `div` reaches
a value, an unanswered operation of its row, or a run-time failure. Without
rules 2 to 5 above, four loops typecheck without `div`, each rejected by one
rule (`Examples.lean`). The proof uses a logical relation over worlds that give
the types of the places around a term and assumes a `Good` interpretation, which `Good.lean` and
`Unfold.lean` build from levels whenever rules 3 and 4 hold.

Nothing is open for the core beyond the listed differences from Nib.
