# Nib

Nib is Tauto without dependent types and proofs. Tauto is a conservative
extension: a Nib program means the same as a Tauto program. Nib has no implicit
rules (no numeric widening, overloading, case-insensitive names or catch-all
types), runs only typed programs, and bounds every side effect with effects.

The normative sources are this document with [`semantics.md`](semantics.md),
[`ownership.md`](ownership.md) and [`classes.md`](classes.md), then the Lean
model (`lean/Proto/Nib/`), then `cases/`. The implementation is fixed when it
disagrees.

## Values and types

| Type | Notes |
|---|---|
| `i32`, `i64`, … | fixed width only; overflow is a runtime error |
| `Decimal` | exact decimal |
| `Float`, `Float32` | IEEE 754 ([`float.md`](float.md)); `Float32` has no literals |
| `Bool`, `Unit` (`#()`), `Never` | |
| `Text` | no concat operator; literals `"…"` (with escapes), `'…'` (raw), ``plaintext`…` `` |
| `(A, B) -> R ! ε` | `ε` is the effect row |
| `struct`, `enum` | named fields and constructors |
| `A \| B` | union, associative, commutative, idempotent |
| `A × B` | ordered product ([`syntax.md`](syntax.md)「Products」) |
| `@a T` | tag: distinguishes types without changing values |

Absence is the library `enum Option`. Types are applied like calls
(`Option(i64)`).

**Type functions** with only `Type` parameters and native-type bodies (no
recursion, computation, effects or row variables) are unfolded at type
positions before Nib.

## Ownership

Kinds `copy ⊑ shared ⊑ affine ⊑ linear`, borrows that never outlive their owners, resumption
counts `0`, `<=1` (default), `1`, `ω`, `direct` operations and control-flow
linearity: [`ownership.md`](ownership.md) and
[`rust-backend.md`](rust-backend.md)「`direct` operations」. Type parameters are
bounded by the universe names `Copy`, `Shared`, `Type`, `Linear`. Shared std
(`List`, `Map`) and affine std (`Buf`, `Vec`, `HashMap`) are bridged only by
`Text::of` and `Buf::of`. `extern { fn … }` declares trusted signatures that
`tauto run` cannot call.

## Type relations

- **Equivalence**: equal normal forms. Tags compare as sets and nested tags
  merge; unions compare modulo ACI; products compare in order
  (`A × (B × C) ≡ A × B × C`, but `(A × B) × C` differs, and `A × Unit` is not
  `A`).
- **Subtyping**: equivalence, forgetting tags (never adding), union injection
  and elimination, product projection and reordering by component type,
  functions (contravariant arguments, covariant results, smaller rows), and
  `Never <: A`. Numeric widening is never subtyping.

## Products

Beyond [`syntax.md`](syntax.md)「Products」: `×` binds tighter than `|`, so
unions inside products need braces (`{A | B} × C`). Components evaluate left to
right. Extraction is by subtyping and annotation (`(x: @a T)`); components of
the same type are positional or tagged. A product's kind is the join of its
components'.

## Arithmetic

- Integer `+ - *` and unary `-` perform `overflow` when the result does not fit.
- Integer `/` is a type error: use named functions (`Nat::div`, `Int::tdiv`,
  `Int::fdiv`, …) that perform `divzero`, or `decimal(x)`. `/` divides
  `Decimal` and floats.
- Mixed widths are type errors.
- Broken invariants `perform stop(message)`; expected failures use `Option`,
  `Result` or `fail`. `Secret(A)`: [`secret.md`](secret.md).

## Names

Names are case-sensitive, with no overloading. Declarations are fully qualified
([`rust-backend.md`](rust-backend.md)「Fully qualified names」). Different enums
may share constructor names: patterns resolve by the scrutinee type,
expressions need one owning type from context, and `Type::Ctor`
disambiguates; declaration order never decides.

## Statements and evaluation

`let`, `var`, `:=`, `fn`, `if`, `match`, `while`, `loop`, `return`, and
declarations. `match` is exhaustive ([`syntax.md`](syntax.md)「Patterns」);
guarded arms never count toward exhaustiveness. A `match` goal mentioning local
values is a proof type and an error in Nib.

### Matching a union

A `match` on a union takes its values apart by member type. An arm is a typed
binding `y: T => e` (with an optional `if` guard), a name `y => e` that binds
the whole value, or `_ => e`; constructor and literal patterns do not apply to
a union directly, so `match s { c: Shape => area(c), n: i64 => n }` narrows
first and `area` matches `Circle(r)`. `T` is one member or a braced union of
members (`rest: {Text | Bool}`), and `y` is bound at `T`; through a borrow it
is a borrow of the member, with the member's kind.

An arm tests the value's head, not a tag: each integer width, `Bool`, `Unit`,
`Text`, `Decimal`, `Float`, `Float32`, a data declaration whatever its type
arguments (a product is `Pair`), and function; `@a T` has the head of `T`. A
typed arm is admissible when every member left out of `T` has a head no member
of `T` has and is not a type variable, and no member of `T` is one; the
scrutinee's type has no unsolved types. So `Option(i64) | Option(Text)`,
`i64 × Text | Bool × Text`, two function members, `@a i64 | @b i64` and
`T | i64` in generic code are rejected, and `Option(T) | i64` is not.
Exhaustiveness is per member: `Never` needs no arm, a guarded arm takes
nothing, and the error names the members no arm takes.

Evaluation is call by value, function then arguments left to right. Closures
capture environments; `var`s are cells shared by closures and continuations.
Observable behaviour is the order of effects and state changes; output goes
through the host operation `show`.

## Effects

- `effect ask(q: Text): i64`; `perform ask("a")`. A function performs only
  what its row says. Effect identity is the declaration plus type arguments.
- Generic operations name their instances (`res(Pos)`, `∀ A. res(A)`); a bare
  `{res}` is an error ([`semantics.md`](semantics.md)「Effects indexed by
  type」).
- Function types inside type arguments keep their rows, and type arguments are
  invariant.
- **Groups** `effect Talk { log, stdout }` name sets of effects; they nest
  without cycles and expand before row checking.
- **Bounded row variables** `<!h: Host>` stand for a subset of `Host`.
- Handlers are deep, arms run outside the handler, and a handler's result type
  is the union of its arms'. Possibly non-terminating code has `div`.
- `perform budget(n, () => { body })` turns `div` into `exceeded`; the
  host counts the steps, so the row has `budget` (`perform budget_memory(n, f)`
  counts cells, and the row has `budget_memory`); see
  [`semantics.md`](semantics.md).

## Concurrency

`std/builtin/par.taut` defines tasks and shared state. The VM defines
the meaning; the Rust backend runs a reactor or a thread per task.

### Tasks

```nib
effect spawn<A>(f: () -> A ! {Host}): Task(A) resume 1
struct(linear) Task(A: Type) { … }
fn Task::join<A>(t: Task(A)): A ! {wait}
fn Task::detach<A>(t: Task(A)): Unit
fn par<A, B>(f: …, g: …): (A × B) ! {∀ T. spawn(T), wait}
```

- `Task` is linear: it is joined or detached.
- Task bodies may perform `div` and every standard effect (the group `Host`)
  except `stdin` and `exit`. The host answers them, never a handler around
  `spawn`, because continuations do not cross threads. `spawn`'s row includes
  the body's standard effects, so signatures show what tasks do and permission
  checks count them.
- To use user effects in a task, install the handler inside the body.
  Libraries take a bounded row variable,
  `fn serve<!h: Host>(conn: (c: Conn) -> Unit ! h): Unit ! {∀ T. spawn(T), tcp_accept} ∪ h`,
  so permission checks ask only for what is used. Handler state is per task;
  shared state goes in `Mutex`, `Atomic` or `Ref`.
- A `Task` cannot be held across `div`, so `spawn_all` and `join_all` are
  structurally recursive.

### Task failure

Typed failures are results (`Task(Result(A, E))`). A runtime error or extern
panic in a task ends only that task (in the main flow, the run), is reported at
once (`a task failed: …`) even when detached, re-raises in whoever joins it,
poisons every `Mutex` whose contents the task held, and releases the task's
host resources. Linear values a failed task leaves are reachable only through
`join` and `Mutex`, which both propagate the failure.

### Shared state and waiting

| Type | Operations |
|---|---|
| `Ref(A)` | `new`, `get`, `set` |
| `Mutex(A)` | `lock` (a `MutexGuard` whose drop puts the contents back), `take`, `put`, `claim` |
| `Atomic` | `u64` with `load`, `store`, `fetch_add` (SeqCst) |
| `Semaphore`, `Channel(A)` | Tauto over `Mutex` |
| `Task::poll(t)` | `Finished(v)` or `Running(t)` |

All waiting is one effect, `wait(s: Signal)`, answered only by the host; a
`Signal` is raised once and never lowered, and programs cannot create one. One
effect lets one thread run many tasks, and `sleep` and network waits use it too
([`host-effects.md`](host-effects.md)「Slow answers」). On the VM,
waiting on a signal nobody raises is a `deadlock` error, and a sender
exceeding a channel's capacity cannot wait for its receiver.

A closure capturing a `var` is a borrowing closure, and a continuation whose
body or arms use a `var` is callable only inside its arm, so no `var` cell
reaches another task.

## Not in Nib

- Tauto only: dependent types, universes, `Prop`, `theorem`, `axiom`,
  `inductive`, totality.
- Nowhere: numeric widening, overloading, catch-all types, `=`/`<>`
  comparisons, `<…>` type application, `[ ]` indexing, `for`, variadics,
  default arguments, `try`.

## Conformance

`cases/` compares acceptance, types, rows, usage, `show` sequences (also
under dynamic ownership checks), drop sequences and runtime errors. Budget
exhaustion points are not compared.
