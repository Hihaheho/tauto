# Ownership, borrowing and resumption

Value kinds, borrows that never outlive their owners, effect resumption counts, and their Lean
proofs. These rules live in `types.rs`, `rows.rs` and `lin.rs`; the kernel is
unchanged, and occurrences in types, propositions and proofs are not uses.

## Kinds

Every type has a kind `copy ⊑ shared ⊑ affine ⊑ linear`, derived from its
structure. A declaration may tighten it (`struct(affine) File`), never loosen
it.

| Kind | Duplicate | Drop | Run time |
|---|---|---|---|
| `copy` | yes | yes | bit copy |
| `shared` | yes | yes | reference count, updated in place when unique |
| `affine` | no | yes | move; dropped at block end |
| `linear` | no | no | move; must be consumed exactly once |

Copy and shared ("duplicable") type identically.

### Kinds of types

```text
kind(machine integers, Bool, Float, Decimal, (), Never) = copy
kind(Text) = shared
kind(A | B), kind(D(T…)) = join of the parts; recursive data is at least shared
kind(function type) = written kind, else shared
kind(&rc T) = shared
kind(Info(T)) = affine
kind(type variable) = its bound, default affine (<A: Shared>, <A: Linear>)
```

Callers check that actual kinds fit bounds. A closure's kind is the join of its
captures. Functions with no shared types in their signature or locals do no
reference counting.

## Use

`lin.rs` runs after type checking. Duplicable bindings are unrestricted;
affine ones move at most once per path and are otherwise dropped at block end;
linear ones move exactly once per path, including `return` and `break`. Uses
are counted per path, and a binding used after a branch must be unused on every
path.

- Moves: arguments, bindings, field stores, `:=` right sides, returns, `match`
  scrutinees, captures, effect arguments.
- Not moves: `&x`, `&mut x`, reading a duplicable field, `==` operands
  ([`classes.md`](classes.md)「`==` and `!=`」), type and proof occurrences.

### `let` and `var`

`let x := e` owns the value. `var x := e` is a cell. A cell of duplicable
contents is shared by closures and continuations. Affine contents are dropped
by `x := v` and moved out only outside closures; closures may only borrow and
assign them. Linear contents are forbidden in a `var`. A loop's condition and
body may move an affine or linear binding declared outside the loop only if
every path assigns it again before the body ends (`xs := Cons(v, xs)`): what
the loop found usable is usable when it repeats.

### `let(stack)`

`let(stack) x := e` puts `x` in the function's frame, without allocation or
reference counting. The type must be sized and non-recursive, `var(stack)` is
an error, and NIR checks independently that the binding is not indirect
([`rust-backend.md`](rust-backend.md)「NIR」). Being on the machine stack is
not promised.

### Fields and `match`

- `s.f` copies duplicable fields. An affine field moves out of an owned `s`
  (a partial move): `s` can no longer be used whole, a field cannot be taken
  twice, and the untaken fields drop with `s`. Nothing moves out of borrows.
- `struct(linear)` values (protocols beyond their fields) cannot be projected;
  destructure them fully. Leftover linear fields are errors.
- `match` on an owned affine or linear value consumes it; write `other => other`
  rather than `_ => e` to keep it. Patterns that ignore linear fields are
  errors. Borrowed scrutinees bind borrowed pattern variables.

### Coercing structs (`coerce`)

A struct built only through functions but used as its contents (sorted
sequences, validated text, placed values) marks one field `coerce`:

```nib
struct Checked { coerce value: Text, length: u64 }
```

| Level | Allows |
|---|---|
| `coerce` | `&W` as `&T`; `w.x` reads inner fields |
| `coerce(mut)` | also `&mut W` as `&mut T` and `w.x := e` |
| `coerce(owned)` | also `W` as `T` |

`T` never becomes `W`; only `W { … }` builds one. `w.x` always names the inner
field; the struct's own fields are `w.W::f`. Coercions never apply at type
variable positions, and after checking they are written out as field paths, so
borrow checking and the kernel see projections.

### Drop order

Unmoved affine bindings drop at block end in reverse declaration order;
temporaries borrowed by a call drop at statement end; `return`, `break` and
`continue` drop live affine bindings. Drop is structural for Tauto types and
Rust `Drop` for extern types, and performs no effects.

## Functions and closures

### Arguments

`x: A` moves, `x: &A` borrows (for duplicable `A` it is used as the value:
「`&A` of a duplicable `A`」), and `x: &mut A` needs a `var`, a field path of
one, or a `&mut` argument. Arguments evaluate left to right.

### Results

`-> &A` needs a borrowed argument and derives from all of them; the body
returns a borrowed argument, a field path of one, or another such call. Only
named functions return bare borrows; closures may return borrow-carrying values
that borrow from all borrowed arguments and captured owners. `-> &mut A`:
[`rust-backend.md`](rust-backend.md)「`-> &mut A` and `let x`」.

### Generics

`<A>` is affine by default. `<!e>` allows any resumption count; `<!e: <=1>`
excludes `ω`.

### Closures

Capturing owned affine or linear variables moves them; `var`s are captured as
cells. Kind decides duplication and call count is separate: an affine closure
that only lends its captures can be called repeatedly and passed as `&f`, while
one that consumes them is callable once. Without a written kind a shared closure
is expected. Kinds are fixed at the definition, so captures whose kind is still
undetermined there are rejected.

### Borrowing closures

A closure capturing borrows or affine `var`s is used like a borrowed variable:
passed to `&f` parameters or called in place. Std higher-order functions take
`&f`. Calling a duplicable function, a borrowing closure or an in-place affine
closure is not a use.

A function lent this way stays a borrow in the callee, whatever kind its type
has (「`&A` of a duplicable `A`」).

## Borrows

### Where borrows appear

`&p` and `&mut p` (`p` a local or field path) appear at borrowed parameters,
as `let` right sides, as `:=` right sides (the assigned holder freezes the
owner like a `let` does), as construction fields (`S { f: &a }`), as `match`
scrutinees, as arguments to generic functions, and as values put into a
container (`Vec::push(&mut v, &a)`). A type argument may hold a borrow
(`Vec(&F)`, `Pair(&F, i64)`, `ident(&a)`) unless its parameter is bounded by
`NoBorrow`; a borrow cannot be an effect argument or a handler's payload, and
an escaping closure cannot capture one. There are no lifetimes; `&mut` comes
only from `var`s.

A value that holds a borrow freezes the owners of what it holds until its last
use, wherever it is stored. It cannot outlive them (「does not live as long
as」), and a function returns one only when its result type says which
arguments it borrows (`borrows(m)`, below).

### Borrow-carrying types

A type carries borrows by structure: `&T`, `&mut T`, structs with such fields,
their `Option`/`Result`/products, and extern `type(borrow)`. Other fields of
such structs must be duplicable. A function without borrowed arguments returns
nothing borrowed, so its body may not return a borrow of its own bindings.
Values holding only `&` of duplicables are used as the values themselves.

### `&A` of a duplicable `A`

`&A` and `A` are different types, and `&A` is always a borrow: stored, it
freezes its owner. Where a duplicable `A` is wanted, a `&A` is copied (for a
type with `struct &A`, by `owned`); where a `&A` is wanted, an `A` is lent for
the call. The copy happens only where a type asks for it, so copying or not
does not change the program.

The copy is allowed because owned data holds no borrow. One duplicable value
may hold one: a *lent function*, the function behind a `&` or `&mut` that is

- a closure that borrows, or a closure written in place that owns an affine
  capture and is dropped when the call returns;
- a parameter whose type holds a `&` of a function type (`cb: &((A) -> B)`,
  `o: Option(&F)`, a struct with such a field): a caller may have lent it
  one of the closures above;
- made from a lent function: `&cb`, `let g := cb`, a pattern variable or a
  field read of a value that holds one, and the result of a call given one
  when the result's type holds a `&` of a function.

A lent function is called, lent on and renamed, and is otherwise a borrowed
variable, so no copy of it is kept. It leaves a function only in a result
whose type holds a `&` of a function, which the caller reads as lent again. It
is given only to a parameter declared with a function type behind `&`: a type
parameter (`x: &A`) stands for values that are kept.

Lending a lent function is an exclusive use, as it may write what it
captured: one call lends it to one argument. A name it was given
(`let g := cb`, `let g := same(cb)`) and a closure written in place that
calls it lend the same function.

Whether a function is lent follows from where its value came from, not from
its type: a `&` of a function read from owned data (`HashMap::get(&m, &k)`)
is the function.

### Borrowed structs (`struct &T`)

A type may define its borrow as another struct, in the same module and over
the same type parameters:

    struct Vec(T) { slots: Slots(T), len: u64 }
    struct &Vec(T) { slots: &Slots(T) }

- Fields of `&T` are duplicable or borrows, or duplicable types whose
  arguments hold shared borrows (`List(Option(&A))`). A `&T` is copied as its
  borrows are, so its kind does not depend on what they borrow. Functions on
  `&T` read its fields; each has one body, and `pub(open)` is allowed.
- `inductive struct &T` is a family of its own to the kernel: `&T(…)` names
  it, `&T { … }` builds it, and a `match` reads it by `&T { f, … }` (or by
  its constructor `Mk`).
  `&orig T` is `T`, and a `T` is lent in a kernel term only by a call written
  out (`Lend::lend`), so the law of `Lend(T)` is a theorem over the two
  families.
- `&mut T` still points at its owner; there is no `struct &mut T`.
- `Slots` has `struct &Slots` too, holding only the lent range (first
  element and count), not the capacity. There is no separate `Slice` type.
  `std/slots_store.taut` writes it as an `inductive struct &Slots` of the
  contents in order (`List(Option(&A))`); the compiler runs it as the host's
  reference to the slots. Its `Lend` instance is for `Copy` elements and for
  a state and a mark that the class `Fresh` gives (`owned` has to make both),
  and the law `lend(&orig owned(y)) = y` is a theorem over the functions the
  instance calls, because `Lend` is a plain `class` and the kernel does not
  read its instances.
- `&T` is implicitly the lent form. `&orig T` (term `&orig x`) is a shared
  reference to the original `T` that does not go through `Lend`: it reads
  `T`'s fields and is read as `T` by the kernel, borrows like `&T`, is made
  from `&mut T`, and becomes `&T` by `lend` (never the other way). Copying it
  copies `T` as is. Without `struct &T`, `&orig T` is `&T`.
- A type with `struct &T` needs an instance of `Lend(T)` (`std`) in the same
  module: `lend(owned: &orig T): &T`, `owned(lent: &T): T` (written for every
  kind, run only for duplicable `T`), and the law `lend(owned(y)) = y`. `&T`
  is a quotient of `T` and may drop information such as capacity.
- The compiler inserts `lend` where a `&T` is expected and a `T` or `&orig T`
  is given, and `owned` where a `T` is expected and a `&T` is given, so
  generic code makes `&T` too. Both are ordinary terms; the kernel is
  unchanged.
- A type without `struct &T` keeps a borrow that points at its owner.

### Counted references (`&rc T`)

`&rc T` is a reference to a `T` in a counted box. It is shared whatever the
kind of `T`: a copy shares the box and raises its count, and the last copy to
drop drops the contents and frees the box, not the end of a block. A struct
with a `&rc T` field gets its kind by the join of its fields as any other, so
`struct Atom { text: &rc Vec(u8) }` is shared.

- `T` is at most affine and holds no borrow: a linear `T` (or a type
  parameter bounded by `Linear`) and a `T` that holds a borrow are errors, and
  a type parameter under `&rc` is bounded by `NoBorrow`. A box is kept and
  returned like any shared value, so nothing in it may need its owner frozen.
- `&rc e` moves the value of `e` into a new box. Where a `&rc T` is written as
  the expected type and a `T` is given, `&rc` is put in, under the same
  condition as lending: the expected type is written and has no unsolved
  type parameter. Making a box is not an effect.
- The contents are only read through a shared borrow: a `&rc T` is read as
  `&orig T` where a `&orig T` or a `&T` is expected (then lent, for a type
  with `struct &T`), and `&b` and `&orig b` of a `b: &rc T` borrow the
  contents. Field reads, calls that take `&T` and `match` go through the same
  borrow: what a pattern binds of it is borrowed. While the borrow is used, `b` is
  borrowed as any duplicable value lent is.
- There is no `&mut` of the contents, nothing moves out of them, and a
  `&rc T` is never given as a `T`. A duplicable `T` is copied out of the borrow
  (`&T → T`).
- The kernel reads `&rc T` as `T` and `&rc e` as `e`, as it reads every `&`;
  a field `&rc T` of an `inductive struct` is a field `T`.
- `==`, `show`, `Debug` and the other operators are those of `T`, through the
  borrow; the box's address is not observed.

### Borrowed variables

`&x: A` parameters, `let x` of borrow-carrying values, and borrowed pattern
variables.

- They may be reborrowed, matched, field-read, have paths borrowed, and be
  passed to `-> &A` functions. A `&mut` one may also be passed as `&mut` and
  written.
- Writing through a borrow is `*x := v` (also `*p.r := v` for a borrow in a
  field); `x := v` rebinds, so on a `&mut` `let` it is an error. `*` appears
  only on the left of `:=`. Reading a borrowed variable yields a reference or a
  value as the expected type requires; with none (unannotated `let`), duplicable
  `T` copies.
- They may not be moved, stored, passed to effects, or captured by escaping
  closures.

### Freezing

`let x := f(&a, &mut b)` with a borrow-carrying result freezes `a` and `b`
while `x` is live: no move, `&mut` or `:=`, and `&` only if not derived from
`&mut b`. Freezing is per field path.

`x` is live at a point when a path from there reads it before a whole write
`x := e` replaces it; `let`, `var` and parameters follow the same rule. Branches
join, a loop is iterated until the sets stay, a closure reads what it captured
wherever its name is read, and a handler's arms and body each read what the
other reads (`k` runs the rest of the body). A field write `x.f := e` and
`&mut x` read `x`. `let y := x` that moves a holder hands its freezes to `y`.
A holder moved anywhere else or captured, and a value whose type
holds an opaque view (`type(affine, borrow)`, whose drop may use the borrow),
stay live to the end of their scope. An owner whose scope ends while a holder
from outside it is still live is "does not live as long as". When values are
dropped does not change.

`borrows(m, …)` after a result type limits what it borrows
(`fn get(m: &HashMap(K, V), k: &K): Option(&V) borrows(m)`); unlisted arguments
are lent only for the call. It is trusted on externs and unsupported on the
Rust backend.

### Parametric `&mut` arguments

A call may put values into the place of a `&mut` argument whose type may
hold a borrow (`Vec::push(&mut v, &a)`), so that place takes in what the
other arguments lend, and, for a borrowed argument, what the places it
borrows hold: the callee may move a value out of them into it.

When the callee is *parametric* the check reads its signature to narrow
this. A callee is parametric when it is a declared function, not a local
or a class method, has no `where`, has no operation in the call's row, and
no parameter whose type may hold a function. If the `&mut` parameter's
declared type holds a borrow only through type parameters (`&mut Vec(A)`,
not `&mut Holder(A)` with a borrow field), then another argument `j` gives

- nothing, when its declared type mentions none of those type parameters;
- what the places it borrows hold, when it is a borrowed parameter that
  mentions one (`b: &mut Vec(A)`);
- what it lends, when it is a value parameter that mentions one (`x: A`).

So `refill(f: &mut Vec(A), b: &mut Vec(A))` may move the values of `b` into
`f`, and `f` then borrows what they borrowed, but `f` never borrows `b`.

Why this is sound: a borrow can enter the place only inside a value of a type
it can hold, which for the place is a value of one of its type parameters
`A`. The body knows nothing of `A`, so it can get a value of type `A` only
from a parameter whose type mentions `A` (a value `x: A`, or one taken out of
a `&mut Vec(A)`), from a function that returns one, or from an instance or a
handler that knows what `A` is. The conditions leave out the last three: no
parameter holds a function (a `k: (&F) -> A` turns any borrow into an `A`),
no `where` (an instance of `Make(A)` may build an `A` holding any borrow it
is given), no operation (a handler is at the caller, where `A` is known), and
no class method (its instance is written at a known type). A borrow of the
place `b` itself is a `&Vec(A)` or `&mut Vec(A)`, never an `A`: `A` would
have to hold itself. The values taken out of `b` borrow what `b` held, which
the caller knows. The rule trusts that an extern's host code keeps to its
declared type, as the rest of the check does.

### Conflicts within one call

Left to right, `&mut p` may not overlap another borrow of an overlapping path,
nor a move a borrow. Split such calls with `let`.

A borrow is read when the callee runs, after all its arguments. An argument
right of `&mut p` may write `p` (`f(&mut w, g(&mut w))`): the callee sees what
it wrote, and the kernel's reading of the call does too (a function with
effects that does this is left out of proofs). An argument right of
`&p` may not write `p`.

### Borrows and effects

- Borrows cannot be effect arguments.
- `&` borrows may live across any effect; `&mut` borrows and affine `var`s not
  across `ω`.
- If a `handle` body or `return` arm borrows outside bindings, its `k` may only
  be called in place in the arm, whatever the resumption count.

## Resumption and control-flow linearity

Effects declare resumption counts; `<=1` is the default and multi-shot is
explicit:

```nib
effect ask(q: Text): i64                 // <=1
effect choose(): Bool resume ω
effect fail(msg: Text): Never resume 0
effect step(): () resume 1
```

Built-ins: `div` is `0`; `exceeded`, `show` and `Match(A)` are `<=1`.

### Arms and `k`

| Count | `k` |
|---|---|
| `0` | absent (writing `k` is an error) |
| `<=1` | affine: at most once |
| `1` | linear: exactly once per path |
| `ω` | duplicable |

Operation arms capture only duplicables, because they run once per `perform`;
thread affine state through returned functions or a `var`. The `return` arm's
free variables count as live across the body.

An arm runs where the body performs its operation, so in the arm the bindings
from outside the `handle` are live as the body left them there: one the body
moved before every call or `perform` that may perform an operation with an arm
is no longer owned. A call whose row has a row variable may perform any of
them.

```nib
fn quiet<A, B, !e>(f: (x: A) -> B ! {log} ∪ e): (x: A) -> B ! e {
  (x: A) => handle { f(x) } with {
    log(s), k => k(#())      // `x` is already `f`'s: `e` may resume ω
  }
}
```

### CFL rules

With `L(t)` the owned bindings live across subexpression `t` (owned during it
and used or dropped after it):

```text
ω ∈ q(ρ(t))         ⟹  L(t) has no affine or linear binding, &mut borrow, or affine var
q(ρ(t)) \ {1} ≠ ∅   ⟹  L(t) has no linear binding
```

This applies to every subexpression, by backward liveness: in
`f(x, perform ask())`, `x` is live across `ask`. Since `div` is `0`, a linear
`resume 1` `k` cannot live across `div` calls; compute first, use fuel, or
declare `<=1`.

### `budget`

Every subexpression of a `budget` body may perform `exceeded` (`<=1`), so no
linear binding lives there, and affine ones drop on exhaustion. `info` is
affine. The body may not borrow outside bindings, because `info` can outlive
them, except when the `budget` is the whole body of a `handle` whose one
`exceeded` arm has no guard and uses neither `info` nor `k`: stopped, the body
is dropped in that arm, inside the `handle`, before anything it borrows can go.
This lets a library run a callback it is lent under a budget:
`handle { perform budget(n, () => { read(x) }) } with { exceeded(_), _ => fallback }`.

| Live value | `0` | `<=1` | `1` | `ω` |
|---|---|---|---|---|
| duplicable, `&` | ok | ok | ok | ok |
| affine, `&mut`, affine `var` | dropped | ok | ok | no |
| linear | no | no | ok | no |

## Drop and clone

There are no user-defined drops, so dropping never runs hidden effects.
`clone(x: &A): A` is built in for affine types whose parts are duplicable or
clonable; not for opaque externs or linear types. `Text` has a clone whatever its
kind is, so an explicit `clone(t)` of a `&Text` stays accepted if `Text` becomes
affine.

A text literal is a constant of the module and freezes nothing, so it fits a
`&Text` with no `&` written (`Text::len("abc")`). Elsewhere it is a `Text`.
The `Text` builtins that only read (`Text::len`, `byte`, `slice`, `compare`,
`escape_debug`) take `&Text`.

## Types, propositions and proofs

Occurrences in types, propositions and proofs are not uses
(`theorem t(f: File): P(f)` is fine). Kinds and counts only reject programs.
Kernel-read shared borrows are stripped before the kernel, and `&mut` never
reaches it. Linear dependent types are out of scope.

## Standard library

The `List` functions (`map`, `each`, `fold`, `fold_once`) are core
(`std/prelude/std.taut`). The containers, shared (persistent `Map`, `Array`,
`Bytes`) and affine (`Buf`, `Vec`, `Slice`), are all in
`std/prelude/collections.taut`, which every file sees without an import, as
it sees `List`. `Text::of` and `Buf::of` bridge them. CFL shapes the signatures: `map` and `each` hold the
remaining list across `f`, so elements are shared; `map_ref`, `each_ref` and
`fold_ref` read a lent list (`&List(A)`) and lend each element to `f`, so the
elements may be affine; `fold` needs a shared
accumulator, while `fold_once` takes `<!e: <=1>`. `<A: Linear>` marks functions
that never drop elements. `replace(x: &mut A, v: A): A` is the only way to move
out of `&mut`. `spawn` and `par` take `affine () -> A`: the host calls a task's
body once, so a body may own what it moves into the task (a `TcpStream`) and
a shared body is passed as it is. `budget` does not bound the host stack used to traverse or drop
recursive data.

### Regions (`std/builtin/region.taut`)

`Region(S)` (affine, freed at its owner's block end) and `RcRegion(S)`
(reference counted) hold an allocation policy; `Region::place` returns a
`Place(T)` borrowing the region, and borrow-carrying rules keep it from
outliving it. The checker knows none of these names. Other backends ignore
placement; Rust makes bump policies real ([`rust-backend.md`](rust-backend.md)
「Regions」).

### Effects returning borrows

An effect whose result carries borrows (`effect place<T>(): Place(T) resume 1`)
is an implicit borrowed argument written in the row:

1. `perform e()` borrows what e's handler answered, and so does a call with e
   in its row.
2. A `handle` removing e replaces "borrows from e" with what the answer in
   `k(v)` borrows; normal freezing applies, and `k` freezes it within the arm.
3. Such an effect whose result may hold a mutable borrow (`&mut`, an opaque
   view, `Place(T)`) resumes at most once: two kept results of `k` would hold
   the same `&mut`. One whose result holds only shared borrows may resume `ω`,
   since kept results only share what `v` lends (`EffectLend.lean`).

`Placed(T)` and `RcPlaced(T)` wrap a placed value with `coerce(mut)` and
`coerce(owned)`; only `new` builds them.

## `extern`

Required extern signatures (types, kinds, rows, counts) are trusted claims
listed with axioms. Opaque `extern` types are field-less structs that only
extern functions construct, affine by declaration, dropped by Rust `Drop`,
never linear. Rust `Result` stays `Result`, `Option<&T>` is `Option(&T)`, and
a panic is `Interrupted`.

A replaceable `extern` block holds Tauto `struct`/`enum` and function bodies
([`extern-fallback.md`](extern-fallback.md)). Those bodies are checked like
ordinary definitions. Their types' representation is sealed to the block:
outside it, no construction, projection, update, or match. Host selection
does not relax ownership, borrowing, or effect rows.

## Runtime semantics

The rules are static except for drop timing, observable through extern `Drop`.
`lin.rs` decides them, and NIR carries what it decided. Two checks read NIR
without `lin.rs` and do not take its decision as given:

- `tauto run --check-ownership` (for tests) runs the program on niri
  (`crates/tauto-niri`), on the NIR the native backends are made from, after
  `anf` and `ownership`. It counts a token for every owned value and stops
  where a value is used after it was moved, dropped twice or never dropped, a
  `linear` value is dropped or kept, a borrow is used after what it borrows
  is gone, or a value inside a continuation copied by `ω` is owned.
- `tauto_nir::loans` (`nir-wf.md`「Borrow sources」) follows on every path
  what each value borrows from, and reports a value used after a local it
  borrows from was moved, given a new value or left its block, and a value
  that leaves the function borrowing one of its locals or a parameter its
  `lends` does not name. `let(stack)` is checked by NIR in the same way.

What niri finds is what a run reaches; what `loans` finds is bounded by its
rules (it does not follow a single field, and does not judge `&` against
`&mut`).

## Lean proofs

### Approach

`HasType` (`lean/Proto/Nib/Typing.lean`) and `Safety.lean` stay. Usage is a
separate judgement `Lin`; `HasType ∧ Lin` is preserved. A `var` is a
`scope` term: its place sits in the term around the body, which names it by
a variable, so the model has no store and no cells. Each file below has its
theorems; the headings name the files.

### Kinds, counts, CFL (`Kind.lean`, `Lin.lean`, `Own.lean`)

`Lin` counts uses (same count in both `if` branches), makes handler arm
captures duplicable and `k`'s kind follow the count, and encodes CFL by
liveness over argument evaluation. Proved: preservation of `Lin` (T1,
`lin_preservation`) for a term among the places around it (`PlaceCtx`:
places are duplicable and own nothing), and that frames captured by `ω`
operations hold nothing owned (T5). The hard case is
`k := (x) => handle { E[x] } …`: copying `k` would duplicate what `E` owns,
which T5 rules out. Uniqueness of owned values (T2) and that a linear value
is lost only by consumption (T3) are not proved over places yet: with no
store, they need owned values marked in the term.

### Continuation copying (`Duplicate.lean`)

At `ω` suspension points frames own nothing and hold only duplicable values
that are not `&mut`.

### A freeze ends at the last use (LastUse.lean)

For a `let` holder, the rule is the lexical one applied to
`{ { let h := e; A }; B }`, where `A` ends at the last use of `h`;
`sink_same` proves the two run alike when `e` runs to a value on its own.
Across an `if`, the `let` floats into each arm (`float_ite_same`), so an arm
that does not read `h` ends its freeze where the arm begins. A loop is a
recursive function in the core, and the checker counts a holder read in a loop
as live through the whole loop, so `A` is the loop. `let y := h` that moves the
holder is the `let` of `y` a step later (`move_let_same`): `h`'s freezes end at
the move and `y`'s follow `y`. A holder moved anywhere else or captured by a
closure keeps its freezes to the end of its scope, since closures that borrow
are not modelled; a value with an opaque view keeps them because its drop may
use the borrow. A `perform` answered outside and `var` holders in loops are not
modelled, so the model is narrower than the checker.

### Not modelled

Reference counting, memory, externs, lifetimes, first-class references,
views, `&`/`&mut` exclusivity, closures that borrow and lent functions. The
borrow check (T4) is not proved over places: a borrow names its place by a
variable, and a place never leaves its `scope` (`ScopeCore.lean`), but moves
out of a place and what borrows them are not modelled.

## Rationale

- Kinds are type properties, so they map one to one to Rust types and the
  kernel only needs erasure.
- Rust resources are affine and linear is opt-in, because "exactly once"
  cannot survive `resume 0` aborts.
- `<=1` is the default so affine values cross ordinary effects.
- Borrows that never outlive their owners are a single syntax walk, provable
  in the syntactic style; first-class references plus continuation capture would enlarge the
  soundness argument. Freezing until the last use rather than the block's end
  removes blocks written only to end a freeze (Expressiveness); the liveness
  walk errs toward live, so it only accepts more programs that are safe.
- `&A → A` for duplicables is a one-way copy, not an equation of types: a
  `&A` stays a borrow, and the copy happens only where an `A` is wanted, so
  copying or not does not change the program.
- A borrowing `handle`'s `k` is in-place only; marking `k` would put lifetimes
  into function types.
- Strong reference cycles are rejected by whole-program analysis
  ([`shared-levels.md`](shared-levels.md)), keeping signatures clean.

## Undecided

1. A `no shared` declaration checking that no reference counting runs.
2. Drop effects such as `struct(affine) File drop ! {io}`.
3. `Decimal`'s kind (`shared` if arbitrary precision).
4. Freezing only on shape-changing updates.
5. Two-phase borrows for `Map::insert(&mut m, w, Map::get(&m, &w) + 1)`.
