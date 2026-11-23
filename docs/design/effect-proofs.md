# Proofs about effectful code

Effectful functions and their handlers can be used in theorems as written.
The elaborator (`crates/tauto-kernel/src/check/effects.rs`) reads each as a
computation tree; the kernel sees only the resulting terms and gains no rules.
Executed code still runs as written. Examples: `examples/handler-proofs.taut`;
cases: `cases/check/effect-computations.eure`,
`cases/check/effect-reading-scope.eure`.

## Computation trees

In the kernel prelude (`crates/tauto-kernel/src/prelude.taut`):

```text
inductive Comp(Op: Type, Res: (Op) -> Type, A: Type): Type {
  CompPure(a: A)
  CompOp(o: Op, k: (Res(o)) -> Comp(Op, Res, A))
}
```

A handler is the fold `Comp::fold`; continuations return handled trees, so
handlers are deep, and may be called any number of times (multi-shot). The
laws of `Comp::bind` and `Comp::fold` (monad laws, handler β, handler/bind
commutation) are in `std/effect.taut`, axiom-free; continuations are compared
pointwise (`CompEq`), without funext.

## Effects and rows

`effect e(P0, …): R` generates three unwritable (`@`) declarations: `e@op`
(an inductive with one constructor `e@args(a0: P0, …)`), `e@res` (returns
`R`) and `e@arm<B>` (builds an arm from a function of arguments and
continuation). An effect's type generics are leading parameters of all three
(`e@op(G…)`, `e@res(G…, o)`, `e@arm<B>(G…, f, o, k)`); a row holds instances
such as `fail(Nat)`, and a call of `f<E>(…) ! {fail(E)}` takes `E` from the
argument types. Effects using non-kernel types (`Text` without its import,
`Float`, …) or a row generic are not read.

**Fixed-width integers.** `i64` and the kernel's `SInt(64)` are one type: in a file
that imports their module (`std::sint` for `i32`, `i64`; `std::uint` for `u8`,
`u32`, `u64`) the kernel reads each written fixed-width type as its family, in
effects, signatures and bodies as in data
([`program-data.md`](program-data.md)), and extraction maps it back. A
function that writes a number or an operator (`1`, `a + b`, `a == b`) at such
a type runs as written, since the kernel has no literals of the family and
reads the operators on its own types; use the family's functions
(`SInt::add_or_overflow64`, `SInt::lt64`). Without the import, `i64` runs as
written and a proof using it is told which module to import (`machine_types`
in `crates/tauto/src/read/runtime.rs`). Cases:
`cases/check/effect-computations.eure`.

**Standard effects.** In a file that imports `std::os`, the standard effects
([`host-effects.md`](host-effects.md)) are read by the same rule as an effect
the file declares: each one whose parameter and answer types the kernel has.
`std/os.taut` declares nothing again; the kernel is given the prelude's own
declarations (`standard_effects` in `crates/tauto/src/read/runtime.rs`). The
`enum`s and `struct`s of `std/builtin/os.taut` whose fields the kernel can
read (`IoError`, `FileStat`, `Process`, …) become families of the same shape,
as a program's data does ([`program-data.md`](program-data.md)), and the
effects are written with the proof side's families for their types (`u64` is
`UInt(64)`, `Text` and `Bytes` are the models in `std/`). A theorem about `fs_read`
is therefore about the effect the program performs. An effect with a type
only the host makes (`Signal`, `CancelToken`, `Secret`, a TLS configuration)
is not read. In a file without the import a function performing a standard
effect runs as written, and a proof using it is told to import `std::os`.

A handler stands for the host. A theorem under one handler says what happens
under that handler; that the real host answers alike is assumed outside
Tauto. A theorem for every list of answers the host may give holds of every
run that ends, since such a run was given finitely many answers, and assumes
nothing of the host. Cases: `cases/check/effect-standard.eure`.

A row is its effects sorted by name: operations
`OpSum(e0@op, OpSum(e1@op, … OpNone))`, answers `res_sum(…)`.

**Row variables.** In `fn f<!e>(…): A ! {claim} ∪ e`, `e` becomes two
parameters `e@rowop: Type`, `e@rowres: (e@rowop) -> Type`, and the row ends in
`e@rowop` instead of `OpNone`. `f` cannot perform `e`'s operations itself, so
it is correct for any instantiation. At a call, `e` is the row of the argument
passed for a row-`e` parameter if that row is known (a function name, a
parameter, a handler continuation), else the caller's row, minus `f`'s own
effects; the call is then lifted to the caller's row with `Comp::lift`. At most
one row variable per function, and parameter rows may only use the function's
own. The two extra arguments are never written (nor extracted).

## Reading functions

`fn f(x: X): A ! {e…}` is checked as `fn f(x: X): Comp(Op, Res, A)`.

| Written | Read as |
|---|---|
| effect-free `v` | `Comp::ret(Op, Res, v)` |
| `perform e(a…)` | `Comp::op(Op, Res, i(e@args(a…)))`, `i` the row injection |
| `let x := c; rest` | `Comp::bind(Op, Res, c, x => rest)` |
| `g(c)` with an effectful argument | bind the argument first |
| call of a function with a smaller row | `Comp::lift` (forward every operation) |
| `match`, `if` | each arm; `match x: T` has type `Comp(Op, Res, T)` |
| `handle { c } with { … }` | `Comp::handle_in`: `c` in the extended row, arms via `e@arm`, others `Comp::forward` |
| `var x: S := v; rest` | get/put effects on `rest`, handled by a state-passing handler; the variables `S` names (type generics of any kind, term parameters) are the two effects' generics |

A `handle` leaving no effects inside an effect-free function, theorem or
definition is read as the value its fold gives (`Comp::handle_val`: the arms
and the return clause are functions into the result type, and no tree is built
to take the value of afterwards), so a theorem about it with symbolic
arguments holds by `Refl` even when an arm goes through a `match` that does
not reduce before it resumes. A handler written in a function with a row
variable still builds a tree (`Comp::handle_in`), and `Comp::value` of such a
tree whose arm is stuck on a `match` does not reduce either. Writes to an outer `var` from
a handler arm are forwarded to that `var`'s handler in order. Where the value
type cannot be inferred, the reading inserts `the(Comp(Op, Res, T), …)` using
only written annotations and result types; otherwise write `let x: T := …`.

A `where` becomes leading dictionary parameters first, as elsewhere. A
`decreasing_by` function is read as a tree, then written out with `wf_fix` at
result type `Comp(Op, Res, A)`: recursive calls sit in `Comp::bind`
continuations, so descent must hold for every effect answer. A row variable's
two parameters are passed through like generics.

## Borrows

Ownership guarantees no aliasing ([`ownership.md`](ownership.md)), so mutating
code has a pure state-passing reading. Effect-free `&mut` and `var` are read
by `check/mutable.rs` ([`self-host.md`](self-host.md)). In effectful functions,
`lend` in `check/effects.rs` rewrites before the tree reading:

| Written | Read as |
|---|---|
| `fn f(c: &mut C, x: A): R ! {e}` | `fn f(c: C, x: A): Mut1(R, C) ! {e}`, body `{ var c: C := c; let r: R := body; mut1(r, c) }` |
| `g(&mut y, &mut z.f, e)` | `{ let m := g(y, z.f, e); match m { mut2(v, s, t) => { y := s; z := Z { f: t, … }; v } } }` |
| `z.f := v` | `z := Z { f: v, … }` |
| `&x`, parameter `&x: A` | `x`, `x: A` |

`&mut` parameters are threaded like `var`, so effects and writes keep their
order. Partial borrows go one field deep, on kernel structs only. Results are
taken apart with `mutK` (`match f(p) { mut1(v, q) => q }`). Examples:
`examples/borrow-proofs.taut`; cases: `cases/check/effect-borrows.eure`.

### Sequential `&mut` calls and proof arguments

A `&mut` call rebinds each lent place under the same display name as before
the call (`docs/design/name-identity.md`); the pre-call and post-call
bindings are different locals. Later proof arguments whose types mention that
name refer to the post-call binding. Reflexivity at that binding is accepted;
a hypothesis typed at the pre-call binding does not inhabit a proof about the
post-call one; and the post-call binder is not definitionally the callee's
returned state, so `Refl` does not discharge a non-reflexive goal that follows
only from the callee (including when that return is a constant). When such a
proof is required, a workable shape is a **merged leaf**: one operation whose
proof arguments are pure expressions of the input only. Reading, diagnostics
and accepting counterparts:
`cases/check/mut-sequential-proof-state.eure`
(`post-state-is-what-later-proof-args-mention`,
`proof-about-input-does-not-type-as-proof-about-post-state`,
`refl-does-not-compute-post-state-after-mut-call`,
`merged-leaf-proof-about-input-only-ok`).

## Not read

These functions are skipped with a reason (execution is unaffected): `div`
(trees would be infinite), non-kernel types, `var`s captured by closures,
guarded or patterned handler arms, `budget`, `∀`-arms over all instances of a
generic effect, instances whose types a call does not fix, more than
one row variable or foreign row variables in parameters, returned borrows,
containers such as `Vec`/`HashMap`, and anything the kernel then rejects.

In a tote, readable functions are given to the kernel and extracted like any
other; unreadable or skipped ones run as written.

## Trust

The kernels check the read terms, so soundness never depends on the reading.
That a theorem speaks about execution depends on the reading matching Nib's
semantics ([`semantics.md`](semantics.md#effects-deep-multi-shot-handlers)).
`lean/Proto/Handlers.lean` supports this: `adequate` shows, for an abstract
machine with bind and handler frames where `perform` captures up to the
nearest handler, that a program running to `v` has a tree folding to
`pure v` (no `var`, rows or elaborator in the model). `heap_adequate` shows a
cell-mutating machine agrees with the state-handler reading of `&mut`,
assuming `NoAlias`; without it they disagree (`alias_disagrees`). Connecting
`heap_adequate` to `adequate`'s machine is not done.

## Undecided

- Reading `div` functions as fuelled trees.
- Arms over every instance of a type-generic effect.
- More than one row variable.
- Standard effects with a type only the host makes, and concurrency (`spawn`, `wait`).
- How the `&mut` reading should keep the link between a post-call state and
  the callee's result under existing computation rules (effect-free and, for
  effects, order / update / handler resume-abort), without adding core rules
  and without a rename-on-every-update surface. Existing hypotheses must keep
  their pre-call meaning; new propositions that need pre-call information must
  name that information explicitly. This reading question stays open even when
  a particular leaf can be split another way. Cases:
  `cases/check/mut-prestate-proofs.eure`.
