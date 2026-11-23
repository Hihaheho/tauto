# Static checks of NIR

niri finds a compiler bug by running a program: a case whose run breaks an
ownership rule or ends otherwise than the whole function does. It finds only
what a run reaches, and says where it broke, not what NIR got wrong.
`tauto_nir::wf` reads a package and reports a broken invariant of NIR
without running it. It is not complete: it states what every pass promises
about binding, types and continuations, and leaves what needs a run (the
values, the order of drops at run time) to niri.

## What it checks

| Rule | Invariant | A pass that breaks it |
|------|-----------|-----------------------|
| `Scope` | Every local a node uses is bound around it on the path it is reached by. A use is a read, a borrow, an assignment's target, a call of a local function value or continuation, a closure's or handler's capture, and a drop on an abort path (`unwind`). | Lowering that reads a local in a branch that never binds it. |
| `Identity` | A use names its local with its binder's name and storage (`Repr`). | A pass that changes a binder's storage and not its uses. |
| `Type` | A read has its binder's type (a borrowed local shows what it borrows); a `let` has its value's type; a closure's and a function's body their result type; a condition is `Bool`; a pattern `inject(union, index, p)` is on a value of `union` (or a borrow of one), which has a member at `index`, and a name `p` binds has that member's type; a call of a function with no type parameters passes its parameter types and has its result type. A function value of a kind copied more freely fits (`copy ⊑ shared ⊑ affine ⊑ linear`), and a borrowed parameter takes the value it borrows. | A stale type left on a binder or on a closure's result. |
| `Arity` | A call passes as many arguments as its callee takes. | |
| `Tier` | A call states its callee's tier. | |
| `Kont` | Each continuation of a function of the tier `O` or `M` (`kont::split`) uses only its argument, its environment and what it binds; each jump passes the environment its target takes. | A continuation that calls a local function value it was not given. |

A type is compared only where it is written in full: one with `Ty::Infer`,
a type parameter or `Never` in it is taken as written.

## Independence

The checks read the block form of a function (`blocks`): each is a forward
dataflow over its blocks to a fixed point, with the parts of a `handle`
solved in order (the body, then the return arm and the other arms from where
the body ended). The block form is lowered from the tree after `anf`, so an
operand that computes a value is named first. The checks share no
free-variable code with the passes they check. `kont::check` read uses with
the same `mentions` that `kont::split` built environments from; when
`mentions` missed a call of a local function value, both missed it, and only
a run found it.

## Where it runs

- `Pass::CheckWf` (`check-wf`): a case's `nir.passes` asks for it, and
  `nir.error` states what it finds in a package written as text
  (`cases/nir-wf.eure`).
- `crates/tauto-niri/tests/wf.rs`: every case the Rust backend compiles is
  checked as compiled and after `anf` and `ownership`. A finding not listed
  in `KNOWN`, with its cause, fails the test.

## Borrow sources

`tauto_nir::loans` is the second judgment on borrows. The checker of the
source decides which borrows a program may make, and NIR carries what it
decided; checked against that decision again, NIR would only be compared
with itself. `loans` instead follows, on every path of a function, what each
value borrows from: a local of the function at one of its lives, or what a
parameter brings from the caller. A move out of a local, a new value given to
it whole and the end of its block start a new life, and a borrow of an
earlier life is gone. A dropped value is not read: a borrow has nothing to
release.

| Rule | Invariant |
|------|-----------|
| `Dangling` | A value is not used (read, borrowed, called, captured) after a local it borrows from was moved out whole, given a new value whole, or left its block. |
| `Escape` | The function's result, a value it returns and a value it writes through a borrowed parameter borrow no local of the function. |
| `Lends` | The result borrows no borrowed parameter that the function's `lends` leaves out. |

A call's result borrows the arguments the callee's `lends` names (an
extern's `borrows(…)` is carried as `ExternDef::lends`); a builtin's
borrows its first argument, and a function value's every argument. A value
written through a `&mut` argument borrows what the other arguments borrow. A
type that cannot hold a borrow carries no source: a number, `Text`, a data
type that is not a view, an owned function value.

What it does not report it does not judge: a borrow of one field (a move or
an assignment of a field leaves the other borrows of the local as they
were), `&` against `&mut`, and a borrow given as a type argument
(`Vec(&T)` through a generic function: a type parameter carries no source).

It runs as `Pass::CheckLoans` (`check-loans`) and in
`crates/tauto-niri/tests/wf.rs` beside `wf`, with a known finding written
in the case as `nir_wf.bug = "<function> loans <Rule>: why"`.

## Ownership

`tauto_nir::ownership::check` (`check-ownership`) reads the block form too:
each owned local (a parameter, a `let`, a name a pattern binds) is in one of
three states on a path (not made, holding its value, moved), and the states
it may be in where paths meet are kept together. A move of a local that may
be moved is a second one; a local that may still hold its value where its
scope ends was not moved. A closure moves what its body moves, once, where it
is made, and not what it clones. A path ends at a value of `Never`. The
right side of `&&` and `||` runs only where the left does not decide, so a
local it moves is to be dropped on the path that skips it. A local given a new value whole is not checked. A block that only runs
where a call aborts is not checked for what it leaves held, nor for a
drop of what a `&&` or `||` before it may have moved.

## Not checked

The capture lists of a
closure against what its body reads, the types of the arguments of a
generic call, the fields of a constructor against its declaration, and the
tier a body needs against the tier its function states.
