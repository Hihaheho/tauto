# Rust target model (`totes/rustgen/model/`)

A model of the generated Rust, used to prove Nib → Rust translation correct
when `crates/tauto-rustgen` is self-hosted. Independent of the
`totes/rustgen/src/` backend.

## Syntax and static information

`inductive_syntax!(rs, …)` in `syntax.taut` defines Rust concrete syntax, its
parser and the trees `rs::Program::I`, `rs::Expr::I`, `rs::Pattern::I`,
`rs::Ty::I` (tables in `model/.tauto-syntax/`). Spans and macro hygiene are
not semantics.

`RsRepresents(sig, scope, control, expr, ty, syntax)` (`source.taut`) says the
tree `syntax` represents the resolved expression `expr` of type `ty`; each
binding, branch, application, pattern and capture has its own constructor,
and there is no escape hatch for arbitrary compound expressions. Parsing
alone gives no semantics.

- `sig`: the resolved, type-checked declaration environment (type spellings,
  Copy vs move, referents, field order, call signatures, constructors, extern
  ABIs, pointer width).
- `scope`: locals and types; resolved locals are indices.
- `control`: the function result type and enclosing loop labels (cleared
  inside closures and async bodies).

The environment does not replace rustc. Its faithfulness (Copy, layout,
lifetimes, callable kinds, generics, trait resolution) and passing Rust's type
and borrow checks are assumptions on the user side. `RsSourceProgram` ties
every function body to one function table but does not recheck layout or
borrows.

## Generated form

One explicit form: parenthesized conditions, operators, references and
dereferences; blocks with a tail expression; resolved paths and type
arguments; locals `v<n>` and labels `'l<n>`, never shadowing.

| Feature | Model |
| --- | --- |
| literals, locals, fields, refs and reborrows | `RsLit`, `RsRead`, `RsField`, `RsDeref`, `RsRef` |
| structs, enums, tuples | type and constructor tables, `RsAggregate` |
| `let`, sequences, assignment | `RsLet`, `RsSeq`, `RsWrite` |
| `if`, `&&`, `\|\|`, `!` | `RsIf` |
| `match` on places / values, guards, nested patterns | `RsMatchPlace` / `RsMatch`, `RsCase`, `RsPattern` |
| functions, indirect calls, recursion | `RsFunction`, `RsCall`, the function table |
| `Fn`/`FnMut`/`FnOnce` closures | `RsLambda` with explicit capture initialization |
| `loop`, `break`, `continue`, `return` | labelled control results |
| `async move`, `.await` | `RsFuture`, `RsAwait` |
| runtime, extern API, scalar operations | typed direct calls `RsPrimitive` with external contracts |

Call, constructor and extern arguments are bound left to right to annotated
locals first (and the callee of an indirect call), so nothing depends on
Rust's defaulting or inference. Captures are evaluated outside, moved, and
borrowed whole at the top of the body. `Fn` uses `Rc::new`, `FnMut`/`FnOnce`
`Box::new`, futures `Box::pin`. Float literals use `from_bits`.

This is not a parser for the backend's literal output: `while` is a labelled
loop, methods are resolved calls, scalar operators are runtime calls, and the
rewriting from the current output into this form belongs to the proof. `use`,
modules, facades, constants, diagnostic macros, embedded parsers and manifest
Rust bindings are outside the model, connected only through named external
contracts.

## Evaluation

`core.taut` defines resolved syntax, values, store and control results;
`semantics.taut` defines finite derivations:

| Judgment | Meaning |
| --- | --- |
| `RsEval(program, rt, env, expr, heap, out, next, trace)` | evaluate an expression |
| `RsEvals` | evaluate a list left to right |
| `RsApply` | call a global, owned or borrowed callable |
| `RsSelect` | try patterns and guards in order |
| `RsFinish` / `RsDrop` | release scopes and values |
| `RsSourceEval` | evaluate with concrete-syntax correspondence |
| `RsProgramRuns` | bind the function table and call the entry |

- Addresses are a root allocation and a field path; freed cells are never
  reused or revived. A move uninitializes its source; after a partial move the
  other fields remain usable but the whole value is unreadable. Shared
  references are Copy, mutable ones move.
- `match` on a place uses it; on a value, a temporary. Guard bindings borrow
  the scrutinee's fields; moves happen only when the guard holds. Guard
  effects are not undone. Wildcards read nothing. There is no rule for a match
  with no matching arm.
- Arguments evaluate left to right; assignment evaluates the right side first
  and drops the old value before writing. Temporaries are dropped on failure.
  Locals drop in reverse binding order, fields in declaration order; capture
  drop order is a permutation, not fixed. `FnOnce` consumes its environment;
  shared borrows call only `Fn`, mutable ones `Fn` and `FnMut`.
- Results: value, `return`, labelled `break`/`continue`, panic, process exit
  with code, abort. Scope exit and panic drop; exit and abort do not; a panic
  during unwinding aborts.

## Runtime boundary and proof scope

`RsRuntime` relates an external operation, its arguments and the store to a
result, store and events. It is an explicit parameter, not an axiom; outcomes
cannot `return`/`break`/`continue` into the caller, and callbacks must go back
through `RsApply`. `RsDrop` takes whether unwinding is in progress;
`drop_handle` covers reference counts and last-owner release.

`integer.taut` computes fixed-width ranges, checked arithmetic, negation and
comparison, and nonnegative arbitrary-precision arithmetic (negative
subtraction fails, not saturates). Floats, text, containers, shared cells,
effect dispatch, continuations, budgets and I/O go through runtime contracts.
Allocation failure and stack limits are not modelled. `RsAwait` runs a future
once; polling, wakers, interleaving and cancellation are not modelled, and the
lack of a finite result says nothing about divergence.

The translation theorem will relate Nib values, store and events to this
model, generate `RsRepresents` and `RsSourceProgram` derivations and discharge
the runtime contracts, for finite runs. Rustc and machine code are out of
scope.
