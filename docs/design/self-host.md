# Self-hosting

Parts of the compiler are rewritten in Tauto as totes under `totes/`, in the
kernel-checked total fragment, with correctness theorems at key points.
`tools/selfhost-harness` checks them against the Rust implementation. Each
tote's README describes its behaviour.

Nothing composes the totes into a compiler that processes its own source: the
CLI uses Rust throughout, and component differentials do not establish
self-hosting.

## Components

| Rust | Tote |
|---|---|
| — | `totes/text`, `totes/unicode`, `std/map.taut` |
| `fmt.rs` | `totes/fmt` |
| `tauto-parol` | `totes/scan`, `llk`, `lr`, `syntax`, `grammar` |
| `tauto-parol-gen` | `totes/llkgen`, `lalrgen` |
| `tauto-surface` | `totes/surface` (the syntax, no reader) |
| `tauto-parse` | `totes/parse` (reads the tree of `totes/syntax` into it) |
| `macros/scope.rs` | `totes/macros` (syntax values, quote, hygiene) |
| `types.rs`, `rows.rs`, `lin.rs` | `totes/nibcheck` |
| `check/core.rs` | `totes/kernel` (rechecks emitted elaborated declarations) |
| `check` (elaboration) | `totes/elaborator` (a subset) |
| `extract.rs` | `totes/extract` |
| `tauto-rustgen` | `totes/rustgen` (an `i64`/`Bool` subset; rejects the rest) |
| `tauto-nir` (`text::parse`) | `totes/nir` (reads a package from NIR text) |
| `tauto-nir` (`blocks::lower_body`, `blocks::print`) | `totes/nir` (`blocks.taut`, `print_blocks.taut`: a function in A-normal form as blocks, and the blocks as text) |
| `tauto-niri` | `totes/niri` (runs a package of NIR text; no coverage or split runs yet) |
| `tauto-llvm` | `totes/llvm` (the LLVM backend; `llvm-backend.md`) |
| `tauto-nibcheck` (`lower`), `tauto-nir` | `totes/lower` (Nib source to NIR text; the `data` items only; `totes/lower/README.md`) |
| `tauto-jsgen` | `totes/jsgen` (the JavaScript backend: the program, its chunks and its declarations) |
| `totebag` (`source.rs`, `lock.rs`, `cache.rs`, `git.rs`, `index/*`), `totebag-index` | `totes/totebag-io` (source trees and their IDs, `Tauto.lock`, the cache, Git, the distributed index's files, histories, syncs and adoption), `totes/index`, `totes/sha256`, `totes/eure` |
| `tauto-analyzer` (`navigate/index.rs`, `navigate.rs` without the types) | `totes/analyzer` (the names of a file, where each is declared and used; definition, hover, references, rename) |

Out of scope: lint (by policy), the CLI, the passes of NIR and the Rust backend, and
the Rust VM `crates/tauto-vm` (needs multi-shot continuations in Nib, and an interpreter on an
interpreter is too slow). The Rust kernel stays authoritative; its literal
arithmetic computes numbers below `2^256`, which Nib's `u64` does not hold.

The elaborator tote covers explicit `def`/`theorem`, single and `mutual`
inductives with no-confusion, total `fn`s, structural `match` (nested patterns,
literals, a final `_`), indexed matches, aligned mutual groups and numeral
level instances. Module blocks can nest and can contain functions and effects.
Re-export aliases resolve to the same constants and operations as the
qualified names of those members. The macro tote lifts and lowers module blocks
and re-exports as syntax values. The elaborator rejects statement macro calls.

## Layout and loading

`totes/<name>/src/*.taut` holds everything; `main.taut` is the entry and loads
last, after dependencies and the other sources in path order. Each declaration
is either runtime code or checked by both kernels; a failed check is never
retried as runtime code, and holes or axioms reject the tote. Checked functions
are extracted and joined with runtime code.

## Coding rules

1. Prefix names with the tote (`scan_next`); match Rust names for the same
   role, porting one Rust function to one Tauto function, so failing
   differentials read side by side.
2. Don't store functions in struct fields; pass borrowing closures.
3. Fallible functions return `Result` or `Option`. No `_ =>` arms.
4. Shell string literals avoid backslashes and `"`.

## Elaboration sugar

Sugar is allowed only where the kernel receives the term as written without
it; it lives in `check/matching.rs` and `check/sugar.rs` and is rechecked by
both kernels. Cases: `cases/check/programs.eure`.

- `fn` generics are implicit `Type` arguments; `match` may appear anywhere;
  `match e: T` matches a fresh variable substituted by `e`, and calls to the
  function being defined become induction hypotheses.
- After `std/text.taut`, string literals are UTF-8 `Text::Mk`. After
  `std/base.taut`, `-`, comparisons, `&&` and `||` read as `Nat`/`Bool`
  functions. `+` and `*` are kernel built-ins recursing on the second argument;
  the kernel computes them directly only on literals.
- Records and record patterns for single-constructor families; `x.f` and `==`
  by type; unannotated `let` substitutes.
- `mutual` fuel ([Termination](#termination)) and `&mut`/`var` (below).

### `&mut` and `var` (`crates/tauto-kernel/src/check/mutable.rs`)

Stateful Nib-shaped code is rewritten syntactically into state passing and
rechecked; extraction emits the original `&mut` Nib.

- `fn f(c: &mut C, x: A): R` reads as `fn f(c: C, x: A): Mut1(R, C)`, so
  theorems state `f(c) = mut1(v, c')`.
- State is threaded by name; assignments become `match mut0(e) { … }`, never
  duplicating terms. A call rebinds each lent place under the same display
  name; later proof arguments mention the post-call binding, but a pre-call
  hypothesis does not inhabit them, and the binder is not definitionally the
  callee's returned state (`docs/design/effect-proofs.md`「Sequential `&mut`
  calls and proof arguments」; cases:
  `cases/check/mut-sequential-proof-state.eure`).
- A state-changing `match` or `if` must be in tail position or have a value
  type annotation. Functions with `while` or `return` are runtime code; lambdas
  cannot change state.

## Extraction

Arguments are classified as type, proof or value from kernel types; only values
remain. Extraction reads the kernel-checked declarations and the source
snapshot, never rereading files.

| Proof side | Nib |
|---|---|
| unindexed `inductive` in `Type` | `enum(shared)` / `struct(shared)`, proof fields dropped |
| indexed families and families storing types | a private tagged representation |
| `Prop` families, `theorem`, `axiom`, `def`, `ghost fn`, proof `let`s | dropped |
| `fn` | type arguments become generics, proof arguments drop |
| `match` on `Nat` / `Bool` | `if` chains |

- **No proofs from unchecked code.** Calling a function with proof arguments,
  or building a constructor with proof fields, from Nib is an extraction error.
- **Dependent data** keeps value arguments and fields, so branches test stored
  tags; impossible branches diverge in an internal function. Each closed
  dependent type is a nominal abstract type at the Nib boundary: values come
  from checked functions and go to functions requiring the same contract.
- **Effects** become private requests with continuations; handlers forward
  foreign operations and reapply themselves on resumption, with resumption
  limits from the kernel's check.
- **Function values** keep all argument positions, passing a contentless value
  for erased ones. Closed function types are abstract at the boundary.
- `inductive struct` / `inductive enum` go the other way: programs run as
  written and the kernel gets the same family ([`program-data.md`](program-data.md)).

**Mapping table (trusted).** These `std/` declarations map to Nib built-ins;
proofs are about their `std/` definitions.

| Proof side | Nib |
|---|---|
| `Nat` | `nat` |
| `UInt(w)`, `SInt(w)` | machine integers |
| `Bool`, `List`, `Option`, products, `Unit`, `Text` | the same Nib types |
| `Array` | shared read-only `Array` ([Arrays](#arrays)) |
| `Bytes` | `Bytes` (slices share storage) |
| `Float` | `Float` ([`float.md`](float.md)) |
| `Stack` | `Vec` operations (top at the end) |
| `Nat::lt`, `le`, `eq`, `sub`, `div_nz`, `rem_nz` | the operators |
| `Quot(A, r)`, `Quot::mk`, `Quot::lift` | `A`, `a`, `f(q)` (representatives are unobservable) |

Trusted overall: both kernels, the mapping table, the Nib runtimes and the
shell. Differentials catch mapping drift. `u64` traps at 2^64 while `Nat` does
not; proof-side values are positions, lengths and parsed literals bounded below
2^63, so the gap never shows.

## Proof-side standard library

- `std/base.taut`: `Bool`, `Nat` and `List` functions with bridging lemmas.
- Integer division has an effect-free `_nz` form taking a non-zero proof, used
  in equations, and a form performing `divzero`; there are no zero-returning
  variants. `/` is reserved for fractions.
- `std/refined.taut`: `Refined(A, P)` pairs a value with an erased proof;
  `refine_by` checks a `Bool` predicate at run time. It is abstract at the Nib
  boundary.
- `std/text.taut`: a UTF-8 byte model mapped to builtins.

### Termination

Non-structural loops take `fuel: Nat` first and fail when it runs out; callers
pass enough from the input size, and theorems say enough fuel never fails.
Mutually recursive functions sharing fuel go in `mutual { fn … }`, each
starting with `match fuel`; `check/steps.rs` turns the group into one
structurally recursive function over request and answer inductives.

### Arrays

`std/array.taut`'s `Array(A)` wraps a list with `get` defined as `List::nth`;
extraction maps it to Nib's shared `Array` with O(1) `get`. The builtins are
trusted to behave as the list definitions.

## Shell

Each tote's `main.taut` reads arguments and files, calls one pure function and
prints: a few dozen lines reviewed by eye.

## Differential tests

`tools/selfhost-harness` runs a tote on a corpus and compares its printed dump
with the one Rust builds, showing context around the first difference. Run it
with `cargo nextest run --locked --manifest-path tools/selfhost-harness/Cargo.toml`.

## Syntax (`totes/scan`, `totes/llk`, `totes/lr`, `totes/syntax`)

The grammar's source of truth is `syntax!(tauto, …)` in
`totes/grammar/src/grammar.taut`; `scripts/generate-tauto-grammar.taut` writes
the bootstrap `tauto.par` from it. The Rust parser stays the compiler's parser.
`scripts/generate-syntax-tables.taut` writes its tables to
`totes/syntax/src/tables/` as whitespace-separated numbers. `scan` runs the
lexer DFAs, `llk` and `lr` the parser drivers, and `syntax` builds the CST,
which differentials compare with Rust's.

## Proofs

Tote theorems live with the code; `tools/selfhost-harness/tests/proofs.rs`
checks they have no holes or axioms. `surface`, `syntax` and `fmt` stop at
totality and types, and differentials check their behaviour.

- **ordmap** (`std/map.taut`): AVL operations equal list operations on the
  in-order entries, assuming a total order; `Nat` and `Text` comparators are
  proved total.
- **scan** (`totes/scan/src/longest.taut`): returned tokens are tokens of a
  run, and none is longer.
- **llk** (`totes/llk/src/derives.taut`) and **lr**
  (`totes/lr/src/derives.taut`): success means the start symbol derives the
  input. Lookahead and table choices are irrelevant to soundness; the remaining
  table assumptions are checked at run time.
- **text and unicode**: decoding an encoded character returns it;
  `totes/unicode` matches Rust's character classes. Write `Nat::mul(64, x)`,
  since `mul` recurses on its second argument.

Proofs about `&mut` functions introduce, for each stuck subexpression, a
continuation function taking it as the last argument, so hypotheses carry
through `Eq::subst`.

## nibcheck soundness (`totes/nibcheck/src/`)

The goal is that a program nibcheck accepts is typed by declarative Nib rules.
The rules are written independently as inductive relations in
`rules_*.taut`, derived from [`nib.md`](nib.md), [`semantics.md`](semantics.md),
[`ownership.md`](ownership.md) and [`classes.md`](classes.md); they are the
specification to review. Where the checker is looser than the docs, fix the
checker or extend docs and rules. Soundness is "if it succeeds", so running out
of fuel is fine.

| Layer | Result |
|---|---|
| 1 Types | type equality, union and tag normalization as sets |
| 2 Unification | `ck_unify` gives equality; `ck_fits` gives subtyping `TySub`; `ck_join` an upper bound |
| 3 Declarations | kinds, well-formed data and signatures |
| 4 Expressions | no errors ⇒ a typing derivation |
| 5 Classes | instance resolution and `where` |
| 6 Effects | inferred rows bound the declarative ones |
| 7 Linearity | the ownership usage rules |
| 8 Whole | no errors ⇒ typed by layers 1–7 |

### Layer 1: unions and tags (`src/union_sound.taut`)

Unions are read as sets; order and duplicate-freedom are not proved.

### Layer 2: `ck_unify` (`src/unify_sound.taut`)

On an ordered substitution, the state only grows and `true` means equal types.
Rigid variables are checked against the final substitution.

### Layer 2: `ck_fits` and `ck_join`

`TySub` covers equality, `Never`, generics, borrows, duplicable values as
borrows, unions, tags, contravariant functions and product reordering. Both
branch types of a join fit its result.

### Layer 3: kinds and declarations

Inferred kinds are at least the documented ones (safe). An error-free report
implies kind annotations hold, names are unique, data and signatures are
registered as written, and written types have derivations. Behaviour these
proofs pin down: field types are rechecked after all data is registered, and
checks record an error when fuel runs out.

### Layer 4: atoms, names and calls

Proved: locals, literals, unshadowed functions, call argument matching,
natural literals and the persistence of recorded obligations. Fresh inference
variables are never bound before allocation. Handlers collect all arm results
first and recheck arms against that result, so an earlier arm cannot rely on a
narrower continuation type. Constructors with shared names are resolved from
constraints before integer defaulting.

### Layer 5: class assumptions

Constraints resolved to generics follow from use-site assumptions. Structural
checks do not skip types containing variables, so `identity == identity` is
rejected while `[] == []` is accepted.

## Caches

- **Native binary cache** (`tools/selfhost-harness/src/native_cache.rs`):
  release tote binaries are cached by the content of every input (sources,
  tables, compiler, environment, toolchain); results and proof verdicts are
  not. Untrackable inputs build without reuse. `TAUTO_SELFHOST_CACHE_TRACE`
  shows hits.
- **Proof cache** (`crates/tauto-kernel/src/check/cache.rs`): a theorem is not
  rechecked while the checker, its statement and its environment are unchanged.
  Proofs are not unfolding values, so editing a proof does not invalidate its
  users. Hits still elaborate and check the statement; only the proof is
  trusted. Functions cache elaborated terms the same way. `TAUTO_CACHE=off` or
  `tauto check --fresh` disables it, and the tactic results kept in
  `$TAUTO_BUILD` with it (`docs/design/build-cache.md`).

## Benchmark

`cargo bench --manifest-path tools/selfhost-harness/Cargo.toml --bench compiler`
compares `totes/nibcheck` with Rust from parsing to identical diagnostics, one
process per sample. Partial numbers are never reported as overall speed.

## Undecided

1. Make the tote name a top-level prefix and drop name prefixes.
2. Git dependencies, versions, `Tauto.lock`.
3. Static data literals.
4. Kernel primitives for `Text` and machine integers if proof-side speed
   matters.
5. Remaining nibcheck soundness: declarations with kind and borrow
   constraints, compound expressions, instance search, handlers and effects,
   linearity, and assembling one theorem.
