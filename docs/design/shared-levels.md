# No strong reference cycles

A static check, on by default, guarantees that the strong reference graph of
Tauto values never has a cycle. The checker and an abstract model are proved;
the translation from Nib to the model's constraints and its correspondence
with the runtimes are not.

## Guarantees

- **G1, acyclicity**: from a proper initial state, using only checked
  operations, no reachable state has a strong cycle.
- **G2, collection**: with correct reference counts on a finite managed heap,
  completed releases and no resurrection, nothing unreachable from roots
  survives because of a cycle.

G1, G2 and correspondence with generated code are separate obligations; G1
alone does not mean binaries never leak. Out of scope: semantic leaks (caches
holding garbage), memory bounds, termination, RSS, unverified externs,
counter overflow. G2's model has no `Weak`.

## Principles

- Memory levels are separate from kinds, universes and lifetimes; the kernel is
  unchanged.
- Users never manage level numbers; the checker infers them.
- Immutable data needs no annotations and long immutable lists are fine, but
  strong references to mutable storage through immutable containers and
  closures are tracked.
- Levels never change on aliasing, calls or multi-shot resumption.
- Unsupported syntax, unknown externs and unknown captures are rejected;
  `Unknown` is not the empty capture row.

## Model

The **frontier** of a value is the set of mutable storage reached by following
strong references through immutable nodes and stopping at the first mutable
one. Mutable storage is anything whose strong targets can change after
publication (cells, `Ref`, mutable containers, `Mutex` holding pointers,
runtime mutable slots); numeric-only storage has no targets. A rule looking only
at cell-free parts misses `cell c → immutable list → closure → cell c`.

The proof heap has per-allocation IDs, immutable/mutable nodes, a logical
creation order `birth`, a `level` per mutable node, and counted edges:

- **I**: an edge between immutable nodes `u → v` has `birth(v) < birth(u)`.
  Immutable objects are built from existing initialized ones; self-reference,
  back-patched recursive closures and in-place updates get no exception.
- **II**: a nonempty path from mutable `a` to mutable `b` through immutable
  nodes has `level(a) < level(b)`.

**Theorem**: I and II imply no strong cycle (a cycle without mutable nodes
would decrease `birth`; with them, levels increase strictly around it).

| Value | Frontier bound |
|---|---|
| integers, booleans, Text | `∅` |
| reference to `Cell<α, T>` | `{α}` |
| immutable products, structs, enums | union of fields |
| immutable `List`, `Array` | element capture row |
| `&rc T` | the frontier of `T` |
| closure | union of what it actually captures |
| saved continuation, suspended budget | frames, values and handler environments held |
| `Weak` | `∅` |
| unchecked extern, type erasure | `Unknown` |

Storage has a fixed level `α` and content bound `κ` with `α ≺ κ`. Every write
(assignment, field write, `replace`, `swap`, insertion, `Ref`/`Mutex`
updates, writes through `&mut`) checks `captures(v) ⊆ κ(c)` and
`α(c) ≺ captures(v)`. A closure capturing `var x` captures the cell:

```text
var f = () => 0
f := () => f()      // the closure holds {level(f_cell)}; storing it needs α ≺ α: rejected
```

Function recursion is fine, but runtimes must not implement it with strong
cycles internally (e.g. self-referencing `Rc`); runtimes are audited for this.

## The checker (`crates/tauto-nibcheck/src/cycle/analysis.rs`)

It runs at the end of `lin::check`, so on every entry (NIR, macros).

- Closures capturing `var` are borrowing and cannot be stored, so first-class
  storage is `Ref`, `Mutex`, `Vec`, `Slots` and host state.
- A **site** is a syntactic place creating storage (`var`,
  `perform ref_new`, `perform mutex_new`, calls of `Vec::new` and
  `Slots::new`, each host function's state) and stands for all storage created there.
- Values are flattened to sets of atoms (storage references, borrowed places,
  closures, `Unknown`), ignoring positions in lists, enums and closure
  environments. Struct literals keep fields apart (`u.lift` holds only what
  `lift` holds) until destructured, written through a place (`&mut x.f`) or
  passed to an untyped extern or host. Sets are the least solution of inclusion
  constraints over the whole program, prelude included; higher-order calls are
  solved through closure sets.
- Generic top-level functions are re-read per direct call (otherwise every
  `Mutex` passed to `Mutex::lock` would mix); recursion, use as a value, or more
  than 4096 copies fall back to a shared copy.
- A typed term's value drops storage kinds its type cannot hold (a
  `Vec(A)` is never a `Ref`), found by walking the type to the first
  `Ref`/`Mutex`/`Vec`/`Slots`, stopping (keeping everything) at function
  types, type parameters and unknown types. Site kinds come from the creating
  extern; `var` and host state are never dropped. This relies on type checking, outside the
  Lean proof.
- Each site's frontier gives a graph over sites; a cycle is rejected, otherwise
  its topological order is the level assignment
  (`sites_acyclic_implies_acyclic`). Structures linking storage of one site
  (e.g. a `Ref` linked list) are rejected even when acyclic at runtime.
  `Unknown` in a frontier is an error.
- A handler's continuation `k` is a closure whose environment is: everything the
  body evaluates and binds; the frames of functions and closures called from it
  (nodes solved with call resolution), except **finished calls**, whose row is
  concrete and contains no effect with an arm keeping `k`
  (`lin::keeps_continuation`), since they are off the stack when `k` is
  captured; and every binding visible at the `handle`. Calls with row
  variables, `?` or through function values are kept; with row errors, all
  are. `lean/Proto/Nib/KeptFrames.lean` (`running_call_performs`,
  `capture_covered`) shows captured frames belong to calls whose rows contain
  the captured effect.
- Hence programs storing continuations in storage are rejected only when truly
  cyclic, e.g. an arm storing `k` in storage the handler can see. External
  generators return `k` from the arm and store it outside the `handle`
  (`cases/lin/kept_continuations.eure`). Diagnostics show the chain
  (`holds continuation <pos> which holds <site>`).
- Prelude externs are classified as allocate, store, load, load `&mut`,
  convert or flatten. A host `extern` has one state per function that holds
  whatever it receives and may return it.
- Runtimes capture only used variables (NIR, backends),
  since holding whole scopes would create unchecked edges. Continuations are
  delimited by their `handle`; the Rust backend's tier M
  (`crates/tauto-rt/src/cps.rs` `Resume`) does not hold the `handle`'s result
  destination or outer handlers ([`rust-backend.md`](rust-backend.md)).
- `Weak(A)` (`Weak::of(r: Ref(A))`, `Weak::get(w) -> Option(Ref(A))`) is a weak
  atom, not an edge; a `Ref` taken out and stored is checked as usual. When
  `Weak::get` turns `None` is backend-defined: after the last strong reference
  on the Rust backend and Rust VM; whenever GC runs on
  JavaScript (`WeakRef`); never on `totes/vm`, whose heap never frees. Without
  cycles, leaving it to GC cannot leak.
- `totes/nibcheck/src/cycle.taut` is the same analysis, self-hosted.

## Proofs

- `lean/Proto/Cycle.lean`: `heap_invariant_implies_acyclic`;
  `sites_acyclic_implies_acyclic` (assuming segments map to site edges).
- `lean/Proto/Collect.lean`: `drain_keeps_reachable`, `drain_collects` (G2).
- `lean/Proto/Analysis.lean`: `analysis_sound`. For the inclusion constraint
  language (copy, join, allocate, store, load, `Weak`, collect), solutions
  cover all reachable states and an acyclic site graph means no strong cycle.
  That the Nib translation loses no runtime copy is not proved, nor the
  correspondence of `KeptFrames` with `analysis.rs`.
- Solver: `crates/tauto-nibcheck/src/cycle/solve.rs`.

### Shared collection model (`meta/memory.taut`, `lean/Proto/Memory.lean`)

The same axiom-free statements in both languages:

- `abstract_acyclic_implies_acyclic`: if every strong edge maps to an abstract
  edge, abstract acyclicity implies concrete acyclicity (edge coverage is an
  explicit premise).
- `drain_preserves_reach`, `drain_reflects_reach`: freeing only zero-count
  values preserves and reflects reachability from roots.
- `ranked_drain_exact`: with a rank increasing along every edge, draining until
  every survivor has a root or a live holder leaves exactly the previously
  reachable values; `drain_exact` uses well-founded incoming edges instead.

Roots and edges are fixed during collection; "zero count" means no root and
no live holder. Counters, release side effects and weak bookkeeping are not
modelled; the drain and its termination are premises (existence for finite
acyclic heaps is `drain_collects`).

## Undecided

- The semantics needed to prove the Nib-to-constraint translation in Lean.
- How extern contracts are written.
