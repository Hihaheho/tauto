# Macro threat model

The design of [`macro.md`](macro.md), seen from the attacker's side.

## Assets

| | Asset | If broken |
|---|---|---|
| A1 | Soundness: accepted proofs are true; accepted programs' types, effects and ownership are right | false theorems, ownership corruption |
| A2 | The host running `tauto`: files, network, environment, processes, clock | exfiltration, tampering |
| A3 | Availability: checking terminates in bounded time and memory | hung checks, occupied CI |
| A4 | Reproducibility: same input, same expansion and verdict | cache poisoning, environment-dependent builds |
| A5 | Visible meaning: readers can see what a macro added | hidden axioms or behaviour |
| A6 | Generated tables and types come from the written grammar | parsing unlike the grammar |

## Threats

| | Attacker | Threat | Defence |
|---|---|---|---|
| T1 | malicious or compromised dependency author | macro reads or writes files, network, environment | restricted rows; the macro host answers no standard effect |
| T2 | same | output smuggles axioms or `extern`s | forbidden in output; kernels recheck |
| T3 | same | loops, huge output, memory exhaustion | budgets |
| T4 | author of DSL text | exploit the parser (deep nesting, huge input) | stack and input limits; safe-Rust driver |
| T5 | writer of a shared cache | plant expansion results | caches are local only |
| T6 | repository writer | commit tables that don't match the grammar | tables carry the grammar hash; CI runs `tauto syntax gen --check` |
| T7 | table generator supply chain | compromised generator | `totes/llkgen` runs only at generation, outside the compiler; output is regenerated and compared |
| T8 | macro author | output captures or impersonates user names | hygiene; capture only through explicit API, shown by `trace` and lint |
| T9 | macro author | generated code does dangerous things at runtime | **not defended**: it is a program like hand-written code; `expand` shows it |
| T10 | AI agent | unreadable proofs via typed macros in `std/` | lints `typed-macro-in-proof` and `macro-capture`, on for `std/` and `meta/` |

## Trust boundaries

| Component | Trusted for | If wrong |
|---|---|---|
| Kernels (`check.rs`, `check/core.rs`) | A1 for proofs | as without macros; both independent checkers must accept |
| `types.rs`, `rows.rs`, `lin.rs` | A1 for executed code | as without macros; rustc rechecks Rust output |
| Macro host (`tauto-macro-vm` and budgets) | A2, A3, A4 | intrusion or hangs. **The only component newly trusted for macros** |
| Grammar tables and driver (`crates/tauto-syntax`) | A6 | misparsing; output is rechecked, so A1 holds |
| `totes/llkgen` | A6 at generation | wrong tables, caught by regeneration |
| Macro functions | nothing | diagnostics or rejection |
| `extern "rust"` signatures | like axioms | as without macros; macros cannot generate `extern` |

### The macro host

The macro host answers no standard effect
([`host-effects.md`](host-effects.md)).

- Types: macro function rows are subsets of `{macro_error, macro_warn, elab, div, budget, budget_memory}`
  (the macro host counts a `budget`, one implementation, so an expansion does not depend on a backend);
  `fmt`/`tokens` functions registered on syntax have `div`, `divzero`, `overflow` and `macro_error`
  only. Host builtins are prelude `extern`s declared with rows
  (`Os::read_file ... ! {fs_read}`), so rows account for every path to the host,
  closures included. Registration rejects untraceable effects
  (`macro.unchecked_effect`) and effects outside the allowed set (`macro.row`).
- Runtime: a standard effect that slips through is not answered; calling an
  `Os::*` builtin is `macro.not_allowed_builtin`. Other builtins (`Ref`,
  `Atomic`, …) touch only values made in the call. Hash maps iterate in
  insertion order, independent of the host.
- Untyped macros run on the same host with the same limits.

Audit points for the macro host: every `builtin` arm touching host
resources is an `Os::*` with an effect in its row; hash order never affects
values, output or step counts; float arithmetic is deterministic (no fused
operations); panics become diagnostics (`catch_unwind`); no recursion on the
Rust stack.

### `include_text!`

`include_text!("path")` is the only language form that reads host files, and
it is not a macro.

- It reads only files of the calling file's tote (the nearest `Tauto.eure`'s
  directory, or the file's directory outside totes) and the directories its
  manifest lists in `package.include-from`, relative to the calling file. A
  listed directory counts only inside the workspace (the outermost directory
  above the tote that holds a `Tauto.eure`), so a tote fetched from elsewhere
  cannot reach files outside itself. Absolute paths, escaping `..` and
  symlinks resolving outside are errors; contents must be UTF-8.
- The loader (`crates/tauto/src/program/include.rs`) replaces only calls
  *written* in files, before expansion; one in macro output is
  `macro.include_text`. So a dependency's macro cannot read user files.
- The result depends only on the path and the file, which becomes a literal in
  cache keys and fingerprints; `tauto-build` emits `rerun-if-changed`.

### Other paths that run code

| Path | Runs | Authority | Relation to macros |
|---|---|---|---|
| tauto macros | Nib run on the bytecode machine of `tauto-vm` | no standard effects | this document |
| `extern "rust"` | generated Rust at runtime | the program's | macros cannot generate externs; no Rust runs during expansion |
| `tauto bind` | declarations from rustdoc JSON | developer command | output is committed and reviewed |
| `tauto-build` from `build.rs` | the whole compiler | Cargo build | macros are still confined to the macro host; a hole in it would reach `build.rs` authority, hence the audit |
| Rust proc-macros | native code in the compiler | everything | tauto never loads native code for macros |
| `tauto syntax gen` | `totes/llkgen` | developer command | committed with grammar hash; never runs during checking |

## Determinism

Expansion depends only on the macro function and what it reaches (normalized),
its argument values, the frozen environment and budget settings; never on time,
randomness, files, environment, threads, hash order or addresses. Scope numbers
come from positions and fresh names from expansion order. Where a budget runs
out may depend on the version of the machine, which is part of the cache key;
`trace` reports steps.

## Limits

The values are in [`macro.md`](macro.md).

| Limit | Prevents |
|---|---|
| steps per call and per file | loops, huge computations |
| depth | infinite self-expanding chains (reported) |
| output node count | checker overload (counted before lowering) |
| machine allocation | memory exhaustion |
| DSL input size: 1 MiB per syntax literal (`macro.input_too_large`) | parser exhaustion |
| parser stack depth 10⁴ (driver keeps its stack as data) | deep nesting |
| wall clock, 60 s default (`Interrupted`) | holes in step accounting; an error, never cached |

Failures are diagnostics: checking continues, and the declaration and its
dependents fail.

These limits bound what runs while checking. A parse the program runs on its
own data (a syntax's `parse` called at run time) has no input or stack limit:
the text is the program's input, not code the checker reads.

## Cache and generated files

- The macro cache is local (`target/tauto/macro-cache/`), keyed as in
  [`macro.md`](macro.md), storing output and records (steps, captures), and
  fingerprint-checked on read. A shared cache would need signed entries;
  rechecking protects A1 but not A5.
- `tauto syntax gen` runs `totes/syntaxgen` (calling `totes/llkgen`) and writes
  `.tauto-syntax/<sha256>.tables` holding the grammar's SHA-256, the generator
  format version, the tables and type generation data. `tauto check` verifies
  only the hash; CI regenerates and compares byte for byte. Never edit tables
  by hand.

## Visibility (A5)

`tauto check` reports, besides axioms and externs, the list of expansions
(macro, position, capture, whether it produced proofs).
`tauto macro expand --write` writes expansions back.
