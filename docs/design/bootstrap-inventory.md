# Self-host implementation coverage

The Tauto compiler is implemented across Rust crates and Tauto totes. The totes are built and run by the Rust CLI and the self-host harness; the CLI does not currently compose them into a Tauto-implemented compiler. The component coverage below distinguishes Tauto implementations from Rust-only components and records the limits of each implementation.

## Component coverage

| Component | Rust implementation | Tauto implementation | Coverage |
|---|---|---|---|
| Lexing and parsing | `tauto-parol`, `tauto-syntax` | `scan`, `llk`, `syntax`, `grammar` | Tauto parsing is exercised by syntax cases. Rust still has a bootstrap parser for the initial declarations. |
| Grammar tables | `tools/tauto-parol-gen` | `llkgen` | Both generators produce grammar tables; Tauto behavior is checked by `llkgen` cases. |
| Surface representation | `tauto-surface` | `surface` | The surface tote is checked over the test corpus. |
| Macro expansion | `tauto-macro`, `tauto-surface::macros` | `macros` | Tauto covers syntax values, quote, and hygiene; expansion is implemented in Rust. |
| Imports and input bundles | `tauto-build`, `totebag` | `rustgen` bundle loader | The Tauto loader covers explicit bundles; it does not discover manifests automatically. |
| Proof elaboration | `tauto-kernel::check` | `elaborator` | The tote handles explicit `def` and `theorem` declarations, single-family `inductive` declarations with the no-confusion definitions (`nc`, `nc_diag`, `noconf`) the host derives for families without indices, total `fn` declarations, and `match` on a variable of an unindexed family with structural recursion through the eliminator, with implicit arguments solved by first-order matching. Nested constructor patterns, numerals, `true`/`false`, and a last `_ =>` are compiled into the same case tree of plain matches as the host builds. A match on an indexed family whose indices are distinct variables abstracts them in the motive, and a recursive call passes the field's indices. A match whose indices are not distinct variables generalizes them with equations, as the host does: each case solves them, an impossible case by the no-confusion of the index's family, the same constructor by equations between its injective fields, and the arm is transported back by `Eq::rec` (`Eq::ind` into `Prop`). A `mutual` block of inductive declarations is checked as one group, and a match on one of its families gives the other families the motive `Unit` and the cases `Unit::Star`, as the host does. A `mutual` block of functions that each match on the same parameter of an unindexed family is compiled as the host compiles an aligned group: one eliminator computes their values as nested `BelowPair`s, and each function is its component. A recursive call on a part deeper than a field (a field of a field, matched in the arm) is compiled as the host compiles it: the motive pairs each value with `below` of it, the values at its parts, by the family's eliminator into `Type`, and a match on such a part generalizes its `below`. A `def` or `theorem` whose leading implicit parameters are typed `Level` is a template, as in the host: it is checked once with its levels as variables and nothing is emitted, and a call that writes its levels as numerals is read as a call of the instance `f@1`, declared (and emitted) the first time a declaration calls it; `Type(u)`, `u + n` and `max` are levels. A template calls templates at its own levels, and their instances are declared first, in the host's order. An `inductive` with leading `Level` parameters is a template too: `UBox(1, …)` and `UBox::Ubox(0, a)` name the instance `UBox@0` and its constructors, which get the no-confusion definitions an ordinary family gets (without `noconf` where the kernel rejects it, as in the host). It rejects higher-order unification, a call of a template whose levels are not numerals, level variables, `l + n` or `max(l, l)`, a match on an instance of a level-polymorphic family, other mutual blocks of functions, a recursive call or a mention of the matched value in a match whose indices are not variables, index equations between a constructor and a term that is not one, variables whose types depend on the matched value, macros, effects, imports, and classes. |
| Proof checking | `tauto-kernel::check::core` | `kernel` | The Tauto kernel rechecks elaborated declarations emitted by Rust. |
| Proof extraction to Nib | `crates/tauto/src/extract.rs` | — | Rust only. |
| Nib type, row, and ownership checking | `tauto-nibcheck` | `nibcheck` | Tauto implementations are compared with Rust implementations by the self-host harness. |
| Intermediate representation and lowering | `tauto-nir`, `tauto-bind` | — | Rust only. |
| Rust code generation | `tauto-rustgen` | `rustgen` | Tauto supports an explicit subset of the source language; unsupported input is rejected. Tote sources are not covered by this subset. |
| JavaScript code generation | `tauto-jsgen` | — | Rust only. |
| Evaluator | `tauto-eval` | — | Rust only. |
| Formatting | `tauto::fmt` | `fmt` | Tauto formatter behavior is covered by cases. |
| Linter, analyzer, and LSP | `tauto-cli`, `tauto-analyzer` | — | Rust only. |
| Runtime | `tauto-rt` | — | Host adapter. |

## Compiler composition

There is no driver that connects the Tauto components into a compiler that processes its own source. The CLI uses Rust for parsing through code generation. The self-host harness builds individual totes with the Rust backend; it can also select the JavaScript backend with `TAUTO_SELFHOST_BACKEND=javascript`.

The `rustgen` tote accepts only its declared subset and rejects unsupported input without forwarding it to the Rust elaborator or code generator. The extraction, lowering, complete elaboration, and complete code generation stages do not have Tauto implementations.

## Verification coverage

The self-host harness compares component outputs with the Rust implementations. These comparisons cover the Tauto kernel, Nib checking, parsing, surface representation, formatting, and other tote-specific interfaces as listed in their cases. Component comparisons do not establish that a Tauto compiler can process its own source, nor do they verify the complete compiler pipeline.
