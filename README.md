<picture>
  <source media="(prefers-color-scheme: dark)" srcset="https://raw.githubusercontent.com/Hihaheho/tauto/main/assets/logo-tauto-dark.svg">
  <source media="(prefers-color-scheme: light)" srcset="https://raw.githubusercontent.com/Hihaheho/tauto/main/assets/logo-tauto.svg">
  <img alt="Tauto" src="https://raw.githubusercontent.com/Hihaheho/tauto/main/assets/logo-tauto.svg" height="100px">
</picture>

# Tauto

*A minimal language for AI to build and prove correct software.*

[日本語](README.ja.md)

Tauto is a small formal language in which an AI writes the program and its
proof, and a human reads and verifies the propositions. What is accepted is
checked by a machine; what is written can be read where it stands.

It has a pure core derived from the Calculus of Constructions, deep multi-shot
algebraic effect handlers, nominal effects, ownership and borrowing, and
resumable execution under a shared step budget. Nib is the part without
dependent types and proofs; tauto is a conservative extension of it. The syntax
can be extended with grammars and macros whose expansions the kernel checks
again. Parts of the toolchain are written in Nib and compared with the Rust
implementation (see [Self-hosting](#self-hosting)).

This is an experimental source release: the Rust compiler and CLI, tools
written in Tauto, and the Lean formalization. The language and command-line
interface may change; this is not a stable release. Source files may use
`.taut` or `.tauto`; this repository uses `.taut`. The design documents are in
[`docs/design/`](docs/design/); if you come from Lean 4, start with
[`docs/guide/from-lean.md`](docs/guide/from-lean.md).

## A taste of the language

Effects and handlers ([`examples/handlers.taut`](examples/handlers.taut)): `ask`
may resume its continuation any number of times (`ω`), and a `budget` that runs
out can be resumed with more steps.

```
pub(open) effect ask(n: i64): i64 resume ω

let c := handle { perform ask(5) + 1 } with {
  ask(n), k => k(n) + k(n + 1)
  return v => v
}
let d := handle { budget(steps: 3) { 7 } } with {
  exceeded(info), k => info.more(100)
}
```

A proof is a term, or a step that writes the goal before and the goals after
it. The tactic is an untrusted macro; the kernel checks every goal written and
the term the tactic made ([`examples/nat/Mul.taut`](examples/nat/Mul.taut),
notation by the syntax macro `nat!`):

```
pub theorem mul_comm(n: Nat, m: Nat): nat!(`$n * $m = $m * $n`) {
  match m: nat!(`$n * $m = $m * $n`) {
    Zero => Eq::sym(mul_zero_l(n))
    Succ(k) => by rewrite!(mul_succ_l(k, n)): nat!(`$n * $k + $n = ${Succ(k)} * $n`) {
      ⊢ nat!(`$n * $k + $n = $n + $k * $n`) from by rewrite!(mul_comm(n, k)) {
        ⊢ nat!(`$k * $n + $n = $n + $k * $n`) from add_comm(k * n, n)
      }
    }
  }
}
```

## Targets

A checked program runs on a machine written in Tauto (`totes/vm`), on the
evaluator (`--backend eval`), or is compiled:

- **Rust** (`tauto build`, `tauto run --backend rust`): a Rust crate linked
  against `tauto-rt`, with no `unsafe`. See [Rust backend](#rust-backend).
- **JavaScript** (`crates/tauto-jsgen`; `tauto build --emit javascript`,
  `tauto run --backend javascript`): standalone ES modules; Node is the default
  target, and a browser loads the output as an ES module. See
  [JavaScript backend](#javascript-backend).
- **WebAssembly**, through the Rust backend built for wasm32
  (`tauto build --backend rust --target wasm32-wasip1` or
  `--target wasm32-unknown-unknown`). wasm32 has no threads, no reactor and no
  `net`; on `wasm32-unknown-unknown` the host effects answer nothing unless the
  embedder installs a host. See [`docs/design/rust-backend.md`](docs/design/rust-backend.md).

The limits of each backend are listed under [Limitations](#limitations).

## Ownership and memory

Values are `copy`, `shared`, `affine` or `linear`; the checker
(`crates/tauto-nibcheck`) checks moves, borrows and that a borrowed place is not
moved while it is lent. The Rust output has no garbage collector: values are
owned and dropped, and `shared` values are reference counted (updated in place
when uniquely owned). A function whose signature and locals mention no `shared`
type does no reference counting. In the JavaScript output the engine's garbage
collector reclaims memory, and the runtime keeps the owners, the drop order and
the release of resources by counting references
([`docs/design/javascript-backend.md`](docs/design/javascript-backend.md#runtime-and-validation)).
See [`docs/design/ownership.md`](docs/design/ownership.md).

## Design principles

Tauto is a language for AI to write and for people to check. What is accepted is
checked by a machine, and what is written can be read where it stands. A few
orthogonal concepts (full dependent types, algebraic effects and ownership) carry
the language. Soundness comes before convenience: every declaration the kernel
accepts is checked again by an independent nameless kernel, and new syntax
expands to terms the kernel already takes, with no new rule. Explicitness comes
before brevity: nothing the reader cannot check on the spot is left to inference
(no motive-inferring rewrite, no `_` holes; implicit arguments only by
first-order matching, class instances found from the head constructor of a type,
one per type). A named hole `?h` marks an unfinished proof and is never accepted;
there is no `sorry`. A proof is a term or a step that writes the goals before
and after it. There is one way to write each thing, and dependencies and
execution are distrusted by default.

## Prerequisites

- Git, and Rust installed with rustup. `rust-toolchain.toml` pins a dated
  nightly toolchain, which rustup installs on first use. The nightly is needed
  because `.cargo/config.toml` enforces a publish-age cooldown on crates and
  passes `-Znext-solver=coherence`.
- Network access for the first build: Cargo fetches the locked dependencies,
  including [Eure](https://github.com/Hihaheho/eure) from a pinned Git revision.
- Optional: Node for the JavaScript backend, `rustup target add wasm32-wasip1`
  (or `wasm32-unknown-unknown`) for Wasm, and Lean 4.34.1 for the formalization
  ([`lean/README.md`](lean/README.md)).

## Quickstart

```bash
git clone https://github.com/Hihaheho/tauto.git
cd tauto
cargo install --locked --path crates/tauto-cli
tauto run examples/handlers.taut    # prints what it `show`s
tauto check examples/proofs.taut    # the kernel checks the theorems
```

Keep the checkout for the examples and library sources. See
[examples](examples/README.md) for larger programs and integrations.

## Repository layout

- `lean/`: the Lean 4 formalization (reference semantics); see
  [`lean/README.md`](lean/README.md).
- `crates/tauto`: the public entry points, source loading, formatting, linting,
  reporting and extraction. It re-exports the implementation crates below,
  keeping paths such as `tauto::check` and `tauto::surface`.
- `crates/tauto-surface`: shared surface terms, parsing, syntax values and scope.
- `crates/tauto-nibcheck`: types, effect rows and ownership checking.
- `crates/tauto-eval`: the evaluator and its execution budget.
- `crates/tauto-macro`: macro expansion with injected checking services.
- `crates/tauto-kernel`: named elaboration and the independent core checker.
  The Rust module names mirror the Lean modules. The dependency boundary
  is described in [`rust-layers.md`](docs/design/rust-layers.md).
- `crates/tauto-cli`: the `tauto` command, including `tauto lsp`.
- `crates/tauto-cli-totes`: the totes the `tauto` command runs (the bytecode
  machine and the table generator), compiled to Rust when the command is built.
  Each tote is compiled by a crate of its own (`crates/tauto-cli-tote-<name>`),
  so the totes are compiled side by side and only a changed one again.
- `crates/tauto-vm`: a bytecode machine that runs checked Tauto programs.
- `crates/tauto-cache`: the build cache: what build steps made, kept under what
  they were made from.
- `crates/tauto-message`, `crates/tauto-messages`: message ids with their
  arguments, and their text in each language, written by the tote `totes/fluent`;
  `crates/tauto-messages-gen` writes `crates/tauto-messages/src/fluent.rs` again
  from that tote.
- `crates/totebag`: the totes a tote depends on, fetched from Git and fixed by
  content in `Tauto.lock`; `crates/totebag-gen` writes its `src/core.rs` again
  from `totes/totebag`. `crates/totebag-index`: the checked core of the
  distributed index, compiled from `totes/index`.
- `crates/tauto-analyzer`: the checker that keeps its work between edits, with
  the editor features on top of it (`navigate`, `assist`, `editor`). `tauto lsp`
  uses it, and so can a tool that edits proofs
  ([README](crates/tauto-analyzer/README.md)).
- `crates/tauto-analyzer-wasm`: that checker compiled to WebAssembly, for an
  editor in a browser: `goals`, `try`, `fill` and `suggest` on files held in
  memory ([README](crates/tauto-analyzer-wasm/README.md)).
- `crates/tauto-parol`: the grammar (`tauto.par`) and its generated parser.
- `crates/tauto-syntax`: the runtime of `syntax` grammars (scanner, LL(k)
  and LALR(1) drivers), read from table files made by `totes/llkgen` and
  `totes/lalrgen`. `crates/tauto-syntax-wasm` is that runtime compiled to
  WebAssembly for the JavaScript backend.
- `crates/tauto-nir`, `crates/tauto-rustgen`, `crates/tauto-rt`,
  `crates/tauto-build`: the Rust backend. `crates/tauto-jsgen` is the
  JavaScript backend. `crates/tauto-bind` is `tauto bind`.
- `cases/`: Eure case files that specify what the implementation answers, for
  tauto and for Nib alike; `tools/tauto-test-suite` runs them. The
  [case format](docs/design/test-suite.md) covers inputs and assertions.
- `tools/selfhost-harness`: tools to build, run and verify compiler components
  written in Tauto, including differential tests against their Rust counterparts.
- `std/` and `meta/`: the proof-language library and the proofs about object
  languages, described below. `std/prelude/` is the part every program sees
  without an import (data, effects, host functions). The kernel reads it too:
  its `enum`s and `struct`s shared with proofs become inductive families, and
  `std/prelude/Ord.taut` is checked in full by both kernels, with no axiom
  other than `Quot::sound` and no hole (`kernel_prelude` in
  `crates/tauto-kernel/src/check.rs`). Built-in types and their instances in
  `std/prelude/Classes.taut` are trusted, not proved.
- `totes/`: the parts of the toolchain written in Nib or in the proof language.
- `examples/`: small programs (`handlers.taut`, `effects.taut`,
  `ownership.taut`, `proofs.taut`), natural-number proofs (`nat/`), the simply
  typed lambda calculus with type safety and strong normalization (`lambda/`),
  verified programs that run (`sort/` and `bst/` for any `Ord` type, `compiler/`,
  `calc/`, `regex/`, `wf/`), and Rust and JavaScript interop demos (`rust/`,
  `javascript/`); [`examples/README.md`](examples/README.md) says where to start.
- `docs/design/`: the design documents: Nib ([`nib.md`](docs/design/nib.md),
  [`semantics.md`](docs/design/semantics.md), [`ownership.md`](docs/design/ownership.md),
  [`classes.md`](docs/design/classes.md), [`shared-levels.md`](docs/design/shared-levels.md),
  [`float.md`](docs/design/float.md)),
  proofs about functions with effects ([`effect-proofs.md`](docs/design/effect-proofs.md)), macros ([`macro.md`](docs/design/macro.md) and
  the `macro-*.md` beside it), [`rust-backend.md`](docs/design/rust-backend.md),
  [`javascript-backend.md`](docs/design/javascript-backend.md),
  [`self-host.md`](docs/design/self-host.md) and [`lean.md`](docs/design/lean.md).

## Development

```bash
scripts/test.sh full
scripts/test.sh focused -p tauto-build --test build_rs
scripts/test.sh focused -p tauto-test-suite --test cases -- <filter>
# Lean 4.34.1; see lean/README.md for the pinned install
(cd lean && ELAN='' LAKE_OVERRIDE_LEAN=false ../.tools/lean-4.34.1/bin/lake --keep-toolchain --no-cache build)
```

The full gate runs the locked workspace suite, checks `meta/KernelSafe.taut`,
and checks formatting of `std/` and `meta/`. The focused tier runs only the
selected tests and does not establish a full pass. Grammar regeneration and
Lean verification are required when those sources change. `scripts/test.sh`
keeps a build directory per checkout (`TAUTO_TEST_CACHE_ROOT` selects a shared
root); the caches of the toolchain itself are described in
[`docs/design/build-cache.md`](docs/design/build-cache.md).

## Using tauto

```sh
cargo run -p tauto-cli --bin tauto -- run   examples/handlers.taut   # prints what it `show`s
cargo run -p tauto-cli --bin tauto -- check examples/proofs.taut     # the kernel checks theorems
```

The other commands, each described below:

```sh
tauto init [PATH]                         # a local tote without overwriting files
tauto add --git URL [NAME] | --path DIR   # depend on a tote; Tauto.eure and Tauto.lock together
tauto remove NAME | update [NAME…] | lock [--check] | fetch | deps  # the totes a tote depends on
tauto index sync | status | check | new | observe | decide | publish  # the indexes Trust.eure trusts, and one's own
tauto fmt [--check] FILE…                 # formatter
tauto lint [--json] [--fix] PATH…         # files, or the .taut files under a directory; rejects holes and other things std/ and meta/ avoid; --json: [{file, line, col, message, kind}]; --fix: writes the import lists and the `=> …` lists
tauto extract FILE…                       # the Nib that `run` makes of the programs, for reading
tauto goals | try | fill | suggest | expand | library FILE …  # proofs a step at a time
tauto test [PATH] [--filter TEXT] [--json] # the perform test statements in the sources
tauto bench PATH [OPTIONS]                # release binary whole-process wall time
tauto doc PATH [-o DIR]                    # highlighted, linked source pages as HTML
tauto build [--release] [-o DIR] FILE     # compile to Rust (also a tote directory)
tauto bind CRATE --config FILE            # declarations for a Rust crate
tauto syntax gen | show | source          # the table files of `syntax` grammars
tauto macro expand | trace | inspect FILE # what macros wrote
tauto lsp                                 # language server on stdin and stdout
```

The messages of the command are in the user's language: `--lang LANG` (`en`,
`ja`), else `$TAUTO_LANG`, else `lang = "ja"` in `~/.config/tauto/config.eure`
(`$XDG_CONFIG_HOME/tauto/config.eure` when set), else `$LC_ALL`,
`$LC_MESSAGES` or `$LANG`, else English. A message is an id and its
arguments (`crates/tauto-message`); its text in each language is in
`crates/tauto-messages/locales/LANG/*.ftl`, written by the tote
`totes/fluent` compiled into `tauto-messages`. A message missing from a
language is shown in English. The command's own messages are there; a
diagnostic a library writes as text rather than as a message is in English.

The [initialization command](docs/design/init.md) creates a local tote without
invoking build tools or resolving dependencies.

The [test command](docs/design/test.md), [benchmark command](docs/design/bench.md),
and [local documentation command](docs/design/doc.md) describe discovery, execution,
measurement boundaries, and output safety. Benchmark warmups and samples repeat
program effects; compilation is outside the timed samples.

Source reading and expansion live in `crates/tauto/src/read.rs`; the public
module paths combine these adapters with the implementation modules
([Rust layers](docs/design/rust-layers.md)).


### Type errors

A type mismatch prints the expected and the found type, then the innermost
part that differs (`theorem wrong(): Eq(Nat, 3, 4) { Refl(Nat, 3) }`):

```text
FAILED  wrong: wrong.taut:1:34: type mismatch: expected `Eq(Nat, 3, 4)`, found `Eq(Nat, 3, 3)`
  differing part: expected `4`, found `3`
```

When the statement came from a syntax macro, the message also says how it was
written (``expected is written as math!(`1 + 2 = 4`)``), and a diagnostic inside
an expansion names the macro that wrote it. Positions in a macro's output point
at the call.

### Writing a proof a step at a time

A hole `?name` stands for a term not written yet, wherever an expression is
(a `match` arm, an argument, the body of a block). The kernel reports it and
accepts nothing that holds one: the declaration is *incomplete*, is never given
to `crates/tauto-kernel/src/check/core.rs`, and whatever uses it is incomplete too. There is no
`sorry`; `tauto lint` rejects a hole, so `std/` and `meta/` have none.

```sh
tauto check [FILE|DIR] [--json] [--verbose] [--summary] # each problem as an annotated snippet, then `ok` when all checked; no path: the tote of the working directory; --summary: the counts and the axioms; --verbose: a line per declaration; exit 0, 3 (only holes left), 1
tauto goals FILE [--hole NAME] [--json] # the variables in scope and the goal `⊢ T` of each hole
tauto try   FILE --hole NAME --with EXPR [--json]  # the file with EXPR for ?NAME, checked, not written
tauto fill  FILE --hole NAME --with EXPR [--json]  # the same, written back when the declaration is not rejected
tauto suggest FILE --hole NAME [--limit N] [--json] # hypotheses and constants whose type fits the hole
tauto expand  FILE --hole NAME --by intro|match(x)|induction(x)|'NAME!(arg)' [--write] [--json]  # a skeleton, with holes
tauto library FILE [--json]            # the constants a proof may use, with their types
tauto assumptions FILE [NAME] [--json] # per declaration: the axioms it rests on, the extern functions it reaches, its holes; exit 0, 3, 1 as check
tauto elaborate FILE [NAME] [--json]   # the term the kernel checks for each body: implicit arguments, instances and motives written out
tauto proof FILE [NAME] [--format block|node|tree|tree-html|natural|json] [--full] [--output FILE] # read-only proof views; natural is the default
tauto proof-status [PATH] [--json]     # counts over the .taut files under PATH: ok, incomplete, holes, failed, axioms used, externs
tauto eval  FILE EXPR                  # EXPR in normal form after FILE's declarations, and its type (a `Text` also as its characters); only shown, a proof states it as a `Refl` theorem
```

`--json` gives `{status, declarations, holes: [{name, declaration, file, line,
col, end_line, end_col, goal, goal_term, declaration_type,
declaration_type_term, context: [{name, type, type_term, kind, origin}],
unresolved_metas}], errors}`. Every type is given twice, as the text a proof
writes (`goal`) and as a tree (`goal_term`: nodes `var`, `nat`, `app` with
`function` and `arguments`, `pi`, `lam`, `exists`, `hole`, …; an operator is an
`app` of its name), so a client need not parse the text. `origin` says whether
a variable of the context is a `parameter` of the declaration, a `local` (a
`let` or a pattern bound it) or an `induction_hypothesis`: such a hypothesis
has a generated name, and a proof reaches it by calling the theorem on the
matched field. A hole is not read where a type is written. A goal that
mentions an implicit argument that nothing else fixes is reported as such, the
unknown listed in `unresolved_metas` as `?name`, not guessed. A hole keeps its
name while the others are filled; `try` and `fill` list the `closed_holes` and
the `new_holes` of the candidate.

`suggest` lists terms that fit the hole by the shape of their types: a
hypothesis of the goal's type, or a constant whose result matches the goal
(the generics fixed by the match), applied to a hole for each premise it
leaves, `AndIntro(?top_a, ?top_b)`. Each has `term` (what `try` takes),
`exact` (no premise left), `arguments` (each premise's hole and type, with
`unresolved_metas` for an unknown the goal did not fix) and `generic` (the
result is a bare unknown, as in `False::elim`, so it fits any goal and is
listed last). It is a guess from the types alone; `try` is what the kernel
says. `expand --by intro` binds the argument of a function-typed goal;
`--by match(x)` (`induction(x)` is the same, a call of the theorem on a
recursive field being the hypothesis) writes an arm for each constructor of
`x`'s type, naming the new holes `<hole>_<constructor>` (`<hole>_body` for
`intro`). `--by 'rewrite!(e)'` writes a step (below) with an arm for each
goal the tactic leaves, naming the holes `<hole>_1`, `<hole>_2`, …. It checks
the result as `try` does and writes it back only with `--write`. `library` lists every constant with its `kind` (`theorem`, `axiom`,
`def`, `inductive`, `constructor`, `eliminator`), `type` and `type_term`,
`implicit` (how many leading generics a call leaves out) and `state`.

A proof may also be written as steps that say their goals. A step is
`by t!(arg): G0 { Δ ⊢ G from p … }`: the tactic `t` makes a term of the goal
`G0` and leaves a goal for each arm, with the variables `Δ` it adds; each arm
proves its goal with any term, another step or a hole. The goals written are
compared with the place's goal and with the ones the tactic left, up to
computation, and the step becomes `the(G0, …the(G, p)…)`, so the kernel checks
every goal written and trusts nothing the tactic made. A step that is the whole
proof of an arm leaves out `: G0`, the arm's goal being it. `std/Rewrite.taut`
has `rewrite!(e)` (`std/Tactic.taut` adds `nat_norm!` and `nat_le!` and imports `Base`), for `e: Eq(A, l, r)`, whose arm's goal is the goal with
`r` for `l`. The step of `Nat::add_comm` in `std/Nat.taut`, as written in
[`docs/design/macro-steps.md`](docs/design/macro-steps.md):

```
Succ(k) => by rewrite!(Nat::add_comm(a, k)): Succ(Nat::add(a, k)) = Nat::add(Succ(k), a) {
  ⊢ Succ(Nat::add(k, a)) = Nat::add(Succ(k), a) from by rewrite!(Nat::add_succ_left(k, a)) {
    ⊢ Succ(Nat::add(k, a)) = Succ(Nat::add(k, a)) from Refl
  }
}
```

`nat_norm!()` proves an equation of `Nat::add`, `Nat::mul`, `Succ`, `Zero` and
numerals, whatever else is a variable (`std/NatNorm.taut`): it reads the two
sides as expressions, and the kernel checks that they have the same normal form
by a normaliser proved sound in Tauto; it leaves no goal, so its arm list is empty.
`nat_le!()` proves `l <= r = true` and `l < r = true` for such expressions when every term
of the normal form of `l` is matched by a term of `r` with the same monomial and a
coefficient that is not smaller (hypotheses are not used); the kernel checks that by
computation, again against a theorem proved in Tauto.

A tactic is a macro whose function takes a `ProofStep` (below); `std/` and
`meta/` call only std's (`tauto lint`). The design is in
[`docs/design/macro-steps.md`](docs/design/macro-steps.md).

An entry of `errors` has the position of the part at fault (`line`, `col`,
`end_line`, `end_col`), a `code` (`type_mismatch`, `too_many_arguments`,
`cannot_infer`, …) and the `message`. A `type_mismatch` also has `expected`
and `found` (as text and as `expected_term` and `found_term`) and, when the
two compare part by part, `differing` with the innermost parts. When the
expected type of a call fixes what an argument must be, the position is that
argument's and `argument` names the call and which argument.

`tauto check` also warns of code that is never used or never runs, in the
file it checks (a tote's own files with `--tote`): a `let`, `var` or local
function nothing reads (`unused_binding`, `unused_function`), a statement after
a `return` (`unreachable_code`), and, in a file that runs alone, a top-level
function or a parameter nothing uses and an `import` nothing is used from. In a
program, a `match` arm that the arms before it already take every value of is
`unreachable_arm`. A name that starts with `_` is not reported. A line reads
`warning CODE: FILE:LINE:COL: message`, and `--json` lists them under
`warnings` with the same fields as an error; a warning does not change the
status or the exit code. The arms no value reaches and the statements after a
`return` are not lowered to NIR, so no backend writes them; a function nothing
calls was already never lowered.

### Proofs written in tauto

`std/` holds generic data and lemmas:

- `Std.taut`: `Option`, `List`, `Pair` and `Ordering` are the prelude's `enum`s and `struct`, which proofs read as families; a `Pair` is written `#(a, b)`, and its type `A × B`.
- `Base.taut`: decisions and `Nat` arithmetic; extraction maps `Nat` onto Nib's unbounded `nat`. `Nat.taut`: its laws (associativity, commutativity, distributivity, order).
- `List.taut`: folds, filters, ranges, zips, `reverse_reverse`, `take`/`drop`, …; `Data.taut`: `Option` and `Pair` functions.
- `Text.taut` and `TextOps.taut`: bytes, slices, prefixes, search, split and join. `Array.taut`.
- `Bytes.taut`: byte sequences as a list of `U8`, which extraction maps onto Nib's `Bytes`, whose slices share their storage; UTF-8-checked conversion to and from `Text`.
- `Stack.taut`: a stack that extraction maps onto Nib's `Vec`.
- `UInt.taut`: `U8`, `U32` and `U64`, a `Nat` below `2^w`, which extraction maps onto Nib's `u8`, `u32` and `u64`, with arithmetic that takes a proof that the result fits, returns `None` when it does not, performs `overflow`, or wraps modulo `2^w`.
- `Int.taut`: integers, as a `Nat` or the negative of one's successor. `SInt.taut`: `I32` and `I64`, an `Int` in `-2^(w-1) .. 2^(w-1)`, mapped onto Nib's `i32` and `i64`, with the same checked arithmetic but no wrapping.
- `Row.taut`: membership.
- `Ord.taut`: `Ord(Nat)`. The class `Ord` and its instances for `List`, `Option` and `Pair`, with their laws, are in the prelude's `std/prelude/Ord.taut`, which programs and proofs both read.
- `Sort.taut`: insertion sort by a comparator: sorted, a permutation of its input in membership and length, unchanged on sorted input.
- `Map.taut`: an AVL ordered map, with its laws in `MapLaws.taut`, `MapRemoveFloor.taut` and `MapText.taut`; `Set.taut`: an ordered set over that map.
- `HashMap.taut`: `Hmap` and `Hset`, a persistent hash map and set (buckets of entries in an ordered map keyed by the hash).
- `Deque.taut`: a double-ended queue of two lists; `Heap.taut`: a priority queue (a leftist heap).
- `Quot.taut`: on the kernel's quotient `Quot(A, r)`, whose classes a function reads with `Quot::lift` and a proof that it respects `r`: lifting over two quotients, exactness for a relation decided by a function, and function extensionality, which rests on the prelude's one axiom `Quot::sound`.

`meta/` holds models of object languages and the proofs about them (the core calculus, the kernel, effects, typing). `meta/` imports `std/`, never the reverse.

`meta/Core.taut` is the Lean file `lean/Proto/Core.lean` re-done in
tauto: terms, renaming and substitution, typing, and the preservation,
progress and type-safety theorems, checked by the kernel with no axioms
(`cargo test -p tauto --test tauto_lib`). [`docs/design/lean.md`](docs/design/lean.md) says what is
proved in tauto and what is proved in Lean (the soundness of the kernel itself). `meta/Kernel*.taut` models the kernel's core and proves its
confluence and subject reduction, and a checker for it that returns typing
derivations; `crates/tauto/tests/kernel_diff.rs` checks the Rust kernel against
that model on generated terms. `def name(params): T := <type>` defines a type or proposition.

### How the kernel checks

`run` checks the program's value types (`crates/tauto-nibcheck/src/types.rs`) and
effect rows (`rows.rs`), then evaluates it with deep multi-shot effect
handlers and `budget` (`docs/design/semantics.md`), printing what it shows with
`perform show(name, v)`. `check` type-checks `theorem`, `axiom`, `inductive` and
fully typed pure `fn` declarations with a bidirectional dependent-type kernel
over the shared surface AST (`crates/tauto-kernel/src/check.rs`): sorts `Prop`,
`Type`, `Type1`, …; conversion up to beta, delta and literal arithmetic; a
proof's axioms are listed; inductive families get a strict-positivity check.
A sort's name (`Prop`, `Type`, `TypeN`) and `_` never name a declaration or a
variable (`_` binds nothing), and a declaration that uses one that did not
check fails too. Every declaration the kernel accepts is checked again by
`crates/tauto-kernel/src/check/core.rs`, an independent checker over locally nameless terms (bound
variables are de Bruijn indices, so no name can be captured) with its own
reduction, conversion, typing and reading of inductive declarations; a
declaration is added only if both accept it.
Two proofs of the same proposition are convertible (proof irrelevance), in
both checkers: the comparison without types runs first, and only when it fails
are the terms compared again with the types of their parts (the type of an
application's head gives the type of each argument, a function's type the type
of its body), so a proof inside a type, a function or a dependent argument is
seen as one. `Prop` still eliminates into data only through the subsingleton
rule above, so no data comes out of a proof
([`cases/check/proof-irrelevance.eure`](cases/check/proof-irrelevance.eure)).
The constants proofs may use (`Eq`, `And`, `Or`, `Not`, `Iff`, `nat_ind`, …)
are in `crates/tauto-kernel/src/prelude.taut`.

### What the kernel does with inductive types

A constructor's name starts with an uppercase letter, and a family or a
constructor without parameters is written without parentheses, in its
declaration and where it is used: `inductive Nat: Type { Zero: Nat
Succ(n: Nat): Nat }`, `Refl`, `Nil`. The one exception is `Bool`, whose
constructors are the literals `false` and `true`, so that `True` and `False`
stay the names of the propositions.

`inductive` declarations are checked (strict positivity, constructor
universes, the family's parameters, which every recursive occurrence must
use unchanged) and their eliminators are **generated**:
`I_ind` into `Prop`, `I_rec` into `Type1`, with the iota rule. A family in
`Prop` eliminates into data only if it has no constructor, or one whose
fields are proofs or appear in its indices (so `Eq`, `And`, `True`, `False`
do and `Or` does not). `Nat`, `Bool`, `Eq`, `And`, `Or`, `Not`, `Iff`, `True`,
`False`, `Unit` and `BelowPair` are such declarations in the prelude, and `Eq::subst`,
`And::left`, `Or::elim`, … are theorems proved from the generated eliminators.

A program's own type becomes one of these by writing `inductive` before it:
`inductive enum Route { Home, Post(u64) }` and `inductive struct Pt { x: u64, label: Text }`
run as written, and the kernel is also given the family of the same name and
constructors (a positional field is `_0`, `_1`, …; a struct is built and matched as
`Pt { … }`), with the proof side's families of the field types (`u64` is `U64`, `Bool`
is `Bool`, `nat` is `Nat`). The functions on it are then checked, and theorems about them
are theorems about the program. A field that holds a function is an error, and so is
a field the kernel has no type for (`i16`, a plain `enum`); a plain `struct` or `enum`
stays a program's type only ([`docs/design/program-data.md`](docs/design/program-data.md)).

`⊢ T from match x { c(a) => e … }` on a parameter is compiled to the eliminator
with an explicit motive (`T` may mention `x`), and a call on a field of the
matched value becomes the induction hypothesis. The motive generalizes the
other parameters, so a recursive call may change any of them except those the
type of `x` mentions (the parameters of its family). A call may also be on a
deeper part, a field of a field matched in the arm (`Cons(a, Cons(b, rest)) =>
f(rest)`): the function is then compiled with a motive that pairs each value
with the values at its parts (`And`, or the prelude's `BelowPair` for data),
for a single family that eliminates into types and whose indices are
variables. The match may be applied to arguments that its motive
generalizes, `(⊢ (H) -> G from match x { c(a) => h => … f(a, h2) … })(h)`; a
recursive call is then the induction hypothesis applied to them. A
recursion on another parameter than the one matched names it with
`decreasing_by y` (on a `fn` or a `theorem`): the body becomes a `match y`
with one arm per constructor, and a `match y` inside it takes the arm of that
constructor, so the function may first match on other parameters (fuel,
`match x { … match fuel { Succ(k) => f(k, …) } }`). Any other recursion is
rejected unless the function says why it terminates (below). A function that is effectful, executable (blocks, `var`,
`perform`, `handle`) or unchecked is skipped and is *not in scope for proofs*.

### Well-founded recursion

`fn f(x: A, p: P): B decreasing_by W => theorem f_eq { … }`, with `W` a `WfRel(A)` (a relation
on `A` and the proof that it is well-founded, `std/WellFounded.taut`; `measure(g)`
for a `g: (A) -> Nat` compares the numbers `g` gives), recurs on the first parameter
along that relation, and the parameters after it may change in the call. A recursive
call `f(y, q, h)` ends with a proof `h` that `y` is below `x`; nothing is inferred.
The kernel gets no rule for it: before anything is checked, the declaration becomes
`f@step` (the body, with the values at the predecessors as a parameter), `f` (that
step under `wf_fix`, which is `Acc_rec`) and `f_eq`, the unfolding equation
(`crates/tauto-kernel/src/check/wf.rs`); the declaration lists `f_eq` after the relation (`=> theorem f_eq`), and the
list must be what it makes. `f` does not compute where the proof of well-foundedness is a
theorem, so a proof about `f` rewrites with `f_eq` and lets `match` compute the rest
(`examples/wf`). A program that is run or extracted reads the declaration as
written, with the proofs left out of the calls. Functions are equal to their eta
expansions in both kernels, which `f_eq` needs for a function of several parameters.

### Universe polymorphism

A `theorem` or `def` may begin its generics with `Level` parameters:
`theorem id<u: Level, A: Type(u)>(x: A): A { x }`. It is a template, not a constant. A
use writes the levels first, `id(1, Nat)`, and is read as a use of `id@1`, the
declaration with `u := 1`, which is declared the first time it is asked for and checked
by both kernels like any monomorphic one. The kernels get no rule for levels, so a
polymorphic declaration proves exactly what its instances prove; the template is also
checked at level `0` where it is written. Levels are numerals (`0`, `1 + 1`,
`max(1, 2)`); they are not inferred, and `Level` is not a type a term can have
(`crates/tauto-kernel/src/check/universe.rs`). Standalone inductive declarations also accept leading
`Level` parameters; constructors and eliminators take the same explicit levels.
`recursor(Family, level)` selects a checked motive universe without reinterpreting
ordinary numeric parameters. Numeric specialization has explicit bounds and
syntax restrictions; see [universe specialization](docs/design/universes.md).

### Implicit arguments, `cases`, mutual and nested types, modules

* **One way to apply.** A type is applied as a function is, in types and in
  terms alike: `Eq(Nat, plus(n, 1), m)`, `List(Nat)`, `Eq((Nat) -> Nat, f, g)`.
  An argument is any expression (or a function type), so it needs no braces.
  `Eq<Nat, {plus(n, 1)}, m>` still parses, but is rejected with the call to
  write instead. Messages print terms the same
  way. `<…>` only declares generics: `theorem sym<A, a, b>(…)`.

* **Implicit arguments.** The generics of a declaration (`theorem sym<A, a, b>(e: …)`)
  and the parameters of an inductive type in its constructors and
  eliminators are implicit: a call that leaves them out has them inferred by
  first-order matching against the explicit arguments (functions last) and
  then the expected type. A call that writes every argument still works, and
  the elaborated term always has every argument, so the kernel never sees an
  implicit one. A bare `Nil` or `Refl` is such a call. A constructor may
  have generics too (`cv_trans<x: KTm, y: KTm, z: KTm>(h1: KConv(x, y), h2:
  KConv(y, z)): KConv(x, z)`): a call writes `cv_trans(h1, h2)`, and a pattern
  lists either every field or only those after the generics. A recursive call
  may leave the generics out; they are inferred like any other call's.
* **`match` on an indexed family unifies the indices.** `match v { Vcons(k, h, t) => h }`
  on `v: Vec(A, Succ(n))` needs no `Vnil` arm: the index `Zero` against
  `Succ(n)` is impossible, by *generated no-confusion* (`I_nc`, `I_nc_diag`,
  `I_noconf` for every index-free inductive type in `Type`, built from its
  eliminator and checked). Constructors are injective, and a variable the
  equations fix is replaced, the arm being transported back with `Eq_rec`
  (`Eq` reduces on `Refl` and, as in Lean, whenever both sides are
  convertible). Any variable in scope may be fixed, a parameter before the
  matched value included (`Klam(b) = f` fixes `f`), as long as the term it is
  fixed to does not mention a variable whose type depends on it. The matched
  value is cast along the equations where the goal mentions it, and a call on
  a recursive field is its induction hypothesis, as in any match. Indices must
  be constructor terms or variables; a stuck index (`plus(n, m)`) is reported,
  not guessed.
* **Nested patterns.** `Succ(Succ(m)) => …` and `Kapp(Klam(b), a) => …` are
  read as a `match` on the field inside the constructor's arm, whose result
  type is the arm's goal, so the arms form an exact case tree of plain matches
  that are compiled and checked as if written by hand. A field one arm splits
  must be split by every arm that reaches it, and arms that overlap are
  rejected rather than ordered. The one exception is a last `_ => e`: it is
  put in every case of the tree that no other arm reaches
  (`Cons(pad(), Nil) => a` then `_ => b`), and must reach at least one.
  A numeral `n` in a pattern on `Nat` is the nested pattern
  `Succ(…Succ(Zero))` (`34 => a` then `_ => b`); a numeral above 1024 is
  rejected, since its case tree is `n` matches deep.
* **Default arm.** A plain `match` may end with `_ => e`: it stands for each
  constructor no arm names (with its fields unnamed, so it recurses on
  none), as if that arm were written out. It must be the last arm and stand
  for at least one constructor; with indices, a constructor they rule out
  needs no arm. `std/` and `meta/` do not use it (`tauto lint`).
* **Where a `match` needs no result type.** `match x { … }` without `-> T`
  takes its type from where it is written: a declaration's body, an arm's
  body, the body of a λ whose type is known, or an argument of a call. For an
  argument, the other arguments (those without a `match`) and the type the
  call is expected to have fix the generics first, and the parameter's type is
  then the `match`'s result type, and gives a λ there the types of its
  parameters: `Or::elim(p, y => match y { AndIntro(a, b) => b }, h => h)`,
  `OrInl(match p { AndIntro(a, b) => b })`. An argument that fixes no
  generics by itself (`Refl`) is left out like a `match`, so a λ before it
  still gets its parameter's type from the arguments after it. A type written
  on a λ's parameter, `(z: Bool) => …`, is that parameter's type wherever the
  λ is written. `match e eqn h { … }` is written there in the same way.
  A declaration's type may hold a `match` on its parameters, as in
  `theorem t(a: Bool): match a { … } = flip(a)`; it takes its result
  type from where it is written in the same way.
* **`let` in proofs.** `{ let h: x = y := p … value }` names an
  intermediate proof or value with its type. The type is required and is
  checked where it is written (`h` stands for `the(T, p)`, the prelude's
  annotated identity, so the kernel sees no new construct); a `let` that is
  not used is rejected, since its type would never be checked.
* **Mutual inductive types and functions.** `mutual { inductive … inductive … }`
  gets one eliminator per family whose motives and minor premises cover the
  group; `mutual { fn … fn … }` defines the members together by `match`, a
  call between members on a field being the induction hypothesis. Several
  members may match on the same family: its motive is the tuple of theirs.
  A member whose body is not a `match` (one that calls the others) is written
  out at each of its calls in the matching members and declared after the
  group; such members may not reach themselves without going through a `match`.
* **No-confusion for groups.** It is generated for every member of a mutual
  or nested group too (the other members get trivial motives), so a `match`
  can invert an index such as `Tperform(e, args)` of a mutual indexed family.
* **Nested inductive types.** `inductive Tree { Node(x: Nat, cs: List(Tree)) }`
  makes `List(Tree)` a member of the group (its constructors are `List`'s, so
  there is no copy and no isomorphism to prove). Recursion is a `mutual`
  block over `Tree` and `List(Tree)`. Nesting is limited to types without
  parameters and to plain (index-free, non-mutual) types such as `List` or
  `Option`; the instantiated constructors are checked for positivity, so
  `Fn(Bad)` with a negative parameter is rejected.
* **Formatter.** `tauto fmt [--check] FILE…` lays a file out again without
  changing a token: two spaces per enclosing `{`, one way of spacing, and a
  line longer than 100 characters broken at its outermost bracket that does
  not fit, one argument per line. A line with a comment inside brackets is
  left as written. `std/` and `meta/` are kept formatted (a test checks it).
* **Modules.** `import "path"` (relative to the importing file, checked
  once, cycles and duplicates rejected). `import std.List` reads
  `std/List.taut` from the standard library that comes with `tauto`, from a
  file anywhere; a tote does not list it in its dependencies. `import text.utf8`
  reads `utf8.taut` (`totes/text/src/utf8.taut`) from `src` of `text`, a dependency of the importing
  file's tote; a file of an additional source is named with the directory first
  (`import text::proof::utf8` reads `totes/text/proof/utf8.taut`). A directory with a `Tauto.eure` is a
  *tote*, the unit of a package; see [Totes](#totes).

## Parser generation

The parser is generated from `crates/tauto-parol/tauto.par` by parol and
committed under `crates/tauto-parol/src/generated/`. parol runs only in
`tools/tauto-parol-gen`, a workspace of its own with its own lockfile.

```bash
bash scripts/generate-tauto-parol.sh          # regenerate
bash scripts/generate-tauto-parol.sh --check  # fail if the committed files are stale
```

## Nib

[`docs/design/nib.md`](docs/design/nib.md) specifies Nib, tauto without dependent types
and proofs. Its cases are in `cases/` with tauto's.
Tauto's own rules sit at the end of `tauto.par`: `theorem`, `axiom`,
`inductive`, `∀`/`∃`, `∧ ∨ ↔ ¬` on types, `decreasing_by`, a result type
on `match`, and kinds on generics.

## Syntax and macros

A `syntax` declaration gives a grammar in the style of `tauto.par` (LL(k)). A
literal such as ``math`1 + 2 = 3` `` is then read by that grammar into a typed
syntax tree. A macro is a Nib function that returns syntax, called explicitly
with `NAME!(…)`. What it takes decides its kind:

- a syntax macro takes a literal: ``math!(`1 + 2 = 3`)``;
- an untyped macro takes an expression and does not check it first:
  `nat!(a + b == b + a)`;
- a typed macro takes an expression that is checked before the macro sees it:
  `m!(e)`;
- a tactic takes a `ProofStep`, the goals of a step `by t!(arg): G0 { … }`,
  and returns a term with a hole `?armK` for each arm: `rewrite!` in
  `std/Tactic.taut`, `reduce_goal!` in `examples/lambda`.

Expansion is hygienic. The kernel gets no new rule: every expansion is checked
again by the kernel and by `types.rs`, `rows.rs` and `lin.rs`, and in a proof a
macro's output must be definitionally equal to what it claims or come with a
proof the kernel checks.

```sh
tauto syntax gen [--check] [DIR]      # write the table files of the grammars in a tote
tauto syntax source DIR NAME         # print the original grammar literal
tauto macro expand [--all | --at LINE:COL | --write] FILE
tauto macro trace [--json | --diff] FILE
tauto macro inspect FILE --at LINE:COL [--json]
```

`tauto check --json` lists the expansions. The table of a grammar is a plain
file (`.tauto-syntax/<sha256>.tables`); no parser generator runs when a program
is read. The design is in [`docs/design/macro.md`](docs/design/macro.md); the macro
system's hygiene (`totes/macros`) and the table generator (`totes/llkgen`,
which writes, character for character, the tables of the generator of
`crates/tauto-parol`) are written in Nib.

Equation chains in proofs are written with the `calc!` macro of `std/Calc.taut`,
a chain of `=` or `↔` whose lines each give the relation, the next expression and
its proof ([`docs/design/syntax.md`](docs/design/syntax.md)); a typed `let` per step
with `Eq::trans` also works (see `examples/nat`).

## Editor support

`tauto lsp` is a language server. It reports what `tauto check` finds as
diagnostics, colours the text of syntax literals with the tokens of their
grammar (semantic tokens), and completes the terminals the grammar can go on
with. On a name it also answers:

- Hover shows the declaration (a function, theorem or constructor as written,
  without its body) and, in a Nib program, the type the checker found, which
  is the only type for a `let` without one. On a macro call it shows what the
  macro expanded to.
- Go to definition and find references follow imports. A name that only a
  macro declares leads to the macro call that made it (through the span map).
- A step whose arm writes a goal (or variables) other than the ones its tactic
  left is a diagnostic with a quick fix (`textDocument/codeAction`) that
  rewrites the arm's `Δ ⊢ G` to what the tactic left. `tauto check --json` has the
  same edit in the error's `fix` (`title`, the range, `text`).
- Rename changes the declaration and every use, in the file and in the files
  that import it, and then reads the edited files again: if any name would
  refer to a different declaration afterwards (the new name is already in
  scope), it refuses. It also refuses where it cannot find every use: a
  name written inside a syntax literal or a `quote`, one that resolves to
  nothing, a field (found by the type of what it is read from), a name the
  prelude declares, and a name of a tote that another file of the tote could
  use without importing it.

The names are read from the text as written, not from what macros expand to.
`tauto goals --json` gives the goal and the variables in scope at each hole, as text and as trees.

## Rust backend

`tauto build` compiles a program to a Rust crate and runs `cargo` on it;
`tauto run --backend rust FILE` builds and runs it. The code is generated
in tiers according to what a function uses (plain values, ownership and
borrowing, closures, and the multi-shot effect machinery), including
`budget`, `extern`, modules and view types, and links against `tauto-rt`. It
contains no `unsafe`.

`tauto build --timings` reports sequential build phases on stderr;
`--timings=json` appends one versioned JSON record on its final line, after any
ordinary diagnostics. The artifact path on stdout and the exit status are unchanged.
Both forms report failures as well as successful builds; neither runs or profiles
the generated program. Phase boundaries, cache observations and the JSON contract
are described in [`docs/design/build-timings.md`](docs/design/build-timings.md).

A Rust crate is used through `extern` declarations or through `tauto bind`,
which reads the crate's rustdoc JSON and writes the declarations
(`bind/<crate>.taut`), the correspondence to Rust (`bind/<crate>.eure`) and a
report of what it could not express (see [Limitations](#limitations)). `examples/rust/` has demos with `regex`
and `serde_json`. The specification is
[`docs/design/rust-backend.md`](docs/design/rust-backend.md).

## JavaScript backend

The JavaScript backend emits standalone ES modules for Node and browsers from the same
checked program as the Rust backend:

```sh
tauto run --backend javascript program.taut
tauto build --emit javascript program.taut -o target/javascript
```

JavaScript builds accept `--declarations` to emit matching `.d.mts` type declarations
for the generated module entry points and host bindings.

The runtime supports asynchronous host effects. Rust externs compile to Wasm,
including generic functions, borrowed results, and callbacks. Target selection
and supported boundaries are described in
[`docs/design/javascript-backend.md`](docs/design/javascript-backend.md), and the
types of JavaScript host bindings in
[`docs/design/javascript-host-types.md`](docs/design/javascript-host-types.md).

## Self-hosting

Parts of the toolchain are rewritten in Nib under `totes/`, and a differential
test (`tools/selfhost-harness`) checks that each gives the same output as the
Rust implementation on the whole corpus: text and ordered-map libraries, the
formatter, the scanner, LL(k) driver and syntax tree, `surface`, and
`nibcheck` (effect rows, types and ownership), plus hygiene and the grammar
table generator. Built with `tauto build`, the Nib versions of the checkers run
slower than the Rust ones, and much faster than in the evaluator. The independent kernel has a Tauto implementation in `totes/kernel`, which
rechecks exported elaborated declarations, including inductive declarations and
eliminator generation. The linter, the named elaborator, the evaluator and the
complete Rust generator are not rewritten. `totes/rustgen` is a Tauto-written
backend for an explicitly checked scalar subset, not a replacement for the
complete backend or a compiler bootstrap. It reads source through `surface`,
emits executable Rust, and rejects unsupported constructs. See
[`totes/rustgen/README.md`](totes/rustgen/README.md).

The totes and their Rust counterparts are:

| Tote | Rust crate or component |
|---|---|
| `surface` | `tauto-surface::surface` |
| `nibcheck` | `tauto-nibcheck::{types, rows, lin}` |
| `kernel` | `tauto-kernel::check::core`: closed declaration checking, reduction, conversion and inductive registration |
| `rustgen` | Scalar `i64`/`Bool` function subset of `tauto-rustgen`; emitted programs are compared with the evaluator |
| `macros` | `tauto-surface::macros` (syntax values, quoting and hygiene); expansion remains in `tauto-macro` |
| `scan`, `llk`, `lr`, `syntax` | `tauto-parol` and the grammar runtime in `tauto-syntax` (`lr` is the LALR(1) driver) |
| `pargen`, `llkgen`, `syntaxgen` | Grammar-table generation (`pargen` reads the grammar and makes the scanners, `llkgen` the LL(k) tables, `syntaxgen` is the program `tauto syntax gen` runs); `tools/tauto-parol-gen` generates the Rust parser |
| `fmt` | `tauto::fmt` |
| `text`, `unicode`, `ordmap` | Library utilities; no separate implementation crate |
| `fluent` | Localized messages (FTL); compiled into `tauto-messages`, which writes the toolchain's messages |
| `hello` | Example tote |

[`totes/kernel/README.md`](totes/kernel/README.md) describes how to export and
replay core declarations; ordinary `tauto check` continues to use the Rust kernels.

Differential tests say the outputs agree; they are not proofs. Which parts are
written in the proof language, where the kernel checks that they terminate and
theorems are stated about them, is described in
[`docs/design/self-host.md`](docs/design/self-host.md).

## Totes

A directory with a `Tauto.eure` is a tote:

```eure
package {
  name = "fmt"
  version = "0.1.0"
}

dependencies {
  text { path = "../text" }
}
```

A tote always has the source directory `src`, which `Tauto.eure` does not
list. A file under `src` is named by its path from `src`: a dependent reads
`src/compiler.taut` of `compiler` as `import compiler::compiler`. Other
directories are listed in `package.additional-sources`, and a file
under one is named with that path first: `proof/compiler.taut` is
`import compiler::proof::compiler`. A directory of `src` may not share the
name of an additional source (`src/proof` and the source `proof` would both
name `compiler::proof::…`). `package.sources` is not accepted. A file of the
same tote is imported by its path (`import "Setoid.taut"`); a tote that has
no `src` can be built from additional sources alone.

`tauto dev` takes the arguments of `tauto run` and runs the program on the
machine written in Tauto (or the evaluator with `--backend eval`) again from the start whenever a source file under the tote (or the
file's directory) changes; a version that does not check is not run, and the running one keeps running. What the
program prints is written as it happens, and on the evaluator a server's listener stays bound
across reloads. See [`docs/design/dev.md`](docs/design/dev.md).

A tote can give `tauto` commands: a `commands` section in its `Tauto.eure`
names a program (`main`, outside the sources) and says what it does (`about`),
and `tauto NAME ARGS…` runs it in a project that depends on the tote directly.
It is checked as `tauto run` checks a program, and the host denies it
everything but what the project's own `Tauto.eure` grants it under
`trust.commands`; no flag widens that. `tauto --help` lists the project's
commands. See [`docs/design/commands.md`](docs/design/commands.md).

`tauto run --tote DIR` and `tauto build DIR` load the tote and the totes it
depends on. `tauto check --tote DIR` checks them, and every other `.taut` and `.tauto`
file in the tote outside its sources (proofs, examples, tests; a directory
with its own `Tauto.eure` is another tote): it lists the tote's own
declarations, and of its dependencies and imports only those that did not
check (`--verbose` lists every one), then a line that counts them. A proof checked
before is taken from the proof cache while its statement and what it uses are
unchanged, so a dependency is checked again only when it changes. A dependency is found by its `path` and named by its own
`Tauto.eure`, whatever its directory is called. The standard library is not a
dependency: a file of any tote reads it with `import std.Nat`, and a
dependency's module with `import text.utf8`. `tauto trust bundle` carries the
standard library files a bundle imports, under `<std>/`.

A dependency may also be a tote in a Git repository, which Totebag fetches
and fixes by content ([`docs/design/totebag.md`](docs/design/totebag.md)):

```eure
dependencies {
  semver {
    git = "https://example.com/tauto/monorepo"
    ref = "refs/heads/main"
    dir = "semver"
  }
}
```

`tauto add --git https://example.com/tauto/monorepo semver` writes that
entry, and `Tauto.lock` beside `Tauto.eure` records the exact commit and the
SHA-256 of its source tree. `check`, `run`, `build`, `test` and `doc` read the
lock and fetch only what it fixes (`--offline` forbids even that); a newer
commit is taken only by `tauto update`.

With `Trust.eure` beside `Tauto.eure`, a new commit is taken only when the
indexes it trusts allow it: Git repositories recording which revisions their
keepers observed and accepted, read and checked by the core in `totes/index`.
`tauto index` syncs them, says why a commit may not be adopted yet, and keeps
one's own index. The user's own policy (`~/.config/tauto/trust.eure`) can only
add to a project's `Trust.eure`; without one, a commit waits 14 days after it
was first observed.

A `rust { … }` block gives the Rust path of each `extern`, the
bindings from `tauto bind`, and the crate dependencies. A key that is not known
is an error. The `Tauto.eure` at the root of this repository names the library
in `std/` and `meta/` and is not read by a tool.

## Limitations

* `check` skips executable bodies (blocks, `var`, `perform`, `handle`); they
  are checked by `run`.
* Implicit arguments are first-order: no unification under binders beyond
  patterns `?f x`, no named arguments. Type classes
  ([`docs/design/classes.md`](docs/design/classes.md)) resolve an instance by the head
  constructor of a type, or from a `where` assumption, and search nothing else.
* A `match` is on a variable in scope, and the parameters after it are
  generalized into the motive. Index unification covers constructors with
  first-order fields (dependent fields are not compared) and does not recurse
  through a changed index. Numeric universe templates support `theorem`, `def`,
  and standalone `inductive`; polymorphic constructor patterns and mutual
  universe templates are not supported. `_rec` retains its Type1 default;
  `recursor(Family, level)` selects another checked motive universe.
* Nested occurrences in parameterized types, and through indexed or mutual
  types, are rejected.
* Effect rows (`crates/tauto-nibcheck/src/rows.rs`) are checked without value types.
  Row variables are names (`|e`) a function may perform only by calling a
  parameter that carries them; whatever cannot be followed is reported as
  unchecked, never read as empty. The Lean rules are not connected to this
  checker. `budget`'s interruption and multi-shot budget sharing are
  guaranteed by the evaluator's tests only.
* Preservation, progress, and that a row without `Div` stops, are proved
  for a non-dependent core of Nib with effects, handlers, `var` and `budget`
  (`lean/Proto/Nib`, `docs/design/semantics.md`); dependent types are open.
* Holes: not in a `mutual` block, not where a type is written. `suggest` matches types as written (first-order, up to bound names), not up to computation.
* No package registry: a tote names its dependencies by path or by Git
  repository, and a project's `Trust.eure` may name the indexes whose
  judgement a new commit needs. The CLI does not crawl other indexes.
* The Rust backend does not cover every form: a `return` inside a
  multi-shot `handle`, and `budget` in the M tier. See
  [`docs/design/rust-backend.md`](docs/design/rust-backend.md).
* Universe levels are not quantified symbolically in the kernels: a `Level`
  template is checked and used through numeric instances, and levels outside a
  template are numerals ([`docs/design/universes.md`](docs/design/universes.md)).
* No cache of macro expansions.
* The evaluator (`tauto-eval`) has no tote implementation, and the linter, the
  named elaborator and the complete Rust generator are not rewritten in Nib.
* `tauto bind` does not write declarations for `unsafe fn`, `async fn`,
  `dyn Trait`, `Send`/`Sync` bounds, const generics, macros, some primitive
  types (`i8`, `i16`, `u16`, `i128`, `u128`, `f32`, `char`), or generic functions
  whose type arguments the configuration does not instantiate; it reports them.
* Wasm goes through the Rust backend only: no threads (tasks run inline), no
  reactor, no `net`, and a panic aborts.

## Supply chain

- `.cargo/config.toml` refuses crate versions published less than 14 days ago
  (enforced by the nightly Cargo pinned in `rust-toolchain.toml`).
- `.gitignore` is an allowlist: everything is ignored unless allowed. Check it
  when you add a new kind of file.

## Dependencies and credits

- [Eure](https://github.com/Hihaheho/eure) (`eure-document`, `eure-reader`,
  `eure-schema`, `eure-fmt`): the format of manifests and case files, from a
  pinned Git revision.
- [parol](https://github.com/jsinger67/parol) generates the parser from
  `tauto.par` (only in `tools/tauto-parol-gen`); the generated parser uses
  `scnr2` at run time.
- [Lean 4](https://lean-lang.org/) for the formalization in `lean/`.
- `query-flow` (incremental queries), `proc-macro2` and `quote` (the Rust
  backend writes token streams), `serde_json` and `rustdoc-types`
  (`tauto bind`), and, in `tauto-rt` behind features, `tokio`, `reqwest` and
  `rustls`. `Cargo.lock` lists every crate.
- Messages are written in FTL (`crates/tauto-messages/locales`).
- The grammar notation, LL(k) table generation, scanner generation, table
  format and runtime design of `crates/tauto-syntax`, `totes/pargen`,
  `totes/llkgen`, `totes/llk`, `totes/scan`, `totes/syntax` and `totes/lr` come from
  [parol](https://github.com/jsinger67/parol) and
  [scnr2](https://github.com/jsinger67/scnr2) by Jörg Singer
  (MIT OR Apache-2.0).
- The Unicode tables in `totes/unicode` and `totes/pargen` are derived from
  the Unicode Character Database (Unicode License v3), through the Rust
  standard library and the `regex-syntax` crate.
- `totes/lalrgen` reproduces the LALR(1) table construction of the
  [lalry](https://github.com/jsinger67/lalry) crate 0.1.0 by Jörg Singer and
  Geoffry Song (MIT OR Apache-2.0), which parol uses.
- The plural rules in `totes/fluent/src/plural.taut` come from Unicode CLDR
  (Unicode License v3).
- `crates/tauto-rt/src/float_math.rs` is derived from the `libm` crate,
  version 0.2.11 (MIT OR Apache-2.0), with its notices kept;
  `crates/tauto-jsgen/src/float.js` ports the same functions to JavaScript.
- [NOTICE](NOTICE) has the notices and license texts.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT) at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this work, as defined in the Apache-2.0 license, shall be dual
licensed as above, without any additional terms or conditions.
