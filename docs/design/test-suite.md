# Case suite

Each Eure document in `cases/` holds a top-level case, named cases under
`cases`, or both (top level runs first). Filter by file and case name. The
schema `tools/tauto-test-suite/case.schema.eure` is generated from the runner's
types; `cargo test -p tauto-test-suite --test schema` checks it is current and
that every case conforms (`TAUTO_UPDATE_SCHEMA=1` rewrites it). Unknown fields,
wrong types, empty `checks`, cases with nothing to check, and incompatible
inputs and expectations fail. `description` is free text.

Language behaviour (acceptance, expansion, diagnostics, output) belongs in
cases, run by every runner. Rust tests keep only what one implementation owns
(generated code shape, optimizer paths, JS runtime internals, host exceptions,
cache invalidation, counters, ABI, CLI arguments and formats), with sources
beside the test, never read from `cases/`. `fixtures` entries (top level only)
carry `source` and a non-empty `reason` and never count as semantic successes.

## Inputs

| Field | Meaning |
|---|---|
| `source` | Source text, or a `path`-tagged file relative to the case (imports resolve from that file; the process cwd never changes) |
| `files`, `entry` | Relative path → text (or `path` to copy, or `real` to link in place), written to a temp dir; `entry` defaults to `main.nib`. A `path` value copies the file; imports resolve from the copy, so include dependencies. A `real` value makes a symlink to the repository file (relative to the case): a check that reads by path sees that file's real path (standard-library membership, `std` tote). Keys still cannot contain `..`, absolute paths, or syntax-table overrides |
| `imports` | `path`-tagged libraries loaded before the entry, resolved in place |
| `tote` | `path`-tagged tote directory, loaded by manifest, checked and run |
| `files_tote = "app"` | Treat a directory in `files` as a real tote (its `Tauto.eure` decides entry and deps; deps' entries don't run). Not with `entry`, `imports`, `parses`, `check_tote`, `run_tote`, or `workspace_check`. `exports` is honoured; host settings are rejected by backend runners |
| `check_tote = "app"` | From the `files` tree root as the working directory, resolve `--tote` with that string (as the CLI does) and check the resulting tote. Paths and other refusals are product errors (`load_error`). Not with `files_tote`, `run_tote`, `workspace_check`, `entry`, `imports`, or `parses` |
| `run_tote = "app"` | Same resolution as `check_tote`, then run that member (with `stdout` / `stderr` / `exit` / `run_error`) |
| `workspace_check = true` | Check every member of the workspace at the `files` root (as `tauto check` at that root). Uses `tote_errors` / `tote_warnings` / `load_error`. Not with `files_tote`, `check_tote`, `run_tote`, or runtime fields |
| `args` | Program arguments for all runners |
| `permissions` | `--allow-*` for the in-process machine; `{dir}` expands to the files dir |
| `links` | Symlinks created beside `files` |

## Writing expectations compactly

Expectations that take an array of objects (`diagnostics`, `holes`, `hovers`) are easier to read as
array sections than as a one-line `[{ "k" => v, … }]`: one field per line. `@ cases.<name>.diagnostics { … }`
uses a section path to enter the case, and each `@ []` in the block appends one element. For a single
element, `@ cases.<name>.diagnostics[]` works too.

```eure
@ cases.broken
source = ```tauto
theorem broken(): False { Zero }
```
checks."broken" = "error: type mismatch: expected `False`, found `Nat`"

@ cases.broken.diagnostics {
  @ []
  name = "broken"
  message = "type mismatch: expected `False`, found `Nat`"
  span = "{ «Zero» }"
}
```

A section runs until the next `@`, so write plain bindings such as `source` and `checks` first and put
array sections last. An empty expectation stays `diagnostics = []`. Short string arrays such as `tests`
or `context` stay on one line as `[...]`.

## Declarations

- `checks`: declaration → verdict. The name must match exactly one declaration;
  qualify with `path::name`, and `name#n` (1-based) for same-file duplicates.
  `checks_all` covers every unlisted declaration (fails if there are none),
  including imports. `declarations` is the exact ordered name list.

  | Verdict | Means |
  |---|---|
  | `ok` | Checked, no axioms |
  | `checked` | Checked, axioms ignored |
  | `axioms: …` | Exact ordered axiom dependencies |
  | `error: …` | Failed with a message containing the text |
  | `incomplete: …` | Exact holes and incomplete dependencies |
  | `skipped` | Not kernel-checked |

- `holes`: ordered list of `declaration`, `name`, `goal`, `context` (and
  optional `file`). Goal and context (`name: type` in binding order) compare as
  printed text. Unlisted holes fail.

## Diagnostics

`diagnostics` is an ordered, complete list per stage (`checks` default,
`types`, `rows`, `lin`), stages in that order. `[]` asserts none.

| Field | Checks |
|---|---|
| `message` | Required substring |
| `name` | Kernel declaration |
| `file` | Path suffix |
| `span` | Source excerpt with one `«…»` pair |
| `fix`, `fix_span` | Fix replacement text and replaced source |
| `fixed_source` | Whole file after applying the fix |

The excerpt without `«»` must occur exactly once in the source (else the case is
wrong); widen it to disambiguate. Numeric positions are not accepted. Fixes are
checked for kernel diagnostics and `rows` (missing effects).

Shorthands: `types`, `rows`, `lin` (success or first error); `parses`
(acceptance only); `load_error` (missing files, cyclic imports); `macro_error`
(first macro error); `check_report` (text that the report of `tauto check`, with its
`file:line:col` places and the message of each problem, contains).

`lang` (a language tag such as `ja`) writes the messages the case reads in that
language, as `TAUTO_LANG` does for the command; without it they are English. It
holds on the case's own thread only, so the other cases stay English. The
backends write English only and do not run a case with `lang`.

`fixes` runs `tauto check --fix` (`check-fix.md`) on `entry` in memory, or
`tauto lint --fix` with `lint = true`, and checks disk is untouched. Fields:
`applied`, `reverted` (ordered edit titles), `files` (final text of changed
files; others must not change), `diff` (`--dry-run` output, trailing spaces
ignored). Not with `files_tote`, `imports` or other program checks.

## Macros and tools

- `expands`: entry statements after expansion, printed by `print_stmts`, exact
  after trimming. Renamed names (`tmp#1`) only the printer can write.
- `trace`, `macro_warnings` (exact ordered warnings, e.g. a typed macro skipped
  on an unchecked declaration).
- `inferred_types` (binding → type), `inferred_rows` (function → effects),
  `inferred_kinds` (type → kind); missing or ambiguous names fail.
- `tote_warnings`, `tote_errors`: ordered substrings from checking a tote
  (`files_tote`, `check_tote`, or each member under `workspace_check`),
  counts must match.
- `check_errors`: ordered substrings of the failures `tauto check FILE` reports
  for `files`' `entry`, errors in what it imports included; counts must match.
- `externs`: the exact ordered list `Report::externs` gives for `files`' `entry`
  (`extern f (b.taut:2)`, paths relative to the files dir): every `extern` the
  user's files the check read declare, nested or not; an unreadable file is
  `unread (file)`.
- `rows_javascript`, `format`, `format_error`, `lint`.
- `format_literals`: entry after formatting syntax literals and comment fences
  with registered `fmt` functions, as `tauto fmt` does, and idempotent.
  `format_literals_warnings` lists warnings (omitted means none).
- `editor_tokens`: DSL colours from `tauto_analyzer::editor::dsl_tokens` as
  `line:col kind text` (1-based, characters, split per line).
  `editor_token_warnings` as above.
- `proofs`: list of `name`, `format` (`block`, `node`, `tree`, `tree-html`,
  `natural` default, `json`), `full`, and exactly one of `output` (exact text or
  `path` file) or `error` (exact); `failed`, `incomplete` check status. JSON
  output must parse.
- `hovers`: `at` text, `occurrence` (0-based), `contains`, `lacks` (texts that
  must not appear), or `absent`; `span` asserts the hover covers exactly that
  occurrence of `at`; `proof` (and `proof_file`) asserts the natural-language
  rendering of that theorem; `buffers` supplies unsaved texts relative to the
  entry's directory.
- `import_fixes`: list of `at` text, `occurrence` (0-based), `fixed_sources`. The imports the
  editor offers for the use of `at` in the entry, one for each file of the tote (or of the
  entry's directory outside a tote) that declares it, in order; each element is the whole
  entry after that import is written. `[]` asserts none.
- `row_hole_fixes`: the same list for `!?`: the edit the language server's quick fix makes at each
  `!?` (the one `tauto check --fix` makes); none for a function that calls itself or a later `!?`.

## Execution

- `stdout`, `stderr`, `exit` (default success), `tests`
  (names of every passing `perform test`, in order), `budget` (the step limit
  of the in-process machine),
  `run_error` (failure containing text; not with success outputs).
- Runs are on the bytecode machine in process (`tauto::exec`). Inline sources
  are also run from a file. Where the drops go is checked statically, not at
  run time: `nir.passes = ["anf", "ownership"]` with `nir.package` compares
  the whole printed NIR, drops included (`cases/lin/drop_clone.eure`).
- A Tauto program the case runs or a backend compiles (`stdout`, `stderr`,
  `exit`, `tests`, `run_error`, `probe_drops`, `build`, `compile_errors`,
  `differential`), or whose extraction it asserts (`extracted_*`,
  `extract_source`), is extracted after real loading and checking, on the
  in-process machine and on every backend, as `tauto run` reads it (there is no
  "assume proved" path). `extract = false` opts out and reads the program as
  written; `extract = true` asks for extraction where it is not the default
  (a check-only case, a Nib entry, a tote, a case whose `checks` expect an
  `error: ` verdict: extraction needs a program that checks). `extract_source = true` prints the extraction to source
  and re-checks and runs it (termination results are not carried over).
  `extracted_nib` maps a full name, unique short name, or `prefix*` (name-sorted)
  to exact Nib printer output. `extracted_text` lists texts that must appear
  in the extraction as `tauto extract` prints it, and `extracted_lacks` texts that
  must not (the shape of what is written: modules, names).
- `probe_drops`: drop order observable on every backend. Programs declare
  `struct(affine) Probe {}` and `extern { fn Probe::new(name: &Text): Probe }`;
  the in-process machine (`tauto::exec`) records probe drops, Rust uses `tauto_rt::probe`'s `Drop`,
  JavaScript the last owner's `release`.
- `eval.unimplemented` or `eval.bug` (a reason) marks a failure of the
  in-process machine (never a format error); success makes the mark stale and fails.
  It covers the in-process machine only: a backend failing the same case needs its own
  opt-out. A filter matching nothing
  fails.

## NIR

`nir` checks how a program is compiled, as NIR text (`nir-text.md`). What a
program writes does not change when a transformation is left out, so
transformations and optimizations are checked here, in the same case as
`stdout`.

| Field | Meaning |
|---|---|
| `passes` | Passes and checks applied in order to the compiled package (`nir-text.md` "Passes") |
| `fns` | Function (`name`, or `name@id` when several share it) → its text |
| `blocks` | Function (as `fns`) → its block form (`nir-text.md` "Blocks"), which must read back as the blocks it was written from |
| `datas` | Data type → its declaration |
| `evidence` | The `evidence` lines |
| `exports` | The `export` lines |
| `package` | The whole package |
| `error` | Substring of the error that reading the input or a pass gives; not with `fns`, `blocks`, `datas`, `evidence`, `exports` or `package` |
| `target` | `rust` (default), `javascript` or `llvm` |
| `library` | `true` compiles every function, reached from the entry or not |
| `source` | A package as text in place of a program, exactly as the printer writes it |

A `files_tote` whose manifest has `exports` is compiled with those functions as
roots, as `tauto build` compiles it.

Texts compare exactly after trimming. `nir.source` is only for packages no
accepted program gives: ones a check refuses, and cases about the text
itself. Such a case holds no program and no expectation of one.

`cargo run -p tauto-test-suite --bin nir-text -- FILE [--target javascript]
[--pass NAME]... [--fn NAME]...` prints the text to expect (`FILE` ending in
`.nir` is read as text). `tests/nir_text.rs` prints and reads back the NIR of
every case that compiles, for both targets, as compiled and after `anf` and
`ownership`. Compiling is nearly all its time, so a source shared by cases is
compiled once and a case's types are checked once for both targets
(`RustCase::compile_backends`). `tests/nir_blocks_text.rs` does the same for
the block form of every function (`nir-text.md` "Blocks"), after `anf` and
after `anf` and `ownership`.

## Scenarios and backends

`Case::scenarios` decides once which of `eval`, `rust`, `javascript`, `vm`,
`llvm`, `niri` run a case. A case where none runs (except selfhost-differential
cases), or with expectations only a non-running scenario reads, fails.
`scenarios = [...]` asserts the exact set.

- Every case that runs runs on every backend (`rust`, `javascript`, `vm`,
  `llvm`, `niri`). There is no list of backends to choose from: a backend
  leaves a case only by saying why it fails it today.
- `compile_errors.rust|javascript|vm|llvm|niri` = `front: …`, `unsupported: …`,
  `generate: …` or `build: …` (stage plus non-empty substring): what the
  backend is meant to do.
- `<backend>.unimplemented` (the backend lacks the feature) or
  `<backend>.bug` (it has the feature and gets it wrong) records a failure
  today with the same stages, `runtime: …`, or `output: …` (part of the
  mismatch with the case's output). The runner confirms the failure and
  reports it as `todo`; success or a different failure makes it stale. These
  marks and the in-process machine's `eval.…` are the entire remaining-work
  list. `niri.…` uses the same field shape: either a compile/runtime
  stage like the other backends, or the ownership rule a case breaks
  today (`UseAfterMove: …`, `Leak: …`, `split: …`).
- One `stdout`, `stderr`, `exit` and `run_error` apply to the
  in-process machine and every backend; there is no per-backend output. Compile-only
  JavaScript cases still pass Node's syntax check.
- Step counts differ per backend:
  `rust_budget_steps` is `tauto_rt::budget::STEPS`. `rust_stack_mb` gives
  the Rust program's threads a stack of that size (`TAUTO_STACK_MB`). `assertion_gaps`
  names what a backend cannot check, which a backend checking everything
  else reports as `partial`; nothing is in it now.
- Backends run in `tools/tauto-test-suite/tests/backends.rs`. With no backend
  named, every backend runs (`rust`, `javascript`, `vm`, `llvm`, `niri`). A
  case that a backend cannot cover yet opts out with `<backend>.bug` or
  `<backend>.unimplemented`. Naming one backend (`-- llvm`, …) runs only
  that one. Each case gets `pass`, `partial: …`, `todo: …` (declared
  failure), or `fail: …`. Any `fail` fails the runner. `llvm` goes through
  the self-hosted tote (`totes/llvm emit`), not the Rust reference crate;
  on a host that is not Linux on x86_64 the scenario is skipped before any
  case runs. `niri` judges ownership ends as
  `crates/tauto-niri/tests/cases.rs` does (unsupported and not-yet-compiled
  ends are counted; unexpected output, split/blocks mismatch, or a stale
  `niri.bug` fail), and also checks `compile_errors.niri` and the shared
  runtime fields (`stdout`, `stderr`, `exit`, `run_error`). Neither `llvm`
  nor `niri` observes `probe_drops`; a case that names them ends
  `partial` when the rest matches. The in-process runner (`tests/cases.rs`,
  on `tauto-vm` through `tauto::exec`) reports pass, unimplemented, or fail.
- `cargo run -p tauto-test-suite --bin case-routes -- <filter>` lists
  expectations and available routes (not results).

## Parallelism

`tests/cases.rs`, `tests/backends.rs` and `tests/fuzz.rs` run cases in parallel
on `available_parallelism()` workers (`TAUTO_TEST_THREADS=n`, `1` for serial),
each on a 256 MiB stack. Results are sorted by case name and judged once at the
end, so output is independent of worker count. Per-worker state: Rust
`work-<n>`/`target-<n>` (rustc incremental cache and Cargo lock), JavaScript
temp dirs, VM `work-<n>`, LLVM modules and binaries; the VM machine is shared.
niri runs in process. Case temp dirs are numbered. A run of one of these
binaries that takes over 30 minutes is stopped as a failure (exit status 124;
`TAUTO_TEST_TIMEOUT_SECS=n`, `0` for no limit), so a hung case cannot stall
plain `cargo test`; `cargo nextest` kills a test after five minutes
(`.config/nextest.toml`). With `CARGO_NET_OFFLINE=true`, generated crates build
`--offline` and fail fast without network.

## Differential fuzzing

`tests/fuzz.rs` generates typed, terminating programs from a seed (arithmetic
at the edges, control flow, data, closures, loops, multi-shot handlers,
counting-independent budgets, and owned affine and linear values with `&`,
`&mut` and moves) and compares the lines shown and runtime errors
across the in-process machine, Rust and JavaScript, using a built-in SplitMix64.
`cargo test -p tauto-test-suite --test fuzz -- [<count> [<first seed>]]` runs
seeds 0..300 by default (`TAUTO_FUZZ_PROFILE=quick` runs 9).
`TAUTO_FUZZ_INTERACTIONS=1` rotates families mixing borrows, row-polymorphic
callbacks and multi-shot resumption, and also compares events with a small
Rust model, catching mistakes all backends share. Failures are saved, shrunk,
and replayed with `TAUTO_FUZZ_FILE` (and `TAUTO_FUZZ_EXPECTED` to require exact
events); fixed mismatches become regression cases.

## Self-host checks

- `differential = "<component>"` compares the Rust oracle with the Tauto
  component on shared inputs; the in-process runner never counts it as success.
  `component_rejects = true` says the oracle accepts the input and the component
  rejects it without producing anything, for a form the component does not read.
  `differential = "extract"` is the extract tote against the host extractor
  (`tools/selfhost-harness/tests/extract.rs`); the program source stays in
  `cases/`.
- `differential_program = "elaborator"` compares acceptance and declarations
  for a complete `files` tree. It preserves tote boundaries and imports.
- `selfhost_entry` with one of `selfhost_stdout`, `selfhost_compile_error` or
  `selfhost_run_error` checks the self-hosted pipeline; generation, build and
  run are separate stages, and a build failure never satisfies a rejection.
- `selfhost-plan` lists every requirement of the shared cases, and the
  harness's `shared-cases` reports per requirement, implementation, executor,
  target and stage. Unobserved, unsupported or timed-out requirements are
  incomplete; differing stages or diagnostics, crashes and stale checkouts fail.
  Setup and execution have separate time limits, and a supervisor killed from
  outside never leaves a success report.
- Bootstrap output checks, component differentials and whole self-host
  compilation are distinct guarantees; none substitutes for another.

## Rust tests in `crates/tauto/tests`

These cover what cases cannot express: report and JSON structure, extraction
and erasure, the instance-law filling API, cache revalidation, kernel
differentials against the model, library mutations rejected by existing proofs,
and manifest and syntax metadata APIs.
