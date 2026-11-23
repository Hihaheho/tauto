# `tauto build --timings`

`--timings` prints a table and `--timings=json` a one-line JSON record as the
last line of stderr (diagnostics may precede it). Stdout and exit status are
unchanged; without the flag no clock is read. Not accepted by `run`. The
record is written whenever valid arguments start a build, on success or
ordinary failure; not on usage errors, panics or kills.

## Phases

Wall-clock time on a monotonic clock, from after argument checking to just
before returning. Phases are consecutive, non-overlapping intervals in
execution order, so they sum to the total; everything between boundaries
belongs to the earlier phase.

| Phase | Covers |
| --- | --- |
| `input` | input detection, manifest, reading a single source file |
| `tote_load_check_extract` | loading a tote's dependencies, imports and includes, expansion, proof checking, extraction |
| `parse_expand` | parsing, macro and class expansion, name resolution |
| `check` | type, effect row and ownership checks, prelude setup |
| `lower` | lowering to NIR |
| `codegen` | output names, Rust binding resolution, generated workspace |
| `write` | comparing and writing generated Rust files |
| `codegen_write` | JavaScript generation and writing (and Rust wasm externs) |
| `native_compile` | running Cargo and reading its diagnostics |
| `finish` | printing artifact paths, dropping build data |

Single files have no tote phase. `--emit rust` runs no Cargo; JavaScript runs
Cargo only for Rust wasm externs, with `codegen_write` intervals before and
after. On failure the last phase is `failed` and unreached phases are absent.

## JSON

- `schema_version: 1`, `kind: "tauto.build.timings"`, `backend`
  (`rust`/`javascript`), `target` (`host`/`node`/`browser`), `status`
  (`ok`/`failed`), `duration_ns`.
- `phases`: in order, each `name`, `duration_ns`, `status`; repeated names are
  kept. Durations are u64 nanoseconds, saturating.
- `cache.native` and `cache.proof`: `not_run`, or `unknown` once Cargo or the
  tote loader was reached. Do not count `unknown` as a miss.
- `cache.generated_sources`: `null`, or for written Rust files
  `{provenance: "content_equality", hits, misses}` (files left unchanged vs
  written).

The record has no paths, sources, environment, URLs or messages. Readers check
`schema_version` and ignore unknown fields.
