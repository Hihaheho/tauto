# Source bundles and trust reports

`tauto trust bundle ROOT ENTRY` prints a JSON bundle: `ENTRY` and the
transitive closure of its relative imports, sorted by path, each with the
SHA-256 of its bytes, plus a report. It carries the proof sources themselves,
not a claim that they passed.

`tauto trust verify BUNDLE` checks the format and hashes, resolves imports
only within the bundle, rechecks everything with a fresh kernel (never the
proof cache) and requires the derived report to equal the stored one. Nothing
is written to disk, and no path becomes a file read, URL or command.
`--axiom-free` rejects any axiom, even unused; this policy belongs to the
receiver, not the bundle.

## What the report says

Per kernel declaration: its status and transitive user axioms. It also lists
axioms, extern names, declared effects and written effect rows (an absent row
is distinct from an empty one), and as unchecked statements the extern
signatures, effect declarations and every function whose body calls `expose`
([`secret.md`](secret.md)). Extern implementations, runtime behaviour,
generated code and binaries are not certified.

The checker record holds the package version and the SHA-256 of the verifier
executable file (not the mapped image). The source revision is `null`. Exact
report equality needs the same executable; there is no claim of reproducible
builds. Hashes prove consistency, not authorship: anyone can edit a bundle and
regenerate a consistent report.

## Accepted sources

Only `import`, `theorem`, `axiom`, `def`, `inductive`, `fn`,
`extern` and `effect` declarations. Each file is first parsed without macro
expansion and rejected if it contains macros, syntax literals, quotes, nested
declarations, includes, manifests or top-level statements; then it is loaded
by the normal loader from the bundle. Module imports are only
`import std::Name` from the checker's own std, and a bundled `<std>/` file
must equal it; tote dependencies are refused.

Export reads files with directory-relative no-follow access (Unix only),
requiring regular files and refusing links in every component. The snapshot
is the bytes read, not an atomic revision.

## Limits

8 MiB document, 256 files, 1 MiB per file, import depth below 64; relative
bounded paths only (no absolute paths, URLs, backslashes, empty components or
escapes); duplicate keys and unknown fields are errors. These are input
limits only; run hostile proofs under your own resource limits.

Tests: `crates/tauto-cli/tests/trust_bundle.rs`.
