# Explicit source bundles

`--bundle BUNDLE MODULE ENTRY` resolves top-level relative imports inside a
portable source bundle, then emits Rust for the supported language described in
[README.md](README.md).
`--graph BUNDLE MODULE` emits dependency-first source IDs and half-open UTF-8 byte
ranges (`ID<TAB>START<TAB>END`), including the entry module. Each original file is
concatenated with one separating newline; surface spans keep that byte base.
This source map is a graph/provenance interface, not an assertion that generated
runtime diagnostics already display per-file names.

Create a new bundle with the explicit host filesystem boundary:

```sh
cargo run --locked -p tauto-selfhost --bin source-bundle -- ROOT OUTPUT
tauto run --tote totes/rustgen -- --graph OUTPUT path/main.taut
tauto run --tote totes/rustgen -- --bundle OUTPUT path/main.taut answer
```

The host enumerates regular `.taut` files under ROOT, sorts portable relative
IDs, and rejects symlinks. It neither parses sources nor discovers imports.
The Tauto loader parses the bundle and original sources, resolves `.` and `..`
relative to the importing module, rejects escapes, cycles and missing modules,
and visits shared dependencies once. Only resolved top-level import statements
are consumed; proofs and every other declaration remain for backend checking.
No compiler is invoked to translate an unsupported input.

The bundle wire format is UTF-8: `TAUTO-SOURCES-1\n`, decimal file count and newline,
then each record's decimal ID byte length, newline, decimal source byte length,
newline, ID bytes, source bytes, newline. IDs must be canonical, relative and
unique. Framing validates UTF-8 boundaries and exact end-of-input. Limits are
4096 files, 16 MiB including framing, and 256 traversal-fuel units. The producer
is for a stable source tree, not a sandbox against concurrent filesystem mutation.
Package manifests and automatic `package.sources` discovery are not interpreted
by this loader; an entry's explicit imports determine its graph.

Run `cargo test --locked -p tauto-selfhost --test bootstrap_graph`. It compares
source order and byte ranges against the existing host loader, executes emitted
Rust after removing its input bundle, and submits the original compiler graph
without removing proof declarations. Acceptance of that graph is not a stage1
compiler or a stage2 fixed point; unsupported compilation must fail without
partial Rust output. Host filesystem IO and the initial compiler build remain
Rust responsibilities.
