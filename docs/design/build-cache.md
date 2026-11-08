# Build cache

The machine-local build cache stores outputs of named build actions and records
the inputs used to produce them. `crates/tauto-cache` provides action keys,
content-addressed blobs, action records, and cache explanations. The cache is
separate from dependency tracking: [totebag](totebag.md) tracks source trees,
while the Rust backend uses the build cache for its runtime artifacts.

## Cached artifacts

| Cache | Where | Key | Shared between projects |
| --- | --- | --- | --- |
| Fetched source trees | `$TAUTO_TOTES/src/<hex>` | `source-v1` of the tree ([totebag](totebag.md)) | yes |
| Checked proofs, elaborated terms | `$TAUTO_CACHE` (`…/tauto/proofs`) | checker source, bound syntax and the checked environment | yes |
| The analyzer's queries | in memory | per statement, cut off at a statement's fingerprint and the kernel digest after it | no |
| Generated Rust, its native build | per project | the generated files are compared before writing | no |
| `tauto-rt` and its crates, built for a debug build | `$TAUTO_BUILD` | rustc, the runtime's sources, its features | yes |

The proof cache keys bound syntax and the checked environment. Opaque theorem
proofs are absent from that environment, so changing a proof does not invalidate its users; and a hit still sends terms
through the core kernel. Lowering, code generation, and native builds do not
use action records in this cache. The runtime artifact cache applies to host
debug builds.

## Actions and blobs

An action is one step of a kind (`verify`, `lower`, `codegen`, …) run on named
inputs. The caller names every input that can change the result and only those:
parsing does not take the target, code generation does.

```text
action-v1 = UTF8("tauto-action-v1\0") || frame(kind) || u64be(number of inputs)
            || each input, in the byte order of its name:
               frame(UTF8(name)) || frame(SHA256(value))
blob-v1   = SHA256(UTF8("tauto-blob-v1\0") || bytes)
```

`frame` is as in `source-v1`. The key says what a step was run on; a blob's
digest says what bytes it made. They are different names: two actions that
make the same bytes keep them once.

```text
$TAUTO_BUILD (else $XDG_CACHE_HOME/tauto/build, else ~/.cache/tauto/build)
  blobs/<hex>      an output, read-only
  actions-v2/<hex> an action's record: the digest of each input, each output
  last-v2/<hex>    the key the action of one kind and subject last had
  tmp/             files being written
```

Every file is written to `tmp/` and renamed into place, and an action is
recorded only after the blobs it names are there: a process that stops
part-way leaves files in `tmp/` and nothing else. A blob read back is hashed
again, and one that differs is not used. Reading takes no lock; two processes
that make the same action write the same files.

Action records carry a format version and length-delimited UTF-8 fields, so
input and output names may contain whitespace, line breaks or zero bytes.
Reading checks the complete record, digest spelling, unique names and the
action key derived from the stored inputs. Unsupported formats and malformed
records are cache misses; their outputs are rebuilt. Record directories are
versioned so readers of different formats cannot overwrite each other's records.

`explain` answers a hit, a first run (nothing of that kind and subject before),
the inputs that changed, were added or were removed since the last run, or a
record lost (same inputs, a blob gone).

## The Rust runtime

A debug build for the host of a crate that depends on `tauto-rt` alone (no
`rust.dependencies`, no bridge crate) does not give the crate to Cargo.
`tauto-rt` and its crates are built once by Cargo for one rustc (`rustc -vV`),
the runtime's files and its features, and their `rlib`s and `rmeta`s are kept
as one action, `rust-runtime`. They are laid out under the project's
`target/tauto/target/rt/<key>/` (linked, else copied), and the generated
library and its `main` are given to rustc with `-C incremental` in the
project's target directory. A second project with the same features builds
only its own code.

When the runtime cannot be built or kept, or a crate it depends on links a
native library from its build directory (which a kept `rlib` does not hold),
the build goes through Cargo as before. A release build and a build for another
target always do.

## What a cached result is trusted for

A blob is bytes this machine made. A cached check is used only under a key that
holds the checker itself, as the proof cache's key holds the kernel's source;
and the core kernel still checks the terms. A result whose inputs cannot all be
named (a step that reads what it was not given) is not cached. Results made
elsewhere are not taken in: a digest says the bytes are the ones named, not
that they were made right.
