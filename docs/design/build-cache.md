# Build cache

`crates/tauto-cache` stores outputs of build actions under keys naming their
inputs. Source trees are tracked separately by [totebag](totebag.md).

| Cache | Where | Key | Shared |
| --- | --- | --- | --- |
| Fetched source trees | `$TAUTO_TOTES/src/<hex>` | `source-v1` of the tree | yes |
| Checked proofs, elaborated terms | `$TAUTO_CACHE` | checker source, bound syntax, checked environment | yes |
| Analyzer queries | memory | per statement fingerprint and kernel digest | no |
| Generated Rust and its build | project | generated files compared before writing | no |
| Machine bytecode of a tote (`tauto run`) | `$TAUTO_BUILD` | tauto executable, arguments, files read | yes |
| `tauto-rt` for debug builds | `$TAUTO_BUILD` | rustc, runtime sources, features | yes |
| Tactic results of proof steps (not with `TAUTO_CACHE=off`) | `$TAUTO_BUILD` | tauto executable, files read, module, declaration | yes |

Opaque proofs are not part of the checked environment, so editing a proof
does not invalidate its users. A proof cache hit still goes through the core
kernel.

## Actions and blobs

An action is one step of a kind (`verify`, `lower`, `codegen`, …) on named
inputs; the caller names exactly the inputs that can change the result.

```text
action-v1 = UTF8("tauto-action-v1\0") || frame(kind) || u64be(number of inputs)
            || for each input, by name bytes: frame(UTF8(name)) || frame(SHA256(value))
blob-v1   = SHA256(UTF8("tauto-blob-v1\0") || bytes)
```

`frame` is as in `source-v1`. Identical outputs of different actions are
stored once.

```text
$TAUTO_BUILD (else $XDG_CACHE_HOME/tauto/build, else ~/.cache/tauto/build)
  blobs/<hex>      outputs, read-only
  actions-v2/<hex> action records: input digests, outputs
  last-v2/<hex>    last key per kind and subject
  tmp/             in-progress writes
```

Files are written to `tmp/` and renamed; a record is written only after its
blobs. Blobs are rehashed on read. No locks: concurrent writers write the same
bytes. Records are versioned, length-delimited and fully validated; anything
malformed is a miss. `explain` reports a hit, a first run, changed / added /
removed inputs, or a lost blob.

## Rust runtime reuse

A host debug build of a crate depending only on `tauto-rt` (no
`rust.dependencies`, no bridge) builds `tauto-rt` once per rustc, runtime
sources and features as action `rust-runtime`, links its `rlib`s into
`target/tauto/target/rt/<key>/`, and compiles the generated code with rustc
directly (`-C incremental`). Cargo resolves the runtime's dependencies with the
same minimum publish age as the generated crate. The runtime cache key
includes that minimum. Release builds, other targets, and runtimes whose
dependencies link native libraries go through Cargo.

## Machine bytecode reuse

`tauto run` of a tote on the machine (the default backend) keeps the bytecode
it compiled and the permissions the program needs as action `vm-program`,
under the same inputs as the kept crate of `--backend rust`: the SHA-256 of
the tauto executable, the arguments other than `--allow-…`, the tote's source
files in order, and the state of every path reading it depended on. While all
of them are unchanged, a run checks the permissions and starts the machine on
the kept bytecode without reading, checking or compiling the tote again. A
run that fails to read, check or compile keeps nothing. A run from kept
bytecode is not given to the JIT, which needs the compiled program; it runs
the same program on the machine alone.

## Trust

A blob is only bytes this machine made. Cached checks are keyed by the
checker itself and re-checked by the core kernel. Steps whose inputs cannot all
be named are not cached, and results made elsewhere are never imported.
