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
cargo run --locked --manifest-path tools/selfhost-harness/Cargo.toml --bin source-bundle -- ROOT OUTPUT
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

## Explicit complete-input plans

`--contract-inputs BUNDLE` audits an ordered set of original source roots and
their imports and literal `include_text!` resource references. It does not expand
macros, check proofs, generate a program, or run one. `--contract-bundle BUNDLE
ENTRY` uses the same original input plan and import loader, then performs the
source-reader substitution below before attempting compilation. Unsupported
declarations, including unused imported proofs, remain in that input.

The host supplies trusted build metadata and exact UTF-8 file bytes. The
`source-bundle --tote-inputs ROOT TOTE ALLOWLIST OUTPUT` command reads only the
portable file IDs listed in ALLOWLIST; blank lines and lines beginning with `#`
are ignored. It does not recursively collect files or discover Tauto imports.
The allowlist must name dependency manifests, source files and resources. A
missing backing file, invalid UTF-8, symlink or escape rejects packaging; the
output must not already exist.

Manifest selection uses the captured `Tauto.eure` bytes. Dependencies are
ordered by name, selected source paths are sorted, and the entry package's main
files come last. Dependency main files are not implicit roots. The selected
roots and all supplied file bytes enter the bundle; no source is printed again,
stripped, extracted or checked by the host producer. Host-specific backend
configuration is unsupported rather than replaced with defaults.

The complete-input wire format is `TAUTO-SOURCES-2\n`, a decimal root count and
newline, then for each ordered root its decimal ID byte length, newline, ID
bytes and newline. The file count and file records follow in the same framing
as version 1. File IDs are unique; root order is preserved, and repeated roots
are visited once. There must be at least one root, every root must have a file,
and root and file counts are each at most 4096. The whole wire remains limited
to 16 MiB. Contents preserve original newlines, NUL bytes and UTF-8 byte offsets.
Decimal fields contain one to eight digits. The existing 256-unit traversal
budget counts import edges and top-level statement traversal, not just depth;
exhaustion is explicitly unsupported rather than partial input success.
Version 2 additionally bounds each ID and written/resolved import or resource
path to 4096 UTF-8 bytes and 256 slash-separated components, before recursive
normalization. Oversized wire IDs are input errors; oversized language paths
are unsupported input-resource limits, not source-language rejection. Version 1
is unchanged.
Non-UTF-8 fixture inputs are outside this transport's scope, not converted to
replacement text.

The Tauto loader resolves each import and resource path relative to its original
file ID. Its audit prints `S<TAB>ID<TAB>START<TAB>END` for dependency-ordered
sources and `R<TAB>RESOURCE<TAB>ORIGIN<TAB>START<TAB>END<TAB>BYTES` for resource
references. Source ranges refer to the original files concatenated with one
newline; resource spans are local to the original source file. Resource entries
record availability, not macro execution. Nonliteral resource requests reject
the audit as unsupported.
Resources cannot leave the nearest supplied ancestor containing `Tauto.eure`,
or the source file's own directory when there is no such manifest. Leaving and
then re-entering that boundary is also rejected; supplying an outside file does
not grant access to it.

The opt-in complete-input commands write one `TAUTO-RUSTGEN-CONTRACT/2 STATUS`
record on standard error. `input-complete` is inventory evidence only;
`generated` alone permits target compilation. `load-rejected` identifies an
actual Tauto import resolution failure; `source-rejected` identifies
a source/compiler rejection. `input-error` and `tables-error` are infrastructure
failures, and `input-unsupported` does not satisfy a semantic rejection contract.
`resource-rejected` is a static resource-audit failure only; it satisfies neither
`load_error` nor `macro_error`.
Failures exit with status 1, have one nonempty diagnostic line, and emit no
partial target or audit output. Ordinary and version-1 commands retain their
protocol.

The strict shared-case adapter preserves path-tagged file inputs, virtual file
IDs, entry selection and the extraction request separately from expectations.
Virtual files and their internal imports use this loader. Disk-backed inputs
require an explicit reviewed allowlist; mixed external/virtual namespaces,
fixture templates, invalid UTF-8 and extraction requests remain incomplete
where their input semantics are not implemented. Audit success never supplies
proof, macro, type, build or runtime observations.
In particular, a resource-audit rejection does not satisfy a shared
`macro_error` assertion, even when its diagnostic names the same resource.

`tools/selfhost-harness/tests/data/rustgen-inputs.txt` declares the compiler's
permitted build inputs. The `input_bundle` test compares the Tauto-resolved
source/resource graph and original bytes with an independent host input oracle;
the oracle does not construct the tested bundle. A single-file import graph
does not include all package-selected roots, such as Unicode class tables and
dependency proof files. Complete input delivery does not establish compiler
selfcompilation or a stage fixed point.

Run `cargo test --locked --manifest-path tools/selfhost-harness/Cargo.toml --test bootstrap_graph`. It compares
source order and byte ranges against the existing host loader, executes emitted
Rust after removing its input bundle, and submits the original compiler graph
without removing proof declarations. Acceptance of that graph is not a stage1
compiler or a stage2 fixed point; unsupported compilation must fail without
partial Rust output. Host filesystem IO and the initial compiler build remain
Rust responsibilities.

The complete-input and strict-adapter checks are separate targets:

```sh
cargo test --locked -p tauto-test-suite --test selfhost
cargo test --locked --manifest-path tools/selfhost-harness/Cargo.toml --test shared_cases --test input_bundle
```

## Source-reader substitution

`--contract-reader BUNDLE` substitutes written `include_text!` calls using only
original bytes supplied by the input plan. `--contract-bundle` performs that same
reader pass before the existing limited Rust emitter. The original source,
ordered roots and dependency-ordered per-file statements remain available;
resource lookup is relative to each original source file, not the entry file.
The reader preserves each replaced call's byte span and the exact UTF-8 resource
text, including CRLF, NUL, empty content and the presence of a final newline.
It does not edit or reparse the original source or recursively read resource text.

Only an argument that the parser reads as a Text literal is accepted. Variables,
function calls and computed paths are not evaluated. Written quote bodies and
ordinary expression arguments of other macros are traversed, but syntax-literal
contents remain opaque. As in the host reader, ordinary function, extern and
class-method `where` constraints are not traversed; instance constraints are.
This is source reading, not user macro evaluation.
Attributes, generated clauses, law declarations and `decreasing_by` reject as
unsupported because the Surface representation does not preserve their complete
terms or metadata. Unknown Surface terms/statements and traversal exhaustion
also reject without partial output.

The resource boundary and portable input limits above remain in force. Missing
supplied resources and invalid literal arguments are semantic reader diagnostics;
nonportable paths, excessive input bounds and unsupported binary transport do not
become language rejection observations. The inventory command still audits paths
without substituting anything, including its unchanged unsupported result for a
dynamic resource path.

`reader-complete` prints the source/resource report followed by
`TAUTO-READER-SURFACE/1` and the substituted Surface dump. This dump is not the
expanded-source printer required by a shared `expands` assertion. It establishes
neither macro-evaluator success nor compilation. `reader-rejected` carries the
original source ID, local start/end byte offsets and an `include.*` diagnostic;
`reader-unsupported` is incomplete evidence. The strict adapter records actual
reader diagnostics under the existing shared `macro_error` requirement, with
`reader_implementation` identifying `tauto-source-reader/include_text` and stating
that no macro evaluator ran. Audit errors are never converted to those diagnostics.
A successful reader pass does not satisfy a missing general macro assertion.

The reader regression target is `cargo test --locked --manifest-path tools/selfhost-harness/Cargo.toml --test
reader_include`. Its structural oracle visits the host Surface tree
without executing macros. Tests keep the bundle bytes unchanged, compare resource
values and spans, check unsupported metadata and dynamic arguments, and run emitted
Rust after removing the disposable input bundle. These checks do not establish
proof extraction, Nib-checker integration, a JavaScript target emitter or a compiler
stage fixed point.
