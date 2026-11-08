# Source bundles and trust reports

`tauto trust bundle ROOT ENTRY` writes a JSON source bundle to standard output.
`ENTRY` is a relative path within the explicitly chosen `ROOT`. The bundle holds
that source and the transitive closure of relative imports, sorted by logical
path, with SHA-256 hashes of their UTF-8 bytes. It contains the actual proof
terms in the source, not a cached assertion that a proof passed. Export does not
write, fetch dependencies, run a program or invoke a backend.

`tauto trust verify BUNDLE` reads the bundle, checks its format and source hashes,
resolves imports only within its source map, and checks its declarations again.
It constructs a fresh kernel without connecting the proof cache; `TAUTO_CACHE`
cannot enable reuse. The derived report must equal the stored report. Missing,
unreachable, cyclic or escaping dependencies are errors. No source is extracted
onto the verifier's filesystem. A source path never becomes a verifier-side file
read, URL, package lookup or shell command.

## Evidence and scope

The report contains each kernel declaration's status and transitive user-axiom
dependencies. It also inventories explicit axioms, external function names,
declared effects and written function effect rows. Source hashes bind the full
signatures and bodies, not just those inventories. An absent effect annotation
is represented separately from an explicitly empty row.

A skipped declaration is not a verified executable body. External function
implementations, runtime behavior, effect guarantees, generated code and
compiled binaries are not certified. External signatures and effect declarations
are listed as unchecked statements, and so is each function whose body calls
`expose` ([`secret.md`](secret.md)): it makes a secret public. The report describes the ordinary Rust
kernel path; it does not assert that two independent implementations replayed
all declarations. The trusted prelude is checked by that kernel as usual and is
part of the checker's executable, not an imported source file.

The checker record gives its package version and the SHA-256 of the verifier's
executable file, read through a bounded buffer. This identifies the opened file's
bytes, not the already mapped process image: replacing an executable path can
make those differ. It is not runtime attestation. The source revision is unknown, explicitly represented as
`null`; the package version is not a source revision or a unique build ID. Exact
report comparison requires the same executable bytes. A different checker build
must produce a fresh report; a matching version string alone is insufficient.
There is no claim of reproducible builds, authenticated distribution or binary
correspondence with any particular source commit.

Hashes and deterministic reports establish consistency, not authorship. A party
can edit source and produce a consistent report by checking it again. Such a
bundle is accepted if its proofs check; this is not signature forgery. A receiver
who requires no additional axioms uses `tauto trust verify BUNDLE --axiom-free`.
That policy belongs to the receiving invocation, not to an editable field in the
bundle. It rejects even an unused explicit axiom. Axiom-free proof declarations
still do not certify external functions or skipped executable code.

## Closed source protocol

The source protocol accepts `import`, `module`, `theorem`, `axiom`, `def`,
`inductive`, `fn`, `extern` and `effect` declarations (those in a `module` too).
It first parses every file directly, without the macro expander, and refuses
macros, syntax literals, quotes, nested declarations, resource includes, package
manifests and executable top-level statements. It then reads the files with the
loader `tauto check` uses, from the bundle's own sources instead of the disk, so
that modules, visibility and qualified names mean what they mean when the files
are checked; the kernel is given the declarations the loader produces. A module
import is only `import std::Name`, read from the standard library that comes
with the checker; a bundled `<std>/` file must equal the checker's own copy.
Imports of a dependency tote are refused. Function and proof blocks may contain local value bindings,
assignments, loops, returns and expressions, but not declarations of other kinds.
A bundle cannot carry a precompiled proof artifact or request a different
verification algorithm. Unsupported fields and source forms are errors rather
than a fallback to ambient files. The protocol is not a general package archive.

Only the explicitly named bundle file and the receiver's executable are read by
verification. Source export uses directory-relative no-follow file access on Unix
systems, requiring regular files and refusing links in every source path
component. Directory descriptors preserve confinement when source directories
are renamed. Export on platforms without that implementation is refused;
verification never needs it. The chosen root is a trusted local input, not a
path supplied by a received bundle. Concurrent source writes may affect the
snapshot captured by export; the report checks precisely the bytes captured,
not a claim of an atomic filesystem revision.

## Limits

The JSON document is limited to 8 MiB, with at most 256 source files, 1 MiB per
source and an import depth below 64. Logical paths are bounded and relative;
absolute paths, URLs, backslashes, empty components and root escapes are refused.
Duplicate source keys and unknown structured fields are errors. These are input
limits, not CPU, memory or wall-clock limits for parsing and kernel normalization.
Receivers of hostile proofs must run the checker within their own process
resource limits. This protocol does not promise denial-of-service isolation.

The protocol's end-to-end cases are in
`crates/tauto-cli/tests/trust_bundle.rs`.
