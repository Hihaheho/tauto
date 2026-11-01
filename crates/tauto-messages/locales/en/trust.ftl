# The messages of `tauto trust`: source bundles of proofs.

trust-usage = usage: tauto trust bundle ROOT ENTRY | tauto trust verify BUNDLE [--axiom-free]
trust-error = trust: { $error }
trust-file-error = { $path }: { $error }
trust-not-regular-file = input must be a regular file
trust-input-too-large = input exceeds byte limit
trust-input-not-utf8 = input is not UTF-8
trust-rooted-read = cannot read rooted source { $name }: { $error }
trust-export-unsupported = source-bundle export requires directory-relative no-follow file access on this platform; verification is portable
trust-invalid-path = invalid bundle path: { $name }
trust-import-not-relative = imports must be relative bundle paths, not URLs or absolute paths
trust-import-empty-component = empty import path component
trust-import-escapes = import escapes bundle root
trust-reader-errors = source has reader errors
trust-unsupported-statement = source-bundle v1 supports import, theorem, axiom, def, inductive, fn, extern and effect declarations only; modules, macros, syntax, resources and executable top-level statements are unsupported
trust-unsupported-term = macros, syntax literals, quotes, nested declarations and include_text are unsupported in source-bundle v1
trust-root-not-dir = ROOT must be a directory
trust-bundle-too-large = serialized bundle exceeds byte limit
trust-cyclic-import = cyclic import
trust-graph-limit = source graph exceeds limit
trust-no-std-file = the standard library has no file { $file }
trust-source-bytes-limit = source bytes exceed limit
trust-invalid-source-count = invalid source count
trust-hash-mismatch = source hash mismatch: { $path }
trust-unreachable-sources = bundle contains unreachable source files
trust-extern-instances = extern instances are unsupported in source-bundle v1
trust-declaration-failed = { $file }: { $name }: { $error }
trust-incomplete-proof = { $file }: { $name }: incomplete proof
trust-import-depth = import depth exceeds limit
trust-missing-source = missing bundled source: { $name }
trust-invalid-bundle = invalid bundle: { $error }
trust-unknown-format = unknown bundle format
trust-report-differs = recomputed report differs; claims, checker executable or evidence changed
trust-axioms-rejected = receiver policy rejects explicit or used axioms
trust-checker-differs = checker executable identity differs

# Approving what a run is trusted with: the `trust` section and `--permissions FILE`.
trust-gate-question = Approve and run? [y/N]
trust-gate-no-terminal = not approved: there is no terminal to ask at; review the above and pass --approve-trust to approve it
trust-gate-not-approved = not approved; nothing was run
trust-gate-new = { $title } has not been approved before:
trust-gate-changed = { $title } changed since it was approved:
trust-gate-nothing-trusted = (nothing is trusted any more)
trust-gate-file-error = { $path }: { $error }
trust-gate-trust-section = The trust section of { $path }
trust-gate-permissions-file = The permissions file { $path }
