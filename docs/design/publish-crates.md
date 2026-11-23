# `tauto publish-crates`

Publishes an existing Cargo workspace in three steps: plan, check, submit. It
does not generate crates, edit versions, commit, tag, push or yank. It needs a
Cargo with multi-package package/publish and never works around a Cargo that
lacks it.

## `plan`

Requires `--manifest-path`, `--registry`, `--out` and `--workspace` or `-p`;
there are no implicit defaults. `publish = false` packages are excluded from
`--workspace` and rejected by `-p`; a manifest's registry restriction must
match.

The plan and its release directory are written outside the workspace, never
over existing ones, owner-only on Unix. The plan records versions, targets and
exclusion reasons, file lists, source hashes, and the identity of the Cargo
executable, config and environment, never tokens.

Sources are copied to a snapshot. In Git, only tracked files, and uncommitted
or untracked changes are rejected; without Git, regular files. Symlinks,
special files and paths that look like credentials are rejected (this is not a
secret scanner; review the file list). Git metadata and
`.cargo_vcs_info.json` are not copied; the remaining file lists must match.
Rejected also: path dependencies outside the workspace, Cargo config in
ancestors outside the workspace, config `include`, quoted or escaped keys, and
ignored workspace config missing from the snapshot. Workspace and Cargo home
config are allowed. After any change, make a new plan.

Cargo runs offline and locked. This is not a network sandbox.

## `check`

Runs Cargo's offline, locked package verification on the snapshot (which
builds the packaged crates; registry state is not consulted), checks that
build-time resources such as syntax tables and `include_text` files are in the
archive, and records the archive hashes. Checking runs build scripts and
compilers: only use trusted sources and config.

## `apply` and `resume`

Both require `--confirm` with the full hash of the reviewed plan. Auth is
Cargo's; the registry name is always passed.

`apply` repeats the check and refuses if anything changed (archives must be
deterministic). It records `submitted-unknown`, lets Cargo publish the
workspace in order, and records `cargo-confirmed` only on success. Publishing
is not atomic: after a failure some packages may be published. Cargo output is
neither parsed nor stored, since it may contain secrets. Cargo repackages at
submission; the archive is compared before and after, which detects but cannot
undo a mismatch. Hostile build scripts, concurrent writers and the toolchain
are not isolated.

`resume` never resubmits a confirmed plan and stops on an unknown one. Check
the registry for versions and checksums, then plan the unpublished packages
anew. Never reset the state file to resubmit; remove a stale lock only after
checking what was sent.

Tests use a fake local Cargo and never publish.
