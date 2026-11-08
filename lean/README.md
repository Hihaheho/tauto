# Lean 4 formalization of Tauto and Nib

Lean models of Tauto's kernel, of Nib's semantics and ownership, and
of macro hygiene and expansion. What each module proves, what it assumes and
what is open is in [`docs/design/lean.md`](../docs/design/lean.md).

Not everything is proved. Strong normalization of the full kernel (`TypedSN`)
and its consistency (`Consistent`) are stated as propositions in
`Proto/Kernel/Normalization.lean`, not proved (strong normalization and
consistency are proved for the predicative fragment, `typedP_sn` and
`consistent_pred`); the completeness of the bidirectional checker
(`Proto/Kernel/BidirComplete.lean`) takes `TypedSN` as a hypothesis; the
ownership analysis (`Proto/Analysis.lean`) does not prove that the translation
of Nib into constraints emits a constraint for every run-time copy; and the
re-check of typed macros (`Proto/Macro/Plug.lean`) leaves out the half for
executable code.

`lake build` passes with Lean 4.34.1, with no `sorry` and no axiom beyond
Lean's own `propext`, `Classical.choice` and `Quot.sound`. To check this for
the main theorems, run after the build:

```bash
ELAN='' LAKE_OVERRIDE_LEAN=false "$LEAN_DIR/bin/lake" env lean Proto/AxiomAudit.lean
```

Each `#print axioms` line must list no axiom outside those three.

## Lean toolchain setup

The Lean binary is installed from the official release, pinned by version and
SHA-256, into `.tools/lean-<version>/` (git-ignored), and called by absolute
path; no toolchain manager, `sudo` or `PATH` change (`ELAN=''` below keeps
`lake` from looking for one). The setup script is
`scripts/setup-lean-4.34.1.sh`:

```bash
bash scripts/setup-lean-4.34.1.sh "$PWD/.tools/lean-4.34.1"
```

Then build with:

```bash
LEAN_DIR="$PWD/.tools/lean-4.34.1"
cd lean && ELAN='' LAKE_OVERRIDE_LEAN=false \
  "$LEAN_DIR/bin/lake" --keep-toolchain --no-cache build
```

If the hash does not match, stop and find out why; never edit the expected
hash to continue. `lean-toolchain` names the same version, 4.34.1.

## Requirements

Lean 4 **v4.34.1**, installed as above. The project has no third-party Lean
dependencies.

```bash
lake build
# or explicitly:
lake env lean Proto.lean
```

Inspect any compilation failure before considering a theorem proven.
