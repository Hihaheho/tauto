# Reviewing a proof's scope

`src/policy.taut` states a denial property about the function named in its goal.
`crates/tauto-cli/tests/trust_mutations.rs` copies that source into a temporary
directory and mutates the implementation, goal, assumptions, proof target and
trust boundary. It also mutates a captured source bundle's bytes and report.
The source in this directory is never changed by the test.

For a bounded smoke subset using an already-built test binary and CLI, run:

```sh
cargo nextest run --locked -p tauto-cli --test trust_mutations trust_smoke --no-capture
```

The smoke subset makes six CLI calls: baseline export and axiom-free replay,
stale-hash rejection, rehashed bad-implementation rejection, and weakened-goal
export and axiom-free replay. Its total CLI deadline is 45 seconds; a timeout
fails rather than skips the check. That deadline does not include Cargo builds.
Its JSON report identifies the subset, omitted checks, and each command's time.
It does not check proof holes, assumptions, axioms, externs, wrong targets,
report concealment, or stale checkouts, and does not replace the full matrix.

Run the full mutation matrix with:

```sh
cargo nextest run --locked -p tauto-cli --test trust_mutations distinguish_rejection --no-capture
```

This command may build the test and CLI first. Later runs reuse Cargo's build
outputs. The experiment itself does not build or execute generated programs,
download dependencies, or use a proof cache. Each CLI invocation has a
30-second deadline; a timeout is a failed experiment, never a rejected proof.

`TAUTO_MUTATION_REPORT` selects a new JSON file for the full matrix observations. Existing
files are not overwritten. `TAUTO_MUTATION_CLI` can select an already-built
executable instead of Cargo's CLI. The report records that override, the
checker's executable hash, the invocation count, each command's time, and elapsed time. A package
version or executable hash is not evidence of the source revision that built it.

The observations distinguish automatic rejection from information that a
reviewer must examine. An accepted bundle is not evidence that the original
requirement, assumptions or implementation target stayed unchanged.
`--axiom-free` excludes explicit axioms, not theorem parameters or external
functions. An offline bundle describes its captured source, not a current
checkout or a compiled executable.

The test asserts these distinctions rather than treating every accepted
mutation as a checker defect. A passing experiment covers only its finite
mutations. It does not establish checker soundness, correctness of the original
requirement, or that a generated executable implements the proved function.
