#!/usr/bin/env bash
# A focused example check, not the workspace's full verification gate.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

cli=${TAUTO_BIN:-target/debug/tauto}
if [[ $cli != /* ]]; then cli="$PWD/$cli"; fi
[[ -x $cli ]] || { printf 'Build tauto first, or set TAUTO_BIN to its executable.\n' >&2; exit 2; }
command -v node >/dev/null || { printf 'Node is required for the JavaScript check.\n' >&2; exit 2; }
output=$(mktemp -d "${TMPDIR:-/tmp}/tauto-bounded-batch.XXXXXXXX")
# Keep the source bundle and measurements for inspection, including on failure.
printf 'Evidence directory: %s\n' "$output"
export TAUTO_LANG=en
export TAUTO_CACHE=off
cp examples/bounded-batch/src/main.taut "$output/main.taut"
cp examples/bounded-batch/Tauto.eure "$output/Tauto.eure"
SECONDS=0
step() {
  local label=$1 started=$SECONDS
  shift
  "$@"
  printf '%s\t%s\n' "$label" "$((SECONDS - started))" >> "$output/seconds.tsv"
}

step proof "$cli" check examples/bounded-batch/src/batch.taut --fresh --summary > "$output/check.txt"
step bundle "$cli" trust bundle . examples/bounded-batch/src/batch.taut > "$output/source-bundle.json"
# Verify from a directory without repository sources. The bundle is source-only.
(
  cd "$output"
  step replay "$cli" trust verify source-bundle.json --axiom-free > verify.json
)
for backend in eval rust javascript vm; do
  entry=(examples/bounded-batch)
  # Eval requires an explicit tote flag; compiled backends recognize the directory.
  if [[ $backend == eval ]]; then entry=(--tote examples/bounded-batch); fi
  step "$backend" "$cli" run --backend "$backend" "${entry[@]}" > "$output/$backend.stdout"
done
for backend in rust javascript vm; do
  diff -u "$output/eval.stdout" "$output/$backend.stdout"
done
# Independent expected values for the concrete scenario, also asserted by the case runner.
cat > "$output/expected.stdout" <<'EXPECTED'
first = Cons(7, Cons(7, Nil))
remaining = Cons(9, Nil)
last = Cons(9, Nil)
drained = Nil
paused = Nil
paused remaining = Cons(7, Cons(7, Cons(9, Nil)))
oversized = Cons(7, Cons(7, Cons(9, Nil)))
oversized remaining = Nil
empty = Nil
empty remaining = Nil
EXPECTED
diff -u "$output/expected.stdout" "$output/eval.stdout"
# Refuse a run whose checked source, driver, or manifest changed while checking.
step source_unchanged "$cli" trust bundle . examples/bounded-batch/src/batch.taut > "$output/source-bundle-after.json"
cmp "$output/source-bundle.json" "$output/source-bundle-after.json"
cmp "$output/main.taut" examples/bounded-batch/src/main.taut
cmp "$output/Tauto.eure" examples/bounded-batch/Tauto.eure
printf 'Checked proofs, axiom-free source replay, and four matching executions.\n'
printf 'This is regression evidence for extraction and backends, not a proof of them.\n'
cat "$output/seconds.tsv"
printf 'Total seconds: %s\n' "$SECONDS"
