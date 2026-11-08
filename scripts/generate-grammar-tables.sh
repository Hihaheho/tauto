#!/usr/bin/env bash
# Regenerates the tables in crates/tauto-syntax/tests/data from their grammars
# (math.par, items.par, their LALR(1) copies *_lr.par, and the syntax tauto
# declaration) with the tote totes/syntaxgen. With --check, fails if the
# committed files differ.
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
DATA=crates/tauto-syntax/tests/data

cd "$REPO_ROOT"

# The generator is the tote totes/syntaxgen, which runs totes/llkgen or
# totes/lalrgen (it reads a grammar on standard input).
# It is compiled into `tauto` (`tauto --tote-main syntaxgen`), so the
# `tauto` this checkout builds runs it, so no separate release build of the
# tote is needed.
cargo build --locked --quiet -p tauto-cli
TAUTO=$(cargo metadata --format-version 1 --no-deps | sed -n 's/.*"target_directory":"\([^"]*\)".*/\1/p')/debug/tauto
GEN=("$TAUTO" --tote-main syntaxgen)
export TAUTO_STEP_LIMIT=200000000000

stale=0
generate() {
  local grammar=$1 tables=$2 out
  out=$(mktemp)
  # Standard input is a read, which the host denies unless allowed.
  "${GEN[@]}" --allow-read -- <"$grammar" >"$out"
  if [ "$CHECK" = 1 ]; then
    cmp -s "$out" "$tables" || { echo "$tables is out of date; run: bash scripts/generate-grammar-tables.sh" >&2; stale=1; }
    rm -f "$out"
  else
    mv "$out" "$tables"
  fi
}

CHECK=0
[ "${1:-}" = "--check" ] && CHECK=1

bash scripts/generate-tauto-grammar.sh "${1:-}"

for name in math math_lr items items_lr; do
  generate "$DATA/$name.par" "$DATA/$name.tables"
done
generate "$DATA/tauto.par" "$DATA/tauto.tables"
# The declared parser uses precisely the table generated for this grammar.
sha=$(sed -n 's/^grammar_sha256 //p' "$DATA/tauto.tables")
tote_table="totes/grammar/.tauto-syntax/$sha.tables"
if [ "$CHECK" = 1 ]; then
  cmp -s "$DATA/tauto.tables" "$tote_table" || { echo "$tote_table is out of date" >&2; stale=1; }
else
  mkdir -p "$(dirname "$tote_table")"
  cp "$DATA/tauto.tables" "$tote_table"
fi
for table in totes/grammar/.tauto-syntax/*.tables; do
  [ -e "$table" ] || continue
  if [ "$table" != "$tote_table" ]; then
    if [ "$CHECK" = 1 ]; then
      echo "$table has no grammar; run: bash scripts/generate-grammar-tables.sh" >&2
      stale=1
    else
      rm -f "$table"
    fi
  fi
done
exit "$stale"
