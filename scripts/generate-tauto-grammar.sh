#!/usr/bin/env bash
# The stage-zero grammar files are projections of Tauto's syntax declaration.
set -euo pipefail
cd "$(dirname "$0")/.."

check=0
[ "${1:-}" = "--check" ] && check=1
out=$(mktemp)
trap 'rm -f "$out"' EXIT
cargo run --locked --quiet -p tauto-cli -- syntax source totes/grammar tauto >"$out"

status=0
for file in crates/tauto-parol/tauto.par crates/tauto-syntax/tests/data/tauto.par; do
  if [ "$check" = 1 ]; then
    cmp -s "$out" "$file" || {
      echo "$file is out of date; run: bash scripts/generate-tauto-grammar.sh" >&2
      status=1
    }
  else
    cp "$out" "$file"
  fi
done
exit "$status"
