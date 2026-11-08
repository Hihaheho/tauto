#!/usr/bin/env bash
# Writes the tables of the grammars in crates/tauto/tests/syntax_fixtures/*.par
# and cases/macro/grammars/*.par as <sha256>.tables to
# crates/tauto/tests/syntax_fixtures/.tauto-syntax and cases/macro/.tauto-syntax,
# with the tote totes/llkgen. With --check, fails if a table is out of date,
# missing or left over.
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)

cd "$REPO_ROOT"

# The generator is the tote totes/syntaxgen, which runs totes/llkgen (it
# reads a grammar on standard input).
# It is compiled into `tauto` (`tauto --tote-main syntaxgen`), so the
# `tauto` this checkout builds runs it, so no separate release build of the
# tote is needed.
cargo build --locked --quiet -p tauto-cli
TAUTO=$(cargo metadata --format-version 1 --no-deps | sed -n 's/.*"target_directory":"\([^"]*\)".*/\1/p')/debug/tauto
GEN=("$TAUTO" --tote-main syntaxgen)
export TAUTO_STEP_LIMIT=200000000000
check=0
[ "${1:-}" = "--check" ] && check=1
if command -v sha256sum >/dev/null 2>&1; then
  hash_command=(sha256sum)
elif command -v shasum >/dev/null 2>&1; then
  hash_command=(shasum -a 256)
else
  echo 'sha256sum or shasum is required.' >&2
  exit 1
fi

status=0
for DIR in crates/tauto/tests/syntax_fixtures cases/macro/grammars; do
  TABLES=$( [ "$DIR" = cases/macro/grammars ] && echo cases/macro/.tauto-syntax || echo "$DIR/.tauto-syntax" )
  if [ "$check" = 0 ]; then
    mkdir -p "$TABLES"
  fi
  expected=$(mktemp)
  for par in "$DIR"/*.par; do
    sha=$("${hash_command[@]}" "$par" | cut -d' ' -f1)
    echo "$sha.tables" >>"$expected"
    table="$TABLES/$sha.tables"
    out=$(mktemp)
    "${GEN[@]}" --allow-read -- <"$par" >"$out"
    if [ "$check" = 1 ]; then
      cmp -s "$out" "$table" || { echo "$table is out of date; run: bash scripts/generate-syntax-fixtures.sh" >&2; status=1; }
      rm -f "$out"
    else
      mv "$out" "$table"
    fi
  done
  for table in "$TABLES"/*.tables; do
    [ -e "$table" ] || continue
    grep -qx "$(basename "$table")" "$expected" || {
      if [ "$check" = 1 ]; then echo "$table has no grammar; run: bash scripts/generate-syntax-fixtures.sh" >&2; status=1; else rm -f "$table"; fi
    }
  done
  rm -f "$expected"

done
exit "$status"
