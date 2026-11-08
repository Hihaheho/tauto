#!/usr/bin/env bash
# Regenerates crates/tauto-parol/src/generated from tauto.par with parol.
# parol lives only in tools/tauto-parol-gen (its own workspace and lockfile),
# so it never enters the workspace's dependency graph. With --check, fails if the
# committed files differ from what the grammar generates, and leaves them as
# they were.
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
GENERATED=crates/tauto-parol/src/generated

cd "$REPO_ROOT"

check=0
[ "${1:-}" = "--check" ] && check=1

bash scripts/generate-tauto-grammar.sh "${1:-}"

mkdir -p .tmp
before=$(mktemp -d .tmp/tauto-parol-before.XXXXXX)
cp -Rp "$GENERATED/." "$before/"
cleanup() {
  # --check restores the committed files even if generation itself fails.
  if [ "$check" = 1 ]; then
    rm -rf "$GENERATED"
    mkdir -p "$GENERATED"
    cp -Rp "$before/." "$GENERATED/"
  fi
  rm -rf "$before"
}
trap cleanup EXIT

RUSTUP_AUTO_INSTALL=0 cargo run --locked --quiet --manifest-path tools/tauto-parol-gen/Cargo.toml

if [ "$check" = 1 ]; then
  status=0
  diff -r "$before" "$GENERATED" >/dev/null || status=1
  if [ "$status" = 1 ]; then
    echo "$GENERATED is out of date; run: bash scripts/generate-tauto-parol.sh" >&2
    exit 1
  fi
fi
