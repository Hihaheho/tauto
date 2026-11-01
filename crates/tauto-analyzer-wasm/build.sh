#!/usr/bin/env bash
# Builds tauto_analyzer.wasm, the checker an editor in a browser loads.
# Needs the wasm32-unknown-unknown target. Usage: build.sh OUT_DIR
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
out="${1:?usage: build.sh OUT_DIR}"
target="$(mktemp -d)"
trap 'rm -rf "$target"' EXIT
# getrandom (under query-flow's hash maps) takes its seed from
# `__getrandom_v03_custom` in src/rand.rs.
RUSTFLAGS="--cfg getrandom_backend=\"custom\" -C opt-level=s -C strip=symbols --remap-path-prefix=$root=. --remap-path-prefix=$HOME=~" \
  cargo build --manifest-path "$here/Cargo.toml" --release --lib \
  --target wasm32-unknown-unknown --target-dir "$target"
mkdir -p "$out"
cp "$target/wasm32-unknown-unknown/release/tauto_analyzer_wasm.wasm" "$out/tauto_analyzer.wasm"
