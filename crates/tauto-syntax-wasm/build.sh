#!/usr/bin/env bash
# Rebuilds the parser the JavaScript backend embeds
# (crates/tauto-jsgen/src/syntax_parser.wasm). Run it after changing
# tauto-syntax; it needs the wasm32-unknown-unknown target.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
target="$(mktemp -d)"
trap 'rm -rf "$target"' EXIT
RUSTFLAGS="-C panic=abort -C opt-level=z -C strip=symbols --remap-path-prefix=$root=. --remap-path-prefix=$HOME=~" \
  cargo build --manifest-path "$here/Cargo.toml" --release --lib \
  --target wasm32-unknown-unknown --target-dir "$target"
cp "$target/wasm32-unknown-unknown/release/tauto_syntax_wasm.wasm" \
  "$root/crates/tauto-jsgen/src/syntax_parser.wasm"
