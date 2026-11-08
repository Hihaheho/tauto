#!/usr/bin/env bash
# Writes totes/unicode/src/tables.taut with totes/unicode/src/tables/<name>.txt,
# from the Unicode data of the Rust toolchain the repository pins
# (rust-toolchain.toml), and totes/pargen/src/uni.taut with
# totes/pargen/src/uni/<name>.txt, from the Unicode classes of regular
# expressions of the regex-syntax crate (the version tools/selfhost-harness
# pins), which parol reads the regular expressions with when it makes the
# committed tables that tools/selfhost-harness/tests/llkgen.rs compares
# totes/llkgen with. With --check, writes nothing and fails if a file is out
# of date.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo run --locked -q --manifest-path tools/selfhost-harness/Cargo.toml --bin write-unicode-tables -- "$@"
