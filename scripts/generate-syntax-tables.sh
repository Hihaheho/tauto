#!/usr/bin/env bash
# Writes totes/syntax/src/tables.taut and totes/syntax/src/tables/<name>.txt,
# the tables of the parser and the scanner of crates/tauto-parol/tauto.par.
# Run it after every change to the grammar. With --check, writes nothing and
# fails if a file is out of date.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo run --locked -q --manifest-path tools/selfhost-harness/Cargo.toml --bin write-syntax-tables -- "$@"
