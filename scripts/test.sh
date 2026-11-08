#!/usr/bin/env bash
# A focused run is development feedback, not the final verification gate.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
checkout=$(pwd -P)

case "${1:-}" in
  focused)
    shift
    if [[ $# -eq 0 ]]; then
      echo 'usage: scripts/test.sh focused <cargo test selection and arguments>' >&2
      exit 2
    fi
    mode=focused
    ;;
  full)
    if [[ $# -ne 1 ]]; then
      echo 'The full gate accepts no filters or skip arguments.' >&2
      exit 2
    fi
    mode=full
    ;;
  *)
    echo 'usage: scripts/test.sh focused <cargo test selection and arguments> | full' >&2
    exit 2
    ;;
esac

fail() { printf '%s\n' "$*" >&2; exit 2; }

# An exact user override is accepted only for an empty or same-checkout cache.
# A complete marker is installed atomically; unknown existing data is untouched.
claim_directory() {
  local directory=$1 owner temporary entry
  mkdir -p -- "$directory" || fail "Cannot create build directory: $directory"
  directory=$(cd -- "$directory" && pwd -P) || fail "Cannot resolve build directory: $directory"
  owner="$directory/.tauto-checkout"
  [[ ! -L "$owner" ]] || fail "Refusing a symlink checkout marker: $owner"
  if [[ ! -e "$owner" ]]; then
    [[ -r "$directory" && -x "$directory" ]] || fail "Cannot inspect build directory: $directory"
    shopt -s dotglob nullglob
    for entry in "$directory"/*; do
      [[ -e "$owner" ]] || fail "Unowned nonempty build directory preserved: $directory. Unset CARGO_TARGET_DIR/CARGO_BUILD_BUILD_DIR before selecting an empty TAUTO_TEST_CACHE_ROOT, or choose an empty exact directory."
      break
    done
    temporary=$(mktemp "$directory/.tauto-owner.XXXXXXXX") || fail "Cannot prepare checkout marker: $directory"
    printf '%s' "$checkout" > "$temporary" || fail "Cannot write checkout marker: $temporary"
    ln -- "$temporary" "$owner" 2>/dev/null || true
    rm -- "$temporary"
  fi
  [[ -f "$owner" && ! -L "$owner" ]] || fail "Checkout marker is not an ordinary file: $owner"
  cmp -s "$owner" <(printf '%s' "$checkout") || fail "Build directory belongs to another checkout: $directory. Choose a distinct cache namespace or empty exact directory; existing contents are preserved."
  printf '%s' "$directory"
}

if [[ $mode == focused ]]; then
  for argument in "$@"; do
    [[ $argument != -- ]] || break
    case "$argument" in
      --target-dir|--target-dir=*|--manifest-path|--manifest-path=*|--config|--config=*|-m|-C)
        fail 'Select focused packages with -p; use the guarded directory environment overrides, not Cargo directory/config arguments.'
        ;;
      --*|-?|-vv) ;;
      -?*) fail 'Use separate short-option values or long options; clustered short options can override checkout identity.' ;;
    esac
  done
fi

if [[ -n ${TAUTO_TEST_CACHE_ROOT:-} ]]; then
  [[ -z ${CARGO_TARGET_DIR:-} && -z ${CARGO_BUILD_BUILD_DIR:-} ]] || fail 'Choose TAUTO_TEST_CACHE_ROOT or exact Cargo directory overrides, not both.'
  # Keeping the full canonical path avoids ambiguous shortened checkout names.
  target="$TAUTO_TEST_CACHE_ROOT/checkouts/${checkout#/}"
else
  target=${CARGO_TARGET_DIR:-"$checkout/target"}
fi
export CARGO_TARGET_DIR
CARGO_TARGET_DIR=$(claim_directory "$target")
build=${CARGO_BUILD_BUILD_DIR:-"$CARGO_TARGET_DIR"}
[[ $build != *'{'* && $build != *'}'* ]] || fail 'Use a concrete CARGO_BUILD_BUILD_DIR, not a path template.'
build=$(claim_directory "$build")
# A fixed inherited build directory defeats a child's own target isolation.
# Apply the outer override as Cargo configuration, not a child environment value.
unset CARGO_BUILD_BUILD_DIR
build_toml=${build//\\/\\\\}
build_toml=${build_toml//\"/\\\"}
build_toml=${build_toml//$'\n'/\\n}
build_toml=${build_toml//$'\r'/\\r}
build_toml=${build_toml//$'\t'/\\t}
build_toml=${build_toml//$'\b'/\\b}
build_toml=${build_toml//$'\f'/\\f}
build_config="build.build-dir=\"$build_toml\""

if [[ $mode == focused ]]; then
  echo 'Focused tests only; run scripts/test.sh full before final verification.' >&2
  exec cargo --config "$build_config" test --locked "$@"
fi
cargo --config "$build_config" test --locked --workspace
cargo --config "$build_config" build --locked -p tauto-cli --bin tauto
printf '%s\0' std/*.taut meta/*.taut | xargs -0 -n1 -P8 cargo --config "$build_config" run -q --locked -p tauto-cli --bin tauto -- check
cargo --config "$build_config" run --locked -p tauto-cli --bin tauto -- lint std/*.taut std/prelude/*.taut meta/*.taut
cargo --config "$build_config" run --locked -p tauto-cli --bin tauto -- fmt --check std/*.taut std/prelude/*.taut meta/*.taut
