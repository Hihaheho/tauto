#!/usr/bin/env bash
# Lean 4.34.1: download a fixed official binary archive and verify its SHA-256.
# Usage: bash setup-lean-4.34.1.sh [ABSOLUTE_INSTALL_DIRECTORY]
# Default: <current directory>/.tools/lean-4.34.1
# Requirements: Bash, curl, unzip, and sha256sum or shasum.
# No sudo, elan, PATH changes, remote installer scripts, or project dependencies.
# The destination must not already exist. This script does not execute Lean.
# Pins verified on 2026-10-21 (Asia/Tokyo) against:
# https://api.github.com/repos/leanprover/lean4/releases/tags/v4.34.1
# https://lean-lang.org/doc/reference/latest/releases/v4.34.1/
# These hashes pin the GitHub assets; they are not an independent signature.
# Install only in a directory whose parent is controlled by you.
set -euo pipefail
umask 077

fail() { printf 'Error: %s\n' "$*" >&2; exit 1; }
[[ $# -le 1 ]] || fail 'Expected at most one install-directory argument.'

version='4.34.1'
case "$(uname -s)/$(uname -m)" in
  Linux/x86_64)
    platform='linux'
    sha256='3013aba02bb8bf31b1cf8c9d956d60fb95bb1c10920dfe91abcaa59cb461ddac'
    ;;
  Linux/aarch64|Linux/arm64)
    platform='linux_aarch64'
    sha256='b4bcf1d79f1b5859c04625058d3707701d87a65815f7f0686a1f14df821954c5'
    ;;
  Darwin/x86_64)
    platform='darwin'
    sha256='60b45c76003a4561fb66d7ec2003569006d255d2860179445e56d3e2a029090e'
    ;;
  Darwin/arm64|Darwin/aarch64)
    platform='darwin_aarch64'
    sha256='9019fcd34e93fddf0ecf9d40d28f05a86ba563ac3b701a9c5116ce1c96379360'
    ;;
  *) fail 'Supported systems: Linux or macOS, x86_64 or arm64.' ;;
esac

for tool in curl unzip; do
  command -v "$tool" >/dev/null 2>&1 || fail "Required command not found: $tool"
done
if command -v sha256sum >/dev/null 2>&1; then
  hash_command=(sha256sum)
elif command -v shasum >/dev/null 2>&1; then
  hash_command=(shasum -a 256)
else
  fail 'sha256sum or shasum is required.'
fi

install_dir="${1:-$(pwd -P)/.tools/lean-$version}"
[[ "$install_dir" == /* ]] || fail 'The install directory must be an absolute path.'
[[ ! -e "$install_dir" && ! -L "$install_dir" ]] || fail "Destination already exists: $install_dir"
parent_dir="$(dirname "$install_dir")"
mkdir -p "$parent_dir"
work_dir="$(mktemp -d "$parent_dir/.lean-download.XXXXXXXX")"
trap 'rm -rf -- "$work_dir"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

archive_root="lean-$version-$platform"
url="https://github.com/leanprover/lean4/releases/download/v$version/$archive_root.zip"
printf 'Downloading %s.zip (approximately 0.8-0.9 GB)...\n' "$archive_root"
curl --disable --fail --location --silent --show-error \
  --proto '=https' --proto-redir '=https' --tlsv1.2 \
  --connect-timeout 20 --max-time 1800 --retry 3 \
  --output "$work_dir/archive.zip" "$url"

actual_sha256="$("${hash_command[@]}" < "$work_dir/archive.zip")"
actual_sha256="${actual_sha256%% *}"
[[ "$actual_sha256" == "$sha256" ]] || fail 'SHA-256 mismatch. Nothing was extracted or executed.'
printf 'SHA-256 verified. Extracting...\n'

# Ignore optional unzip settings inherited from the invoking shell.
unset UNZIP UNZIPOPT
unzip -q "$work_dir/archive.zip" -d "$work_dir/unpacked"
source_dir="$work_dir/unpacked/$archive_root"
[[ -d "$source_dir" && ! -L "$source_dir" ]] || fail 'Unexpected archive layout.'
[[ -x "$source_dir/bin/lean" && -x "$source_dir/bin/lake" ]] || fail 'Expected executables are missing.'

# Reserve a new destination atomically; never merge with an existing install.
mkdir "$install_dir"
shopt -s dotglob nullglob
contents=("$source_dir"/*)
mv -- "${contents[@]}" "$install_dir/"
printf 'Installed Lean %s. Executable paths:\n%s\n%s\n' \
  "$version" "$install_dir/bin/lean" "$install_dir/bin/lake"
