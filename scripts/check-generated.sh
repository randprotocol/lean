#!/usr/bin/env bash
# Regenerates every file under Rand/Generated/ from the pinned circuits commit and fails
# on any difference from what is committed (generated files are never edited by hand).
#
# RAND_SOURCES_LOCAL_CIRCUITS=/path/to/zkp-circuits fetches from a local clone instead.
set -euo pipefail
cd "$(dirname "$0")/.."

scripts/fetch-sources.sh circuits
(cd exporter && cargo build --locked --quiet)
bin=exporter/target/debug/air2lean

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/RV32"
"$bin" alu        --out "$tmp/RV32/Alu.lean"
"$bin" alu-honest --out "$tmp/RV32/AluHonest.lean"
"$bin" alu-vectors --out "$tmp/RV32/AluVectors.lean"
"$bin" tables     --out "$tmp/RV32/Tables.lean"

if ! diff -r "$tmp" Rand/Generated; then
  echo "check-generated: Rand/Generated/ differs from the exporter's output (diff above)" >&2
  exit 1
fi
echo "check-generated: ok"
