#!/usr/bin/env bash
# Fails if Rand/ contains sorry/admit/axiom/native_decide, or if any published
# theorem depends on an axiom outside {propext, Classical.choice, Quot.sound}.
set -euo pipefail
cd "$(dirname "$0")/.."

if grep -rnE '\bsorry\b|\badmit\b|^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom\b|\bnative_decide\b' Rand Rand.lean RandTest RandTest.lean Audit.lean 2>/dev/null \
   | grep -v 'Audit.lean:.*native_decide'; then
  echo "audit: forbidden token found (sorry|admit|axiom|native_decide)" >&2
  exit 1
fi

out=$(lake env lean Audit.lean 2>&1) || { echo "$out" >&2; exit 1; }
echo "$out" | grep -v 'module system'
if echo "$out" | grep -q 'error'; then exit 1; fi
echo "audit: ok"
