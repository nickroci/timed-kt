#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "== forbidden constructs and resource overrides =="
if grep -RInE '\b(axiom|admit|unsafe|implemented_by|native_decide)\b|set_option (maxHeartbeats|maxRecDepth)' \
    TimedKt TimedKt.lean comparator 2>/dev/null; then
  echo "ERROR: forbidden construct or resource override found"
  exit 1
fi

echo "== sorry-free project =="
if grep -RInE '\bsorry\b|sorryAx' TimedKt TimedKt.lean 2>/dev/null; then
  echo "ERROR: sorry found"
  exit 1
fi

# Comparator trusted statements (comparator/*/): only the Challenge file may contain sorry; it is
# the placeholder file comparator checks against Solution. (Source grep; the exact check is the
# build log of `lake build ComparatorKtHeadline`, where only Challenge may report `sorry`.)
echo "== sorry-free comparator Statement/Solution (Challenge exempt) =="
if grep -RInE '\bsorry\b|sorryAx' comparator --include='*.lean' 2>/dev/null \
    | grep -vE '^comparator/[^/]+/Challenge\.lean:'; then
  echo "ERROR: sorry found outside a comparator Challenge file"
  exit 1
fi

echo "== imports, suppressions, and measurement scaffolding =="
if grep -RInE '^import Mathlib$|#nolint|set_option linter\.|#count_heartbeats|set_option profiler true|trace_state' \
    TimedKt comparator --include='*.lean' 2>/dev/null; then
  echo "ERROR: broad import, linter suppression, or temporary scaffolding found"
  exit 1
fi

echo "== no Levin claim about the fuel measure =="
if grep -RIni 'levin' TimedKt/FuelCost.lean TimedKt/Trace.lean 2>/dev/null; then
  echo "ERROR: 'Levin' appears in a fuel-measure module"
  exit 1
fi

echo "== project-level linter debt =="
if grep -nE '^(weak\.)?linter\..*= *false\b' lakefile.toml; then
  echo "ERROR: strict linters disabled in lakefile"
  exit 1
fi

echo "audit OK"
