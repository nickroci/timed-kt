#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Re-elaborate every project module so linter warnings surface even on cached
# builds, and fail on any warning. (Warnings do not fail `lake build` by
# themselves; this gate makes the zero-warning standard enforceable.)
log=$(mktemp)
trap 'rm -f "$log"' EXIT

find TimedKt -name '*.lean' -exec touch {} +
touch TimedKt.lean
lake build 2>&1 | tee "$log"

if grep -E "warning:" "$log" >/dev/null; then
  echo "ERROR: build produced warnings"
  grep -E "warning:" "$log"
  exit 1
fi
echo "strict build OK (no warnings)"
