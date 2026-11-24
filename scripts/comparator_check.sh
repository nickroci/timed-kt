#!/usr/bin/env bash
# Run leanprover/comparator on the trusted statements of this package (comparator/config*.json).
#
# Adapted from anthropics/formal-math .github/scripts/comparator-check.sh (Copyright 2026 Anthropic, PBC;
# Apache-2.0, https://www.apache.org/licenses/LICENSE-2.0). Changes from the original:
#   * no `go`, no landrun build. If COMPARATOR_LANDRUN names a real landrun binary (Linux Landlock) it is
#     used. Otherwise comparator is pointed at the fake-landrun shim shipped in the comparator repo
#     (scripts/fake-landrun.sh), which runs every child process WITHOUT any sandbox: a Solution that
#     tampers with the check is then not excluded, and the result is reported as "unsandboxed".
#   * lean4export is taken at the tag named after the project's toolchain only (no vX.Y.0 fallback).
#   * `--tools-only` builds the tools and stops.
#
# Run from the package root (the directory holding lakefile.toml / lean-toolchain), after `lake build`:
#     ./scripts/comparator_check.sh [--tools-only] [CONFIG.json ...]
# Default configurations: comparator/config*.json. Needs elan, git, cargo, jq.
# Prints PASS only if comparator prints "Your solution is okay!" (statement match, standard axioms only,
# Lean kernel replay and nanoda replay of the exported Solution closure).
set -euo pipefail

cd "$(dirname "$0")/.."

COMPARATOR_COMMIT="${COMPARATOR_COMMIT:-575674928e239f5bc452aab72d1dd7b0f1326494}"
NANODA_COMMIT="${NANODA_COMMIT:-68d5ca9db226849b41a6fff59d796ff19d0a8840}"
TOOLS_DIR="${TOOLS_DIR:-$HOME/.cache/lean-ci-tools}"
LOG_DIR="${LOG_DIR:-$PWD/.lake/comparator-logs}"

die() { echo "error: $*" >&2; exit 1; }

tools_only=""
if [ "${1:-}" = "--tools-only" ]; then tools_only=1; shift; fi

[ -f lean-toolchain ] || die "run this from a project directory containing lean-toolchain"
for tool in git cargo jq lean lake; do
  command -v "$tool" >/dev/null 2>&1 || die "$tool is required"
done

toolchain="$(tr -d '[:space:]' < lean-toolchain)"
tag="v${toolchain#*:v}"
if [ -z "${LEAN4EXPORT_COMMIT:-}" ]; then
  refs="$(git ls-remote https://github.com/leanprover/lean4export "refs/tags/$tag" "refs/tags/$tag^{}")"
  LEAN4EXPORT_COMMIT="$(awk -v t="refs/tags/$tag^{}" '$2==t {print $1}' <<<"$refs")"
  [ -n "$LEAN4EXPORT_COMMIT" ] || LEAN4EXPORT_COMMIT="$(awk -v t="refs/tags/$tag" '$2==t {print $1}' <<<"$refs")"
  [ -n "$LEAN4EXPORT_COMMIT" ] || die "leanprover/lean4export has no release $tag for toolchain $toolchain"
fi

if [ "$#" -gt 0 ]; then
  configs=("$@")
else
  shopt -s nullglob
  configs=(comparator/config*.json)
  shopt -u nullglob
fi
[ -n "$tools_only" ] || [ "${#configs[@]}" -gt 0 ] || die "no comparator configuration found"

mkdir -p "$TOOLS_DIR/bin" "$LOG_DIR"

checkout_at() {  # <url> <dir> <commit>
  if [ ! -d "$2/.git" ]; then
    git clone --quiet --filter=blob:none "$1" "$2"
  fi
  if [ "$(git -C "$2" rev-parse HEAD)" != "$3" ]; then
    git -C "$2" fetch --quiet --depth 1 origin "$3"
    git -C "$2" checkout --quiet --detach "$3"
  fi
}

echo "== comparator @ $COMPARATOR_COMMIT"
checkout_at https://github.com/leanprover/comparator.git "$TOOLS_DIR/comparator" "$COMPARATOR_COMMIT"
(cd "$TOOLS_DIR/comparator" && lake build comparator)
comparator_bin="$TOOLS_DIR/comparator/.lake/build/bin/comparator"
if [ -n "${COMPARATOR_LANDRUN:-}" ]; then
  landrun_bin="$COMPARATOR_LANDRUN"; mode="sandboxed by $COMPARATOR_LANDRUN"
else
  landrun_bin="$TOOLS_DIR/comparator/scripts/fake-landrun.sh"; mode="unsandboxed"   # shim (see header)
fi

echo "== lean4export @ $LEAN4EXPORT_COMMIT"
checkout_at https://github.com/leanprover/lean4export.git "$TOOLS_DIR/lean4export" "$LEAN4EXPORT_COMMIT"
export_toolchain="$(tr -d '[:space:]' < "$TOOLS_DIR/lean4export/lean-toolchain")"
[ "$export_toolchain" = "$toolchain" ] || die "lean4export $LEAN4EXPORT_COMMIT targets $export_toolchain but the project uses $toolchain"
(cd "$TOOLS_DIR/lean4export" && lake build lean4export)
lean4export_bin="$TOOLS_DIR/lean4export/.lake/build/bin/lean4export"

echo "== nanoda_lib @ $NANODA_COMMIT"
checkout_at https://github.com/robsimmons/nanoda_lib.git "$TOOLS_DIR/nanoda" "$NANODA_COMMIT"
cargo build --release --locked --quiet --manifest-path "$TOOLS_DIR/nanoda/Cargo.toml"
nanoda_bin="$TOOLS_DIR/nanoda/target/release/nanoda_bin"

for bin in "$comparator_bin" "$lean4export_bin" "$nanoda_bin" "$landrun_bin"; do
  [ -x "$bin" ] || die "missing tool $bin"
done
if [ -n "$tools_only" ]; then echo "tools built in $TOOLS_DIR"; exit 0; fi

[ "$mode" != unsandboxed ] || echo "WARNING: unsandboxed run (fake-landrun shim)." >&2
lean_prefix="$(lean --print-prefix)"
export PATH="$lean_prefix/bin:$PATH"
export COMPARATOR_LANDRUN="$landrun_bin"
export COMPARATOR_LEAN4EXPORT="$lean4export_bin"
export COMPARATOR_NANODA="$nanoda_bin"
export LEAN_ABORT_ON_PANIC=1

failures=0
for cfg in "${configs[@]}"; do
  name="$(tr '/' '_' <<<"${cfg%.json}")"
  log="$LOG_DIR/$name.log"
  jq -e '.permitted_axioms - ["propext", "Quot.sound", "Classical.choice"] == []' "$cfg" >/dev/null \
    || die "$cfg: permitted_axioms must be a subset of propext, Quot.sound, Classical.choice"
  checked_cfg="$LOG_DIR/$name.json"
  jq '.enable_nanoda = true' "$cfg" > "$checked_cfg"

  echo "== comparator $cfg  (log: $log)"
  start=$(date +%s)
  set +e
  lake env "$comparator_bin" "$checked_cfg" 2>&1 | tee "$log"
  status="${PIPESTATUS[0]}"
  set -e
  echo "elapsed $(( $(date +%s) - start ))s"
  if [ "$status" -eq 0 ] && grep -qxF 'Your solution is okay!' "$log"; then
    echo "PASS ($mode) $cfg"
  else
    echo "FAIL: comparator did not accept $cfg (exit status $status)"
    failures=$((failures + 1))
  fi
done

[ "$failures" -eq 0 ] || die "$failures comparator configuration(s) not accepted"
echo "All ${#configs[@]} comparator configuration(s) accepted ($mode)."
