#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Axiom gate: the headline theorems must depend on nothing beyond the three
# axioms of Lean's standard library (propext, Classical.choice, Quot.sound).
# Requires the package oleans (run after `lake build`).

THEOREMS=(
  TimedKt.Kt_cond_le_Kt
  TimedKt.Wt_cond_le_Wt
  TimedKt.TimedDecompressor.exists_runs_condKt
  TimedKt.ktTransfer_add_Kt_cond
  TimedKt.condKt_timedUniversal_le
  TimedKt.Kt_cond_le_realized
  TimedKt.Kt_cond_le_length
  TimedKt.Wt_cond_le_Kt_cond
  TimedKt.Kt_cond_le_of_flaggedRunsW
  TimedKt.Kt_triangle
  TimedKt.Kt_le_Kt_cond_add_Kt
  TimedKt.Wt_triangle
  TimedKt.Bt_triangle
  TimedKt.compRuns_iff_produces
  TimedKt.isDecompressor_compUniversal
  TimedKt.universalRuns_iff_produces
  TimedKt.Run.deterministic
  TimedKt.runBounded_sound
  TimedKt.runBounded_complete
  TimedKt.fuel_exceeds_writes_unboundedly
  TimedKt.ktRate_le_one
  TimedKt.ktRate_eq_zero_of_witnesses
  TimedKt.ktRate_eq_zero_of_uniform_code
  TimedKt.ttKtRate_le_one
  TimedKt.ttKtRate_eq_zero_of_witnesses
  TimedKt.rKt_le_Kt
  TimedKt.rKt_cond_le_Kt
  TimedKt.Kt_cond_le_of_flaggedRuns
  TimedKt.Kt_nil
)

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

{
  echo "import TimedKt"
  for thm in "${THEOREMS[@]}"; do
    echo "#print axioms $thm"
  done
} > "$tmpdir/AxiomGate.lean"

if ! out="$(lake env lean "$tmpdir/AxiomGate.lean" 2>&1)"; then
  echo "ERROR: lean invocation failed"
  echo "$out"
  exit 1
fi

echo "$out"

violations=0
reports=0
while IFS= read -r line; do
  case "$line" in
    *"depends on axioms: ["*)
      reports=$((reports + 1))
      axioms="${line#*depends on axioms: \[}"
      axioms="${axioms%]}"
      IFS=',' read -ra parts <<< "$axioms"
      for ax in "${parts[@]}"; do
        ax="${ax#"${ax%%[![:space:]]*}"}"
        ax="${ax%"${ax##*[![:space:]]}"}"
        case "$ax" in
          propext|Classical.choice|Quot.sound|"") ;;
          *)
            echo "ERROR: disallowed axiom '$ax' in: $line"
            violations=1
            ;;
        esac
      done
      ;;
    *"does not depend on any axioms"*)
      reports=$((reports + 1))
      ;;
  esac
done <<< "$out"

if [ "$violations" -ne 0 ]; then
  exit 1
fi

if [ "$reports" -ne "${#THEOREMS[@]}" ]; then
  echo "ERROR: expected ${#THEOREMS[@]} axiom reports, got $reports"
  exit 1
fi

echo "axiom gate OK: only propext, Classical.choice, Quot.sound"
