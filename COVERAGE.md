# Source → Lean coverage map

Maintenance rule: every change that formalizes, retires, or renames a public-facing
result must update this file. Consult this map before formalizing anything; if a row
exists, build on the named theorems instead of re-deriving them.

Sources:

- **Levin73** — L. A. Levin, *Universal sequential search problems*, Problemy
  Peredachi Informatsii 9(3):115–116, 1973
  ([bibliographic record](https://www.mathnet.ru/eng/ppi914)): the `Kt` measure and
  its machine-invariance.
- **LV** — M. Li and P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*, 3rd ed., Springer 2008; resource-bounded complexity is Chapter 7
  (Kt and universal search, §7.5): standard facts about K and time-bounded K.
- **KC-lib** — the
  [`kolmogorov_complexity`](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean)
  library, pinned at commit `f11c8f01` (see `lake-manifest.json`): the untimed layer
  this package builds on.

Rows with source "—" are constructions of this package (the operational ledgers, the
fuel comparison layer, and the write/bit-priced measures) rather than formalizations
of a specific literature statement.

Status legend: ✅ formalized · 🟡 partial / scoped · ❌ not started · ➖ out of scope.

## Definitions

| Result | Source | Lean | Status |
|---|---|---|---|
| Conditional Kt over a timed machine, `min {\|p\| + ⌈log₂ t⌉}` as `ENat` infimum | Levin73 | `TimedDecompressor.condKt`, `plainKt` (`Timed.lean`) | ✅ |
| Public `Kt`, `Kt_cond` at the universal machine | Levin73 | `Kt`, `Kt_cond` (`Kt.lean`) | ✅ |
| Ceiling log characterization (least `k` with `t ≤ 2^k`) | — | `ceilLog2_isLeast` (`CeilLog2.lean`) | ✅ |
| Natural-number wrapper | — | `natKt`, `natKt_le` (`Kt.lean`) | ✅ |

## The timed machine

| Result | Source | Lean | Status |
|---|---|---|---|
| Flagged universal machine (context-erasure flag) and its clocked relation | standard machine convention | `flaggedUniversal`, `FlaggedRuns`, `timedFlaggedUniversal` (`Flagged.lean`) | ✅ |
| Fuel-free operational semantics for `Nat.Partrec.Code` | — | `Run` (`Run.lean`) | ✅ |
| `Run` sound and complete for `Code.eval` | — | `exists_run_iff_exists_tracen` + `evaln_of_tracen` (`Run.lean`, `Trace.lean`) | ✅ |
| Determinism: unique trace and transition count | — | `Run.deterministic`, `numSteps_eq_of_run` (`Run.lean`) | ✅ |
| Clocked universal machine; clock-forgetting is definitional | — | `UniversalRuns`, `timedUniversal_toMap` (`UniversalRun.lean`) | ✅ |
| Soundness/completeness of the clocked relation | — | `universalRuns_iff_produces` (`UniversalRun.lean`) | ✅ |
| Existence/uniqueness of the transition count per successful run | — | `UniversalRuns.unique` (`UniversalRun.lean`) | ✅ |

## Invariance and bounds

| Result | Source | Lean | Status |
|---|---|---|---|
| **Conditioning** `Kt(x\|y) ≤ Kt(x) + O(1)` — here with constant `0` | LV | `Kt_cond_le_Kt` (`Kt.lean`), `condKt_flagged_cond_le_plain` (`Flagged.lean`) | ✅ |
| Conditioning for the write measure, constant `0` | — | `Wt_cond_le_Wt` (`WriteOnce.lean`) | ✅ |
| Time-side invariance over code-realized timed decompressors with linear simulation bounds | Levin73 | `condKt_timedUniversal_le` (`Invariance.lean`); public form at `+2`: `Kt_cond_le_realized` | ✅ (scoped to the stated class) |
| Comparison class inhabited | — | `idTimed`, `idTimedRealization` (`Invariance.lean`) | ✅ |
| `K(x\|y) ≤ Kt(x\|y)` over the same machine, bitstring `K` | LV | `K_cond_le_Kt_cond`, `K_le_Kt` (`Kt.lean`) | ✅ |
| `Kt(x\|y) ≤ \|x\| + O(1)` | LV | `Kt_cond_le_length` (`Kt.lean`) | ✅ |
| Witness upper bounds from concrete runs | — | `Kt_cond_le_of_runs`, `condKt_le_of_runs` | ✅ |
| Finiteness ↔ producibility | — | `Kt_cond_lt_top_iff` | ✅ |
| Triangle/composition inequality `Kt(x\|z) ≤ Kt(x\|y) + Kt(y\|z) + c` | LV | needs an explicit program combiner on the universal tape with bit-length and runtime overhead | ❌ |
| Untimed description-side invariance | KC-lib | `Kolmogorov.existsIsOptimalConditional` (dependency) | ✅ upstream |

## Attainment and information transfer

| Result | Source | Lean | Status |
|---|---|---|---|
| Attainment: a finite `condKt` is attained by an actual run | — | `TimedDecompressor.exists_runs_condKt` (`InfoTransfer.lean`) | ✅ |
| Everywhere-finiteness of the public measures | — | `Kt_cond_lt_top`, `Kt_lt_top`, `Wt_lt_top` (`InfoTransfer.lean`) | ✅ |
| Witness runtime bound: an optimal run within `2 ^ Kt(x\|y)` transitions | — | `exists_run_time_le_two_pow_Kt_cond` (`InfoTransfer.lean`) | ✅ |
| Information transfer `Kt(x) − Kt(x\|y)`, analogue of `I(y : x) = K(x) − K(x\|y)` | LV | `ktTransfer`, `ktTransfer_add_Kt_cond`, `ktTransfer_le_Kt`, `ktTransfer_lt_top`, `ktTransfer_empty` (`InfoTransfer.lean`) | ✅ |
| Transfer halves runtime: `Kt(x) = m` and transfer `g` give a run within `2 ^ (m − g)` | — | `exists_run_time_le_two_pow_of_ktTransfer` (`InfoTransfer.lean`) | ✅ |
| Information transfer for the write measure | — | `wtTransfer`, `wtTransfer_add_Wt_cond`, `wtTransfer_le_Wt`, `wtTransfer_lt_top`, `wtTransfer_empty` (`InfoTransfer.lean`) | ✅ |

## The write-once ledger

| Result | Source | Lean | Status |
|---|---|---|---|
| Write ledger of the universal machine; uniqueness of `(x, t, w)` | — | `UniversalRunsW`, `UniversalRunsW.unique` (`WriteOnce.lean`) | ✅ |
| Write-priced complexity `Wt_cond`, `Wt` (`min {\|p\| + ⌈log₂ w⌉}`) | — | `Wt_cond`, `Wt` (`WriteOnce.lean`) | ✅ |
| `Wt ≤ Kt` — additive, zero overhead | new here | `Wt_cond_le_Kt_cond`, `Wt_le_Kt` | ✅ |
| Finiteness ↔ producibility for the write measure | — | `Wt_cond_lt_top_iff` | ✅ |
| `Kt ≤` write witness `+ O(log description)` per witness | new here | `Kt_cond_le_of_flaggedRunsW` | ✅ |
| `K ≤ Wt`; `Wt(x\|y) ≤ \|x\| + c` with explicit `c` | — | `K_cond_le_Wt_cond`, `Wt_cond_le_length`, `Wt_le_length` | ✅ |
| Bit-content ledger and production-dominates-output | — | `traceBits`, `size_output_le_traceBits` (`Trace.lean`) | ✅ |
| Write/transition separation instance (linear, not unbounded) | — | `precLoop_ledgers` (`Examples.lean`) | ✅ |
| Measure-level `Kt ≤ Wt + O(1)` (uniform additive constant) | — | as open against the step clock as against fuel; the per-witness log penalty is the proven form | ❌ |
| Bit-priced (`traceBits`) complexity measure: `Bt_cond`, `Bt`; ledger forgetting; uniqueness of `(x, t, b)`; witness bound; `K ≤ Bt`; finiteness ↔ producibility; conditioning constant `0` | — | `UniversalRunsB`, `FlaggedRunsB`, `Bt_cond`, `Bt`, `Bt_cond_le_of_flaggedRunsB`, `K_cond_le_Bt_cond`, `Bt_cond_lt_top_iff`, `Bt_cond_le_Bt` (`BitCost.lean`) | ✅ |
| Comparison of `Bt` with `Wt` or `Kt` (either direction) | — | per-run ledger domination fails both ways (unbounded `Nat.size` up, `Nat.size 0 = 0` down); no measure-level route proved | ❌ |

## The fuel clock (the rejected alternative)

| Result | Source | Lean | Status |
|---|---|---|---|
| Least-fuel cost | — | `minFuel` (`FuelCost.lean`) | ✅ |
| Fuel diverges unboundedly from writes | — | `fuel_exceeds_writes_unboundedly` | ✅ |
| Successor: constant transitions, linear fuel | — | `succ_transitions_constant_fuel_linear` (`Examples.lean`) | ✅ |
| Writes/transitions linearly equivalent per fixed code | — | `Run.length_le_steps`, `Run.steps_le`, `Run.sandwich` | ✅ |
| A fully developed fuel-priced measure (its own chain rule and relativization theory) | — | not developed here; `minFuel` exists only as the comparison point for the divergence theorems | ➖ (out of scope) |

## Hygiene and CI

| Check | Lean / script | Status |
|---|---|---|
| Headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound` | `scripts/check_axioms.sh` (CI step after the build) | ✅ |

## Open items

- Comparison of `Bt` with `Wt` or `Kt`: the pointwise route is closed both ways, so
  any inequality needs a genuinely different argument (or a refutation).
- Triangle/composition inequality (the ❌ above): requires a program combiner
  `p₁ ⊕ p₂` on the universal tape and its runtime accounting.
- Linear-overhead self-simulation of `timedUniversal` (a `Realization` of the
  universal machine by itself); equivalently, a fuel-free self-interpreter with a
  proved linear slowdown.
- Exact `Kt` values for small concrete strings (`native_decide`-free evaluation
  strategy needed).
