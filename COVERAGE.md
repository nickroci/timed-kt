# Source → Lean coverage map

Maintenance rule: every change that formalizes, retires, or renames a public-facing
result must update this file. Consult this map before formalizing anything; if a row
exists, build on the named theorems instead of re-deriving them.

Sources:

- **Levin73** — L. Levin, *Universal sequential search problems* (1973): the `Kt`
  measure and its machine-invariance.
- **LV** — Li, Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*: standard facts about K and time-bounded K.
- **KC-lib** — the `kolmogorov_complexity` library (pinned dependency): the untimed
  layer this package builds on.

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
| **Conditioning** `Kt(x\|y) ≤ Kt(x) + O(1)` — here with constant `0` (refuted outright for the parent's fuel measure) | LV | `Kt_cond_le_Kt` (`Kt.lean`), `condKt_flagged_cond_le_plain` (`Flagged.lean`) | ✅ |
| Conditioning for the write measure, constant `0` | — | `Wt_cond_le_Wt` (`WriteOnce.lean`) | ✅ |
| Time-side invariance over code-realized timed decompressors with linear simulation bounds | Levin73 | `condKt_timedUniversal_le` (`Invariance.lean`); public form at `+2`: `Kt_cond_le_realized` | ✅ (scoped to the stated class) |
| Comparison class inhabited | — | `idTimed`, `idTimedRealization` (`Invariance.lean`) | ✅ |
| `K(x\|y) ≤ Kt(x\|y)` over the same machine, bitstring `K` | LV | `K_cond_le_Kt_cond`, `K_le_Kt` (`Kt.lean`) | ✅ |
| `Kt(x\|y) ≤ \|x\| + O(1)` | LV | `Kt_cond_le_length` (`Kt.lean`) | ✅ |
| Witness upper bounds from concrete runs | — | `Kt_cond_le_of_runs`, `condKt_le_of_runs` | ✅ |
| Finiteness ↔ producibility | — | `Kt_cond_lt_top_iff` | ✅ |
| Triangle/composition inequality `Kt(x\|z) ≤ Kt(x\|y) + Kt(y\|z) + c` | LV | needs an explicit program combiner on the universal tape with bit-length and runtime overhead | ❌ |
| Untimed description-side invariance | KC-lib | `Kolmogorov.existsIsOptimalConditional` (dependency) | ✅ upstream |

## The write-once ledger

| Result | Source | Lean | Status |
|---|---|---|---|
| Write ledger of the universal machine; uniqueness of `(x, t, w)` | parent V2 | `UniversalRunsW`, `UniversalRunsW.unique` (`WriteOnce.lean`) | ✅ |
| Write-priced complexity `Wt_cond`, `Wt` (`min {\|p\| + ⌈log₂ w⌉}`) | parent `writeLevin` | `Wt_cond`, `Wt` (`WriteOnce.lean`) | ✅ |
| `Wt ≤ Kt` — additive, zero overhead (vs. multiplicative-only against the fuel clock) | new here | `Wt_cond_le_Kt_cond`, `Wt_le_Kt` | ✅ |
| `Kt ≤` write witness `+ O(log description)` per witness | new here | `Kt_cond_le_of_universalRunsW` | ✅ |
| `K ≤ Wt`; `Wt(x\|y) ≤ \|x\| + c` with explicit `c` | parent `K_le_writeLevin` | `K_cond_le_Wt_cond`, `Wt_cond_le_length` | ✅ |
| Bit-content ledger and production-dominates-output | parent V2 | `traceBits`, `size_output_le_traceBits` (`Trace.lean`) | ✅ |
| Write/transition separation instance (linear, not unbounded) | parent V2 | `precLoop_ledgers` (`Examples.lean`) | ✅ |
| Measure-level `Kt ≤ Wt + O(1)` (uniform additive constant) | open in parent | as open against the step clock as against fuel; the per-witness log penalty is the proven form | ❌ |
| Bit-priced (`traceBits`) complexity measure | parent V2 | not defined here | ➖ (route exists via `UniversalRunsW`) |

## The legacy fuel measure (regression layer)

| Result | Source | Lean | Status |
|---|---|---|---|
| Least-fuel cost | parent project | `minFuel` (`FuelCost.lean`) | ✅ |
| Fuel diverges unboundedly from writes | parent project | `fuel_exceeds_writes_unboundedly` | ✅ |
| Successor: constant transitions, linear fuel | parent project | `succ_transitions_constant_fuel_linear` (`Examples.lean`) | ✅ |
| Writes/transitions linearly equivalent per fixed code | parent project | `Run.length_le_steps`, `Run.steps_le`, `Run.sandwich` | ✅ |
| Full fuel-priced `FuelKt` measure (renamed old `Kt`, chain rule, log-relativization) | parent project | not ported; lives in the parent tree under its old names | ➖ (port on demand) |

## Open items

- Triangle/composition inequality (the one ❌ above): requires a program combiner
  `p₁ ⊕ p₂` on the universal tape and its runtime accounting.
- Linear-overhead self-simulation of `timedUniversal` (a `Realization` of the
  universal machine by itself); equivalently, a fuel-free self-interpreter with a
  proved linear slowdown.
- Exact `Kt` values for small concrete strings (`native_decide`-free evaluation
  strategy needed).
- Migration of the parent `irreducibility` tree onto this package (renaming its
  fuel-priced `Kt` family per `KT_CORRECTION_TODO.md` step 1).
