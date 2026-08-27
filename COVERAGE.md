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
- **Lutz03** — J. H. Lutz, *Dimension in complexity classes*, SIAM J. Comput.
  32(5):1236–1259, 2003: resource-bounded (constructive/effective) dimension. The
  Kolmogorov-complexity characterization of constructive dimension as
  `liminf K(Z↾n)/n` is E. Mayordomo, *A Kolmogorov complexity characterization of
  constructive Hausdorff dimension*, Inf. Process. Lett. 84(1):1–3, 2002; the
  `limsup` form corresponds to the strong dimension of K. B. Athreya,
  J. M. Hitchcock, J. H. Lutz, and E. Mayordomo, *Effective strong dimension in
  algorithmic information and computational complexity*, SIAM J. Comput.
  37(3):671–705, 2007.
- **ABKMR** — E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek,
  D. Ronneburger, *Power from random strings*, SIAM J. Comput. 35(6):1467–1493,
  2006: measuring a function family through the complexity of its truth table.
- **Oliveira19** — I. C. Oliveira, *Randomness and intractability in Kolmogorov
  complexity*, ICALP 2019, LIPIcs 132, 32:1–32:14: the randomized time-bounded
  measure `rKt` — success probability at least `2/3`, description and time priced,
  randomness free.
- **GKLO22** — H. Goldberg, V. Kabanets, Z. Lu, I. C. Oliveira, *Probabilistic
  Kolmogorov complexity with applications to average-case complexity*, CCC 2022,
  LIPIcs 234, 16:1–16:60: probabilistic Kolmogorov measures (`pK`, `pKt`) and their
  average-case theory.

Rows with source "—" are constructions of this package (the operational ledgers, the
fuel comparison layer, and the write/bit-priced measures) rather than formalizations
of a specific literature statement.

Status legend: ✅ formalized · 🟡 partial / scoped · ❌ not started · ➖ out of scope.

## Definitions

| Result | Source | Lean | Status |
|---|---|---|---|
| Conditional Kt over a timed machine, `min {\|p\| + ⌈log₂ t⌉}` as `ENat` infimum | Levin73 | `TimedDecompressor.condKt`, `plainKt` (`Timed.lean`) | ✅ |
| Public `Kt`, `Kt_cond` at the composing universal machine | Levin73 | `Kt`, `Kt_cond` (`Kt.lean`) | ✅ |
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
| Self-delimiting length code with exact parse and primrec decoder | Elias-gamma convention | `gammaCode`, `gammaParse_eq_some_iff`, `gammaCode_append_inj`, `primrec_gammaParse` (`Gamma.lean`) | ✅ |
| Composing universal machine (comp flag, erase bit, gamma split, recursion) | — | `compUniversal`, fuel invariance `compEvalFuel_eq_of_lt` (`Comp.lean`) | ✅ |
| Computability of the composing machine (stack machine + `Partrec.fix`) | — | `compStep`, `compUniversal_eq_fix`, `isDecompressor_compUniversal` (`CompPartrec.lean`) | ✅ |
| Clocked composing relation; soundness/completeness; uniqueness of `(x, t)` | — | `CompRuns`, `compRuns_iff_produces`, `CompRuns.unique`, `timedCompUniversal` (`CompRun.lean`) | ✅ |
| Transfer: composing machine ≤ flagged machine `+ 2` | — | `condKt_comp_le_condKt_flagged` (`CompRun.lean`) | ✅ |

## Invariance and bounds

| Result | Source | Lean | Status |
|---|---|---|---|
| **Conditioning** `Kt(x\|y) ≤ Kt(x) + O(1)` — here with constant `0` | LV | `Kt_cond_le_Kt` (`Kt.lean`), `condKt_comp_cond_le_plain` (`CompRun.lean`), `condKt_flagged_cond_le_plain` (`Flagged.lean`) | ✅ |
| Conditioning for the write measure, constant `0` | — | `Wt_cond_le_Wt` (`WriteOnce.lean`) | ✅ |
| Time-side invariance over code-realized timed decompressors with linear simulation bounds | Levin73 | `condKt_timedUniversal_le` (`Invariance.lean`); public form at `+4`: `Kt_cond_le_realized` | ✅ (scoped to the stated class) |
| Comparison class inhabited | — | `idTimed`, `idTimedRealization` (`Invariance.lean`) | ✅ |
| `K(x\|y) ≤ Kt(x\|y)` over the same machine, bitstring `K` | LV | `K_cond_le_Kt_cond`, `K_le_Kt` (`Kt.lean`) | ✅ |
| `Kt(x\|y) ≤ \|x\| + O(1)` | LV | `Kt_cond_le_length` (`Kt.lean`) | ✅ |
| Witness upper bounds from concrete runs | — | `Kt_cond_le_of_runs`, `condKt_le_of_runs` | ✅ |
| Finiteness ↔ producibility | — | `Kt_cond_lt_top_iff` | ✅ |
| **Triangle/composition inequality**: `Kt_cond x y = n₁ → Kt_cond y z = n₂ → Kt_cond x z ≤ n₁ + n₂ + 3 * ceilLog2 (n₁ + 1) + 7` (explicit constant) — the logarithmic delimitation term is necessary for any plain-style (non-prefix-free) program format (an injective packing of two arbitrary programs into one costs a log on some inputs); a uniform constant is the property of a prefix-free sibling measure, not of plain `Kt` | LV | `Kt_triangle` (`Triangle.lean`); composition as a machine primitive (comp flag, erase bit, gamma split, recursion) | ✅ |
| Easy direction of symmetry of information: `Kt(x) ≤ Kt(x\|y) + Kt(y) + 3 ⌈log₂⌉ + 7` | LV | `Kt_le_Kt_cond_add_Kt` (`Triangle.lean`), triangle at `z = []` | ✅ |
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
| Write ledger of the universal machines; uniqueness of `(x, t, w)` | — | `UniversalRunsW`, `FlaggedRunsW`, `CompRunsW`, with `.unique` at each layer (`WriteOnce.lean`) | ✅ |
| Write-priced complexity `Wt_cond`, `Wt` (`min {\|p\| + ⌈log₂ w⌉}`) | — | `Wt_cond`, `Wt` (`WriteOnce.lean`) | ✅ |
| `Wt ≤ Kt` — additive, zero overhead | new here | `Wt_cond_le_Kt_cond`, `Wt_le_Kt` | ✅ |
| Finiteness ↔ producibility for the write measure | — | `Wt_cond_lt_top_iff` | ✅ |
| `Kt ≤` write witness `+ O(log description)` per witness | new here | `Kt_cond_le_of_flaggedRunsW` | ✅ |
| `K ≤ Wt`; `Wt(x\|y) ≤ \|x\| + c` with explicit `c` | — | `K_cond_le_Wt_cond`, `Wt_cond_le_length`, `Wt_le_length` | ✅ |
| Attainment for the ledger measures (infimum realized by an actual ledgered run) | — | `exists_compRunsW_Wt_cond`, `exists_compRunsB_Bt_cond` (`Triangle.lean`) | ✅ |
| Ledger triangles: `Wt_cond x z ≤ m₁ + m₂ + 2 * ceilLog2 (m₁ + 1) + 4`, same for `Bt_cond` | — | `Wt_triangle`, `Bt_triangle` (`Triangle.lean`) | ✅ |
| Bit-content ledger and production-dominates-output | — | `traceBits`, `size_output_le_traceBits` (`Trace.lean`) | ✅ |
| Write/transition separation instance (linear, not unbounded) | — | `precLoop_ledgers` (`Examples.lean`) | ✅ |
| Measure-level `Kt ≤ Wt + O(1)` (uniform additive constant) | — | as open against the step clock as against fuel; the per-witness log penalty is the proven form | ❌ |
| Bit-priced (`traceBits`) complexity measure: `Bt_cond`, `Bt`; ledger forgetting; uniqueness of `(x, t, b)`; witness bound; `K ≤ Bt`; finiteness ↔ producibility; conditioning constant `0` | — | `UniversalRunsB`, `FlaggedRunsB`, `CompRunsB`, `Bt_cond`, `Bt`, `Bt_cond_le_of_compRunsB`, `K_cond_le_Bt_cond`, `Bt_cond_lt_top_iff`, `Bt_cond_le_Bt` (`BitCost.lean`) | ✅ |
| Comparison of `Bt` with `Wt` or `Kt` (either direction) | — | per-run ledger domination fails both ways (unbounded `Nat.size` up, `Nat.size 0 = 0` down); no measure-level route proved | ❌ |

## The asymptotic layer

| Result | Source | Lean | Status |
|---|---|---|---|
| Sequence prefixes with length and prefix-monotonicity | — | `seqPrefix`, `seqPrefix_length`, `seqPrefix_prefix` (`Asymptotic.lean`) | ✅ |
| The `ℕ`-valued profile `Kt(Z↾n)`, grounded by finiteness, with the `ENat` bridge | — | `ktProfile`, `ktProfile_cast` | ✅ |
| Hardcode ceiling at the profile: `ktProfile Z n ≤ n + c` | LV (length upper bound) | `ktProfile_le` | ✅ |
| The rate `limsup Kt(Z↾n)/n` in `ℝ≥0∞` | Lutz03 (constructive dimension), time-bounded analogue | `ktRate` | ✅ |
| Rate ceiling: `ktRate Z ≤ 1` for every sequence | Lutz03, time-bounded analogue of the dimension ceiling | `ktRate_le_one` | ✅ |
| Collapse ladder, level 1 — nonuniform prefix witnesses (sublinear advice): vanishing description and log-runtime densities force rate `0` | — | `ktRate_eq_zero_of_witnesses` | ✅ |
| Collapse ladder, level 2 — one fixed code, arbitrary (possibly noncomputable) input family: code-uniform with advice inputs | — | `ktRate_eq_zero_of_code` | ✅ |
| Collapse ladder, level 3 — fully uniform: one fixed code on the canonical input `Nat.bits n`, no advice; description density discharged internally | — | `ktRate_eq_zero_of_uniform_code`, `bits_length_le_ceilLog2_succ`, `eventually_mul_ceilLog2_succ_le`, `tendsto_ceilLog2_succ_div_atTop_nhds_zero` | ✅ |
| Characteristic-sequence framing: canonical enumeration, characteristic sequence and its rate (enumeration-dependent — **not** the ABKMR truth table) | — | `bitStringEnum`, `charSeq`, `charSeqKtRate`, `charSeqKtRate_le_one`, `charSeqKtRate_eq_zero_of_witnesses` | ✅ |
| Truth tables per arity: lexicographic enumeration of length-`n` inputs (counted, complete, duplicate-free), the `2 ^ n`-bit table, its profile, and the rate normalized by table length; ceiling and witness collapse | ABKMR (meta-complexity convention) | `lexStrings`, `lexStrings_length`, `mem_lexStrings`, `lexStrings_nodup`, `truthTable`, `truthTable_length`, `ttProfile`, `ttKtRate`, `ttKtRate_le_one`, `ttKtRate_eq_zero_of_witnesses` | ✅ |
| Code-uniform collapse for the per-arity truth-table rate (a level-2/3 analogue over the `2 ^ n` denominator) | — | not stated; only the witness form `ttKtRate_eq_zero_of_witnesses` is proved | ❌ |
| Write-measure rate and its comparison to the time rate | — | `wtProfile`, `wtProfile_cast`, `wtRate`, `wtRate_le_ktRate` | ✅ |
| A sequence of positive `Kt`-rate and zero `K`-rate (computational depth as a density) | — | not constructed; the layer provides only the bracketing theorems | ❌ |

## The probabilistic layer

| Result | Source | Lean | Status |
|---|---|---|---|
| Random tapes (`Fin R → Bool`, `2 ^ R` of them), success within a time cutoff, success count, two-thirds majority — parameterized by how the tape enters the context | Oliveira19 (convention) | `card_randomTapes`, `SucceedsOn`, `successCountAt`, `successCount`, `HasMajorityAt`, `HasMajority` (`Probabilistic.lean`) | ✅ |
| Monotonicity in the time bound (definitional from the `∃ t' ≤ t` cutoff) | — | `SucceedsOn.mono`, `successCountAt_mono`, `successCount_mono`, `HasMajorityAt.mono`, `HasMajority.mono` | ✅ |
| The probabilistic measure, randomness as context; tape length minimized over but unpriced | Oliveira19, GKLO22 | `pKtAt`, `pKt`, `ctxJoin`, `pKt_cond` | ✅ |
| Witness upper bound from any majority | — | `pKtAt_le_of_hasMajority` | ✅ |
| **Zero-constant embeddings** `pKt(x) ≤ Kt(x)` and `pKt(x\|y) ≤ Kt(x)` — the context-erasing witness succeeds on every random tape | deterministic-to-probabilistic comparison, here with constant `0` | `pKt_le_Kt`, `pKt_cond_le_Kt`; general form `pKtAt_le_Kt`, via `exists_forall_succeedsOn_Kt`, `hasMajorityAt_of_forall_succeedsOn` | ✅ |
| Positivity and everywhere-finiteness | — | `one_le_pKt`, `one_le_pKt_cond`, `pKt_lt_top`, `pKt_cond_lt_top`; general forms `one_le_pKtAt`, `HasMajorityAt.one_le_programLength` | ✅ |
| Conditioning for the probabilistic measure, `pKt(x\|y) ≤ pKt(x)` | LV (analogue of the deterministic conditioning) | the erase bits discard conditioning string and randomness together; the statement needs a randomness-preserving erase — a machine variant discarding `y` while keeping the tape — a further machine-design step | ❌ |
| Coding theorem and average-case applications for the probabilistic measure | Oliveira19, GKLO22 | require probability-weighted enumeration and clocked self-simulation — the linear-overhead self-interpreter open item (see Invariance scope) | ➖ (out of scope) |

## Certified evaluation

| Result | Source | Lean | Status |
|---|---|---|---|
| Step-budgeted evaluator: exact trace and transition count under a budget, computable, budget-structural | — | `runBounded` (`Evaluator.lean`) | ✅ |
| Soundness: an evaluator success is a `Run` derivation within budget | — | `runBounded_sound` | ✅ |
| Completeness: every derivation is found at any sufficient budget; equivalence and budget-monotonicity | — | `runBounded_complete`, `runBounded_eq_some_iff`, `runBounded_mono` | ✅ |
| Decidable bounded halting; exact `numSteps` from a success | — | `runBounded_isSome_iff`, `decidableRunWithin`, `numSteps_of_runBounded` | ✅ |
| Certificate pipeline: evaluator success → flagged run → embed bridge → `Kt_cond` witness bound | — | `flaggedRuns_of_runBounded`, `Kt_cond_le_of_flaggedRuns` (`Kt.lean`), `Kt_cond_le_of_runBounded`, `Kt_le_of_runBounded` | ✅ |
| Concrete certified bounds `Kt [true] ≤ 9`, `Kt [false] ≤ 7`, `Kt_cond [true] [true] ≤ 9` (composing-machine values; concrete numerals are machine-relative) | — | `Kt_singleton_true_le`, `Kt_singleton_false_le`, `Kt_cond_singleton_true_self_le` | ✅ |
| Machine floor `5 ≤ Kt_cond x y`; the first exact value `Kt_cond [] y = 5`, `Kt [] = 5` (composing machine) | — | `five_le_Kt_cond`, `five_le_Kt`, `CompRuns.five_le_time`, `CompRuns.two_le_length`, `Kt_cond_nil`, `Kt_nil` | ✅ |

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
- Linear-overhead self-simulation of `timedUniversal` (a `Realization` of the
  universal machine by itself); equivalently, a fuel-free self-interpreter with a
  proved linear slowdown.
- Exact `Kt` values beyond the floor: the step-budgeted evaluator
  (`Evaluator.lean`) now provides the `native_decide`-free evaluation route, and
  `Kt [] = 5` is exact on the public composing machine (machine floor + the
  embedded one-bit eraser). Exact values for nonempty strings need a finite
  enumeration of the programs and budgets between the floor and the certified
  upper bounds (not started).
- A `Kt`-rate/`K`-rate separation (a ❌ in the asymptotic layer): exhibiting a
  sequence of positive `Kt`-rate and zero `K`-rate needs an untimed `K`-rate layer
  and a depth construction; neither is started.
- A code-uniform collapse for the truth-table rate (the other ❌ in the asymptotic
  layer): the analogue of ladder levels 2–3 over the `2 ^ n` denominator needs a
  uniform encoding of the arity as an input tape and a table-normalized unary-prefix
  absorption; only the witness form is proved.
- Conditioning for the probabilistic measure (the ❌ in the probabilistic layer):
  `pKt(x|y) ≤ pKt(x)` needs a randomness-preserving context-erase convention — a
  machine variant that discards the conditioning string while keeping the random
  tape. The present erase bits discard the whole context, which is exactly what makes the
  deterministic embeddings zero-constant and is too coarse for this statement.
