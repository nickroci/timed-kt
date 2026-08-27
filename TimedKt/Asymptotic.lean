/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import TimedKt.InfoTransfer

/-!
# The Asymptotic Layer: Complexity Rates of Infinite Sequences

Single-instance `Kt` admits hardcoding: `Kt(x) ≤ |x| + O(1)` (`Kt_cond_le_length`), so
per-instance optimality cannot separate computing an output from printing it, and for a
one-bit output even the conditional complexity is `O(1)` outright. The standard
resolution measures a whole output family at once: fix an infinite sequence
`Z : ℕ → Bool` and track the complexity of its finite prefixes as a function of their
length. The rate built here is the time-bounded sibling of the prefix-complexity
densities of constructive dimension (J. H. Lutz, *Dimension in complexity classes*,
SIAM J. Comput. 32(5), 2003; the Kolmogorov-complexity characterization of effective
dimension is due to E. Mayordomo, Inf. Process. Lett. 84(1), 2002, and the `limsup`
form used here corresponds to the strong dimension of Athreya, Hitchcock, Lutz, and
Mayordomo, SIAM J. Comput. 37(3), 2007). Measuring an `n`-input Boolean function
through the complexity of its `2 ^ n`-bit truth table — its values on all length-`n`
inputs in lexicographic order — is the meta-complexity convention (E. Allender,
H. Buhrman, M. Koucký, D. van Melkebeek, D. Ronneburger, *Power from random strings*,
SIAM J. Comput. 35(6), 2006); that object lives in the truth-table layer below
(`truthTable`, `ttKtRate`), separate from the enumeration-dependent characteristic
sequence (`charSeq`, `charSeqKtRate`).

## Main definitions

* `seqPrefix Z n` — the length-`n` prefix of `Z` as a bitstring;
* `ktProfile Z n` — `Kt` of that prefix, landed in `ℕ` (grounded by `Kt_lt_top`);
* `ktRate Z` — the limsup density `limsup_n (ktProfile Z n / n)` in `ℝ≥0∞`;
* `charSeq f`, `charSeqKtRate f` — the characteristic sequence of a Boolean function
  on bitstrings with respect to the canonical enumeration `bitStringEnum`, and its
  `Kt`-rate. Enumeration-dependent — **not** the truth table of the ABKMR
  convention;
* `lexStrings n`, `truthTable f n`, `ttProfile f n`, `ttKtRate f` — the `2 ^ n`-bit
  truth table of the `n`-input restriction of `f` (the ABKMR convention), its
  `Kt`-profile, and the per-arity rate normalized by the table length `2 ^ n`;
* `wtProfile`, `wtRate` — the prefix construction over the write measure `Wt`.

## Main results

* `ktProfile_le` / `ktRate_le_one` — **the hardcode ceiling**: the profile grows at
  most linearly (`ktProfile Z n ≤ n + c`), so every sequence, however uncomputable,
  has rate at most `1`; `ttKtRate_le_one` is the same ceiling for truth tables.
* **The collapse ladder** — three uniformity levels, each forcing `ktRate Z = 0`:
  `ktRate_eq_zero_of_witnesses` (per-prefix witnesses of vanishing description and
  log-runtime density; the witnesses may vary arbitrarily with `n`, so this is a
  *nonuniform*, sublinear-advice collapse), `ktRate_eq_zero_of_code` (one fixed
  code fed an arbitrary — possibly noncomputable — input family: code-uniform with
  advice inputs), and `ktRate_eq_zero_of_uniform_code` (one fixed code on the
  canonical input `Nat.bits n`: fully uniform, no advice).
* `wtRate_le_ktRate` — the write rate is dominated by the time rate, from `Wt_le_Kt`.

Between the ceiling and the collapse lies the layer's point: hardcoding is priced at
the rate level, so separations invisible per instance become visible as densities. A
sequence of positive `Kt`-rate and zero `K`-rate would exhibit computational depth as
a density; no such separation is claimed here — this module provides the definitions
and the two bracketing theorems.
-/

open Filter Kolmogorov Nat.Partrec Topology

open scoped ENNReal

namespace TimedKt

/-! ### Prefixes of an infinite sequence -/

/-- The length-`n` prefix of an infinite sequence `Z`, as a bitstring:
`[Z 0, Z 1, …, Z (n-1)]`. -/
def seqPrefix (Z : ℕ → Bool) (n : ℕ) : BitString :=
  (List.range n).map Z

@[simp] theorem seqPrefix_length (Z : ℕ → Bool) (n : ℕ) :
    (seqPrefix Z n).length = n := by
  simp [seqPrefix]

/-- Longer prefixes extend shorter ones: `seqPrefix Z m` is a prefix of `seqPrefix Z n`
whenever `m ≤ n`. -/
theorem seqPrefix_prefix (Z : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    seqPrefix Z m <+: seqPrefix Z n := by
  have heq : seqPrefix Z m = (seqPrefix Z n).take m := by
    rw [seqPrefix, seqPrefix, ← List.map_take, List.take_range, min_eq_left h]
  exact heq ▸ List.take_prefix m _

/-! ### The complexity profile -/

/-- The **complexity profile** of a sequence: `Kt` of its length-`n` prefix, as a
natural number. The truncation is well-grounded: the public measure is everywhere
finite (`Kt_lt_top`), and `ktProfile_cast` recovers the `ENat` value exactly. -/
noncomputable def ktProfile (Z : ℕ → Bool) (n : ℕ) : ℕ :=
  (Kt (seqPrefix Z n)).toNat

/-- The profile carries the full `ENat` value of the measure: casting back loses
nothing, by finiteness. -/
theorem ktProfile_cast (Z : ℕ → Bool) (n : ℕ) :
    (ktProfile Z n : ENat) = Kt (seqPrefix Z n) :=
  ENat.natCast_toNat (Kt_lt_top _).ne

/-- An `ENat` upper bound on `Kt` of a prefix transfers to the profile. -/
theorem ktProfile_le_of_Kt_le {Z : ℕ → Bool} {n m : ℕ}
    (h : Kt (seqPrefix Z n) ≤ (m : ENat)) : ktProfile Z n ≤ m := by
  simpa [ktProfile] using ENat.toNat_le_toNat h (ENat.natCast_lt_top m).ne

/-- **The hardcode ceiling.** The profile of every sequence grows at most linearly:
`ktProfile Z n ≤ n + c` for a universal constant `c`, from the length upper bound
`Kt_cond_le_length` — printing the prefix verbatim is always available. -/
theorem ktProfile_le : ∃ c : ℕ, ∀ (Z : ℕ → Bool) (n : ℕ), ktProfile Z n ≤ n + c := by
  obtain ⟨c, hc⟩ := Kt_cond_le_length
  refine ⟨c, fun Z n => ktProfile_le_of_Kt_le ?_⟩
  have h := hc (seqPrefix Z n) []
  rw [Kt_cond_empty] at h
  calc Kt (seqPrefix Z n)
      ≤ (programLength (seqPrefix Z n) : ENat) + c := h
    _ = ((n + c : ℕ) : ENat) := by simp

/-! ### The complexity rate -/

/-- The **complexity rate** of a sequence: the limsup density of the profile,
`ktRate Z = limsup_n (ktProfile Z n / n)`, valued in `ℝ≥0∞`. The rate is the
time-bounded sibling of the prefix-complexity densities of constructive dimension
(the `limsup` form corresponds to the strong dimension of Athreya, Hitchcock, Lutz,
and Mayordomo). -/
noncomputable def ktRate (Z : ℕ → Bool) : ℝ≥0∞ :=
  atTop.limsup fun n => (ktProfile Z n : ℝ≥0∞) / n

/-- A constant over `n` tends to zero: `c / n → 0` in `ℝ≥0∞` along `atTop`. -/
theorem tendsto_natCast_div_atTop_nhds_zero (c : ℕ) :
    Tendsto (fun n : ℕ => (c : ℝ≥0∞) / n) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top c))

/-- **The hardcode ceiling at the rate level**: `ktRate Z ≤ 1` for every sequence.
Eventually `ktProfile Z n / n ≤ 1 + c / n`, and the right-hand side converges to `1`,
so the limsup is at most `1`. Printing pins every sequence, however uncomputable, at
rate at most one. -/
theorem ktRate_le_one (Z : ℕ → Bool) : ktRate Z ≤ 1 := by
  obtain ⟨c, hc⟩ := ktProfile_le
  have hev : ∀ᶠ n : ℕ in atTop,
      (ktProfile Z n : ℝ≥0∞) / n ≤ 1 + (c : ℝ≥0∞) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    calc (ktProfile Z n : ℝ≥0∞) / n
        ≤ ((n + c : ℕ) : ℝ≥0∞) / n :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr (hc Z n)) n
      _ = (n : ℝ≥0∞) / n + (c : ℝ≥0∞) / n := by
          rw [Nat.cast_add, ENNReal.add_div]
      _ = 1 + (c : ℝ≥0∞) / n := by
          rw [ENNReal.div_self hn0 (ENNReal.natCast_ne_top n)]
  have hlim : Tendsto (fun n : ℕ => 1 + (c : ℝ≥0∞) / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_natCast_div_atTop_nhds_zero c)
  calc ktRate Z
      ≤ atTop.limsup fun n : ℕ => 1 + (c : ℝ≥0∞) / n := limsup_le_limsup hev
    _ = 1 := hlim.limsup_eq

/-! ### Density helpers

Additive constants — such as the comp flag and the extra transition of the public
machine's embed node, or a fixed code's unary prefix — are invisible to vanishing
densities. -/

/-- Additive constants are invisible to vanishing densities: if `u n / n → 0` then
`(u n + k) / n → 0`. -/
theorem tendsto_add_const_div_atTop_nhds_zero {u : ℕ → ℕ} (k : ℕ)
    (hu : Tendsto (fun n => (u n : ℝ≥0∞) / n) atTop (𝓝 0)) :
    Tendsto (fun n => ((u n + k : ℕ) : ℝ≥0∞) / n) atTop (𝓝 0) := by
  simpa [Nat.cast_add, ENNReal.add_div]
    using hu.add (tendsto_natCast_div_atTop_nhds_zero k)

/-- The log-runtime density survives an additive constant on the runtime:
if `ceilLog2 (S n) / n → 0` then `ceilLog2 (S n + k) / n → 0`, through the one-bit
subadditivity `ceilLog2_add_le`. -/
theorem tendsto_ceilLog2_add_const_div_atTop_nhds_zero {S : ℕ → ℕ} (k : ℕ)
    (hS : Tendsto (fun n => (ceilLog2 (S n) : ℝ≥0∞) / n) atTop (𝓝 0)) :
    Tendsto (fun n => (ceilLog2 (S n + k) : ℝ≥0∞) / n) atTop (𝓝 0) := by
  have hlim := tendsto_add_const_div_atTop_nhds_zero (ceilLog2 k + 1) hS
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le)
    (fun n => ENNReal.div_le_div_right (Nat.cast_le.mpr (ceilLog2_add_le _ _)) n)

/-! ### The collapse ladder, level 1: prefix witnesses (sublinear advice) -/

/-- **The prefix-witness collapse (sublinear advice).** If every prefix of `Z` is
produced by some run of the flagged machine with program length at most `g n` and
transition count at most `T n`, and both densities `g n / n` and `ceilLog2 (T n) / n`
vanish — sublinear description and subexponential time — then `ktRate Z = 0`. The
hypothesis is `∀ n, ∃ p`: the witness program may vary arbitrarily with `n`, nothing
ties the program at length `n` to the program at length `n + 1`, so this is a
*nonuniform* collapse — a sublinear-advice family already forces rate `0`. The
code-uniform and fully uniform strengthenings are `ktRate_eq_zero_of_code` and
`ktRate_eq_zero_of_uniform_code` below. The flagged witnesses reach the public
measure through the embed bridge (`Kt_cond_le_of_flaggedRuns`); its one-bit,
one-transition overhead is absorbed by the density hypotheses. Hardcoding pins the
rate at the ceiling `1` (`ktRate_le_one`); vanishing-density witnesses collapse it to
`0`, so cheap generation is visible at the rate level even though every single prefix
admits the printing bound. -/
theorem ktRate_eq_zero_of_witnesses {Z : ℕ → Bool} {g T : ℕ → ℕ}
    (h : ∀ n, ∃ p t, FlaggedRuns p [] (seqPrefix Z n) t ∧
      programLength p ≤ g n ∧ t ≤ T n)
    (hg : Tendsto (fun n => (g n : ℝ≥0∞) / n) atTop (𝓝 0))
    (hT : Tendsto (fun n => (ceilLog2 (T n) : ℝ≥0∞) / n) atTop (𝓝 0)) :
    ktRate Z = 0 := by
  have hbound : ∀ n, ktProfile Z n ≤ (g n + 1) + ceilLog2 (T n + 1) := by
    intro n
    obtain ⟨p, t, hrun, hp, ht⟩ := h n
    refine ktProfile_le_of_Kt_le ?_
    calc Kt (seqPrefix Z n)
        = Kt_cond (seqPrefix Z n) [] := (Kt_cond_empty _).symm
      _ ≤ ((programLength p + 1 + ceilLog2 (t + 1) : ℕ) : ENat) :=
          Kt_cond_le_of_flaggedRuns hrun
      _ ≤ (((g n + 1) + ceilLog2 (T n + 1) : ℕ) : ENat) :=
          Nat.cast_le.mpr
            (Nat.add_le_add (by omega) (ceilLog2_mono (by omega)))
  have hle : ∀ n : ℕ, (ktProfile Z n : ℝ≥0∞) / n ≤
      ((g n + 1 : ℕ) : ℝ≥0∞) / n + (ceilLog2 (T n + 1) : ℝ≥0∞) / n := by
    intro n
    calc (ktProfile Z n : ℝ≥0∞) / n
        ≤ (((g n + 1) + ceilLog2 (T n + 1) : ℕ) : ℝ≥0∞) / n :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr (hbound n)) n
      _ = ((g n + 1 : ℕ) : ℝ≥0∞) / n + (ceilLog2 (T n + 1) : ℝ≥0∞) / n := by
          rw [Nat.cast_add, ENNReal.add_div]
  have hlim : Tendsto (fun n => (ktProfile Z n : ℝ≥0∞) / n) atTop (𝓝 0) := by
    have hg' := tendsto_add_const_div_atTop_nhds_zero 1 hg
    have hT' := tendsto_ceilLog2_add_const_div_atTop_nhds_zero 1 hT
    have hsum := hg'.add hT'
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) hle
  exact hlim.limsup_eq

/-! ### The collapse ladder, level 2: one code, advice inputs

A generator is most naturally given as a single `Nat.Partrec.Code` fed a family of
input tapes. The corollary `ktRate_eq_zero_of_code` packages such a family into the
witness form: the code enters the program through its unary prefix, a constant
contribution absorbed by the vanishing-density hypotheses. The code is fixed, but the
input family `d n` is an arbitrary function `ℕ → BitString` — possibly noncomputable
— so this level is code-uniform with a sublinear advice family on the input tape;
full uniformity is level 3 (`ktRate_eq_zero_of_uniform_code`). -/

/-- **The code-plus-advice collapse.** Suppose one code `c` generates every prefix
of `Z`: on the input tape `d n` (with empty context), of length at most `g n`, the code
runs to a value decoding to `seqPrefix Z n` within `S n` transitions. If the densities
`g n / n` and `ceilLog2 (S n) / n` vanish, then `ktRate Z = 0`. The code is one fixed
`Nat.Partrec.Code`, but the input family `d` is arbitrary — possibly noncomputable —
so the `d n` are sublinear advice strings, not a uniform input encoding. The witness
program is `false :: unaryPrefix (encode c) ++ d n`; the unary prefix contributes the
constant `encode c + 1` to the description, absorbed by the density hypotheses. -/
theorem ktRate_eq_zero_of_code {Z : ℕ → Bool} {c : Code}
    {d : ℕ → BitString} {g S : ℕ → ℕ}
    (hlen : ∀ n, programLength (d n) ≤ g n)
    (h : ∀ n, ∃ (T : List ℕ) (steps r : ℕ),
      Run c (Encodable.encode (d n, ([] : BitString))) T steps ∧
      T.getLast? = some r ∧
      (Encodable.decode r : Option BitString).getD [] = seqPrefix Z n ∧
      steps ≤ S n)
    (hg : Tendsto (fun n => (g n : ℝ≥0∞) / n) atTop (𝓝 0))
    (hS : Tendsto (fun n => (ceilLog2 (S n) : ℝ≥0∞) / n) atTop (𝓝 0)) :
    ktRate Z = 0 := by
  refine ktRate_eq_zero_of_witnesses
    (g := fun n => g n + (Encodable.encode c + 2))
    (T := fun n => S n + (Encodable.encode c + 3)) (fun n => ?_)
    (tendsto_add_const_div_atTop_nhds_zero _ hg)
    (tendsto_ceilLog2_add_const_div_atTop_nhds_zero _ hS)
  obtain ⟨T, steps, r, hrun, hlast, hdec, hsteps⟩ := h n
  have hu := universalRuns_of_run hrun hlast
  rw [hdec] at hu
  refine ⟨false :: (unaryPrefix (Encodable.encode c) ++ d n),
    Encodable.encode c + 1 + steps + 1 + 1,
    ⟨false, _, _, rfl, hu, rfl⟩, ?_, ?_⟩
  · have hdn : (d n).length ≤ g n := hlen n
    simp only [programLength, List.length_cons, List.length_append, length_unaryPrefix]
    omega
  · omega

/-! ### The collapse ladder, level 3: fully uniform

Fixing the canonical input encoding `Nat.bits n` removes the last nonuniformity of
level 2: one code, the index `n` itself as the input tape, no advice family. The
description density is then not a hypothesis but a theorem — the binary expansion has
length at most `ceilLog2 (n + 1)`, and `ceilLog2 (n + 1) / n → 0`. -/

/-- The binary expansion of `n` has length at most `ceilLog2 (n + 1)`: from
`Nat.size_le`, since `n < 2 ^ ceilLog2 (n + 1)`. -/
theorem bits_length_le_ceilLog2_succ (n : ℕ) : n.bits.length ≤ ceilLog2 (n + 1) := by
  rw [Nat.size_eq_bits_len]
  refine Nat.size_le.mpr ?_
  have h := le_two_pow_ceilLog2 (n + 1)
  omega

/-- The ceiling logarithm is sublinear against every slope: for every `k`, eventually
`k * ceilLog2 (n + 1) ≤ n`. The two-power floor `2 ^ (m - 1) ≤ n` for
`m = ceilLog2 (n + 1)` beats `k * m` once `m ≥ 2 * k + 4` (splitting the exponent at
`m / 2`); smaller `m` is covered by `n` eventually exceeding the constant
`k * (2 * k + 4)`. -/
theorem eventually_mul_ceilLog2_succ_le (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, k * ceilLog2 (n + 1) ≤ n := by
  filter_upwards [eventually_ge_atTop (k * (2 * k + 4)), eventually_ge_atTop 1]
    with n hn hn1
  set m := ceilLog2 (n + 1) with hm
  by_cases hcase : 2 * k + 4 ≤ m
  · -- large `m`: `k * m ≤ 2 ^ (m - 1) ≤ n`
    have hfloor : 2 ^ (m - 1) < n + 1 :=
      Nat.pow_pred_clog_lt_self Nat.one_lt_two (by omega)
    have hhalf : m / 2 < 2 ^ (m / 2) := Nat.lt_two_pow_self
    have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
    have hsucc : m + 1 ≤ 2 ^ (m / 2 + 1) := by
      have hp : 2 ^ (m / 2 + 1) = 2 ^ (m / 2) * 2 := Nat.pow_succ ..
      omega
    have hmul : k * (m + 1) ≤ 2 ^ (k + (m / 2 + 1)) :=
      calc k * (m + 1) ≤ 2 ^ k * 2 ^ (m / 2 + 1) := Nat.mul_le_mul hk2.le hsucc
        _ = 2 ^ (k + (m / 2 + 1)) := (Nat.pow_add 2 _ _).symm
    have hexp : 2 ^ (k + (m / 2 + 1)) ≤ 2 ^ (m - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    calc k * m ≤ k * (m + 1) := Nat.mul_le_mul le_rfl (Nat.le_succ m)
      _ ≤ 2 ^ (k + (m / 2 + 1)) := hmul
      _ ≤ 2 ^ (m - 1) := hexp
      _ ≤ n := by omega
  · -- small `m`: `k * m` is below the constant `n` has passed
    exact (Nat.mul_le_mul le_rfl (by omega : m ≤ 2 * k + 4)).trans hn

/-- The log-density of the identity vanishes: `ceilLog2 (n + 1) / n → 0` in `ℝ≥0∞`.
This is the density that prices the canonical input `Nat.bits n`. -/
theorem tendsto_ceilLog2_succ_div_atTop_nhds_zero :
    Tendsto (fun n : ℕ => (ceilLog2 (n + 1) : ℝ≥0∞) / n) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  filter_upwards [eventually_mul_ceilLog2_succ_le j, eventually_ge_atTop 1]
    with n hn hn1
  have hpos : 0 < ceilLog2 (n + 1) := Nat.clog_pos Nat.one_lt_two (by omega)
  have hne : (ceilLog2 (n + 1) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  calc (ceilLog2 (n + 1) : ℝ≥0∞) / n
      ≤ (ceilLog2 (n + 1) : ℝ≥0∞) / ((j : ℝ≥0∞) * (ceilLog2 (n + 1) : ℝ≥0∞)) :=
        ENNReal.div_le_div le_rfl (by exact_mod_cast hn)
    _ = 1 / (j : ℝ≥0∞) := by
        simpa using
          ENNReal.mul_div_mul_right 1 (j : ℝ≥0∞) hne (ENNReal.natCast_ne_top _)
    _ ≤ ε := by rw [one_div]; exact hj.le

/-- **The uniform collapse** — the fully uniform level of the ladder: one fixed code,
the canonical input `Nat.bits n`, no advice. If the code `c`, fed the binary expansion
of the index `n` itself (with empty context), produces `seqPrefix Z n` within `S n`
transitions, and the log-runtime density `ceilLog2 (S n) / n` vanishes, then
`ktRate Z = 0`. The description density of level 2 is discharged, not hypothesized:
the input has length at most `ceilLog2 (n + 1)` (`bits_length_le_ceilLog2_succ`), and
that density vanishes (`tendsto_ceilLog2_succ_div_atTop_nhds_zero`). -/
theorem ktRate_eq_zero_of_uniform_code {Z : ℕ → Bool} {c : Code} {S : ℕ → ℕ}
    (h : ∀ n, ∃ (T : List ℕ) (steps r : ℕ),
      Run c (Encodable.encode ((n.bits : BitString), ([] : BitString))) T steps ∧
      T.getLast? = some r ∧
      (Encodable.decode r : Option BitString).getD [] = seqPrefix Z n ∧
      steps ≤ S n)
    (hS : Tendsto (fun n => (ceilLog2 (S n) : ℝ≥0∞) / n) atTop (𝓝 0)) :
    ktRate Z = 0 :=
  ktRate_eq_zero_of_code (d := fun n => (n.bits : BitString))
    (g := fun n => ceilLog2 (n + 1)) (fun n => bits_length_le_ceilLog2_succ n) h
    tendsto_ceilLog2_succ_div_atTop_nhds_zero hS

/-! ### Characteristic sequences of Boolean functions -/

/-- The canonical enumeration of bitstrings: the bijection `ℕ ≃ BitString` obtained
from the encodability and infinitude of `List Bool`
(`Denumerable.ofEncodableOfInfinite`), listing bitstrings in increasing order of their
`Encodable.encode` value. This order does **not** sort by length — it interleaves
lengths — so prefixes of the characteristic sequence below are fragments relative to
this enumeration, never the truth table of a single arity. -/
def bitStringEnum : ℕ ≃ BitString :=
  letI : Denumerable (List Bool) := Denumerable.ofEncodableOfInfinite (List Bool)
  (Denumerable.eqv (List Bool)).symm

/-- The **characteristic sequence** of a Boolean function on bitstrings, with respect
to the canonical enumeration: bit `i` is the value of `f` at the `i`-th bitstring of
`bitStringEnum`. A length-`n` prefix of this sequence is an enumeration-dependent
fragment of the characteristic function of `f`; it is **not** the `2 ^ n`-bit truth
table of the `n`-input restriction of `f` in the ABKMR convention — that object is
`truthTable` below. -/
def charSeq (f : BitString → Bool) : ℕ → Bool :=
  fun i => f (bitStringEnum i)

/-- The **characteristic-sequence complexity rate** of a Boolean function: the
`Kt`-rate of its characteristic sequence. A legitimate family-rate object, but
relative to the canonical enumeration `bitStringEnum`: it prices the first `n` values
of `f` along that enumeration. For the truth-table rate of the ABKMR convention see
`ttKtRate`. -/
noncomputable def charSeqKtRate (f : BitString → Bool) : ℝ≥0∞ :=
  ktRate (charSeq f)

/-- The hardcode ceiling for characteristic sequences: `charSeqKtRate f ≤ 1` for
every function. -/
theorem charSeqKtRate_le_one (f : BitString → Bool) : charSeqKtRate f ≤ 1 :=
  ktRate_le_one (charSeq f)

/-- The witness collapse for characteristic sequences: runs producing the
characteristic-sequence prefixes with vanishing description and log-runtime densities
force `charSeqKtRate f = 0`. -/
theorem charSeqKtRate_eq_zero_of_witnesses {f : BitString → Bool} {g T : ℕ → ℕ}
    (h : ∀ n, ∃ p t, FlaggedRuns p [] (seqPrefix (charSeq f) n) t ∧
      programLength p ≤ g n ∧ t ≤ T n)
    (hg : Tendsto (fun n => (g n : ℝ≥0∞) / n) atTop (𝓝 0))
    (hT : Tendsto (fun n => (ceilLog2 (T n) : ℝ≥0∞) / n) atTop (𝓝 0)) :
    charSeqKtRate f = 0 :=
  ktRate_eq_zero_of_witnesses h hg hT

/-! ### Truth tables of Boolean functions

The ABKMR convention measures an `n`-input Boolean function through its `2 ^ n`-bit
truth table: the values on all length-`n` inputs in lexicographic order. The rate of
this layer is per arity, normalized by the table length `2 ^ n` — the honest
denominator for a family whose `n`-th member is a `2 ^ n`-bit string. -/

/-- All length-`n` bitstrings in lexicographic order (`false < true`, first position
most significant): the strings beginning with `false` precede those beginning with
`true`, recursively. `lexStrings_length` counts them; `mem_lexStrings` and
`lexStrings_nodup` certify that the list enumerates exactly the length-`n` strings,
without repetition. -/
def lexStrings : ℕ → List BitString
  | 0 => [[]]
  | n + 1 => (lexStrings n).map (false :: ·) ++ (lexStrings n).map (true :: ·)

@[simp] theorem lexStrings_length (n : ℕ) : (lexStrings n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [lexStrings, List.length_append, List.length_map, ih, Nat.pow_succ]
      omega

/-- `lexStrings n` contains exactly the bitstrings of length `n`. -/
theorem mem_lexStrings {x : BitString} {n : ℕ} :
    x ∈ lexStrings n ↔ x.length = n := by
  induction n generalizing x with
  | zero => cases x <;> simp [lexStrings]
  | succ n ih =>
      cases x with
      | nil => simp [lexStrings, ih]
      | cons b tl => cases b <;> simp [lexStrings, ih]

/-- The enumeration has no repetitions. -/
theorem lexStrings_nodup (n : ℕ) : (lexStrings n).Nodup := by
  induction n with
  | zero => simp [lexStrings]
  | succ n ih =>
      refine (ih.map List.cons_injective).append (ih.map List.cons_injective) ?_
      intro x hf ht
      obtain ⟨u, -, rfl⟩ := List.mem_map.mp hf
      obtain ⟨v, -, hv⟩ := List.mem_map.mp ht
      exact Bool.false_ne_true (List.head_eq_of_cons_eq hv.symm)

/-- The **truth table** of `f` at arity `n` (the ABKMR convention): the `2 ^ n`-bit
string whose `i`-th bit is the value of `f` at the `i`-th length-`n` bitstring in
lexicographic order. -/
def truthTable (f : BitString → Bool) (n : ℕ) : BitString :=
  (lexStrings n).map f

@[simp] theorem truthTable_length (f : BitString → Bool) (n : ℕ) :
    (truthTable f n).length = 2 ^ n := by
  simp [truthTable]

/-- The **truth-table profile** of a Boolean function: `Kt` of its arity-`n` truth
table, as a natural number — grounded by `Kt_lt_top`. -/
noncomputable def ttProfile (f : BitString → Bool) (n : ℕ) : ℕ :=
  (Kt (truthTable f n)).toNat

/-- The truth-table profile carries the full `ENat` value of the measure. -/
theorem ttProfile_cast (f : BitString → Bool) (n : ℕ) :
    (ttProfile f n : ENat) = Kt (truthTable f n) :=
  ENat.natCast_toNat (Kt_lt_top _).ne

/-- An `ENat` upper bound on `Kt` of a truth table transfers to the profile. -/
theorem ttProfile_le_of_Kt_le {f : BitString → Bool} {n m : ℕ}
    (h : Kt (truthTable f n) ≤ (m : ENat)) : ttProfile f n ≤ m := by
  simpa [ttProfile] using ENat.toNat_le_toNat h (ENat.natCast_lt_top m).ne

/-- The hardcode ceiling at the truth-table profile: `ttProfile f n ≤ 2 ^ n + c` for
a universal constant `c`, from the length upper bound `Kt_cond_le_length` — printing
the table verbatim is always available. -/
theorem ttProfile_le : ∃ c : ℕ, ∀ (f : BitString → Bool) (n : ℕ),
    ttProfile f n ≤ 2 ^ n + c := by
  obtain ⟨c, hc⟩ := Kt_cond_le_length
  refine ⟨c, fun f n => ttProfile_le_of_Kt_le ?_⟩
  have h := hc (truthTable f n) []
  rw [Kt_cond_empty] at h
  calc Kt (truthTable f n)
      ≤ (programLength (truthTable f n) : ENat) + c := h
    _ = ((2 ^ n + c : ℕ) : ENat) := by simp

/-- The **truth-table complexity rate** of a Boolean function: the limsup of the
per-arity table complexity normalized by the table length,
`ttKtRate f = limsup_n (ttProfile f n / 2 ^ n)`, valued in `ℝ≥0∞`. This is the rate
of the ABKMR truth-table convention: the denominator is the number of bits of the
arity-`n` table, so hardcoding the table pins the rate at `1` (`ttKtRate_le_one`). -/
noncomputable def ttKtRate (f : BitString → Bool) : ℝ≥0∞ :=
  atTop.limsup fun n => (ttProfile f n : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞)

/-- A constant over `2 ^ n` tends to zero, by comparison with `c / n` through
`n ≤ 2 ^ n`. -/
theorem tendsto_natCast_div_two_pow_atTop_nhds_zero (c : ℕ) :
    Tendsto (fun n : ℕ => (c : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_natCast_div_atTop_nhds_zero c) (fun _ => zero_le) fun n => ?_
  exact ENNReal.div_le_div le_rfl
    (Nat.cast_le.mpr (Nat.le_of_lt Nat.lt_two_pow_self))

/-- Additive constants are invisible to vanishing table densities: if
`u n / 2 ^ n → 0` then `(u n + k) / 2 ^ n → 0`. -/
theorem tendsto_add_const_div_two_pow_atTop_nhds_zero {u : ℕ → ℕ} (k : ℕ)
    (hu : Tendsto (fun n => (u n : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞)) atTop (𝓝 0)) :
    Tendsto (fun n => ((u n + k : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞)) atTop (𝓝 0) := by
  simpa [Nat.cast_add, ENNReal.add_div]
    using hu.add (tendsto_natCast_div_two_pow_atTop_nhds_zero k)

/-- The log-runtime table density survives an additive constant on the runtime,
through the one-bit subadditivity `ceilLog2_add_le`. -/
theorem tendsto_ceilLog2_add_const_div_two_pow_atTop_nhds_zero {S : ℕ → ℕ} (k : ℕ)
    (hS : Tendsto (fun n => (ceilLog2 (S n) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞))
      atTop (𝓝 0)) :
    Tendsto (fun n => (ceilLog2 (S n + k) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞))
      atTop (𝓝 0) := by
  have hlim := tendsto_add_const_div_two_pow_atTop_nhds_zero (ceilLog2 k + 1) hS
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le)
    (fun n => ENNReal.div_le_div_right (Nat.cast_le.mpr (ceilLog2_add_le _ _)) _)

/-- **The hardcode ceiling for truth tables**: `ttKtRate f ≤ 1` for every function.
Eventually `ttProfile f n / 2 ^ n ≤ 1 + c / 2 ^ n`, and the right-hand side converges
to `1`. This is the table-length ceiling of the ABKMR convention: every Boolean
function, however hard, is pinned at rate at most one by printing its tables. -/
theorem ttKtRate_le_one (f : BitString → Bool) : ttKtRate f ≤ 1 := by
  obtain ⟨c, hc⟩ := ttProfile_le
  have hev : ∀ n : ℕ, (ttProfile f n : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) ≤
      1 + (c : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
    intro n
    have hn0 : ((2 ^ n : ℕ) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.two_pow_pos n).ne'
    calc (ttProfile f n : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞)
        ≤ ((2 ^ n + c : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr (hc f n)) _
      _ = ((2 ^ n : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) +
            (c : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
          rw [Nat.cast_add, ENNReal.add_div]
      _ = 1 + (c : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
          rw [ENNReal.div_self hn0 (ENNReal.natCast_ne_top _)]
  have hlim : Tendsto (fun n : ℕ => 1 + (c : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞))
      atTop (𝓝 1) := by
    simpa using
      tendsto_const_nhds.add (tendsto_natCast_div_two_pow_atTop_nhds_zero c)
  calc ttKtRate f
      ≤ atTop.limsup fun n : ℕ => 1 + (c : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) :=
        limsup_le_limsup (Eventually.of_forall hev)
    _ = 1 := hlim.limsup_eq

/-- **The witness collapse for truth tables.** If every arity-`n` table of `f` is
produced by some run of the flagged machine with program length at most `g n` and
transition count at most `T n`, and both table densities `g n / 2 ^ n` and
`ceilLog2 (T n) / 2 ^ n` vanish, then `ttKtRate f = 0`. As at level 1 of the prefix
ladder, the witnesses may vary arbitrarily with `n`: this is a nonuniform,
sublinear-advice collapse, table-normalized. -/
theorem ttKtRate_eq_zero_of_witnesses {f : BitString → Bool} {g T : ℕ → ℕ}
    (h : ∀ n, ∃ p t, FlaggedRuns p [] (truthTable f n) t ∧
      programLength p ≤ g n ∧ t ≤ T n)
    (hg : Tendsto (fun n => (g n : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞)) atTop (𝓝 0))
    (hT : Tendsto (fun n => (ceilLog2 (T n) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞))
      atTop (𝓝 0)) :
    ttKtRate f = 0 := by
  have hbound : ∀ n, ttProfile f n ≤ (g n + 1) + ceilLog2 (T n + 1) := by
    intro n
    obtain ⟨p, t, hrun, hp, ht⟩ := h n
    refine ttProfile_le_of_Kt_le ?_
    calc Kt (truthTable f n)
        = Kt_cond (truthTable f n) [] := (Kt_cond_empty _).symm
      _ ≤ ((programLength p + 1 + ceilLog2 (t + 1) : ℕ) : ENat) :=
          Kt_cond_le_of_flaggedRuns hrun
      _ ≤ (((g n + 1) + ceilLog2 (T n + 1) : ℕ) : ENat) :=
          Nat.cast_le.mpr
            (Nat.add_le_add (by omega) (ceilLog2_mono (by omega)))
  have hle : ∀ n : ℕ, (ttProfile f n : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) ≤
      ((g n + 1 : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) +
        (ceilLog2 (T n + 1) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
    intro n
    calc (ttProfile f n : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞)
        ≤ (((g n + 1) + ceilLog2 (T n + 1) : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr (hbound n)) _
      _ = ((g n + 1 : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) +
            (ceilLog2 (T n + 1) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
          rw [Nat.cast_add, ENNReal.add_div]
  have hlim : Tendsto (fun n => (ttProfile f n : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞))
      atTop (𝓝 0) := by
    have hg' := tendsto_add_const_div_two_pow_atTop_nhds_zero 1 hg
    have hT' := tendsto_ceilLog2_add_const_div_two_pow_atTop_nhds_zero 1 hT
    have hsum := hg'.add hT'
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) hle
  exact hlim.limsup_eq

/-! ### The write-measure analogue -/

/-- The write-measure profile: `Wt` of the length-`n` prefix, as a natural number —
grounded by `Wt_lt_top`. -/
noncomputable def wtProfile (Z : ℕ → Bool) (n : ℕ) : ℕ :=
  (Wt (seqPrefix Z n)).toNat

/-- The write profile carries the full `ENat` value of the write measure. -/
theorem wtProfile_cast (Z : ℕ → Bool) (n : ℕ) :
    (wtProfile Z n : ENat) = Wt (seqPrefix Z n) :=
  ENat.natCast_toNat (Wt_lt_top _).ne

/-- The **write-measure rate**: the limsup density of the write profile. -/
noncomputable def wtRate (Z : ℕ → Bool) : ℝ≥0∞ :=
  atTop.limsup fun n => (wtProfile Z n : ℝ≥0∞) / n

/-- The write profile never exceeds the time profile: pointwise from `Wt_le_Kt`,
transported through `toNat` by finiteness. -/
theorem wtProfile_le_ktProfile (Z : ℕ → Bool) (n : ℕ) :
    wtProfile Z n ≤ ktProfile Z n :=
  ENat.toNat_le_toNat (Wt_le_Kt _) (Kt_lt_top _).ne

/-- Rate comparison: `wtRate Z ≤ ktRate Z` — the limsup of a pointwise-dominated
density is dominated. -/
theorem wtRate_le_ktRate (Z : ℕ → Bool) : wtRate Z ≤ ktRate Z :=
  limsup_le_limsup (Eventually.of_forall fun n =>
    ENNReal.div_le_div_right (Nat.cast_le.mpr (wtProfile_le_ktProfile Z n)) n)

end TimedKt
