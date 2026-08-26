/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import TimedKt.InfoTransfer

/-!
# The Asymptotic Layer: Complexity Profiles of Infinite Sequences

Single-instance `Kt` admits hardcoding: `Kt(x) ≤ |x| + O(1)` (`Kt_cond_le_length`), so
per-instance optimality cannot separate computing an output from printing it, and for a
one-bit output even the conditional complexity is `O(1)` outright. The standard
resolution measures a whole output family at once: fix an infinite sequence
`Z : ℕ → Bool` and track the complexity of its finite prefixes as a function of their
length. This is the convention of constructive dimension, where the density of
`K(Z↾n)` in `n` characterizes the effective Hausdorff dimension of `Z` (J. H. Lutz,
*Dimension in complexity classes*, SIAM J. Comput. 32(5), 2003; the Kolmogorov-complexity
characterization is due to E. Mayordomo, Inf. Process. Lett. 84(1), 2002).

This module builds the profile and its rate: `seqPrefix Z n` is the length-`n` prefix
of `Z` as a bitstring, `ktProfile Z n` is its `Kt`, landed in `ℕ` — well-grounded
because the public measure is everywhere finite (`Kt_lt_top`) — and `ktRate Z` is the
limsup density `limsup_n (ktProfile Z n / n)` in `ℝ≥0∞`. The hardcode bound transfers:
`ktProfile Z n ≤ n + c` for a universal constant `c` (`ktProfile_le`), so the profile of
every sequence, however uncomputable, grows at most linearly and the rate never exceeds
the ceiling `1` (`ktRate_le_one`). Separations therefore cannot live in upper bounds on
single prefixes; they live in the growth rate of the profile.
-/

open Filter Kolmogorov Topology

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

end TimedKt
