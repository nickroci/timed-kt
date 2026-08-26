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

/-! ### The generator collapse -/

/-- **The generator collapse.** If every prefix of `Z` is produced by some run of the
flagged machine with program length at most `g n` and transition count at most `T n`,
and both densities `g n / n` and `ceilLog2 (T n) / n` vanish — sublinear description
and subexponential time — then `ktRate Z = 0`. Hardcoding pins the rate at the ceiling
`1` (`ktRate_le_one`); a uniform generator collapses it to `0`, so algorithms are
visible at the rate level even though every single prefix admits the printing bound. -/
theorem ktRate_eq_zero_of_witnesses {Z : ℕ → Bool} {g T : ℕ → ℕ}
    (h : ∀ n, ∃ p t, FlaggedRuns p [] (seqPrefix Z n) t ∧
      programLength p ≤ g n ∧ t ≤ T n)
    (hg : Tendsto (fun n => (g n : ℝ≥0∞) / n) atTop (𝓝 0))
    (hT : Tendsto (fun n => (ceilLog2 (T n) : ℝ≥0∞) / n) atTop (𝓝 0)) :
    ktRate Z = 0 := by
  have hbound : ∀ n, ktProfile Z n ≤ g n + ceilLog2 (T n) := by
    intro n
    obtain ⟨p, t, hrun, hp, ht⟩ := h n
    refine ktProfile_le_of_Kt_le ?_
    calc Kt (seqPrefix Z n)
        = Kt_cond (seqPrefix Z n) [] := (Kt_cond_empty _).symm
      _ ≤ ((programLength p + ceilLog2 t : ℕ) : ENat) := Kt_cond_le_of_runs hrun
      _ ≤ ((g n + ceilLog2 (T n) : ℕ) : ENat) :=
          Nat.cast_le.mpr (Nat.add_le_add hp (ceilLog2_mono ht))
  have hle : ∀ n : ℕ, (ktProfile Z n : ℝ≥0∞) / n ≤
      (g n : ℝ≥0∞) / n + (ceilLog2 (T n) : ℝ≥0∞) / n := by
    intro n
    calc (ktProfile Z n : ℝ≥0∞) / n
        ≤ ((g n + ceilLog2 (T n) : ℕ) : ℝ≥0∞) / n :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr (hbound n)) n
      _ = (g n : ℝ≥0∞) / n + (ceilLog2 (T n) : ℝ≥0∞) / n := by
          rw [Nat.cast_add, ENNReal.add_div]
  have hlim : Tendsto (fun n => (ktProfile Z n : ℝ≥0∞) / n) atTop (𝓝 0) := by
    have hsum := hg.add hT
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) hle
  exact hlim.limsup_eq

/-! ### The fixed-code form

A generator is most naturally given as a single `Nat.Partrec.Code` fed a family of
input tapes. The corollary `ktRate_eq_zero_of_code` packages such a family into the
witness form: the code enters the program through its unary prefix, a constant
contribution absorbed by the vanishing-density hypotheses. -/

/-- Additive constants are invisible to vanishing densities: if `u n / n → 0` then
`(u n + k) / n → 0`. -/
theorem tendsto_add_const_div_atTop_nhds_zero {u : ℕ → ℕ} (k : ℕ)
    (hu : Tendsto (fun n => (u n : ℝ≥0∞) / n) atTop (𝓝 0)) :
    Tendsto (fun n => ((u n + k : ℕ) : ℝ≥0∞) / n) atTop (𝓝 0) := by
  simpa [Nat.cast_add, ENNReal.add_div]
    using hu.add (tendsto_natCast_div_atTop_nhds_zero k)

/-- The ceiling logarithm absorbs additive constants at constant cost:
`ceilLog2 (a + k) ≤ ceilLog2 a + (ceilLog2 (k + 1) + 1)`. -/
theorem ceilLog2_add_le (a k : ℕ) :
    ceilLog2 (a + k) ≤ ceilLog2 a + (ceilLog2 (k + 1) + 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using (ceilLog2_mono (Nat.le_succ k)).trans (Nat.le_succ _)
  · have hmul : a + k ≤ (a + 1) * (k + 1) := by
      have : (a + 1) * (k + 1) = a * k + a + k + 1 := by ring
      omega
    calc ceilLog2 (a + k)
        ≤ ceilLog2 ((a + 1) * (k + 1)) := ceilLog2_mono hmul
      _ ≤ ceilLog2 (a + 1) + ceilLog2 (k + 1) := ceilLog2_mul_le _ _
      _ ≤ (ceilLog2 a + 1) + ceilLog2 (k + 1) :=
          Nat.add_le_add_right (ceilLog2_succ_le ha) _
      _ = ceilLog2 a + (ceilLog2 (k + 1) + 1) := by omega

/-- The log-runtime density survives an additive constant on the runtime:
if `ceilLog2 (S n) / n → 0` then `ceilLog2 (S n + k) / n → 0`. -/
theorem tendsto_ceilLog2_add_const_div_atTop_nhds_zero {S : ℕ → ℕ} (k : ℕ)
    (hS : Tendsto (fun n => (ceilLog2 (S n) : ℝ≥0∞) / n) atTop (𝓝 0)) :
    Tendsto (fun n => (ceilLog2 (S n + k) : ℝ≥0∞) / n) atTop (𝓝 0) := by
  have hlim := tendsto_add_const_div_atTop_nhds_zero (ceilLog2 (k + 1) + 1) hS
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le)
    (fun n => ENNReal.div_le_div_right (Nat.cast_le.mpr (ceilLog2_add_le _ _)) n)

/-- **The fixed-code generator collapse.** Suppose one code `c` generates every prefix
of `Z`: on the input tape `d n` (with empty context), of length at most `g n`, the code
runs to a value decoding to `seqPrefix Z n` within `S n` transitions. If the densities
`g n / n` and `ceilLog2 (S n) / n` vanish, then `ktRate Z = 0`. The witness program is
`false :: unaryPrefix (encode c) ++ d n`; the unary prefix contributes the constant
`encode c + 1` to the description, absorbed by the density hypotheses. -/
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

/-! ### Truth tables of Boolean functions -/

/-- The canonical enumeration of bitstrings: the bijection `ℕ ≃ BitString` obtained
from the encodability and infinitude of `List Bool`
(`Denumerable.ofEncodableOfInfinite`), listing bitstrings in increasing order of their
`Encodable.encode` value. -/
def bitStringEnum : ℕ ≃ BitString :=
  letI : Denumerable (List Bool) := Denumerable.ofEncodableOfInfinite (List Bool)
  (Denumerable.eqv (List Bool)).symm

/-- The **truth-table sequence** of a Boolean function on bitstrings: bit `i` is the
value of `f` at the `i`-th bitstring of the canonical enumeration. Measuring a function
family through the complexity of its truth table is the meta-complexity convention. -/
def truthTableSeq (f : BitString → Bool) : ℕ → Bool :=
  fun i => f (bitStringEnum i)

/-- The **truth-table complexity rate** of a Boolean function: the `Kt`-rate of its
truth-table sequence. -/
noncomputable def ttKtRate (f : BitString → Bool) : ℝ≥0∞ :=
  ktRate (truthTableSeq f)

/-- The hardcode ceiling for truth tables: `ttKtRate f ≤ 1` for every function. -/
theorem ttKtRate_le_one (f : BitString → Bool) : ttKtRate f ≤ 1 :=
  ktRate_le_one (truthTableSeq f)

/-- The generator collapse for truth tables: runs producing the truth-table prefixes
with vanishing description and log-runtime densities force `ttKtRate f = 0`. -/
theorem ttKtRate_eq_zero_of_witnesses {f : BitString → Bool} {g T : ℕ → ℕ}
    (h : ∀ n, ∃ p t, FlaggedRuns p [] (seqPrefix (truthTableSeq f) n) t ∧
      programLength p ≤ g n ∧ t ≤ T n)
    (hg : Tendsto (fun n => (g n : ℝ≥0∞) / n) atTop (𝓝 0))
    (hT : Tendsto (fun n => (ceilLog2 (T n) : ℝ≥0∞) / n) atTop (𝓝 0)) :
    ttKtRate f = 0 :=
  ktRate_eq_zero_of_witnesses h hg hT

end TimedKt
