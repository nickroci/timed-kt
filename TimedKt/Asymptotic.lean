/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
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

This module builds the profile: `seqPrefix Z n` is the length-`n` prefix of `Z` as a
bitstring, and `ktProfile Z n` is its `Kt`, landed in `ℕ` — well-grounded because the
public measure is everywhere finite (`Kt_lt_top`). The hardcode bound transfers:
`ktProfile Z n ≤ n + c` for a universal constant `c` (`ktProfile_le`), so the profile of
every sequence, however uncomputable, grows at most linearly. Separations therefore
cannot live in upper bounds on single prefixes; they live in the growth rate of the
profile, developed on top of this layer.
-/

open Kolmogorov

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

end TimedKt
