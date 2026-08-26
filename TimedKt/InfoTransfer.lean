/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import Mathlib.Order.Lattice.Nat
import TimedKt.WriteOnce

/-!
# Attainment, Witness Runtime, and Information Transfer

Consequences of the timed measures being infima of sets of natural-number costs.

**Attainment.** A finite `condKt` is not merely approximated by runs — it is attained
by one (`TimedDecompressor.exists_runs_condKt`): the candidate set is a set of
natural-number casts, so a finite infimum is the cast of the least realized cost, and
that cost is priced off an actual run. Attainment turns statements about the measure
into statements about concrete runs of the machine.

**Witness runtime.** At the flagged universal machine `Kt_cond` is everywhere finite
(`Kt_cond_lt_top`, from the length upper bound `Kt_cond_le_length`), so attainment
needs no hypothesis there: for every `x` and `y` some optimal run produces `x` from
`y`, and its transition count is at most two to the measured complexity
(`exists_run_time_le_two_pow_Kt_cond`). The optimal description length bounds the
honest runtime — each bit of measured complexity at most doubles the transition
count of the optimal witness.
-/

open Kolmogorov

namespace TimedKt

/-! ### Attainment -/

/-- **Attainment**: a finite `condKt` is attained by an actual run. The candidate
costs form a set of natural numbers, nonempty by finiteness, so the least of them is
realized (`Nat.sInf_mem`) and equals the `ENat` infimum defining the measure. -/
theorem TimedDecompressor.exists_runs_condKt (D : TimedDecompressor) {x y : BitString}
    (h : D.condKt x y < ⊤) :
    ∃ p t, D.Runs p y x t ∧
      D.condKt x y = ((programLength p + ceilLog2 t : ℕ) : ENat) := by
  have hne :
      {n : ℕ | ∃ p t, D.Runs p y x t ∧ programLength p + ceilLog2 t = n}.Nonempty := by
    obtain ⟨n, hn, -⟩ := sInf_lt_iff.mp h
    obtain ⟨p, t, hrun, rfl⟩ := hn
    exact ⟨programLength p + ceilLog2 t, p, t, hrun, rfl⟩
  obtain ⟨p, t, hrun, hpt⟩ := Nat.sInf_mem hne
  refine ⟨p, t, hrun, le_antisymm (condKt_le_of_runs hrun) (le_sInf ?_)⟩
  rintro n ⟨q, u, hqu, rfl⟩
  exact Nat.cast_le.mpr (hpt.trans_le (Nat.sInf_le ⟨q, u, hqu, rfl⟩))

/-! ### Finiteness of the public measures -/

/-- The public conditional measure is everywhere finite: the length upper bound
`Kt_cond_le_length` never exceeds a natural number. -/
theorem Kt_cond_lt_top (x y : BitString) : Kt_cond x y < ⊤ := by
  obtain ⟨c, hc⟩ := Kt_cond_le_length
  refine (hc x y).trans_lt ?_
  rw [← Nat.cast_add]
  exact ENat.natCast_lt_top _

/-- The public plain measure is everywhere finite. -/
theorem Kt_lt_top (x : BitString) : Kt x < ⊤ :=
  Kt_cond_lt_top x []

/-! ### The witness runtime bound -/

/-- **The witness runtime bound.** For every `x` and `y` there is an optimal run of
the flagged machine: `FlaggedRuns p y x t` with `Kt_cond x y = n` and `t ≤ 2 ^ n`.
The measured complexity prices the witness's program length and the ceiling logarithm
of its transition count together, so the count itself is at most `2 ^ n`: each bit of
measured complexity at most doubles the honest runtime of the optimal witness. -/
theorem exists_run_time_le_two_pow_Kt_cond (x y : BitString) :
    ∃ (p : BitString) (t n : ℕ),
      FlaggedRuns p y x t ∧ Kt_cond x y = (n : ENat) ∧ t ≤ 2 ^ n := by
  obtain ⟨p, t, hrun, heq⟩ :=
    timedFlaggedUniversal.exists_runs_condKt (Kt_cond_lt_top x y)
  refine ⟨p, t, programLength p + ceilLog2 t, hrun, heq, ?_⟩
  calc t ≤ 2 ^ ceilLog2 t := le_two_pow_ceilLog2 t
    _ ≤ 2 ^ (programLength p + ceilLog2 t) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)

end TimedKt
