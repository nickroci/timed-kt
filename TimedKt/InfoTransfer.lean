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

end TimedKt
