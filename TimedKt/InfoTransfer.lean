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

**Witness runtime.** At the composing universal machine `Kt_cond` is everywhere finite
(`Kt_cond_lt_top`, from the length upper bound `Kt_cond_le_length`), so attainment
needs no hypothesis there: for every `x` and `y` some optimal run produces `x` from
`y`, and its transition count is at most two to the measured complexity
(`exists_run_time_le_two_pow_Kt_cond`). The optimal description length bounds the
runtime — each bit of measured complexity at most doubles the transition
count of the optimal witness.

**Information transfer.** `ktTransfer y x = Kt x - Kt_cond x y` is the time-bounded
analogue of the mutual-information quantity `I(y : x) = K(x) - K(x | y)` of Li and
Vitányi: the `Kt`-information the context `y` carries about `x`. On this machine the
quantity is well-defined with no context-size correction term, precisely because
conditioning is free (`Kt_cond_le_Kt`, additive constant zero); a fuel-priced
variant taxes the mere receipt of the context, so its transfer would need a
correction of order `log |y|` before contexts could be compared. Nonnegativity needs
no statement: the transfer lives in `ℕ∞`. The defining identity is
`ktTransfer y x + Kt_cond x y = Kt x` (`ktTransfer_add_Kt_cond`), and combining it
with the witness runtime bound gives the halving corollary
(`exists_run_time_le_two_pow_of_ktTransfer`): if `Kt x = m` and the transfer is `g`,
some run produces `x` from `y` within `2 ^ (m - g)` transitions — every bit of
information the context carries about `x` halves the worst-case witness runtime.

The write measure supports the same construction (`wtTransfer`), from the same two
ingredients: conditioning at constant zero (`Wt_cond_le_Wt`) and finiteness
(`Wt_le_length`).
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
the composing machine: `CompRuns p y x t` with `Kt_cond x y = n` and `t ≤ 2 ^ n`.
The measured complexity prices the witness's program length and the ceiling logarithm
of its transition count together, so the count itself is at most `2 ^ n`: each bit of
measured complexity at most doubles the runtime of the optimal witness. -/
theorem exists_run_time_le_two_pow_Kt_cond (x y : BitString) :
    ∃ (p : BitString) (t n : ℕ),
      CompRuns p y x t ∧ Kt_cond x y = (n : ENat) ∧ t ≤ 2 ^ n := by
  obtain ⟨p, t, hrun, heq⟩ :=
    timedCompUniversal.exists_runs_condKt (Kt_cond_lt_top x y)
  refine ⟨p, t, programLength p + ceilLog2 t, hrun, heq, ?_⟩
  calc t ≤ 2 ^ ceilLog2 t := le_two_pow_ceilLog2 t
    _ ≤ 2 ^ (programLength p + ceilLog2 t) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)

/-! ### Information transfer -/

/-- **Information transfer**: the `Kt`-information the context `y` carries about `x`,
`ktTransfer y x = Kt x - Kt_cond x y` (truncated subtraction in `ℕ∞`) — the
time-bounded analogue of `I(y : x) = K(x) - K(x | y)`. No context-size correction
term is needed, because conditioning is free on this machine (`Kt_cond_le_Kt`,
additive constant zero); nonnegativity is automatic in `ℕ∞`. -/
noncomputable def ktTransfer (y x : BitString) : ENat :=
  Kt x - Kt_cond x y

/-- **The transfer identity**: `ktTransfer y x + Kt_cond x y = Kt x` — the transfer
and the residual conditional complexity partition the plain complexity exactly.
Truncated subtraction cancels because `Kt_cond_le_Kt` provides the ordering. -/
theorem ktTransfer_add_Kt_cond (y x : BitString) :
    ktTransfer y x + Kt_cond x y = Kt x :=
  tsub_add_cancel_of_le (Kt_cond_le_Kt x y)

/-- The transfer never exceeds the plain complexity. -/
theorem ktTransfer_le_Kt (y x : BitString) : ktTransfer y x ≤ Kt x :=
  tsub_le_self

/-- The transfer is everywhere finite. -/
theorem ktTransfer_lt_top (y x : BitString) : ktTransfer y x < ⊤ :=
  (ktTransfer_le_Kt y x).trans_lt (Kt_lt_top x)

/-- The plain measure is the conditional measure at the empty context,
definitionally. -/
theorem Kt_cond_empty (x : BitString) : Kt_cond x [] = Kt x := rfl

/-- The empty context transfers nothing. -/
theorem ktTransfer_empty (x : BitString) : ktTransfer [] x = 0 :=
  tsub_eq_zero_of_le (Kt_cond_empty x).ge

/-- **Transfer halves runtime.** If `Kt x = m` and the context transfers `g` bits,
some run produces `x` from `y` within `2 ^ (m - g)` transitions: every bit of
information the context carries about `x` halves the worst-case witness runtime. -/
theorem exists_run_time_le_two_pow_of_ktTransfer {x y : BitString} {m g : ℕ}
    (hK : Kt x = (m : ENat)) (hg : ktTransfer y x = (g : ENat)) :
    ∃ p t, CompRuns p y x t ∧ t ≤ 2 ^ (m - g) := by
  obtain ⟨p, t, n, hrun, hn, ht⟩ := exists_run_time_le_two_pow_Kt_cond x y
  have hsum : ((g + n : ℕ) : ENat) = ((m : ℕ) : ENat) := by
    rw [Nat.cast_add, ← hg, ← hn, ← hK]
    exact ktTransfer_add_Kt_cond y x
  have hgnm : g + n = m := by exact_mod_cast hsum
  refine ⟨p, t, hrun, ?_⟩
  have hn' : n = m - g := by omega
  exact hn' ▸ ht

/-! ### The write-measure analogue -/

/-- The write measure is everywhere finite: the length upper bound `Wt_le_length`
never exceeds a natural number. -/
theorem Wt_lt_top (x : BitString) : Wt x < ⊤ :=
  (Wt_le_length x).trans_lt (ENat.natCast_lt_top _)

/-- **Information transfer for the write measure**:
`wtTransfer y x = Wt x - Wt_cond x y`, from the same two ingredients as `ktTransfer`
— conditioning at constant zero (`Wt_cond_le_Wt`) and finiteness (`Wt_le_length`). -/
noncomputable def wtTransfer (y x : BitString) : ENat :=
  Wt x - Wt_cond x y

/-- The transfer identity for the write measure. -/
theorem wtTransfer_add_Wt_cond (y x : BitString) :
    wtTransfer y x + Wt_cond x y = Wt x :=
  tsub_add_cancel_of_le (Wt_cond_le_Wt x y)

/-- The write transfer never exceeds the plain write complexity. -/
theorem wtTransfer_le_Wt (y x : BitString) : wtTransfer y x ≤ Wt x :=
  tsub_le_self

/-- The write transfer is everywhere finite. -/
theorem wtTransfer_lt_top (y x : BitString) : wtTransfer y x < ⊤ :=
  (wtTransfer_le_Wt y x).trans_lt (Wt_lt_top x)

/-- The plain write measure is the conditional one at the empty context,
definitionally. -/
theorem Wt_cond_empty (x : BitString) : Wt_cond x [] = Wt x := rfl

/-- The empty context transfers nothing on the write measure. -/
theorem wtTransfer_empty (x : BitString) : wtTransfer [] x = 0 :=
  tsub_eq_zero_of_le (Wt_cond_empty x).ge

end TimedKt
