/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.Invariance
import TimedKt.Flagged

/-!
# The Public Definitions: `Kt` and `Kt_cond`

The timed complexity of this package, instantiated at the timed flagged universal
machine (`TimedKt.Flagged`):

* `Kt_cond x y = min { |p| + ceilLog2 t : the flagged machine runs p on context y,
  producing x in t transitions }`, and
* `Kt x = Kt_cond x []`.

Program length is the bit-length of an actual bitstring program; `t` counts
transitions of the operational semantics (`TimedKt.Run` under the machine's cost
convention, plus one transition for the context flag). Neither `progSize` nor
`Code.evaln` fuel occurs in the definitions.

## Main results

* `Kt_cond_le_Kt`: **the conditioning theorem** — `Kt(x | y) ≤ Kt(x)`, with additive
  constant zero. The parent project refuted the constant-overhead form outright for
  its fuel-priced measure; for the transition clock and the flagged machine it holds
  for free.
* `Kt_cond_le_realized`: invariance — `Kt(x | y) ≤ Kt_D(x | y) + (overhead + 2)` for
  every code-realized timed decompressor `D` with a linear simulation bound.
* `K_le_Kt` / `K_cond_le_Kt_cond`: the library's bitstring complexities of the same
  machine bound `Kt` from below.
* `Kt_cond_le_length`: `Kt_cond x y ≤ |x| + O(1)`.
* `natKt`: the natural-number wrapper, with `natKt_le`.
-/

open Kolmogorov

namespace TimedKt

/-- **Conditional timed complexity** over the flagged universal machine:
`Kt_cond x y = min { |p| + ceilLog2 t }` over clocked runs producing `x` from
context `y`. -/
noncomputable def Kt_cond (x y : BitString) : ENat :=
  timedFlaggedUniversal.condKt x y

/-- **Timed complexity** over the flagged universal machine: `Kt x = Kt_cond x []`. -/
noncomputable def Kt (x : BitString) : ENat :=
  timedFlaggedUniversal.plainKt x

/-- **The conditioning theorem.** Conditioning never costs: `Kt(x | y) ≤ Kt(x)`, with
additive constant zero — the machine's context flag turns any plain witness into a
conditional one of the same length and transition count. Contrast: for the parent
project's fuel-priced measure even `Kt(x | y) ≤ Kt(x) + C` is refuted, because fuel
taxes the mere receipt of the conditioning input. -/
theorem Kt_cond_le_Kt (x y : BitString) : Kt_cond x y ≤ Kt x :=
  condKt_flagged_cond_le_plain x y

/-- A clocked run of the flagged machine gives a witness upper bound on `Kt_cond`. -/
theorem Kt_cond_le_of_runs {p y x : BitString} {t : ℕ}
    (h : FlaggedRuns p y x t) :
    Kt_cond x y ≤ ((programLength p + ceilLog2 t : ℕ) : ENat) :=
  TimedDecompressor.condKt_le_of_runs (D := timedFlaggedUniversal) h

/-- The library's conditional complexity of the flagged machine bounds `Kt_cond` from
below: dropping the clock only shrinks the cost. -/
theorem K_cond_le_Kt_cond (x y : BitString) :
    condK flaggedUniversal x y ≤ Kt_cond x y :=
  timedFlaggedUniversal.condK_le_condKt x y

/-- The library's plain complexity of the flagged machine bounds `Kt` from below. -/
theorem K_le_Kt (x : BitString) : plainK flaggedUniversal x ≤ Kt x :=
  timedFlaggedUniversal.plainK_le_plainKt x

/-- `Kt_cond` is finite exactly on the outputs the flagged machine produces. -/
theorem Kt_cond_lt_top_iff {x y : BitString} :
    Kt_cond x y < ⊤ ↔ ∃ p, produces flaggedUniversal p y x :=
  TimedDecompressor.condKt_lt_top_iff

/-- **Invariance for the public `Kt`.** For every timed decompressor `D` with a code
realization `R`, `Kt(x | y) ≤ Kt_D(x | y) + (R.overhead + 2)`: the unflagged
machine's invariance theorem (`condKt_timedUniversal_le`) transfers through the
two-unit cost of the context flag. -/
theorem Kt_cond_le_realized (D : TimedDecompressor) (R : D.Realization)
    (x y : BitString) :
    Kt_cond x y ≤ D.condKt x y + ((R.overhead + 2 : ℕ) : ENat) := by
  calc Kt_cond x y ≤ timedUniversal.condKt x y + 2 :=
        condKt_flagged_le_condKt_universal x y
    _ ≤ D.condKt x y + (R.overhead : ENat) + 2 :=
        add_le_add (condKt_timedUniversal_le D R x y) le_rfl
    _ = D.condKt x y + ((R.overhead + 2 : ℕ) : ENat) := by
        push_cast
        rw [add_assoc]

/-- **The length upper bound**: `Kt_cond x y ≤ |x| + c` for a universal constant `c`.
In particular `Kt_cond` and `Kt` are everywhere finite. -/
theorem Kt_cond_le_length :
    ∃ c : ℕ, ∀ x y : BitString, Kt_cond x y ≤ (programLength x : ENat) + c := by
  refine ⟨idTimedRealization.overhead + 2, fun x y => ?_⟩
  calc Kt_cond x y
      ≤ idTimed.condKt x y + ((idTimedRealization.overhead + 2 : ℕ) : ENat) :=
        Kt_cond_le_realized idTimed idTimedRealization x y
    _ ≤ (programLength x : ENat) + (idTimedRealization.overhead + 2 : ℕ) :=
        add_le_add (idTimed_condKt_le x y) le_rfl

/-! ### The natural-number wrapper

Numbers enter the bitstring theory through `Nat.bits`, the little-endian binary
expansion. This is a wrapper over the bitstring definitions, not a separate theory. -/

/-- Timed complexity of a natural number: `Kt` of its binary expansion. -/
noncomputable def natKt (n : ℕ) : ENat :=
  Kt n.bits

/-- The wrapper is definitionally `Kt` of the binary expansion. -/
theorem natKt_def (n : ℕ) : natKt n = Kt n.bits := rfl

/-- `natKt n ≤ |n.bits| + c`: a number costs at most its binary length plus a
universal constant. -/
theorem natKt_le : ∃ c : ℕ, ∀ n : ℕ, natKt n ≤ ((n.bits.length : ℕ) : ENat) + c := by
  obtain ⟨c, hc⟩ := Kt_cond_le_length
  exact ⟨c, fun n => hc n.bits []⟩

end TimedKt
