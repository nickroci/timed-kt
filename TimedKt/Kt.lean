/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.Invariance
import TimedKt.CompRun

/-!
# The Public Definitions: `Kt` and `Kt_cond`

The timed complexity of this package, instantiated at the timed composing universal
machine (`TimedKt.CompRun`):

* `Kt_cond x y = min { |p| + ceilLog2 t : the composing machine runs p on context y,
  producing x in t transitions }`, and
* `Kt x = Kt_cond x []`.

Program length is the bit-length of an actual bitstring program; `t` counts
transitions of the operational semantics (`TimedKt.Run` under the machine's cost
convention, plus the flag transitions and the gamma scan of the composing layer).
Neither `progSize` nor `Code.evaln` fuel occurs in the definitions.

The composing machine embeds the flagged universal machine of `TimedKt.Flagged`
behind one comp flag and adds a composition primitive; this is what makes the
triangle inequality (`TimedKt.Triangle`) provable with logarithmic overhead while
every constant-overhead property of the flagged machine survives at `+2`.

## Main results

* `Kt_cond_le_Kt`: **the conditioning theorem** — `Kt(x | y) ≤ Kt(x)`, with additive
  constant zero. A plain witness becomes a conditional witness by flipping the
  single erase bit at its root (`condKt_comp_cond_le_plain`). A fuel-priced variant
  is incompatible with any constant-overhead form, because `Code.evaln`'s input
  guard taxes the mere receipt of the conditioning input.
* `Kt_cond_le_realized`: invariance — `Kt(x | y) ≤ Kt_D(x | y) + (overhead + 4)` for
  every code-realized timed decompressor `D` with a linear simulation bound.
* `K_le_Kt` / `K_cond_le_Kt_cond`: the library's bitstring complexities of the same
  machine bound `Kt` from below.
* `Kt_cond_le_length`: `Kt_cond x y ≤ |x| + O(1)`.
* `natKt`: the natural-number wrapper, with `natKt_le`.
-/

open Kolmogorov

namespace TimedKt

/-- **Conditional timed complexity** over the composing universal machine:
`Kt_cond x y = min { |p| + ceilLog2 t }` over clocked runs producing `x` from
context `y`. -/
noncomputable def Kt_cond (x y : BitString) : ENat :=
  timedCompUniversal.condKt x y

/-- **Timed complexity** over the composing universal machine: `Kt x = Kt_cond x []`. -/
noncomputable def Kt (x : BitString) : ENat :=
  timedCompUniversal.plainKt x

/-- **The conditioning theorem.** Conditioning never costs: `Kt(x | y) ≤ Kt(x)`, with
additive constant zero — a plain witness becomes a conditional witness of the same
length and transition count by flipping the single erase bit at its root. Contrast:
a fuel-priced variant cannot satisfy even `Kt(x | y) ≤ Kt(x) + C`, because
`Code.evaln`'s input guard (`Code.evaln_bound`) taxes the mere receipt of the
conditioning input. -/
theorem Kt_cond_le_Kt (x y : BitString) : Kt_cond x y ≤ Kt x :=
  condKt_comp_cond_le_plain x y

/-- A clocked run of the composing machine gives a witness upper bound on
`Kt_cond`. -/
theorem Kt_cond_le_of_runs {p y x : BitString} {t : ℕ}
    (h : CompRuns p y x t) :
    Kt_cond x y ≤ ((programLength p + ceilLog2 t : ℕ) : ENat) :=
  TimedDecompressor.condKt_le_of_runs (D := timedCompUniversal) h

/-- The library's conditional complexity of the composing machine bounds `Kt_cond`
from below: dropping the clock only shrinks the cost. -/
theorem K_cond_le_Kt_cond (x y : BitString) :
    condK compUniversal x y ≤ Kt_cond x y :=
  timedCompUniversal.condK_le_condKt x y

/-- The library's plain complexity of the composing machine bounds `Kt` from below. -/
theorem K_le_Kt (x : BitString) : plainK compUniversal x ≤ Kt x :=
  timedCompUniversal.plainK_le_plainKt x

/-- `Kt_cond` is finite exactly on the outputs the composing machine produces. -/
theorem Kt_cond_lt_top_iff {x y : BitString} :
    Kt_cond x y < ⊤ ↔ ∃ p, produces compUniversal p y x :=
  TimedDecompressor.condKt_lt_top_iff

/-- **Invariance for the public `Kt`.** For every timed decompressor `D` with a code
realization `R`, `Kt(x | y) ≤ Kt_D(x | y) + (R.overhead + 4)`: the unflagged
machine's invariance theorem (`condKt_timedUniversal_le`) transfers through the
two-unit cost of the context flag and the two-unit cost of the comp flag. -/
theorem Kt_cond_le_realized (D : TimedDecompressor) (R : D.Realization)
    (x y : BitString) :
    Kt_cond x y ≤ D.condKt x y + ((R.overhead + 4 : ℕ) : ENat) := by
  calc Kt_cond x y ≤ timedFlaggedUniversal.condKt x y + 2 :=
        condKt_comp_le_condKt_flagged x y
    _ ≤ timedUniversal.condKt x y + 2 + 2 :=
        add_le_add (condKt_flagged_le_condKt_universal x y) le_rfl
    _ ≤ D.condKt x y + (R.overhead : ENat) + 2 + 2 :=
        add_le_add (add_le_add (condKt_timedUniversal_le D R x y) le_rfl) le_rfl
    _ = D.condKt x y + ((R.overhead + 4 : ℕ) : ENat) := by
        push_cast
        rw [add_assoc, add_assoc]
        norm_num

/-- **The length upper bound**: `Kt_cond x y ≤ |x| + c` for a universal constant `c`.
In particular `Kt_cond` and `Kt` are everywhere finite. -/
theorem Kt_cond_le_length :
    ∃ c : ℕ, ∀ x y : BitString, Kt_cond x y ≤ (programLength x : ENat) + c := by
  refine ⟨idTimedRealization.overhead + 4, fun x y => ?_⟩
  calc Kt_cond x y
      ≤ idTimed.condKt x y + ((idTimedRealization.overhead + 4 : ℕ) : ENat) :=
        Kt_cond_le_realized idTimed idTimedRealization x y
    _ ≤ (programLength x : ENat) + (idTimedRealization.overhead + 4 : ℕ) :=
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
