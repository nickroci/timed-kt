/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import KolmogorovMathlib.Core.Invariance
import TimedKt.UniversalRun

/-!
# The Flagged Universal Machine

The public `Kt` of this package is defined over a universal machine with one extra
convention: the first program bit is a **context flag**. On program `b :: p`, the
machine runs the timed universal machine of `TimedKt.UniversalRun` on `p`, with the
context erased when `b = true` and passed through when `b = false`:

* `flaggedUniversal (true :: p, y) = universalDecompressor (p, [])`
* `flaggedUniversal (false :: p, y) = universalDecompressor (p, y)`

The flag costs one bit of description and one transition, and buys the conditioning
theorem outright: a plain-complexity witness `b :: p` runs with empty context, so
`true :: p` is a conditional witness for every context `y` — same length, same time.
`Kt(x | y) ≤ Kt(x)` therefore holds with additive constant zero
(`condKt_flagged_cond_le_plain`; the public statement is `Kt_cond_le_Kt` in
`TimedKt.Kt`).

Choosing a universal machine with this closure property is the standard resolution:
without the flag, erasing the context requires either wrapping the simulated code
(which inflates the unary prefix quadratically) or a self-interpreter with a proved
linear-overhead transition bound (open; see the README's invariance scope). The
comparison-class optimality of the unflagged machine transfers at cost `2`
(`condKt_flagged_le_condKt_universal`).
-/

open Nat.Partrec Kolmogorov

namespace TimedKt

/-- The **flagged universal decompressor**: the first program bit decides whether the
context is erased (`true`) or passed through (`false`); the rest of the tape is run by
`universalDecompressor`. Undefined on the empty program. -/
def flaggedUniversal : Map := fun sy =>
  (Part.ofOption sy.1.head?).bind fun b =>
    universalDecompressor (sy.1.tail, bif b then [] else sy.2)

/-- On a nonempty program the flagged machine is the universal machine on the tail,
with the context selected by the flag. -/
theorem flaggedUniversal_cons (b : Bool) (p y : BitString) :
    flaggedUniversal (b :: p, y) =
      universalDecompressor (p, bif b then [] else y) := by
  simp [flaggedUniversal]

/-- The flagged machine is a decompressor. -/
theorem isDecompressor_flaggedUniversal : isDecompressor flaggedUniversal := by
  have hhead : Computable fun sy : BitString × BitString => sy.1.head? :=
    (Primrec.list_head?.comp Primrec.fst).to_comp
  have htail : Computable fun q : (BitString × BitString) × Bool => q.1.1.tail :=
    (Primrec.list_tail.comp (Primrec.fst.comp Primrec.fst)).to_comp
  have hctx : Computable fun q : (BitString × BitString) × Bool =>
      bif q.2 then ([] : BitString) else q.1.2 :=
    Computable.cond Computable.snd (Computable.const [])
      (Computable.snd.comp Computable.fst)
  exact Partrec.bind (Computable.ofOption hhead)
    ((isDecompressorUniversalDecompressor.comp (htail.pair hctx)).to₂)

/-- The clocked flagged machine: one transition for the flag, then a clocked
universal run on the tail with the selected context. -/
def FlaggedRuns (s y x : BitString) (t : ℕ) : Prop :=
  ∃ b p t', s = b :: p ∧ UniversalRuns p (bif b then [] else y) x t' ∧ t = t' + 1

/-- Soundness and completeness of the clocked flagged relation. -/
theorem flaggedRuns_iff_produces (s y x : BitString) :
    produces flaggedUniversal s y x ↔ ∃ t, FlaggedRuns s y x t := by
  cases s with
  | nil =>
      constructor
      · intro hprod
        rw [produces] at hprod
        simp [flaggedUniversal] at hprod
      · rintro ⟨t, b, p, t', heq, -, -⟩
        exact absurd heq (by simp)
  | cons b p =>
      rw [produces, flaggedUniversal_cons]
      constructor
      · intro hprod
        obtain ⟨t', ht'⟩ :=
          (universalRuns_iff_produces p (bif b then [] else y) x).mp hprod
        exact ⟨t' + 1, b, p, t', rfl, ht', rfl⟩
      · rintro ⟨t, b', p', t', heq, hrun, rfl⟩
        obtain ⟨rfl, rfl⟩ : b = b' ∧ p = p' := by
          injection heq with h1 h2
          exact ⟨h1, h2⟩
        exact (universalRuns_iff_produces _ _ _).mpr ⟨t', hrun⟩

/-- Output and transition count are unique per tape and context. -/
theorem FlaggedRuns.unique {s y x₁ x₂ : BitString} {t₁ t₂ : ℕ}
    (h₁ : FlaggedRuns s y x₁ t₁) (h₂ : FlaggedRuns s y x₂ t₂) :
    x₁ = x₂ ∧ t₁ = t₂ := by
  obtain ⟨b₁, p₁, t₁', heq₁, hrun₁, rfl⟩ := h₁
  obtain ⟨b₂, p₂, t₂', heq₂, hrun₂, rfl⟩ := h₂
  rw [heq₁] at heq₂
  obtain ⟨rfl, rfl⟩ : b₁ = b₂ ∧ p₁ = p₂ := by
    injection heq₂ with h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨rfl, rfl⟩ := hrun₁.unique hrun₂
  exact ⟨rfl, rfl⟩

/-- The **timed flagged universal machine** — the machine of the public `Kt`. -/
def timedFlaggedUniversal : TimedDecompressor where
  toMap := flaggedUniversal
  Runs := FlaggedRuns
  partrec := isDecompressor_flaggedUniversal
  runs_iff_produces := flaggedRuns_iff_produces
  one_le_time := by
    rintro p y x t ⟨b, q, t', -, -, rfl⟩
    omega

/-! ### Transfer from the unflagged machine -/

/-- Passing the context through costs one bit and one transition:
the flagged machine is at most `2` worse than the unflagged one. -/
theorem condKt_flagged_le_condKt_universal (x y : BitString) :
    timedFlaggedUniversal.condKt x y ≤ timedUniversal.condKt x y + 2 := by
  refine sInfLeSInfAdd ?_
  rintro n ⟨p, t, hrun, rfl⟩
  have ht1 : 1 ≤ t := timedUniversal.one_le_time p y x t hrun
  have hF : FlaggedRuns (false :: p) y x (t + 1) := ⟨false, p, t, rfl, hrun, rfl⟩
  refine ⟨((programLength (false :: p) + ceilLog2 (t + 1) : ℕ) : ENat),
    ⟨false :: p, t + 1, hF, rfl⟩, ?_⟩
  rw [← Nat.cast_add]
  refine Nat.cast_le.mpr ?_
  have hlog := ceilLog2_succ_le ht1
  simp only [programLength, List.length_cons]
  omega

/-- **Conditioning is free.** A plain-complexity witness runs with empty context, so
flipping its flag to `true` gives a conditional witness of the same length and the
same transition count: `Kt(x | y) ≤ Kt(x)` with additive constant zero. -/
theorem condKt_flagged_cond_le_plain (x y : BitString) :
    timedFlaggedUniversal.condKt x y ≤ timedFlaggedUniversal.plainKt x := by
  refine le_sInf ?_
  rintro n ⟨s, t, hrun, rfl⟩
  obtain ⟨b, p, t', rfl, hrun', rfl⟩ := hrun
  have hctx : (bif b then [] else ([] : BitString)) = ([] : BitString) := by
    cases b <;> rfl
  rw [hctx] at hrun'
  have hF : FlaggedRuns (true :: p) y x (t' + 1) := ⟨true, p, t', rfl, hrun', rfl⟩
  refine le_trans
    (TimedDecompressor.condKt_le_of_runs (D := timedFlaggedUniversal) hF) ?_
  refine Nat.cast_le.mpr ?_
  simp [programLength]

end TimedKt
