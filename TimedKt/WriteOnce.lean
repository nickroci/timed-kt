/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import Mathlib.Tactic.Ring
import TimedKt.Kt

/-!
# The Write-Once Ledger, and Write-Priced Complexity

The operational relation `Run` carries the write-once trace alongside its transition
count, so the universal machines have a second ledger for free: the number of values
the simulated code commits to its append-only tape. This module exposes that ledger —
`UniversalRunsW` for the unflagged machine, `FlaggedRunsW` for the public flagged
machine — and defines the write-priced complexity

* `Wt_cond x y = min { |p| + ceilLog2 w : the flagged machine runs p on context y,
  producing x with w committed writes }`, and `Wt x = Wt_cond x []`.

## Write convention

The write ledger of a run is the length of the simulated code's write-once trace
(`T.length`): the context flag, the unary-prefix scan, and the result decode commit
nothing. As with the clock, this convention is fixed here and quoted in the README.

## Relation to the transition-priced `Kt`

In the parent project, the write-priced and fuel-priced measures separate unboundedly,
and the comparison `Wt ≤ Kt` could only be proved multiplicatively. Against the
transition clock both pathologies disappear:

* `Wt_cond_le_Kt_cond` — every write is a transition, on the same run of the same
  program, so `Wt_cond ≤ Kt_cond` with no overhead at all;
* `Kt_cond_le_of_flaggedRunsW` — transitions are linear in writes per fixed code
  (`Run.steps_le`), so each write witness bounds `Kt_cond` within an additive penalty
  logarithmic in the witness's own description data.

The conditioning theorem also holds for the write measure, with constant zero
(`Wt_cond_le_Wt`), by the same context flag.
-/

open Nat.Partrec Kolmogorov

namespace TimedKt

/-- The code named by a program tape's unary prefix. -/
def parsedCode (s : BitString) : Code :=
  Denumerable.ofNat Code (s.takeWhile id).length

/-- The clocked unflagged machine with its **write ledger**: `UniversalRunsW s y x t w`
extends `UniversalRuns s y x t` by recording that the simulated code commits exactly
`w` values to its write-once trace. -/
def UniversalRunsW (s y x : BitString) (t w : ℕ) : Prop :=
  ∃ (code : Code) (T : List ℕ) (steps r : ℕ),
    (Encodable.decode ((s.takeWhile id).length) : Option Code) = some code ∧
    Run code (Encodable.encode (s.drop ((s.takeWhile id).length + 1), y)) T steps ∧
    T.getLast? = some r ∧
    x = (Encodable.decode r : Option BitString).getD [] ∧
    t = (s.takeWhile id).length + 1 + steps + 1 ∧
    w = T.length

/-- Forgetting the write ledger gives exactly the clocked relation. -/
theorem universalRuns_iff_universalRunsW (s y x : BitString) (t : ℕ) :
    UniversalRuns s y x t ↔ ∃ w, UniversalRunsW s y x t w := by
  constructor
  · rintro ⟨code, T, steps, r, hdec, hrun, hlast, hx, ht⟩
    exact ⟨T.length, code, T, steps, r, hdec, hrun, hlast, hx, ht, rfl⟩
  · rintro ⟨w, code, T, steps, r, hdec, hrun, hlast, hx, ht, -⟩
    exact ⟨code, T, steps, r, hdec, hrun, hlast, hx, ht⟩

/-- Output, transition count, and write count are unique per tape and context. -/
theorem UniversalRunsW.unique {s y x₁ x₂ : BitString} {t₁ t₂ w₁ w₂ : ℕ}
    (h₁ : UniversalRunsW s y x₁ t₁ w₁) (h₂ : UniversalRunsW s y x₂ t₂ w₂) :
    x₁ = x₂ ∧ t₁ = t₂ ∧ w₁ = w₂ := by
  obtain ⟨c₁, T₁, s₁, r₁, hdec₁, hrun₁, hlast₁, hx₁, ht₁, hw₁⟩ := h₁
  obtain ⟨c₂, T₂, s₂, r₂, hdec₂, hrun₂, hlast₂, hx₂, ht₂, hw₂⟩ := h₂
  rw [hdec₁] at hdec₂
  obtain rfl : c₁ = c₂ := Option.some.inj hdec₂
  obtain ⟨rfl, rfl⟩ := hrun₁.deterministic hrun₂
  rw [hlast₁] at hlast₂
  obtain rfl : r₁ = r₂ := Option.some.inj hlast₂
  exact ⟨hx₁.trans hx₂.symm, ht₁.trans ht₂.symm, hw₁.trans hw₂.symm⟩

/-- The write count is positive, and bounds neither side trivially: every successful
run commits at least the output. -/
theorem UniversalRunsW.one_le_writes {s y x : BitString} {t w : ℕ}
    (h : UniversalRunsW s y x t w) : 1 ≤ w := by
  obtain ⟨_, T, _, _, -, hrun, -, -, -, hw⟩ := h
  exact hw ▸ hrun.one_le_length

/-- Writes never exceed the transition count of the same run. -/
theorem UniversalRunsW.writes_le_time {s y x : BitString} {t w : ℕ}
    (h : UniversalRunsW s y x t w) : w ≤ t := by
  obtain ⟨_, T, steps, _, -, hrun, -, -, ht, hw⟩ := h
  have := hrun.length_le_steps
  omega

/-- **Transitions are linear in writes**, per witness: the prefix scan is bounded by
the program length and the code execution by `2 * w * (progSize + 1)`
(`Run.steps_le`). -/
theorem UniversalRunsW.time_le {s y x : BitString} {t w : ℕ}
    (h : UniversalRunsW s y x t w) :
    t ≤ (programLength s + 2 * progSize (parsedCode s) + 4) * w := by
  obtain ⟨code, T, steps, r, hdec, hrun, hlast, hx, ht, hwl⟩ := h
  have hcode : code = parsedCode s := by
    have h2 := Denumerable.decode_eq_ofNat Code ((s.takeWhile id).length)
    rw [h2] at hdec
    exact (Option.some.inj hdec).symm
  set P := progSize (parsedCode s) with hP
  have hw1 : 1 ≤ w := hwl ▸ hrun.one_le_length
  have hsteps : steps ≤ 2 * w * (P + 1) := by
    have := hrun.steps_le_doc
    rw [← hwl, hcode] at this
    exact this
  have hi : (s.takeWhile id).length ≤ programLength s :=
    (List.takeWhile_prefix id).length_le
  have h1 : t ≤ programLength s + 2 + 2 * w * (P + 1) := by omega
  have h2 : programLength s + 2 ≤ (programLength s + 2) * w :=
    Nat.le_mul_of_pos_right _ hw1
  calc t ≤ programLength s + 2 + 2 * w * (P + 1) := h1
    _ ≤ (programLength s + 2) * w + 2 * w * (P + 1) := by omega
    _ = (programLength s + 2 * P + 4) * w := by ring

/-! ### The write ledger of the flagged machine -/

/-- The clocked flagged machine with its write ledger: the context flag commits
nothing, so the writes are those of the inner run. -/
def FlaggedRunsW (s y x : BitString) (t w : ℕ) : Prop :=
  ∃ b p t', s = b :: p ∧ UniversalRunsW p (bif b then [] else y) x t' w ∧ t = t' + 1

/-- Forgetting the write ledger gives exactly the flagged clocked relation. -/
theorem flaggedRuns_iff_flaggedRunsW (s y x : BitString) (t : ℕ) :
    FlaggedRuns s y x t ↔ ∃ w, FlaggedRunsW s y x t w := by
  constructor
  · rintro ⟨b, p, t', rfl, hrun, rfl⟩
    obtain ⟨w, hw⟩ := (universalRuns_iff_universalRunsW _ _ _ _).mp hrun
    exact ⟨w, b, p, t', rfl, hw, rfl⟩
  · rintro ⟨w, b, p, t', rfl, hw, rfl⟩
    exact ⟨b, p, t', rfl, (universalRuns_iff_universalRunsW _ _ _ _).mpr ⟨w, hw⟩, rfl⟩

/-- Output, transition count, and write count are unique per tape and context. -/
theorem FlaggedRunsW.unique {s y x₁ x₂ : BitString} {t₁ t₂ w₁ w₂ : ℕ}
    (h₁ : FlaggedRunsW s y x₁ t₁ w₁) (h₂ : FlaggedRunsW s y x₂ t₂ w₂) :
    x₁ = x₂ ∧ t₁ = t₂ ∧ w₁ = w₂ := by
  obtain ⟨b₁, p₁, t₁', heq₁, hw₁, rfl⟩ := h₁
  obtain ⟨b₂, p₂, t₂', heq₂, hw₂, rfl⟩ := h₂
  rw [heq₁] at heq₂
  obtain ⟨rfl, rfl⟩ : b₁ = b₂ ∧ p₁ = p₂ := by
    injection heq₂ with h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨rfl, rfl, rfl⟩ := hw₁.unique hw₂
  exact ⟨rfl, rfl, rfl⟩

/-- **Conditional write-priced complexity** over the flagged universal machine:
`Wt_cond x y = min { |p| + ceilLog2 w }` over write-ledgered runs producing `x` from
context `y`. -/
noncomputable def Wt_cond (x y : BitString) : ENat :=
  sInf {n | ∃ p t w, FlaggedRunsW p y x t w ∧
    ((programLength p + ceilLog2 w : ℕ) : ENat) = n}

/-- **Write-priced complexity**: `Wt x = Wt_cond x []`. -/
noncomputable def Wt (x : BitString) : ENat :=
  Wt_cond x []

/-- A write-ledgered run gives a witness upper bound on `Wt_cond`. -/
theorem Wt_cond_le_of_flaggedRunsW {p y x : BitString} {t w : ℕ}
    (h : FlaggedRunsW p y x t w) :
    Wt_cond x y ≤ ((programLength p + ceilLog2 w : ℕ) : ENat) :=
  sInf_le ⟨p, t, w, h, rfl⟩

/-- The library's conditional complexity bounds `Wt_cond` from below: dropping the
write ledger only shrinks the cost. -/
theorem K_cond_le_Wt_cond (x y : BitString) :
    condK flaggedUniversal x y ≤ Wt_cond x y := by
  refine le_sInf ?_
  rintro n ⟨p, t, w, hrun, rfl⟩
  have hprod : produces flaggedUniversal p y x :=
    (flaggedRuns_iff_produces p y x).mpr
      ⟨t, (flaggedRuns_iff_flaggedRunsW p y x t).mpr ⟨w, hrun⟩⟩
  calc condK flaggedUniversal x y
      ≤ ((programLength p : ℕ) : ENat) := sInf_le ⟨p, hprod, rfl⟩
    _ ≤ ((programLength p + ceilLog2 w : ℕ) : ENat) := by
        exact_mod_cast Nat.le_add_right _ _

/-- **Writes never exceed transitions.** Every timed witness is a write witness of the
same program with a smaller ledger, so `Wt_cond ≤ Kt_cond` with no overhead. In the
parent project this comparison against the fuel clock is only multiplicative; against
the transition clock it is free. -/
theorem Wt_cond_le_Kt_cond (x y : BitString) : Wt_cond x y ≤ Kt_cond x y := by
  refine le_sInf ?_
  rintro n ⟨p, t, hrun, rfl⟩
  obtain ⟨w, hw⟩ := (flaggedRuns_iff_flaggedRunsW p y x t).mp hrun
  have hwt : w ≤ t := by
    obtain ⟨b, q, t', -, hq, rfl⟩ := hw
    have := hq.writes_le_time
    omega
  refine le_trans (Wt_cond_le_of_flaggedRunsW hw) ?_
  exact Nat.cast_le.mpr (Nat.add_le_add_left (ceilLog2_mono hwt) _)

/-- `Wt ≤ Kt` with no overhead. -/
theorem Wt_le_Kt (x : BitString) : Wt x ≤ Kt x :=
  Wt_cond_le_Kt_cond x []

/-- **The conditioning theorem for the write measure**: `Wt(x | y) ≤ Wt(x)` with
additive constant zero, by the same context flag as `Kt_cond_le_Kt`. -/
theorem Wt_cond_le_Wt (x y : BitString) : Wt_cond x y ≤ Wt x := by
  refine le_sInf ?_
  rintro n ⟨s, t, w, hrun, rfl⟩
  obtain ⟨b, p, t', rfl, hw, rfl⟩ := hrun
  have hctx : (bif b then [] else ([] : BitString)) = ([] : BitString) := by
    cases b <;> rfl
  rw [hctx] at hw
  have hF : FlaggedRunsW (true :: p) y x (t' + 1) w := ⟨true, p, t', rfl, hw, rfl⟩
  refine le_trans (Wt_cond_le_of_flaggedRunsW hF) ?_
  refine Nat.cast_le.mpr ?_
  simp [programLength]

/-- **Transitions are linear in writes.** Each write witness bounds the
transition-priced `Kt_cond` within an additive penalty logarithmic in the witness's
description data. -/
theorem Kt_cond_le_of_flaggedRunsW {s y x : BitString} {t w : ℕ}
    (h : FlaggedRunsW s y x t w) :
    Kt_cond x y ≤ ((programLength s + ceilLog2 w +
      ceilLog2 (programLength s + 2 * progSize (parsedCode s.tail) + 4) : ℕ) : ENat) := by
  obtain ⟨b, p, t', rfl, hw, rfl⟩ := h
  have hF : FlaggedRuns (b :: p) y x (t' + 1) :=
    ⟨b, p, t', rfl, (universalRuns_iff_universalRunsW _ _ _ _).mpr ⟨w, hw⟩, rfl⟩
  have hw1 : 1 ≤ w := hw.one_le_writes
  have htle := hw.time_le
  have ht1 : t' + 1
      ≤ (programLength (b :: p) + 2 * progSize (parsedCode p) + 4) * w := by
    have hlen : programLength (b :: p) = programLength p + 1 := by
      simp [programLength]
    rw [hlen]
    calc t' + 1
        ≤ (programLength p + 2 * progSize (parsedCode p) + 4) * w + 1 := by omega
      _ ≤ (programLength p + 2 * progSize (parsedCode p) + 4) * w + w := by omega
      _ = (programLength p + 1 + 2 * progSize (parsedCode p) + 4) * w := by ring
  have hlog : ceilLog2 (t' + 1)
      ≤ ceilLog2 (programLength (b :: p) + 2 * progSize (parsedCode p) + 4)
        + ceilLog2 w :=
    le_trans (ceilLog2_mono ht1) (ceilLog2_mul_le _ _)
  refine le_trans (Kt_cond_le_of_runs hF) ?_
  rw [show (b :: p).tail = p from rfl]
  refine Nat.cast_le.mpr ?_
  omega

/-- **The length upper bound for `Wt`**: the projection code `Code.left` outputs its
program with a single write, so `Wt_cond x y ≤ |x| + c` for the explicit constant
`c = encode Code.left + 2`. -/
theorem Wt_cond_le_length (x y : BitString) :
    Wt_cond x y ≤ ((programLength x + (Encodable.encode Code.left + 2) : ℕ) : ENat) := by
  have hrun : Run Code.left (Encodable.encode (x, y))
      [(Encodable.encode (x, y)).unpair.1] 1 := Run.left _
  have hlast : [(Encodable.encode (x, y)).unpair.1].getLast? =
      some (Encodable.encode x) := by
    rw [Encodable.encode_prod_val, Nat.unpair_pair]
    simp
  have hW : UniversalRunsW (unaryPrefix (Encodable.encode Code.left) ++ x) y x
      (Encodable.encode Code.left + 1 + 1 + 1) 1 := by
    refine ⟨Code.left, [(Encodable.encode (x, y)).unpair.1], 1, Encodable.encode x,
      ?_, ?_, ?_, ?_, ?_, rfl⟩
    · rw [takeWhile_unaryPrefix, Encodable.encodek]
    · rw [takeWhile_unaryPrefix, drop_unaryPrefix]
      exact hrun
    · exact hlast
    · rw [Encodable.encodek]
      simp
    · rw [takeWhile_unaryPrefix]
  have hFW : FlaggedRunsW
      (false :: (unaryPrefix (Encodable.encode Code.left) ++ x)) y x
      (Encodable.encode Code.left + 1 + 1 + 1 + 1) 1 :=
    ⟨false, unaryPrefix (Encodable.encode Code.left) ++ x,
      Encodable.encode Code.left + 1 + 1 + 1, rfl, hW, rfl⟩
  refine le_trans (Wt_cond_le_of_flaggedRunsW hFW) ?_
  refine Nat.cast_le.mpr ?_
  have hlen : programLength (false :: (unaryPrefix (Encodable.encode Code.left) ++ x))
      = Encodable.encode Code.left + 2 + programLength x := by
    simp [programLength, List.length_append, length_unaryPrefix]
    omega
  simp only [hlen, ceilLog2_one]
  omega

end TimedKt
