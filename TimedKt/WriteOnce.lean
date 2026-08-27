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
`UniversalRunsW` for the unflagged machine, `FlaggedRunsW` for the flagged machine,
`CompRunsW` for the public composing machine — and defines the write-priced
complexity

* `Wt_cond x y = min { |p| + ceilLog2 w : the composing machine runs p on context y,
  producing x with w committed writes }`, and `Wt x = Wt_cond x []`.

## Write convention

The write ledger of a run is the length of the simulated code's write-once trace
(`T.length`): the context flag, the unary-prefix scan, and the result decode commit
nothing. On the composing layer the comp flag, the erase bit, and the gamma scan
commit nothing either, and a composition node's ledger is the sum of its stages'
ledgers (`w = w₂ + w₁`). As with the clock, this convention is fixed here and quoted
in the README.

## Relation to the transition-priced `Kt`

On a fuel clock no comparison of this quality is available: fuel diverges unboundedly
from the committed work (`fuel_exceeds_writes_unboundedly`), so a fuel-priced time
measure cannot track the write ledger at zero overhead. Against the transition clock
the two ledgers are tightly coupled:

* `Wt_cond_le_Kt_cond` — every write is a transition, on the same run of the same
  program, so `Wt_cond ≤ Kt_cond` with no overhead at all;
* `Kt_cond_le_of_flaggedRunsW` — transitions are linear in writes per fixed code
  (`Run.steps_le`), so each flagged write witness bounds `Kt_cond` within an additive
  penalty logarithmic in the witness's own description data (plus the two-unit embed
  cost of the composing layer).

The conditioning theorem also holds for the write measure, with constant zero
(`Wt_cond_le_Wt`), by the same root bit flip as `Kt_cond_le_Kt`.
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

/-- Every flagged write-ledgered run commits at least one write. -/
theorem FlaggedRunsW.one_le_writes {s y x : BitString} {t w : ℕ}
    (h : FlaggedRunsW s y x t w) : 1 ≤ w := by
  obtain ⟨b, p, t', -, hU, -⟩ := h
  exact hU.one_le_writes

/-- Writes never exceed the transition count of the same flagged run. -/
theorem FlaggedRunsW.writes_le_time {s y x : BitString} {t w : ℕ}
    (h : FlaggedRunsW s y x t w) : w ≤ t := by
  obtain ⟨b, p, t', -, hU, rfl⟩ := h
  have := hU.writes_le_time
  omega

/-! ### The write ledger of the composing machine -/

/-- The clocked composing machine with its **write ledger**: the comp flag, the
erase bit, and the gamma scan commit nothing, an embed node carries the flagged
ledger, and a composition node's ledger is the sum of its stages' ledgers. -/
inductive CompRunsW : BitString → BitString → BitString → ℕ → ℕ → Prop
  | embed {s z x : BitString} {t w : ℕ} :
      FlaggedRunsW s z x t w → CompRunsW (false :: s) z x (t + 1) w
  | comp {b : Bool} {p₁ p₂ z y x : BitString} {t₂ t₁ w₂ w₁ : ℕ} :
      CompRunsW p₂ (bif b then [] else z) y t₂ w₂ →
      CompRunsW p₁ y x t₁ w₁ →
      CompRunsW (true :: b :: (gammaCode p₁.length ++ p₁ ++ p₂)) z x
        (t₂ + t₁ + (gammaCode p₁.length).length + 2) (w₂ + w₁)

/-- Inversion of an embed node of the write-ledgered relation. -/
theorem CompRunsW.embed_inv {s z x : BitString} {t w : ℕ}
    (h : CompRunsW (false :: s) z x t w) :
    ∃ t', FlaggedRunsW s z x t' w ∧ t = t' + 1 := by
  cases h with
  | embed hF => exact ⟨_, hF, rfl⟩

/-- Inversion of a composition node of the write-ledgered relation. -/
theorem CompRunsW.comp_inv {b : Bool} {r z x : BitString} {t w : ℕ}
    (h : CompRunsW (true :: b :: r) z x t w) :
    ∃ (p₁ p₂ y : BitString) (t₂ t₁ w₂ w₁ : ℕ),
      r = gammaCode p₁.length ++ p₁ ++ p₂ ∧
      CompRunsW p₂ (bif b then [] else z) y t₂ w₂ ∧
      CompRunsW p₁ y x t₁ w₁ ∧
      t = t₂ + t₁ + (gammaCode p₁.length).length + 2 ∧ w = w₂ + w₁ := by
  cases h with
  | comp h₂ h₁ => exact ⟨_, _, _, _, _, _, _, rfl, h₂, h₁, rfl, rfl⟩

/-- Forgetting the write ledger: every write-ledgered run is a clocked run. -/
theorem CompRunsW.toCompRuns {s z x : BitString} {t w : ℕ}
    (h : CompRunsW s z x t w) : CompRuns s z x t := by
  induction h with
  | embed hF =>
      exact CompRuns.embed ((flaggedRuns_iff_flaggedRunsW _ _ _ _).mpr ⟨_, hF⟩)
  | comp _ _ ih₂ ih₁ => exact CompRuns.comp ih₂ ih₁

/-- Every clocked run carries a write ledger. -/
theorem CompRuns.exists_compRunsW {s z x : BitString} {t : ℕ}
    (h : CompRuns s z x t) : ∃ w, CompRunsW s z x t w := by
  induction h with
  | embed hF =>
      obtain ⟨w, hw⟩ := (flaggedRuns_iff_flaggedRunsW _ _ _ _).mp hF
      exact ⟨w, CompRunsW.embed hw⟩
  | comp _ _ ih₂ ih₁ =>
      obtain ⟨w₂, h₂⟩ := ih₂
      obtain ⟨w₁, h₁⟩ := ih₁
      exact ⟨w₂ + w₁, CompRunsW.comp h₂ h₁⟩

/-- Forgetting the write ledger gives exactly the clocked composing relation. -/
theorem compRuns_iff_compRunsW (s z x : BitString) (t : ℕ) :
    CompRuns s z x t ↔ ∃ w, CompRunsW s z x t w :=
  ⟨CompRuns.exists_compRunsW, fun ⟨_, hw⟩ => hw.toCompRuns⟩

/-- Output, transition count, and write count are unique per tape and context. -/
theorem CompRunsW.unique {s z x₁ x₂ : BitString} {t₁ t₂ w₁ w₂ : ℕ}
    (h₁ : CompRunsW s z x₁ t₁ w₁) (h₂ : CompRunsW s z x₂ t₂ w₂) :
    x₁ = x₂ ∧ t₁ = t₂ ∧ w₁ = w₂ := by
  revert h₂
  induction h₁ generalizing x₂ t₂ w₂ with
  | embed hF =>
      intro h₂
      obtain ⟨t', hF', rfl⟩ := CompRunsW.embed_inv h₂
      obtain ⟨rfl, rfl, rfl⟩ := hF.unique hF'
      exact ⟨rfl, rfl, rfl⟩
  | comp hp₂ hp₁ ih₂ ih₁ =>
      intro h₂
      obtain ⟨q₁, q₂, y', t₂', t₁', w₂', w₁', hlist, hq₂, hq₁, rfl, rfl⟩ :=
        CompRunsW.comp_inv h₂
      rw [List.append_assoc, List.append_assoc] at hlist
      obtain ⟨hlen, happ⟩ := gammaCode_append_inj hlist
      obtain ⟨rfl, rfl⟩ := List.append_inj happ (by omega)
      obtain ⟨rfl, rfl, rfl⟩ := ih₂ hq₂
      obtain ⟨rfl, rfl, rfl⟩ := ih₁ hq₁
      exact ⟨rfl, rfl, rfl⟩

/-- Every write-ledgered composing run commits at least one write. -/
theorem CompRunsW.one_le_writes {s z x : BitString} {t w : ℕ}
    (h : CompRunsW s z x t w) : 1 ≤ w := by
  induction h with
  | embed hF => exact hF.one_le_writes
  | comp _ _ ih₂ ih₁ => omega

/-- Writes never exceed the transition count of the same composing run. -/
theorem CompRunsW.writes_le_time {s z x : BitString} {t w : ℕ}
    (h : CompRunsW s z x t w) : w ≤ t := by
  induction h with
  | embed hF =>
      have := hF.writes_le_time
      omega
  | comp _ _ ih₂ ih₁ => omega

/-! ### The write-priced complexity -/

/-- **Conditional write-priced complexity** over the composing universal machine:
`Wt_cond x y = min { |p| + ceilLog2 w }` over write-ledgered runs producing `x` from
context `y`. -/
noncomputable def Wt_cond (x y : BitString) : ENat :=
  sInf {n | ∃ p t w, CompRunsW p y x t w ∧
    ((programLength p + ceilLog2 w : ℕ) : ENat) = n}

/-- **Write-priced complexity**: `Wt x = Wt_cond x []`. -/
noncomputable def Wt (x : BitString) : ENat :=
  Wt_cond x []

/-- A write-ledgered run gives a witness upper bound on `Wt_cond`. -/
theorem Wt_cond_le_of_compRunsW {p y x : BitString} {t w : ℕ}
    (h : CompRunsW p y x t w) :
    Wt_cond x y ≤ ((programLength p + ceilLog2 w : ℕ) : ENat) :=
  sInf_le ⟨p, t, w, h, rfl⟩

/-- The library's conditional complexity bounds `Wt_cond` from below: dropping the
write ledger only shrinks the cost. -/
theorem K_cond_le_Wt_cond (x y : BitString) :
    condK compUniversal x y ≤ Wt_cond x y := by
  refine le_sInf ?_
  rintro n ⟨p, t, w, hrun, rfl⟩
  have hprod : produces compUniversal p y x :=
    (compRuns_iff_produces p y x).mpr ⟨t, hrun.toCompRuns⟩
  calc condK compUniversal x y
      ≤ ((programLength p : ℕ) : ENat) := sInf_le ⟨p, hprod, rfl⟩
    _ ≤ ((programLength p + ceilLog2 w : ℕ) : ENat) := by
        exact_mod_cast Nat.le_add_right _ _

/-- `Wt_cond` is finite exactly on the outputs the composing machine produces — the
write-ledger analogue of `Kt_cond_lt_top_iff`. -/
theorem Wt_cond_lt_top_iff {x y : BitString} :
    Wt_cond x y < ⊤ ↔ ∃ p, produces compUniversal p y x := by
  constructor
  · intro h
    obtain ⟨n, hn, -⟩ := sInf_lt_iff.mp h
    obtain ⟨p, t, w, hrun, rfl⟩ := hn
    exact ⟨p, (compRuns_iff_produces p y x).mpr ⟨t, hrun.toCompRuns⟩⟩
  · rintro ⟨p, hprod⟩
    obtain ⟨t, hC⟩ := (compRuns_iff_produces p y x).mp hprod
    obtain ⟨w, hw⟩ := hC.exists_compRunsW
    exact lt_of_le_of_lt (Wt_cond_le_of_compRunsW hw) (ENat.natCast_lt_top _)

/-- **Writes never exceed transitions.** Every timed witness is a write witness of the
same program with a smaller ledger, so `Wt_cond ≤ Kt_cond` with no overhead — both
prices are read off the same operational run, which is what a fuel clock (divergent
from the work performed) cannot offer. -/
theorem Wt_cond_le_Kt_cond (x y : BitString) : Wt_cond x y ≤ Kt_cond x y := by
  refine le_sInf ?_
  rintro n ⟨p, t, hrun, rfl⟩
  obtain ⟨w, hw⟩ := hrun.exists_compRunsW
  have hwt : w ≤ t := hw.writes_le_time
  refine le_trans (Wt_cond_le_of_compRunsW hw) ?_
  exact Nat.cast_le.mpr (Nat.add_le_add_left (ceilLog2_mono hwt) _)

/-- `Wt ≤ Kt` with no overhead. -/
theorem Wt_le_Kt (x : BitString) : Wt x ≤ Kt x :=
  Wt_cond_le_Kt_cond x []

/-- **The conditioning theorem for the write measure**: `Wt(x | y) ≤ Wt(x)` with
additive constant zero, by the same root bit flip as `Kt_cond_le_Kt` — the write
ledger is untouched by the flip. -/
theorem Wt_cond_le_Wt (x y : BitString) : Wt_cond x y ≤ Wt x := by
  refine le_sInf ?_
  rintro n ⟨s, t, w, hrun, rfl⟩
  cases hrun with
  | embed hFW =>
      obtain ⟨fb, q, t', heq, hU, rfl⟩ := hFW
      have hctx : (bif fb then [] else ([] : BitString)) = ([] : BitString) := by
        cases fb <;> rfl
      rw [hctx] at hU
      have hF' : FlaggedRunsW (true :: q) y x (t' + 1) w := ⟨true, q, t', rfl, hU, rfl⟩
      have hC : CompRunsW (false :: true :: q) y x (t' + 1 + 1) w :=
        CompRunsW.embed hF'
      refine le_trans (Wt_cond_le_of_compRunsW hC) ?_
      refine Nat.cast_le.mpr ?_
      subst heq
      simp [programLength]
  | comp hp₂ hp₁ =>
      have hctx : ∀ b : Bool, (bif b then [] else ([] : BitString)) = [] := by
        intro b; cases b <;> rfl
      rw [hctx] at hp₂
      have hC := CompRunsW.comp (b := true) (z := y) hp₂ hp₁
      refine le_trans (Wt_cond_le_of_compRunsW hC) ?_
      refine Nat.cast_le.mpr ?_
      simp [programLength]

/-- **Transitions are linear in writes.** Each flagged write witness bounds the
transition-priced `Kt_cond` within an additive penalty logarithmic in the witness's
description data, plus the two-unit embed cost of the composing layer. -/
theorem Kt_cond_le_of_flaggedRunsW {s y x : BitString} {t w : ℕ}
    (h : FlaggedRunsW s y x t w) :
    Kt_cond x y ≤ ((programLength s + ceilLog2 w +
      ceilLog2 (programLength s + 2 * progSize (parsedCode s.tail) + 4) + 2 : ℕ) :
        ENat) := by
  obtain ⟨b, p, t', rfl, hw, rfl⟩ := h
  have hF : FlaggedRuns (b :: p) y x (t' + 1) :=
    ⟨b, p, t', rfl, (universalRuns_iff_universalRunsW _ _ _ _).mpr ⟨w, hw⟩, rfl⟩
  have hC : CompRuns (false :: b :: p) y x (t' + 1 + 1) := CompRuns.embed hF
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
  have hlog2 : ceilLog2 (t' + 1 + 1) ≤ ceilLog2 (t' + 1) + 1 :=
    ceilLog2_succ_le (by omega)
  refine le_trans (Kt_cond_le_of_runs hC) ?_
  rw [show (b :: p).tail = p from rfl]
  refine Nat.cast_le.mpr ?_
  simp only [programLength, List.length_cons] at hlog ⊢
  omega

/-- **The length upper bound for `Wt`**: the projection code `Code.left` outputs its
program with a single write, so `Wt_cond x y ≤ |x| + c` for the explicit constant
`c = encode Code.left + 3`. -/
theorem Wt_cond_le_length (x y : BitString) :
    Wt_cond x y ≤ ((programLength x + (Encodable.encode Code.left + 3) : ℕ) : ENat) := by
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
  have hC : CompRunsW
      (false :: false :: (unaryPrefix (Encodable.encode Code.left) ++ x)) y x
      (Encodable.encode Code.left + 1 + 1 + 1 + 1 + 1) 1 :=
    CompRunsW.embed hFW
  refine le_trans (Wt_cond_le_of_compRunsW hC) ?_
  refine Nat.cast_le.mpr ?_
  have hlen : programLength
      (false :: false :: (unaryPrefix (Encodable.encode Code.left) ++ x))
      = Encodable.encode Code.left + 3 + programLength x := by
    simp [programLength, List.length_append, length_unaryPrefix]
    omega
  simp only [hlen, ceilLog2_one]
  omega

/-- The length upper bound for the plain `Wt`: `Wt_cond_le_length` at the empty
context. -/
theorem Wt_le_length (x : BitString) :
    Wt x ≤ ((programLength x + (Encodable.encode Code.left + 3) : ℕ) : ENat) :=
  Wt_cond_le_length x []

end TimedKt
