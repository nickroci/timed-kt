/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.WriteOnce

/-!
# The Bit Ledger, and Bit-Priced Complexity

The write-once tape carries two ledgers (`TimedKt.Trace`): `numWrites` counts commit
events, `traceBits` their information content — the total `Nat.size` of the committed
values. `TimedKt.WriteOnce` prices the universal machines by the first ledger; this
module prices them by the second. `UniversalRunsB`, `FlaggedRunsB`, and `CompRunsB`
extend the clocked relations by recording `b = (T.map Nat.size).sum` for each inner
run's write-once trace `T`, and the bit-priced complexity is

* `Bt_cond x y = min { |p| + ceilLog2 b : the composing machine runs p on context y,
  producing x with b committed bits }`, and `Bt x = Bt_cond x []`.

## Bit convention

As with the transition clock and the write count, the ledger of a run is that of the
simulated codes' write-once traces: the context flag, the unary-prefix scan, and the
result decode commit nothing, and on the composing layer the comp flag, the erase
bit, and the gamma scan commit nothing either. A composition node's ledger is the
sum of its stages' ledgers.

## Relation to `Wt` and `Kt`

No inequality between `Bt` and `Wt`, or between `Bt` and `Kt`, is claimed in either
direction. The per-run ledger comparison fails both ways: a single write may carry
arbitrarily many bits (`Nat.size` is unbounded), so the bit ledger dominates neither
the write count nor the transition count; and a written value `0` has `Nat.size 0 = 0`,
so the bit ledger is not dominated by them either. The pointwise route that proves
`Wt_cond_le_Kt_cond` is therefore closed here, and no measure-level comparison is
asserted; whether one holds at some witness-dependent overhead is open.

What is proved: the definitional layer (forgetting the ledger recovers the clocked
relations; `(x, t, b)` is unique per tape and context), the witness upper bound
(`Bt_cond_le_of_compRunsB`), the untimed lower bound (`K_cond_le_Bt_cond`),
finiteness exactly on producible outputs (`Bt_cond_lt_top_iff`), and the conditioning
theorem with additive constant zero (`Bt_cond_le_Bt`), by the same root bit flip as
`Kt_cond_le_Kt` and `Wt_cond_le_Wt`.
-/

open Nat.Partrec Kolmogorov

namespace TimedKt

/-- The clocked unflagged machine with its **bit ledger**: `UniversalRunsB s y x t b`
extends `UniversalRuns s y x t` by recording that the simulated code commits exactly
`b` bits — the total `Nat.size` of its write-once trace. -/
def UniversalRunsB (s y x : BitString) (t b : ℕ) : Prop :=
  ∃ (code : Code) (T : List ℕ) (steps r : ℕ),
    (Encodable.decode ((s.takeWhile id).length) : Option Code) = some code ∧
    Run code (Encodable.encode (s.drop ((s.takeWhile id).length + 1), y)) T steps ∧
    T.getLast? = some r ∧
    x = (Encodable.decode r : Option BitString).getD [] ∧
    t = (s.takeWhile id).length + 1 + steps + 1 ∧
    b = (T.map Nat.size).sum

/-- Forgetting the bit ledger gives exactly the clocked relation. -/
theorem universalRuns_iff_universalRunsB (s y x : BitString) (t : ℕ) :
    UniversalRuns s y x t ↔ ∃ b, UniversalRunsB s y x t b := by
  constructor
  · rintro ⟨code, T, steps, r, hdec, hrun, hlast, hx, ht⟩
    exact ⟨(T.map Nat.size).sum, code, T, steps, r, hdec, hrun, hlast, hx, ht, rfl⟩
  · rintro ⟨b, code, T, steps, r, hdec, hrun, hlast, hx, ht, -⟩
    exact ⟨code, T, steps, r, hdec, hrun, hlast, hx, ht⟩

/-- Output, transition count, and bit count are unique per tape and context. -/
theorem UniversalRunsB.unique {s y x₁ x₂ : BitString} {t₁ t₂ b₁ b₂ : ℕ}
    (h₁ : UniversalRunsB s y x₁ t₁ b₁) (h₂ : UniversalRunsB s y x₂ t₂ b₂) :
    x₁ = x₂ ∧ t₁ = t₂ ∧ b₁ = b₂ := by
  obtain ⟨c₁, T₁, s₁, r₁, hdec₁, hrun₁, hlast₁, hx₁, ht₁, hb₁⟩ := h₁
  obtain ⟨c₂, T₂, s₂, r₂, hdec₂, hrun₂, hlast₂, hx₂, ht₂, hb₂⟩ := h₂
  rw [hdec₁] at hdec₂
  obtain rfl : c₁ = c₂ := Option.some.inj hdec₂
  obtain ⟨rfl, rfl⟩ := hrun₁.deterministic hrun₂
  rw [hlast₁] at hlast₂
  obtain rfl : r₁ = r₂ := Option.some.inj hlast₂
  exact ⟨hx₁.trans hx₂.symm, ht₁.trans ht₂.symm, hb₁.trans hb₂.symm⟩

/-! ### The bit ledger of the flagged machine -/

/-- The clocked flagged machine with its bit ledger: the context flag commits nothing,
so the bits are those of the inner run. -/
def FlaggedRunsB (s y x : BitString) (t b : ℕ) : Prop :=
  ∃ fl p t', s = fl :: p ∧ UniversalRunsB p (bif fl then [] else y) x t' b ∧ t = t' + 1

/-- Forgetting the bit ledger gives exactly the flagged clocked relation. -/
theorem flaggedRuns_iff_flaggedRunsB (s y x : BitString) (t : ℕ) :
    FlaggedRuns s y x t ↔ ∃ b, FlaggedRunsB s y x t b := by
  constructor
  · rintro ⟨fl, p, t', rfl, hrun, rfl⟩
    obtain ⟨b, hb⟩ := (universalRuns_iff_universalRunsB _ _ _ _).mp hrun
    exact ⟨b, fl, p, t', rfl, hb, rfl⟩
  · rintro ⟨b, fl, p, t', rfl, hb, rfl⟩
    exact ⟨fl, p, t', rfl, (universalRuns_iff_universalRunsB _ _ _ _).mpr ⟨b, hb⟩, rfl⟩

/-- Output, transition count, and bit count are unique per tape and context. -/
theorem FlaggedRunsB.unique {s y x₁ x₂ : BitString} {t₁ t₂ b₁ b₂ : ℕ}
    (h₁ : FlaggedRunsB s y x₁ t₁ b₁) (h₂ : FlaggedRunsB s y x₂ t₂ b₂) :
    x₁ = x₂ ∧ t₁ = t₂ ∧ b₁ = b₂ := by
  obtain ⟨f₁, p₁, t₁', heq₁, hb₁, rfl⟩ := h₁
  obtain ⟨f₂, p₂, t₂', heq₂, hb₂, rfl⟩ := h₂
  rw [heq₁] at heq₂
  obtain ⟨rfl, rfl⟩ : f₁ = f₂ ∧ p₁ = p₂ := by
    injection heq₂ with h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨rfl, rfl, rfl⟩ := hb₁.unique hb₂
  exact ⟨rfl, rfl, rfl⟩

/-! ### The bit ledger of the composing machine -/

/-- The clocked composing machine with its **bit ledger**: the comp flag, the erase
bit, and the gamma scan commit nothing, an embed node carries the flagged ledger,
and a composition node's ledger is the sum of its stages' ledgers. -/
inductive CompRunsB : BitString → BitString → BitString → ℕ → ℕ → Prop
  | embed {s z x : BitString} {t b : ℕ} :
      FlaggedRunsB s z x t b → CompRunsB (false :: s) z x (t + 1) b
  | comp {fl : Bool} {p₁ p₂ z y x : BitString} {t₂ t₁ b₂ b₁ : ℕ} :
      CompRunsB p₂ (bif fl then [] else z) y t₂ b₂ →
      CompRunsB p₁ y x t₁ b₁ →
      CompRunsB (true :: fl :: (gammaCode p₁.length ++ p₁ ++ p₂)) z x
        (t₂ + t₁ + (gammaCode p₁.length).length + 2) (b₂ + b₁)

/-- Inversion of an embed node of the bit-ledgered relation. -/
theorem CompRunsB.embed_inv {s z x : BitString} {t b : ℕ}
    (h : CompRunsB (false :: s) z x t b) :
    ∃ t', FlaggedRunsB s z x t' b ∧ t = t' + 1 := by
  cases h with
  | embed hF => exact ⟨_, hF, rfl⟩

/-- Inversion of a composition node of the bit-ledgered relation. -/
theorem CompRunsB.comp_inv {fl : Bool} {r z x : BitString} {t b : ℕ}
    (h : CompRunsB (true :: fl :: r) z x t b) :
    ∃ (p₁ p₂ y : BitString) (t₂ t₁ b₂ b₁ : ℕ),
      r = gammaCode p₁.length ++ p₁ ++ p₂ ∧
      CompRunsB p₂ (bif fl then [] else z) y t₂ b₂ ∧
      CompRunsB p₁ y x t₁ b₁ ∧
      t = t₂ + t₁ + (gammaCode p₁.length).length + 2 ∧ b = b₂ + b₁ := by
  cases h with
  | comp h₂ h₁ => exact ⟨_, _, _, _, _, _, _, rfl, h₂, h₁, rfl, rfl⟩

/-- Forgetting the bit ledger: every bit-ledgered run is a clocked run. -/
theorem CompRunsB.toCompRuns {s z x : BitString} {t b : ℕ}
    (h : CompRunsB s z x t b) : CompRuns s z x t := by
  induction h with
  | embed hF =>
      exact CompRuns.embed ((flaggedRuns_iff_flaggedRunsB _ _ _ _).mpr ⟨_, hF⟩)
  | comp _ _ ih₂ ih₁ => exact CompRuns.comp ih₂ ih₁

/-- Every clocked run carries a bit ledger. -/
theorem CompRuns.exists_compRunsB {s z x : BitString} {t : ℕ}
    (h : CompRuns s z x t) : ∃ b, CompRunsB s z x t b := by
  induction h with
  | embed hF =>
      obtain ⟨b, hb⟩ := (flaggedRuns_iff_flaggedRunsB _ _ _ _).mp hF
      exact ⟨b, CompRunsB.embed hb⟩
  | comp _ _ ih₂ ih₁ =>
      obtain ⟨b₂, h₂⟩ := ih₂
      obtain ⟨b₁, h₁⟩ := ih₁
      exact ⟨b₂ + b₁, CompRunsB.comp h₂ h₁⟩

/-- Forgetting the bit ledger gives exactly the clocked composing relation. -/
theorem compRuns_iff_compRunsB (s z x : BitString) (t : ℕ) :
    CompRuns s z x t ↔ ∃ b, CompRunsB s z x t b :=
  ⟨CompRuns.exists_compRunsB, fun ⟨_, hb⟩ => hb.toCompRuns⟩

/-- Output, transition count, and bit count are unique per tape and context. -/
theorem CompRunsB.unique {s z x₁ x₂ : BitString} {t₁ t₂ b₁ b₂ : ℕ}
    (h₁ : CompRunsB s z x₁ t₁ b₁) (h₂ : CompRunsB s z x₂ t₂ b₂) :
    x₁ = x₂ ∧ t₁ = t₂ ∧ b₁ = b₂ := by
  revert h₂
  induction h₁ generalizing x₂ t₂ b₂ with
  | embed hF =>
      intro h₂
      obtain ⟨t', hF', rfl⟩ := CompRunsB.embed_inv h₂
      obtain ⟨rfl, rfl, rfl⟩ := hF.unique hF'
      exact ⟨rfl, rfl, rfl⟩
  | comp hp₂ hp₁ ih₂ ih₁ =>
      intro h₂
      obtain ⟨q₁, q₂, y', t₂', t₁', b₂', b₁', hlist, hq₂, hq₁, rfl, rfl⟩ :=
        CompRunsB.comp_inv h₂
      rw [List.append_assoc, List.append_assoc] at hlist
      obtain ⟨hlen, happ⟩ := gammaCode_append_inj hlist
      obtain ⟨rfl, rfl⟩ := List.append_inj happ (by omega)
      obtain ⟨rfl, rfl, rfl⟩ := ih₂ hq₂
      obtain ⟨rfl, rfl, rfl⟩ := ih₁ hq₁
      exact ⟨rfl, rfl, rfl⟩

/-! ### The bit-priced complexity -/

/-- **Conditional bit-priced complexity** over the composing universal machine:
`Bt_cond x y = min { |p| + ceilLog2 b }` over bit-ledgered runs producing `x` from
context `y`. -/
noncomputable def Bt_cond (x y : BitString) : ENat :=
  sInf {n | ∃ p t b, CompRunsB p y x t b ∧
    ((programLength p + ceilLog2 b : ℕ) : ENat) = n}

/-- **Bit-priced complexity**: `Bt x = Bt_cond x []`. -/
noncomputable def Bt (x : BitString) : ENat :=
  Bt_cond x []

/-- A bit-ledgered run gives a witness upper bound on `Bt_cond`. -/
theorem Bt_cond_le_of_compRunsB {p y x : BitString} {t b : ℕ}
    (h : CompRunsB p y x t b) :
    Bt_cond x y ≤ ((programLength p + ceilLog2 b : ℕ) : ENat) :=
  sInf_le ⟨p, t, b, h, rfl⟩

/-- The library's conditional complexity bounds `Bt_cond` from below: dropping the bit
ledger only shrinks the cost. -/
theorem K_cond_le_Bt_cond (x y : BitString) :
    condK compUniversal x y ≤ Bt_cond x y := by
  refine le_sInf ?_
  rintro n ⟨p, t, b, hrun, rfl⟩
  have hprod : produces compUniversal p y x :=
    (compRuns_iff_produces p y x).mpr ⟨t, hrun.toCompRuns⟩
  calc condK compUniversal x y
      ≤ ((programLength p : ℕ) : ENat) := sInf_le ⟨p, hprod, rfl⟩
    _ ≤ ((programLength p + ceilLog2 b : ℕ) : ENat) := by
        exact_mod_cast Nat.le_add_right _ _

/-- `Bt_cond` is finite exactly on the outputs the composing machine produces. -/
theorem Bt_cond_lt_top_iff {x y : BitString} :
    Bt_cond x y < ⊤ ↔ ∃ p, produces compUniversal p y x := by
  constructor
  · intro h
    obtain ⟨n, hn, -⟩ := sInf_lt_iff.mp h
    obtain ⟨p, t, b, hrun, rfl⟩ := hn
    exact ⟨p, (compRuns_iff_produces p y x).mpr ⟨t, hrun.toCompRuns⟩⟩
  · rintro ⟨p, hprod⟩
    obtain ⟨t, hC⟩ := (compRuns_iff_produces p y x).mp hprod
    obtain ⟨b, hb⟩ := hC.exists_compRunsB
    exact lt_of_le_of_lt (Bt_cond_le_of_compRunsB hb) (ENat.natCast_lt_top _)

/-- **The conditioning theorem for the bit measure**: `Bt(x | y) ≤ Bt(x)` with additive
constant zero, by the same root bit flip as `Kt_cond_le_Kt` and `Wt_cond_le_Wt`. -/
theorem Bt_cond_le_Bt (x y : BitString) : Bt_cond x y ≤ Bt x := by
  refine le_sInf ?_
  rintro n ⟨s, t, b, hrun, rfl⟩
  cases hrun with
  | embed hFB =>
      obtain ⟨fl, q, t', heq, hU, rfl⟩ := hFB
      have hctx : (bif fl then [] else ([] : BitString)) = ([] : BitString) := by
        cases fl <;> rfl
      rw [hctx] at hU
      have hF' : FlaggedRunsB (true :: q) y x (t' + 1) b := ⟨true, q, t', rfl, hU, rfl⟩
      have hC : CompRunsB (false :: true :: q) y x (t' + 1 + 1) b :=
        CompRunsB.embed hF'
      refine le_trans (Bt_cond_le_of_compRunsB hC) ?_
      refine Nat.cast_le.mpr ?_
      subst heq
      simp [programLength]
  | comp hp₂ hp₁ =>
      have hctx : ∀ fl : Bool, (bif fl then [] else ([] : BitString)) = [] := by
        intro fl; cases fl <;> rfl
      rw [hctx] at hp₂
      have hC := CompRunsB.comp (fl := true) (z := y) hp₂ hp₁
      refine le_trans (Bt_cond_le_of_compRunsB hC) ?_
      refine Nat.cast_le.mpr ?_
      simp [programLength]

end TimedKt
