/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.CompPartrec

/-!
# The Timed Composing Universal Machine

This module equips the composing universal machine (`TimedKt.Comp`) with its
transition count, producing `timedCompUniversal` — the machine of the public `Kt`
after the swap in `TimedKt.Kt`.

## Cost convention

On top of the flagged machine's clock (`TimedKt.Flagged`, `TimedKt.UniversalRun`):

* the comp flag costs `1` transition, so an embed node costs `t + 1` for an inner
  flagged run of `t`;
* a composition node costs its erase bit (`1`), the scan of the gamma length code
  (`1` per bit, `(gammaCode ℓ).length` in total), the split of the tape into the
  two blocks (atomic — the same license as the machine's free pair-encode), and
  the two recursive stages at their own clocks:
  `t = t₂ + t₁ + (gammaCode ℓ).length + 2`.

The write and bit ledgers of `TimedKt.WriteOnce` and `TimedKt.BitCost` follow the
matching convention: flags and the gamma scan commit nothing, and a composition
node's ledger is the sum of its stages' ledgers.

## Main results

* `compRuns_iff_produces` — soundness and completeness of the clocked relation for
  `compUniversal` (strong induction on the tape length; the leaf case is
  `flaggedRuns_iff_produces`).
* `CompRuns.unique` — output and transition count are unique per tape and context
  (unique decodability of the gamma split, `gammaCode_append_inj`).
* `timedCompUniversal` — the timed machine.
* `condKt_comp_le_condKt_flagged` — embedding costs one bit and one transition, so
  the composing machine is at most `2` worse than the flagged machine.
* `condKt_comp_cond_le_plain` — **conditioning is free** on the composing machine:
  a plain witness becomes a conditional witness of the same length and transition
  count by flipping the single erase bit at its root (the flagged flag for an embed
  node, the comp erase bit for a composition node) — no induction over the tape.
-/

open Kolmogorov

namespace TimedKt

/-- The **clocked composing machine**. An embed node charges one transition for the
comp flag on top of the flagged machine's clock; a composition node charges the
erase bit, one transition per gamma-code bit, and the two recursive stages:
`t = t₂ + t₁ + (gammaCode ℓ).length + 2`. The split itself is atomic. -/
inductive CompRuns : BitString → BitString → BitString → ℕ → Prop
  | embed {s z x : BitString} {t : ℕ} :
      FlaggedRuns s z x t → CompRuns (false :: s) z x (t + 1)
  | comp {b : Bool} {p₁ p₂ z y x : BitString} {t₂ t₁ : ℕ} :
      CompRuns p₂ (bif b then [] else z) y t₂ →
      CompRuns p₁ y x t₁ →
      CompRuns (true :: b :: (gammaCode p₁.length ++ p₁ ++ p₂)) z x
        (t₂ + t₁ + (gammaCode p₁.length).length + 2)

/-- Inversion of an embed node. -/
theorem CompRuns.embed_inv {s z x : BitString} {t : ℕ}
    (h : CompRuns (false :: s) z x t) :
    ∃ t', FlaggedRuns s z x t' ∧ t = t' + 1 := by
  cases h with
  | embed hF => exact ⟨_, hF, rfl⟩

/-- Inversion of a composition node: the tape decomposes as a gamma-delimited
split, with both stages clocked. -/
theorem CompRuns.comp_inv {b : Bool} {r z x : BitString} {t : ℕ}
    (h : CompRuns (true :: b :: r) z x t) :
    ∃ (p₁ p₂ y : BitString) (t₂ t₁ : ℕ),
      r = gammaCode p₁.length ++ p₁ ++ p₂ ∧
      CompRuns p₂ (bif b then [] else z) y t₂ ∧
      CompRuns p₁ y x t₁ ∧
      t = t₂ + t₁ + (gammaCode p₁.length).length + 2 := by
  cases h with
  | comp h₂ h₁ => exact ⟨_, _, _, _, _, rfl, h₂, h₁, rfl⟩

/-- A clocked run realizes the untimed semantics: structural induction on the
derivation, with the composition equation of `compUniversal` at each comp node. -/
theorem CompRuns.produces {s z x : BitString} {t : ℕ} (h : CompRuns s z x t) :
    produces compUniversal s z x := by
  induction h with
  | embed hF =>
      rw [Kolmogorov.produces, compUniversal_embed]
      exact (flaggedRuns_iff_produces _ _ _).mpr ⟨_, hF⟩
  | comp h₂ h₁ ih₂ ih₁ =>
      rw [Kolmogorov.produces, List.append_assoc,
        compUniversal_comp_of_parse (gammaParse_gammaCode_append _ _),
        List.drop_left, List.take_left]
      exact Part.mem_bind_iff.mpr ⟨_, ih₂, ih₁⟩

/-- A produced output has a clocked run: strong induction on the tape length, with
the leaf case delegated to the flagged machine and the comp case splitting the
parsed tape. -/
theorem exists_compRuns_of_produces :
    ∀ (n : ℕ) (s z x : BitString), s.length ≤ n → produces compUniversal s z x →
      ∃ t, CompRuns s z x t := by
  intro n
  induction n with
  | zero =>
      intro s z x hn hp
      obtain rfl : s = [] := List.length_eq_zero_iff.mp (by omega)
      rw [Kolmogorov.produces, compUniversal_nil] at hp
      exact absurd hp (Part.notMem_none _)
  | succ n ih =>
      intro s z x hn hp
      rcases s with - | ⟨hd, tl⟩
      · rw [Kolmogorov.produces, compUniversal_nil] at hp
        exact absurd hp (Part.notMem_none _)
      rcases hd
      · rw [Kolmogorov.produces, compUniversal_embed] at hp
        obtain ⟨t, hF⟩ := (flaggedRuns_iff_produces _ _ _).mp hp
        exact ⟨t + 1, CompRuns.embed hF⟩
      rcases tl with - | ⟨b, r⟩
      · rw [Kolmogorov.produces, compUniversal_flag_nil] at hp
        exact absurd hp (Part.notMem_none _)
      simp only [List.length_cons] at hn
      cases hpr : gammaParse r with
      | none =>
          rw [Kolmogorov.produces, compUniversal_comp_of_parse_none hpr] at hp
          exact absurd hp (Part.notMem_none _)
      | some lr =>
          obtain ⟨ℓ, rest⟩ := lr
          rw [Kolmogorov.produces, compUniversal_comp_of_parse hpr] at hp
          obtain ⟨y, hy, hx⟩ := Part.mem_bind_iff.mp hp
          by_cases hℓ : ℓ ≤ rest.length
          · have hrest : rest.length < r.length := length_rest_lt_of_gammaParse hpr
            obtain ⟨t₂, h₂⟩ := ih (rest.drop ℓ) (bif b then [] else z) y
              (by rw [List.length_drop]; omega) hy
            obtain ⟨t₁, h₁⟩ := ih (rest.take ℓ) y x
              (by rw [List.length_take]; omega) hx
            have htk : (rest.take ℓ).length = ℓ := by
              rw [List.length_take]; omega
            have htape : true :: b :: r =
                true :: b :: (gammaCode (rest.take ℓ).length ++ rest.take ℓ ++
                  rest.drop ℓ) := by
              rw [eq_gammaCode_append_of_gammaParse hpr, htk, List.append_assoc,
                List.take_append_drop]
            rw [htape]
            exact ⟨t₂ + t₁ + (gammaCode (rest.take ℓ).length).length + 2,
              CompRuns.comp h₂ h₁⟩
          · have hnil : rest.drop ℓ = [] := by
              rw [List.drop_eq_nil_iff]
              omega
            rw [hnil, compUniversal_nil] at hy
            exact absurd hy (Part.notMem_none _)

/-- Soundness and completeness of the clocked composing relation. -/
theorem compRuns_iff_produces (s z x : BitString) :
    produces compUniversal s z x ↔ ∃ t, CompRuns s z x t :=
  ⟨fun hp => exists_compRuns_of_produces s.length s z x le_rfl hp,
    fun ⟨_, h⟩ => h.produces⟩

/-- **Output and transition count are unique** per tape and context. The comp case
is the unique decodability of the gamma split (`gammaCode_append_inj`). -/
theorem CompRuns.unique {s z x₁ x₂ : BitString} {t₁ t₂ : ℕ}
    (h₁ : CompRuns s z x₁ t₁) (h₂ : CompRuns s z x₂ t₂) : x₁ = x₂ ∧ t₁ = t₂ := by
  revert h₂
  induction h₁ generalizing x₂ t₂ with
  | embed hF =>
      intro h₂
      obtain ⟨t', hF', rfl⟩ := CompRuns.embed_inv h₂
      obtain ⟨rfl, rfl⟩ := hF.unique hF'
      exact ⟨rfl, rfl⟩
  | comp hp₂ hp₁ ih₂ ih₁ =>
      intro h₂
      obtain ⟨q₁, q₂, y', t₂', t₁', hlist, hq₂, hq₁, rfl⟩ := CompRuns.comp_inv h₂
      rw [List.append_assoc, List.append_assoc] at hlist
      obtain ⟨hlen, happ⟩ := gammaCode_append_inj hlist
      obtain ⟨rfl, rfl⟩ := List.append_inj happ (by omega)
      obtain ⟨rfl, rfl⟩ := ih₂ hq₂
      obtain ⟨rfl, rfl⟩ := ih₁ hq₁
      exact ⟨rfl, rfl⟩

/-- The **timed composing universal machine** — the machine of the public `Kt`
after the swap in `TimedKt.Kt`. -/
def timedCompUniversal : TimedDecompressor where
  toMap := compUniversal
  Runs := CompRuns
  partrec := isDecompressor_compUniversal
  runs_iff_produces := compRuns_iff_produces
  one_le_time := by
    rintro p y x t h
    cases h <;> omega

/-! ### Transfer from the flagged machine -/

/-- Embedding costs one bit and one transition: the composing machine is at most
`2` worse than the flagged machine. -/
theorem condKt_comp_le_condKt_flagged (x y : BitString) :
    timedCompUniversal.condKt x y ≤ timedFlaggedUniversal.condKt x y + 2 := by
  refine sInfLeSInfAdd ?_
  rintro n ⟨p, t, hrun, rfl⟩
  have ht1 : 1 ≤ t := timedFlaggedUniversal.one_le_time p y x t hrun
  have hC : CompRuns (false :: p) y x (t + 1) := CompRuns.embed hrun
  refine ⟨((programLength (false :: p) + ceilLog2 (t + 1) : ℕ) : ENat),
    ⟨false :: p, t + 1, hC, rfl⟩, ?_⟩
  rw [← Nat.cast_add]
  refine Nat.cast_le.mpr ?_
  have hlog := ceilLog2_succ_le ht1
  simp only [programLength, List.length_cons]
  omega

/-- **Conditioning is free on the composing machine.** A plain witness becomes a
conditional witness of the same length and transition count by flipping the single
erase bit at its root: the flagged machine's context flag for an embed node, the
comp node's own erase bit for a composition node. No induction over the tape is
needed — which is exactly what the comp node's erase bit is for. -/
theorem condKt_comp_cond_le_plain (x y : BitString) :
    timedCompUniversal.condKt x y ≤ timedCompUniversal.plainKt x := by
  refine le_sInf ?_
  rintro n ⟨s, t, hrun, rfl⟩
  cases hrun with
  | embed hF =>
      obtain ⟨fb, q, t', heq, hU, rfl⟩ := hF
      have hctx : (bif fb then [] else ([] : BitString)) = ([] : BitString) := by
        cases fb <;> rfl
      rw [hctx] at hU
      have hF' : FlaggedRuns (true :: q) y x (t' + 1) := ⟨true, q, t', rfl, hU, rfl⟩
      have hC : CompRuns (false :: true :: q) y x (t' + 1 + 1) := CompRuns.embed hF'
      refine le_trans
        (TimedDecompressor.condKt_le_of_runs (D := timedCompUniversal) hC) ?_
      refine Nat.cast_le.mpr ?_
      subst heq
      simp [programLength]
  | comp hp₂ hp₁ =>
      have hctx : ∀ b : Bool, (bif b then [] else ([] : BitString)) = [] := by
        intro b; cases b <;> rfl
      rw [hctx] at hp₂
      have hC := CompRuns.comp (b := true) (z := y) hp₂ hp₁
      refine le_trans
        (TimedDecompressor.condKt_le_of_runs (D := timedCompUniversal) hC) ?_
      refine Nat.cast_le.mpr ?_
      simp [programLength]

end TimedKt
