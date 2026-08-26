/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Computability.PartrecCode
import Mathlib.Data.ENat.Basic

/-!
# The Write-Once Trace Evaluator

This module ports the fuel-free layer of `Irreducibility.V2.Trace` from the parent
project. `tracen k c n` runs the code `c` on input `n` with fuel `k`, mirroring
Mathlib's `Code.evaln` clause for clause, but returns the append-only list of every
value materialized during the computation, in evaluation order, with the output as the
last element.

The fuel parameter is scaffolding, not a cost: `tracen_mono` shows a successful trace
is identical at every larger fuel, `tracen_unique` that it is independent of the fuel
entirely, and `canonTrace` packages the resulting fuel-free canonical trace. `numWrites`
counts its entries. The agreement lemmas (`evaln_eq_tracen_bind` and consequences)
identify the trace's last element with the `Code.evaln` output, which is how the
operational semantics of `TimedKt.Run` is connected to `Code.eval`.

This file deliberately contains no cost measure priced by fuel; the legacy fuel-priced
quantities live in `TimedKt.FuelCost`.
-/

open Nat.Partrec

namespace TimedKt

/-- The **write-once trace**: the append-only list of every value committed while
running `c` on `n` within fuel `k`, in evaluation order, output last. Mirrors
`Code.evaln`; in particular it is `none` when fuel is exhausted or the input exceeds
the `evaln` reading floor (`guard (n ≤ k)`). -/
def tracen : ℕ → Code → ℕ → Option (List ℕ)
  | 0, _ => fun _ => Option.none
  | k + 1, Code.zero => fun n => do
      guard (n ≤ k)
      pure [0]
  | k + 1, Code.succ => fun n => do
      guard (n ≤ k)
      pure [Nat.succ n]
  | k + 1, Code.left => fun n => do
      guard (n ≤ k)
      pure [n.unpair.1]
  | k + 1, Code.right => fun n => do
      guard (n ≤ k)
      pure [n.unpair.2]
  | k + 1, Code.pair cf cg => fun n => do
      guard (n ≤ k)
      let tf ← tracen (k + 1) cf n
      let tg ← tracen (k + 1) cg n
      let vf ← tf.getLast?
      let vg ← tg.getLast?
      pure (tf ++ tg ++ [Nat.pair vf vg])
  | k + 1, Code.comp cf cg => fun n => do
      guard (n ≤ k)
      let tg ← tracen (k + 1) cg n
      let vg ← tg.getLast?
      let tf ← tracen (k + 1) cf vg
      pure (tg ++ tf)
  | k + 1, Code.prec cf cg => fun n => do
      guard (n ≤ k)
      n.unpaired fun a m =>
        m.casesOn (tracen (k + 1) cf a) fun y => do
          let ti ← tracen k (Code.prec cf cg) (Nat.pair a y)
          let vi ← ti.getLast?
          let tg ← tracen (k + 1) cg (Nat.pair a (Nat.pair y vi))
          pure (ti ++ tg)
  | k + 1, Code.rfind' cf => fun n => do
      guard (n ≤ k)
      n.unpaired fun a m => do
        let tx ← tracen (k + 1) cf (Nat.pair a m)
        let x ← tx.getLast?
        if x = 0 then
          pure (tx ++ [m])
        else
          let tr ← tracen k (Code.rfind' cf) (Nat.pair a (m + 1))
          pure (tx ++ tr)

/-! ### Basic reductions -/

/-- No fuel, no trace. -/
@[simp] theorem tracen_zero (c : Code) (n : ℕ) : tracen 0 c n = Option.none := by
  simp only [tracen]

/-- The leaf `Code.zero` commits exactly `[0]` (within the reading floor). -/
theorem tracen_zero_code (k n : ℕ) :
    tracen (k + 1) Code.zero n = if n ≤ k then some [0] else Option.none := by
  simp only [tracen]
  by_cases h : n ≤ k <;> simp [h]

/-- The leaf `Code.succ` commits exactly `[n + 1]`. -/
theorem tracen_succ_code (k n : ℕ) :
    tracen (k + 1) Code.succ n = if n ≤ k then some [Nat.succ n] else Option.none := by
  simp only [tracen]
  by_cases h : n ≤ k <;> simp [h]

/-! ### Agreement between `tracen` and `Code.evaln` -/

/-- Every produced trace is nonempty: each clause appends at least one element. -/
theorem tracen_ne_nil : ∀ {k c n L}, tracen k c n = some L → L ≠ [] := by
  suffices h : ∀ (k : ℕ) (c : Code), ∀ {n L}, tracen k c n = some L → L ≠ [] by
    intro k c n L; exact h k c
  intro k c
  induction k, c using tracen.induct with
  | case1 c => intro n L h; simp only [tracen, reduceCtorEq] at h
  | case2 k | case3 k | case4 k | case5 k =>
      intro n L h; rw [tracen] at h
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, hL⟩ := h
      rw [Option.pure_def, Option.some.injEq] at hL
      subst hL; simp
  | case6 k cf cg ihf ihg =>
      intro n L h; rw [tracen] at h
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, tf, _, tg, _, vf, _, vg, _, hL⟩ := h
      rw [Option.pure_def, Option.some.injEq] at hL
      subst hL; simp
  | case7 k cf cg ihg ihf =>
      intro n L h; rw [tracen] at h
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, tg, _, vg, _, tf, htf, hL⟩ := h
      rw [Option.pure_def, Option.some.injEq] at hL
      subst hL
      exact List.append_ne_nil_of_right_ne_nil _ (ihf htf)
  | case8 k cf cg ihf ihprec ihg =>
      intro n L h; rw [tracen] at h
      simp only [Nat.unpaired, bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, h⟩ := h
      cases hm : n.unpair.2 with
      | zero =>
          rw [hm] at h; simp only [Nat.rec_zero] at h
          exact ihf h
      | succ m =>
          rw [hm] at h; simp only [Option.bind_eq_some_iff] at h
          obtain ⟨ti, hti, _, _, _, _, hL⟩ := h
          rw [Option.pure_def, Option.some.injEq] at hL
          subst hL
          exact List.append_ne_nil_of_left_ne_nil (ihprec hti) _
  | case9 k cf ihf ihrf =>
      intro n L h; rw [tracen] at h
      simp only [Nat.unpaired, bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, tx, htx, x, hx, h⟩ := h
      by_cases hx0 : x = 0
      · rw [if_pos hx0, Option.pure_def, Option.some.injEq] at h
        subst h; simp
      · rw [if_neg hx0, Option.bind_eq_some_iff] at h
        obtain ⟨tr, _, hL⟩ := h
        rw [Option.pure_def, Option.some.injEq] at hL
        subst hL
        exact List.append_ne_nil_of_left_ne_nil (ihf htx) _

/-- **Trace–reference agreement**: `evaln` produces exactly when `tracen` does, and the
output is the trace's final element. -/
theorem evaln_eq_tracen_bind (k : ℕ) (c : Code) (n : ℕ) :
    Code.evaln k c n = (tracen k c n).bind List.getLast? := by
  induction k, c using tracen.induct generalizing n with
  | case1 c => simp [Code.evaln]
  | case2 k | case3 k | case4 k | case5 k =>
      rw [tracen, Code.evaln]
      by_cases h : n ≤ k <;> simp [h]
  | case6 k cf cg ihf ihg =>
      rw [tracen, Code.evaln]
      by_cases h : n ≤ k
      · simp only [h, guard_true, pure_bind, Seq.seq]
        rw [ihf, ihg]
        rcases tracen (k + 1) cf n with _ | tf
        · simp
        rcases tracen (k + 1) cg n with _ | tg
        · simp
        simp only [Option.bind_some]
        rcases hvf : tf.getLast? with _ | vf <;> rcases hvg : tg.getLast? with _ | vg <;>
          simp [hvf, hvg]
      · simp [h]
  | case7 k cf cg ihg ihf =>
      rw [tracen, Code.evaln]
      by_cases h : n ≤ k
      · simp only [h, guard_true, bind, ihg]
        rcases htg : tracen (k + 1) cg n with _ | tg
        · simp
        simp only [Option.bind_some]
        rcases hvg : tg.getLast? with _ | vg
        · simp
        simp only [Option.bind_some, ihf, pure]
        rcases htf : tracen (k + 1) cf vg with _ | tf
        · simp
        simp [List.getLast?_append_of_ne_nil _ (tracen_ne_nil htf)]
      · simp [h]
  | case8 k cf cg ihf ihprec ihg =>
      rw [tracen, Code.evaln]
      by_cases h : n ≤ k
      · simp only [h, guard_true, Nat.unpaired, bind]
        cases hm : n.unpair.2 with
        | zero =>
            simp only [Nat.rec_zero, ihf]
            simp [pure]
        | succ m =>
            simp only [ihprec]
            rcases hti : tracen k (cf.prec cg) (Nat.pair n.unpair.1 m) with _ | ti
            · simp
            simp only [Option.bind_some]
            rcases hvi : ti.getLast? with _ | vi
            · simp
            simp only [Option.bind_some, ihg]
            rcases htg : tracen (k + 1) cg (Nat.pair n.unpair.1 (Nat.pair m vi)) with _ | tg
            · simp
            simp [List.getLast?_append_of_ne_nil _ (tracen_ne_nil htg)]
      · simp [h]
  | case9 k cf ihf ihrf =>
      rw [tracen, Code.evaln]
      by_cases h : n ≤ k
      · simp only [h, guard_true, Nat.unpaired, bind, ihf]
        rcases htx : tracen (k + 1) cf (Nat.pair n.unpair.1 n.unpair.2) with _ | tx
        · simp
        simp only [Option.bind_some]
        rcases hx : tx.getLast? with _ | x
        · simp
        simp only [Option.bind_some]
        by_cases hx0 : x = 0
        · simp only [hx0, if_true]
          simp [pure]
        · simp only [hx0, if_false, ihrf]
          rcases htr : tracen k (cf.rfind') (Nat.pair n.unpair.1 (n.unpair.2 + 1)) with _ | tr
          · simp
          simp [List.getLast?_append_of_ne_nil _ (tracen_ne_nil htr)]
      · simp [h]

/-- If a trace exists, the reference output is its last element. -/
theorem evaln_of_tracen {k c n L} (h : tracen k c n = some L) :
    Code.evaln k c n = L.getLast? := by
  rw [evaln_eq_tracen_bind, h, Option.bind_some]

/-- Whenever `evaln` produces a value, so does `tracen`, with a matching last element. -/
theorem tracen_isSome_of_evaln {k c n x} (h : Code.evaln k c n = some x) :
    ∃ L, tracen k c n = some L ∧ L.getLast? = some x := by
  rw [evaln_eq_tracen_bind] at h
  rcases ht : tracen k c n with _ | L
  · rw [ht, Option.bind_none] at h; exact absurd h (by simp)
  · rw [ht, Option.bind_some] at h
    exact ⟨L, rfl, h⟩

/-! ### Fuel-monotonicity and fuel-independence -/

/-- **Fuel-monotonicity of the trace.** A successful trace is identical at any larger
fuel: more fuel never alters an entry of the append-only tape. Modeled on
`Code.evaln_mono`. -/
theorem tracen_mono :
    ∀ {k₁ k₂ : ℕ} {c : Code} {n : ℕ} {L : List ℕ},
      k₁ ≤ k₂ → tracen k₁ c n = some L → tracen k₂ c n = some L := by
  suffices H : ∀ (k₁ : ℕ) (c : Code),
      ∀ {n : ℕ} {k₂ : ℕ} {L : List ℕ},
        k₁ ≤ k₂ → tracen k₁ c n = some L → tracen k₂ c n = some L by
    intro k₁ k₂ c n L; exact H k₁ c
  intro k₁ c
  induction k₁, c using tracen.induct with
  | case1 c => intro n k₂ L _ h; simp only [tracen, reduceCtorEq] at h
  | case2 k | case3 k | case4 k | case5 k =>
      intro n k₂ L hl h
      obtain ⟨k₂, rfl⟩ : ∃ j, k₂ = j + 1 :=
        (Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le k.succ_pos hl)).imp (by intro j hj; omega)
      rw [tracen] at h ⊢
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h ⊢
      obtain ⟨_, hle, ho⟩ := h
      exact ⟨(), le_trans hle (Nat.le_of_succ_le_succ hl), ho⟩
  | case6 k cf cg ihf ihg =>
      intro n k₂ L hl h
      obtain ⟨k₂, rfl⟩ : ∃ j, k₂ = j + 1 :=
        (Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le k.succ_pos hl)).imp (by intro j hj; omega)
      have hl' := Nat.le_of_succ_le_succ hl
      rw [tracen] at h ⊢
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h ⊢
      obtain ⟨_, hle, tf, htf, tg, htg, vf, hvf, vg, hvg, hL⟩ := h
      exact ⟨(), le_trans hle hl', tf, ihf hl htf, tg, ihg hl htg, vf, hvf, vg, hvg, hL⟩
  | case7 k cf cg ihg ihf =>
      intro n k₂ L hl h
      obtain ⟨k₂, rfl⟩ : ∃ j, k₂ = j + 1 :=
        (Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le k.succ_pos hl)).imp (by intro j hj; omega)
      have hl' := Nat.le_of_succ_le_succ hl
      rw [tracen] at h ⊢
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h ⊢
      obtain ⟨_, hle, tg, htg, vg, hvg, tf, htf, hL⟩ := h
      exact ⟨(), le_trans hle hl', tg, ihg hl htg, vg, hvg, tf, ihf hl htf, hL⟩
  | case8 k cf cg ihf ihprec ihg =>
      intro n k₂ L hl h
      obtain ⟨k₂, rfl⟩ : ∃ j, k₂ = j + 1 :=
        (Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le k.succ_pos hl)).imp (by intro j hj; omega)
      have hl' := Nat.le_of_succ_le_succ hl
      rw [tracen] at h ⊢
      simp only [bind, Nat.unpaired, Option.bind_eq_some_iff, Option.guard_eq_some'] at h ⊢
      obtain ⟨_, hle, h⟩ := h
      refine ⟨(), le_trans hle hl', ?_⟩
      cases hm : n.unpair.2 with
      | zero =>
          rw [hm] at h; simp only [Nat.rec_zero] at h ⊢
          exact ihf hl h
      | succ m =>
          rw [hm] at h; simp only [Option.bind_eq_some_iff] at h ⊢
          obtain ⟨ti, hti, vi, hvi, tg, htg, hL⟩ := h
          exact ⟨ti, ihprec hl' hti, vi, hvi, tg, ihg hl htg, hL⟩
  | case9 k cf ihf ihrf =>
      intro n k₂ L hl h
      obtain ⟨k₂, rfl⟩ : ∃ j, k₂ = j + 1 :=
        (Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le k.succ_pos hl)).imp (by intro j hj; omega)
      have hl' := Nat.le_of_succ_le_succ hl
      rw [tracen] at h ⊢
      simp only [bind, Nat.unpaired, Option.bind_eq_some_iff, Option.guard_eq_some'] at h ⊢
      obtain ⟨_, hle, tx, htx, x, hx, h⟩ := h
      refine ⟨(), le_trans hle hl', tx, ihf hl htx, x, hx, ?_⟩
      by_cases hx0 : x = 0
      · rw [if_pos hx0] at h ⊢; exact h
      · rw [if_neg hx0] at h ⊢
        simp only [Option.bind_eq_some_iff] at h ⊢
        obtain ⟨tr, htr, hL⟩ := h
        exact ⟨tr, ihrf hl' htr, hL⟩

/-- **Fuel-independence of the trace.** Any two successful traces of the same `(c, n)`,
at whatever fuels, are equal. -/
theorem tracen_unique {k₁ k₂ : ℕ} {c : Code} {n : ℕ} {L₁ L₂ : List ℕ}
    (h₁ : tracen k₁ c n = some L₁) (h₂ : tracen k₂ c n = some L₂) : L₁ = L₂ := by
  have e₁ : tracen (max k₁ k₂) c n = some L₁ := tracen_mono (le_max_left k₁ k₂) h₁
  have e₂ : tracen (max k₁ k₂) c n = some L₂ := tracen_mono (le_max_right k₁ k₂) h₂
  rw [e₁] at e₂
  exact (Option.some.injEq _ _ ▸ e₂)

/-! ### The canonical trace and the write count -/

open Classical in
/-- The **canonical write-once tape** of `c` on `input`: the fuel-independent trace, or
`none` if `c` never halts on `input`. Well-defined by `tracen_unique`. -/
noncomputable def canonTrace (c : Code) (input : ℕ) : Option (List ℕ) :=
  if h : ∃ k, (tracen k c input).isSome = true then
    tracen (Nat.find h) c input
  else
    none

/-- Any produced trace is the canonical trace. -/
theorem canonTrace_eq_of_tracen {c : Code} {input k : ℕ} {L : List ℕ}
    (h : tracen k c input = some L) : canonTrace c input = some L := by
  classical
  have hex : ∃ k, (tracen k c input).isSome = true := ⟨k, by rw [h]; rfl⟩
  rw [canonTrace, dif_pos hex]
  obtain ⟨L', hL'⟩ : ∃ L', tracen (Nat.find hex) c input = some L' := by
    rcases hh : tracen (Nat.find hex) c input with _ | L'
    · exact absurd (Nat.find_spec hex) (by rw [hh]; simp)
    · exact ⟨L', rfl⟩
  rw [hL', tracen_unique hL' h]

/-- `canonTrace` produces exactly when `c` halts on `input`. -/
theorem canonTrace_eq_some_iff_evaln {c : Code} {input : ℕ} :
    (∃ L, canonTrace c input = some L) ↔ (∃ r x, Code.evaln r c input = some x) := by
  classical
  constructor
  · rintro ⟨L, hL⟩
    have hex : ∃ k, (tracen k c input).isSome = true := by
      by_contra hne
      rw [canonTrace, dif_neg hne] at hL
      exact absurd hL (by simp)
    rw [canonTrace, dif_pos hex] at hL
    obtain ⟨x, hx⟩ : ∃ x, L.getLast? = some x := by
      rcases hgl : L.getLast? with _ | x
      · exact absurd (List.getLast?_eq_none_iff.mp hgl) (tracen_ne_nil hL)
      · exact ⟨x, rfl⟩
    exact ⟨Nat.find hex, x, by rw [evaln_of_tracen hL, hx]⟩
  · rintro ⟨r, x, hx⟩
    obtain ⟨L, hL, _⟩ := tracen_isSome_of_evaln hx
    exact ⟨L, canonTrace_eq_of_tracen hL⟩

/-- The **write count**: the number of values committed to the canonical write-once
tape, or `⊤` if `c` never halts on `input`. -/
noncomputable def numWrites (c : Code) (input : ℕ) : ℕ∞ :=
  match canonTrace c input with
  | Option.some L => (L.length : ℕ∞)
  | Option.none => ⊤

/-- When `c` produces a trace `L`, the write count is `L.length`. -/
theorem numWrites_of_tracen {c : Code} {input k : ℕ} {L : List ℕ}
    (h : tracen k c input = some L) : numWrites c input = (L.length : ℕ∞) := by
  simp only [numWrites, canonTrace_eq_of_tracen h]

/-- The **write bits**: the total bit-length (`Nat.size`) of the values committed to
the canonical write-once tape, or `⊤` if `c` never halts. `numWrites` and `traceBits`
are the two ledgers of the write-once tape — event count and bit content. Neither
dominates the other pointwise (`Nat.size 0 = 0`, while a single write can carry
arbitrarily many bits); no physical-tape cost is defined or bounded here. -/
noncomputable def traceBits (c : Code) (input : ℕ) : ℕ∞ :=
  match canonTrace c input with
  | Option.some L => ((L.map Nat.size).sum : ℕ∞)
  | Option.none => ⊤

/-- When `c` produces a trace `L`, the bit cost is the sum of the written values'
sizes. -/
theorem traceBits_of_tracen {c : Code} {input k : ℕ} {L : List ℕ}
    (h : tracen k c input = some L) :
    traceBits c input = ((L.map Nat.size).sum : ℕ∞) := by
  simp only [traceBits, canonTrace_eq_of_tracen h]

/-- Production dominates the end state: the output is committed on the tape (it is
the last element), so its own bit content is at most the total committed bits. -/
theorem size_output_le_traceBits {c : Code} {input k x : ℕ} {L : List ℕ}
    (htr : tracen k c input = some L) (hx : Code.evaln k c input = some x) :
    (Nat.size x : ℕ∞) ≤ traceBits c input := by
  rw [traceBits_of_tracen htr]
  have hgl : L.getLast? = some x := by rw [← evaln_of_tracen htr, hx]
  have hxmem : x ∈ L := List.mem_of_getLast? hgl
  have hmem : Nat.size x ∈ L.map Nat.size := List.mem_map_of_mem hxmem
  have hle : Nat.size x ≤ (L.map Nat.size).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
  exact_mod_cast hle

/-- `Code.succ` on input `N` commits exactly one write, regardless of `N`. -/
theorem numWrites_succ (N : ℕ) : numWrites Code.succ N = 1 := by
  have h : tracen (N + 1) Code.succ N = some [Nat.succ N] := by
    rw [tracen_succ_code]; simp
  rw [numWrites_of_tracen h]; simp

end TimedKt
