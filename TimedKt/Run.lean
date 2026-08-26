/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.ProgSize
import TimedKt.Trace
import Mathlib.Tactic.Linarith

/-!
# The Operational Evaluation Relation

This module defines the operational evaluation relation for `Nat.Partrec.Code` and
proves its determinism.

`Run c n T s` is an inductive evaluation relation for `Nat.Partrec.Code`, defined
without fuel and without reference to `Code.evaln`. It carries the write-once trace `T`
(output last, as in `TimedKt.tracen`) and a transition count `s`: one transition is one
dispatch on a `Code` constructor, i.e. one node of the evaluation call tree. This is
the operational semantics whose transition count the timed complexity `Kt` prices; the
timed universal machine reuses `Run` for its code-execution portion.

## Main results

* `Run.deterministic`: for fixed `(c, n)` the trace and the transition count are
  unique.
* `exists_run_iff_exists_tracen`: a `Run` exists exactly for the halting computations;
  together with `evaln_of_tracen` this connects `Run` to `Code.eval`.
* `Run.length_le_steps` and `Run.steps_le`: writes and transitions are linearly
  equivalent per fixed code, with slope `2 * (progSize c + 1)`. These calibrate the
  step ledger against the write ledger; they are not used by the definition of `Kt`.
* `numSteps`: the `ℕ∞`-valued transition count of `c` on `input`.
-/

open Nat.Partrec

namespace TimedKt

/-- **Evaluation with a transition count.** `Run c n T s` states that running `c` on
input `n` commits the append-only trace `T` (output last) and dispatches on exactly `s`
`Code` constructors, so `s` is the size of the evaluation call tree. Fuel-free by
construction.

Node arities: leaves are tips; `pair`, `comp`, `prec`-successor and `rfind'`-failure
are binary; `prec`-at-zero and `rfind'`-success are unary. Writes are committed by
leaves, by `pair`, and by a successful `rfind'` trial only. -/
inductive Run : Code → ℕ → List ℕ → ℕ → Prop
  | zero (n : ℕ) : Run Code.zero n [0] 1
  | succ (n : ℕ) : Run Code.succ n [Nat.succ n] 1
  | left (n : ℕ) : Run Code.left n [n.unpair.1] 1
  | right (n : ℕ) : Run Code.right n [n.unpair.2] 1
  | pair {cf cg : Code} {n : ℕ} {tf tg : List ℕ} {vf vg sf sg : ℕ} :
      Run cf n tf sf → Run cg n tg sg →
      tf.getLast? = some vf → tg.getLast? = some vg →
      Run (Code.pair cf cg) n (tf ++ tg ++ [Nat.pair vf vg]) (sf + sg + 1)
  | comp {cf cg : Code} {n : ℕ} {tg tf : List ℕ} {vg sg sf : ℕ} :
      Run cg n tg sg → tg.getLast? = some vg → Run cf vg tf sf →
      Run (Code.comp cf cg) n (tg ++ tf) (sf + sg + 1)
  | precZero {cf cg : Code} {a : ℕ} {t : List ℕ} {s : ℕ} :
      Run cf a t s → Run (Code.prec cf cg) (Nat.pair a 0) t (s + 1)
  | precSucc {cf cg : Code} {a y : ℕ} {ti tg : List ℕ} {vi si sg : ℕ} :
      Run (Code.prec cf cg) (Nat.pair a y) ti si → ti.getLast? = some vi →
      Run cg (Nat.pair a (Nat.pair y vi)) tg sg →
      Run (Code.prec cf cg) (Nat.pair a (y + 1)) (ti ++ tg) (si + sg + 1)
  | rfindFound {cf : Code} {a m : ℕ} {tx : List ℕ} {sx : ℕ} :
      Run cf (Nat.pair a m) tx sx → tx.getLast? = some 0 →
      Run (Code.rfind' cf) (Nat.pair a m) (tx ++ [m]) (sx + 1)
  | rfindStep {cf : Code} {a m x : ℕ} {tx tr : List ℕ} {sx sr : ℕ} :
      Run cf (Nat.pair a m) tx sx → tx.getLast? = some x → x ≠ 0 →
      Run (Code.rfind' cf) (Nat.pair a (m + 1)) tr sr →
      Run (Code.rfind' cf) (Nat.pair a m) (tx ++ tr) (sx + sr + 1)

/-- Every trace is nonempty. -/
theorem Run.ne_nil {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    T ≠ [] := by
  induction h with
  | zero _ => simp
  | succ _ => simp
  | left _ => simp
  | right _ => simp
  | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => simp
  | @comp _ _ _ _ _ _ _ _ _ _ _ _ ihf =>
      exact List.append_ne_nil_of_right_ne_nil _ ihf
  | @precZero _ _ _ _ _ _ ih => exact ih
  | @precSucc _ _ _ _ _ _ _ _ _ _ _ _ ihi _ =>
      exact List.append_ne_nil_of_left_ne_nil ihi _
  | @rfindFound _ _ _ _ _ _ _ _ => simp
  | @rfindStep _ _ _ _ _ _ _ _ _ _ _ _ ihx _ =>
      exact List.append_ne_nil_of_left_ne_nil ihx _

/-- Every trace has at least one write. -/
theorem Run.one_le_length {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    1 ≤ T.length := List.length_pos_iff.mpr h.ne_nil

/-! ### Writes never exceed transitions -/

/-- The write count never exceeds the transition count: each node commits at most one
value. -/
theorem Run.length_le_steps {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    T.length ≤ s := by
  induction h with
  | zero _ => simp
  | succ _ => simp
  | left _ => simp
  | right _ => simp
  | @pair _ _ _ _ _ _ _ _ _ _ _ _ _ ihf ihg =>
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
  | @comp _ _ _ _ _ _ _ _ _ _ _ ihg ihf =>
      simp only [List.length_append]; omega
  | @precZero _ _ _ _ _ _ ih => omega
  | @precSucc _ _ _ _ _ _ _ _ _ _ _ _ ihi ihg =>
      simp only [List.length_append]; omega
  | @rfindFound _ _ _ _ _ _ _ ih =>
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
  | @rfindStep _ _ _ _ _ _ _ _ _ _ _ _ ihx ihr =>
      simp only [List.length_append]; omega

/-! ### Transitions are linear in writes -/

/-- An inductive hypothesis stated at `progSize cf + 1` may be re-read at any larger
code size. -/
private theorem relax {s L p q : ℕ} (h : s + p + 1 ≤ 2 * L * (p + 1)) (hq : p + 1 ≤ q) :
    s + p + 1 ≤ 2 * L * q :=
  le_trans h (Nat.mul_le_mul_left (2 * L) hq)

/-- For every evaluation derivation, the transition count satisfies
`s + (progSize c + 1) ≤ 2 * |T| * (progSize c + 1)`. The slack `progSize c + 1` on the
left pays for the silent (`comp`) and unary (`prec`-at-zero) nodes in the induction. -/
theorem Run.steps_le {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    s + progSize c + 1 ≤ 2 * T.length * (progSize c + 1) := by
  induction h with
  | zero _ => simp [progSize]
  | succ _ => simp [progSize]
  | left _ => simp [progSize]
  | right _ => simp [progSize]
  | @pair cf cg n tf tg vf vg sf sg hf hg _ _ ihf ihg =>
      have hpf : 1 ≤ progSize cf := progSize_pos cf
      have hpg : 1 ≤ progSize cg := progSize_pos cg
      have h1 : sf + progSize cf + 1 ≤ 2 * tf.length * (progSize cf + progSize cg + 2) :=
        relax ihf (by omega)
      have h2 : sg + progSize cg + 1 ≤ 2 * tg.length * (progSize cf + progSize cg + 2) :=
        relax ihg (by omega)
      simp only [progSize, List.length_append, List.length_cons, List.length_nil]
      nlinarith [h1, h2, hpf, hpg, Nat.zero_le (tf.length * progSize cf),
        Nat.zero_le (tg.length * progSize cg)]
  | @comp cf cg n tg tf vg sg sf hg _ hf ihg ihf =>
      have hLf : 1 ≤ tf.length := hf.one_le_length
      have hLg : 1 ≤ tg.length := hg.one_le_length
      have hpf : 1 ≤ progSize cf := progSize_pos cf
      have hpg : 1 ≤ progSize cg := progSize_pos cg
      have h1 : sf + progSize cf + 1 + 2 * tf.length * (progSize cg + 1)
          ≤ 2 * tf.length * (progSize cf + progSize cg + 2) := by nlinarith [ihf]
      have h2 : sg + progSize cg + 1 ≤ 2 * tg.length * (progSize cf + progSize cg + 2) :=
        relax ihg (by omega)
      simp only [progSize, List.length_append]
      nlinarith [h1, h2, hLf, hLg, hpf, hpg, Nat.zero_le (tf.length * progSize cg)]
  | @precZero cf cg a t s hs ih =>
      have hL : 1 ≤ t.length := hs.one_le_length
      have hpf : 1 ≤ progSize cf := progSize_pos cf
      have hpg : 1 ≤ progSize cg := progSize_pos cg
      have hmul : progSize cg ≤ t.length * progSize cg :=
        Nat.le_mul_of_pos_left _ (by omega)
      simp only [progSize]
      nlinarith [ih, hL, hpf, hpg, hmul, Nat.zero_le (t.length * progSize cf)]
  | @precSucc cf cg a y ti tg vi si sg hi _ hg ihi ihg =>
      have hpf : 1 ≤ progSize cf := progSize_pos cf
      have hpg : 1 ≤ progSize cg := progSize_pos cg
      have h2 : sg + progSize cg + 1 ≤ 2 * tg.length * (progSize cf + progSize cg + 2) :=
        relax ihg (by omega)
      simp only [progSize, List.length_append] at ihi ⊢
      nlinarith [ihi, h2, hpf, hpg]
  | @rfindFound cf a m tx sx hx _ ih =>
      have hL : 1 ≤ tx.length := hx.one_le_length
      have hpf : 1 ≤ progSize cf := progSize_pos cf
      simp only [progSize, List.length_append, List.length_cons, List.length_nil]
      nlinarith [ih, hL, hpf, Nat.zero_le (tx.length * progSize cf)]
  | @rfindStep cf a m x tx tr sx sr hx _ _ hr ihx ihr =>
      have hLx : 1 ≤ tx.length := hx.one_le_length
      have hLr : 1 ≤ tr.length := hr.one_le_length
      have hpf : 1 ≤ progSize cf := progSize_pos cf
      simp only [progSize, List.length_append] at ihr ⊢
      nlinarith [ihx, ihr, hLx, hLr, hpf, Nat.zero_le (tx.length * progSize cf)]

/-- Weakened form: `s ≤ 2 * |T| * (progSize c + 1)`. -/
theorem Run.steps_le_doc {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    s ≤ 2 * T.length * (progSize c + 1) := by
  have := h.steps_le
  omega

/-- Writes and transitions are linearly equivalent per fixed code. -/
theorem Run.sandwich {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    T.length ≤ s ∧ s + progSize c + 1 ≤ 2 * T.length * (progSize c + 1) :=
  ⟨h.length_le_steps, h.steps_le⟩

/-! ### The bridge to `tracen`

A `Run` exists exactly for the halting computations, and the trace it carries is the
canonical write-once tape. -/

section Bridge

private theorem tracen_prec_zero' {cf cg : Code} {k a : ℕ} {L : List ℕ}
    (hguard : Nat.pair a 0 ≤ k) (h : tracen (k + 1) cf a = some L) :
    tracen (k + 1) (Code.prec cf cg) (Nat.pair a 0) = some L := by
  rw [tracen]
  simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some', Nat.unpaired,
    Nat.unpair_pair]
  exact ⟨(), hguard, h⟩

private theorem tracen_prec_succ' {cf cg : Code} {k a y vi : ℕ} {ti tg : List ℕ}
    (hguard : Nat.pair a (y + 1) ≤ k)
    (hti : tracen k (Code.prec cf cg) (Nat.pair a y) = some ti)
    (hvi : ti.getLast? = some vi)
    (htg : tracen (k + 1) cg (Nat.pair a (Nat.pair y vi)) = some tg) :
    tracen (k + 1) (Code.prec cf cg) (Nat.pair a (y + 1)) = some (ti ++ tg) := by
  rw [tracen]
  simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some', Nat.unpaired,
    Nat.unpair_pair]
  exact ⟨(), hguard, ti, hti, vi, hvi, tg, htg, rfl⟩

private theorem tracen_rfind_found' {cf : Code} {k a m : ℕ} {tx : List ℕ}
    (hguard : Nat.pair a m ≤ k)
    (htx : tracen (k + 1) cf (Nat.pair a m) = some tx)
    (hx : tx.getLast? = some 0) :
    tracen (k + 1) (Code.rfind' cf) (Nat.pair a m) = some (tx ++ [m]) := by
  rw [tracen]
  simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some', Nat.unpaired,
    Nat.unpair_pair]
  refine ⟨(), hguard, tx, htx, 0, hx, ?_⟩
  simp

private theorem tracen_rfind_step' {cf : Code} {k a m x : ℕ} {tx tr : List ℕ}
    (hguard : Nat.pair a m ≤ k)
    (htx : tracen (k + 1) cf (Nat.pair a m) = some tx)
    (hx : tx.getLast? = some x) (hx0 : x ≠ 0)
    (htr : tracen k (Code.rfind' cf) (Nat.pair a (m + 1)) = some tr) :
    tracen (k + 1) (Code.rfind' cf) (Nat.pair a m) = some (tx ++ tr) := by
  rw [tracen]
  simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some', Nat.unpaired,
    Nat.unpair_pair]
  refine ⟨(), hguard, tx, htx, x, hx, ?_⟩
  rw [if_neg hx0]
  simp only [Option.bind_eq_some_iff]
  exact ⟨tr, htr, rfl⟩

private theorem tracen_pair' {cf cg : Code} {k n : ℕ} {tf tg : List ℕ} {vf vg : ℕ}
    (hf : tracen (k + 1) cf n = some tf) (hg : tracen (k + 1) cg n = some tg)
    (hvf : tf.getLast? = some vf) (hvg : tg.getLast? = some vg) (hn : n ≤ k) :
    tracen (k + 1) (Code.pair cf cg) n = some (tf ++ tg ++ [Nat.pair vf vg]) := by
  rw [tracen]
  simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some']
  exact ⟨(), hn, tf, hf, tg, hg, vf, hvf, vg, hvg, rfl⟩

private theorem tracen_comp' {cf cg : Code} {k n : ℕ} {tg tf : List ℕ} {vg : ℕ}
    (hg : tracen (k + 1) cg n = some tg) (hvg : tg.getLast? = some vg)
    (hf : tracen (k + 1) cf vg = some tf) (hn : n ≤ k) :
    tracen (k + 1) (Code.comp cf cg) n = some (tg ++ tf) := by
  rw [tracen]
  simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some']
  exact ⟨(), hn, tg, hg, vg, hvg, tf, hf, rfl⟩

/-- Every `Run` records a genuine `tracen` trace. -/
theorem exists_tracen_of_run {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    ∃ k, tracen k c n = some T := by
  induction h with
  | zero n => exact ⟨n + 1, by rw [tracen_zero_code, if_pos (le_refl n)]⟩
  | succ n => exact ⟨n + 1, by rw [tracen_succ_code, if_pos (le_refl n)]⟩
  | left n =>
      refine ⟨n + 1, ?_⟩
      rw [tracen]
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some']
      exact ⟨(), le_refl n, rfl⟩
  | right n =>
      refine ⟨n + 1, ?_⟩
      rw [tracen]
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some']
      exact ⟨(), le_refl n, rfl⟩
  | @pair cf cg n tf tg vf vg sf sg _ _ hvf hvg ihf ihg =>
      obtain ⟨kf, hkf⟩ := ihf
      obtain ⟨kg, hkg⟩ := ihg
      refine ⟨max (max kf kg) (n + 1), ?_⟩
      obtain ⟨k, hk⟩ : ∃ k, max (max kf kg) (n + 1) = k + 1 :=
        ⟨max (max kf kg) (n + 1) - 1, by omega⟩
      rw [hk]
      exact tracen_pair' (tracen_mono (by omega) hkf) (tracen_mono (by omega) hkg)
        hvf hvg (by omega)
  | @comp cf cg n tg tf vg sg sf _ hvg _ ihg ihf =>
      obtain ⟨kg, hkg⟩ := ihg
      obtain ⟨kf, hkf⟩ := ihf
      refine ⟨max (max kf kg) (n + 1), ?_⟩
      obtain ⟨k, hk⟩ : ∃ k, max (max kf kg) (n + 1) = k + 1 :=
        ⟨max (max kf kg) (n + 1) - 1, by omega⟩
      rw [hk]
      exact tracen_comp' (tracen_mono (by omega) hkg) hvg
        (tracen_mono (by omega) hkf) (by omega)
  | @precZero cf cg a t s _ ih =>
      obtain ⟨kf, hkf⟩ := ih
      refine ⟨max kf (Nat.pair a 0 + 1), ?_⟩
      obtain ⟨k, hk⟩ : ∃ k, max kf (Nat.pair a 0 + 1) = k + 1 :=
        ⟨max kf (Nat.pair a 0 + 1) - 1, by omega⟩
      rw [hk]
      exact tracen_prec_zero' (by omega) (tracen_mono (by omega) hkf)
  | @precSucc cf cg a y ti tg vi si sg _ hvi _ ihi ihg =>
      obtain ⟨ki, hki⟩ := ihi
      obtain ⟨kg, hkg⟩ := ihg
      refine ⟨max (max ki kg) (Nat.pair a (y + 1)) + 1, ?_⟩
      exact tracen_prec_succ' (by omega) (tracen_mono (by omega) hki) hvi
        (tracen_mono (by omega) hkg)
  | @rfindFound cf a m tx sx _ hx ihx =>
      obtain ⟨kx, hkx⟩ := ihx
      refine ⟨max kx (Nat.pair a m + 1), ?_⟩
      obtain ⟨k, hk⟩ : ∃ k, max kx (Nat.pair a m + 1) = k + 1 :=
        ⟨max kx (Nat.pair a m + 1) - 1, by omega⟩
      rw [hk]
      exact tracen_rfind_found' (by omega) (tracen_mono (by omega) hkx) hx
  | @rfindStep cf a m x tx tr sx sr _ hx hx0 _ ihx ihr =>
      obtain ⟨kx, hkx⟩ := ihx
      obtain ⟨kr, hkr⟩ := ihr
      refine ⟨max (max kx kr) (Nat.pair a m) + 1, ?_⟩
      exact tracen_rfind_step' (by omega) (tracen_mono (by omega) hkx) hx hx0
        (tracen_mono (by omega) hkr)

/-- Every `tracen` trace is recorded by a `Run` (with some transition count). -/
theorem exists_run_of_tracen : ∀ (k : ℕ) (c : Code), ∀ {n : ℕ} {T : List ℕ},
    tracen k c n = some T → ∃ s, Run c n T s := by
  intro k c
  induction k, c using tracen.induct with
  | case1 c => intro n T h; simp only [tracen, reduceCtorEq] at h
  | case2 k =>
      intro n T h; rw [tracen] at h
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, hT⟩ := h
      rw [Option.pure_def, Option.some.injEq] at hT
      subst hT; exact ⟨1, Run.zero n⟩
  | case3 k =>
      intro n T h; rw [tracen] at h
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, hT⟩ := h
      rw [Option.pure_def, Option.some.injEq] at hT
      subst hT; exact ⟨1, Run.succ n⟩
  | case4 k =>
      intro n T h; rw [tracen] at h
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, hT⟩ := h
      rw [Option.pure_def, Option.some.injEq] at hT
      subst hT; exact ⟨1, Run.left n⟩
  | case5 k =>
      intro n T h; rw [tracen] at h
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, hT⟩ := h
      rw [Option.pure_def, Option.some.injEq] at hT
      subst hT; exact ⟨1, Run.right n⟩
  | case6 k cf cg ihf ihg =>
      intro n T h; rw [tracen] at h
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, tf, hf, tg, hg, vf, hvf, vg, hvg, hT⟩ := h
      rw [Option.pure_def, Option.some.injEq] at hT
      subst hT
      obtain ⟨sf, hsf⟩ := ihf hf
      obtain ⟨sg, hsg⟩ := ihg hg
      exact ⟨sf + sg + 1, Run.pair hsf hsg hvf hvg⟩
  | case7 k cf cg ihg ihf =>
      intro n T h; rw [tracen] at h
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, tg, hg, vg, hvg, tf, hf, hT⟩ := h
      rw [Option.pure_def, Option.some.injEq] at hT
      subst hT
      obtain ⟨sg, hsg⟩ := ihg hg
      obtain ⟨sf, hsf⟩ := ihf hf
      exact ⟨sf + sg + 1, Run.comp hsg hvg hsf⟩
  | case8 k cf cg ihf ihprec ihg =>
      intro n T h; rw [tracen] at h
      simp only [Nat.unpaired, bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, h⟩ := h
      have hn : Nat.pair n.unpair.1 n.unpair.2 = n := Nat.pair_unpair n
      by_cases hm : n.unpair.2 = 0
      · rw [hm] at h
        simp only [Nat.rec_zero] at h
        rw [hm] at hn
        obtain ⟨s, hs⟩ := ihf h
        have key : Run (Code.prec cf cg) (Nat.pair n.unpair.1 0) T (s + 1) :=
          Run.precZero hs
        rw [hn] at key
        exact ⟨s + 1, key⟩
      · obtain ⟨y, hy⟩ : ∃ y, n.unpair.2 = y + 1 := ⟨n.unpair.2 - 1, by omega⟩
        rw [hy] at h
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨ti, hti, vi, hvi, tg, htg, hT⟩ := h
        rw [Option.pure_def, Option.some.injEq] at hT
        subst hT
        rw [hy] at hn
        obtain ⟨si, hsi⟩ := ihprec hti
        obtain ⟨sg, hsg⟩ := ihg htg
        have key : Run (Code.prec cf cg) (Nat.pair n.unpair.1 (y + 1)) (ti ++ tg)
            (si + sg + 1) := Run.precSucc hsi hvi hsg
        rw [hn] at key
        exact ⟨si + sg + 1, key⟩
  | case9 k cf ihf ihrf =>
      intro n T h; rw [tracen] at h
      simp only [Nat.unpaired, bind, Option.bind_eq_some_iff, Option.guard_eq_some'] at h
      obtain ⟨_, _, tx, htx, x, hx, h⟩ := h
      have hn : Nat.pair n.unpair.1 n.unpair.2 = n := Nat.pair_unpair n
      by_cases hx0 : x = 0
      · rw [if_pos hx0, Option.pure_def, Option.some.injEq] at h
        subst h
        subst hx0
        obtain ⟨sx, hsx⟩ := ihf htx
        have key : Run (Code.rfind' cf) (Nat.pair n.unpair.1 n.unpair.2)
            (tx ++ [n.unpair.2]) (sx + 1) := Run.rfindFound hsx hx
        rw [hn] at key
        exact ⟨sx + 1, key⟩
      · rw [if_neg hx0] at h
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨tr, htr, hT⟩ := h
        rw [Option.pure_def, Option.some.injEq] at hT
        subst hT
        obtain ⟨sx, hsx⟩ := ihf htx
        obtain ⟨sr, hsr⟩ := ihrf htr
        have key : Run (Code.rfind' cf) (Nat.pair n.unpair.1 n.unpair.2) (tx ++ tr)
            (sx + sr + 1) := Run.rfindStep hsx hx hx0 hsr
        rw [hn] at key
        exact ⟨sx + sr + 1, key⟩

/-- A `Run` exists exactly for the halting computations. -/
theorem exists_run_iff_exists_tracen {c : Code} {n : ℕ} :
    (∃ T s, Run c n T s) ↔ ∃ k T, tracen k c n = some T := by
  constructor
  · rintro ⟨T, s, h⟩
    obtain ⟨k, hk⟩ := exists_tracen_of_run h
    exact ⟨k, T, hk⟩
  · rintro ⟨k, T, hk⟩
    obtain ⟨s, hs⟩ := exists_run_of_tracen k c hk
    exact ⟨T, s, hs⟩

/-- The trace carried by a `Run` is the canonical write-once tape. -/
theorem numWrites_of_run {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    numWrites c n = (T.length : ℕ∞) := by
  obtain ⟨k, hk⟩ := exists_tracen_of_run h
  exact numWrites_of_tracen hk

/-- No `Run` means infinite write cost. -/
theorem numWrites_eq_top_of_no_run {c : Code} {n : ℕ} (h : ¬ ∃ T s, Run c n T s) :
    numWrites c n = ⊤ := by
  classical
  have hnex : ¬ ∃ k, (tracen k c n).isSome = true := by
    rintro ⟨k, hk⟩
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp hk
    exact h (exists_run_iff_exists_tracen.mpr ⟨k, T, hT⟩)
  have hnone : canonTrace c n = Option.none := by rw [canonTrace, dif_neg hnex]
  unfold numWrites
  rw [hnone]

end Bridge

/-! ### Determinism

The timed machine needs determinism: uniqueness of the transition count for every
successful run is part of the timed-machine contract. -/

/-- **Determinism.** For fixed `(c, n)`, the trace and the transition count of a `Run`
are unique: the derivation tree is forced by the code's shape and the sub-results. -/
theorem Run.deterministic {c : Code} {n : ℕ} {T₁ T₂ : List ℕ} {s₁ s₂ : ℕ}
    (h₁ : Run c n T₁ s₁) (h₂ : Run c n T₂ s₂) : T₁ = T₂ ∧ s₁ = s₂ := by
  induction h₁ generalizing T₂ s₂ with
  | zero n => cases h₂; exact ⟨rfl, rfl⟩
  | succ n => cases h₂; exact ⟨rfl, rfl⟩
  | left n => cases h₂; exact ⟨rfl, rfl⟩
  | right n => cases h₂; exact ⟨rfl, rfl⟩
  | @pair cf cg n tf tg vf vg sf sg hf hg hvf hvg ihf ihg =>
      cases h₂ with
      | @pair _ _ _ tf' tg' vf' vg' sf' sg' hf' hg' hvf' hvg' =>
          obtain ⟨rfl, rfl⟩ := ihf hf'
          obtain ⟨rfl, rfl⟩ := ihg hg'
          rw [hvf] at hvf'
          rw [hvg] at hvg'
          obtain rfl := Option.some.inj hvf'
          obtain rfl := Option.some.inj hvg'
          exact ⟨rfl, rfl⟩
  | @comp cf cg n tg tf vg sg sf hg hvg hf ihg ihf =>
      cases h₂ with
      | @comp _ _ _ tg' tf' vg' sg' sf' hg' hvg' hf' =>
          obtain ⟨rfl, rfl⟩ := ihg hg'
          rw [hvg] at hvg'
          obtain rfl := Option.some.inj hvg'
          obtain ⟨rfl, rfl⟩ := ihf hf'
          exact ⟨rfl, rfl⟩
  | @precZero cf cg a t s hs ih =>
      generalize hIn : Nat.pair a 0 = inp at h₂
      cases h₂ with
      | @precZero _ _ a' t' s' hs' =>
          obtain ⟨rfl, -⟩ := Nat.pair_eq_pair.mp hIn
          obtain ⟨rfl, rfl⟩ := ih hs'
          exact ⟨rfl, rfl⟩
      | @precSucc _ _ a' y' ti' tg' vi' si' sg' hi' hvi' hg' =>
          obtain ⟨-, h0⟩ := Nat.pair_eq_pair.mp hIn
          omega
  | @precSucc cf cg a y ti tg vi si sg hi hvi hg ihi ihg =>
      generalize hIn : Nat.pair a (y + 1) = inp at h₂
      cases h₂ with
      | @precZero _ _ a' t' s' hs' =>
          obtain ⟨-, h0⟩ := Nat.pair_eq_pair.mp hIn
          omega
      | @precSucc _ _ a' y' ti' tg' vi' si' sg' hi' hvi' hg' =>
          obtain ⟨rfl, hy⟩ := Nat.pair_eq_pair.mp hIn
          obtain rfl : y = y' := by omega
          obtain ⟨rfl, rfl⟩ := ihi hi'
          rw [hvi] at hvi'
          obtain rfl := Option.some.inj hvi'
          obtain ⟨rfl, rfl⟩ := ihg hg'
          exact ⟨rfl, rfl⟩
  | @rfindFound cf a m tx sx hx hlast ihx =>
      generalize hIn : Nat.pair a m = inp at h₂
      cases h₂ with
      | @rfindFound _ a' m' tx' sx' hx' hlast' =>
          obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hIn
          obtain ⟨rfl, rfl⟩ := ihx hx'
          exact ⟨rfl, rfl⟩
      | @rfindStep _ a' m' x' tx' tr' sx' sr' hx' hlast' hne' hr' =>
          obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hIn
          obtain ⟨rfl, rfl⟩ := ihx hx'
          rw [hlast] at hlast'
          exact absurd (Option.some.inj hlast').symm hne'
  | @rfindStep cf a m x tx tr sx sr hx hlast hne hr ihx ihr =>
      generalize hIn : Nat.pair a m = inp at h₂
      cases h₂ with
      | @rfindFound _ a' m' tx' sx' hx' hlast' =>
          obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hIn
          obtain ⟨rfl, rfl⟩ := ihx hx'
          rw [hlast] at hlast'
          exact absurd (Option.some.inj hlast') hne
      | @rfindStep _ a' m' x' tx' tr' sx' sr' hx' hlast' hne' hr' =>
          obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hIn
          obtain ⟨rfl, rfl⟩ := ihx hx'
          rw [hlast] at hlast'
          obtain rfl := Option.some.inj hlast'
          obtain ⟨rfl, rfl⟩ := ihr hr'
          exact ⟨rfl, rfl⟩

/-- Uniqueness of the transition count, stated alone. -/
theorem Run.steps_unique {c : Code} {n : ℕ} {T₁ T₂ : List ℕ} {s₁ s₂ : ℕ}
    (h₁ : Run c n T₁ s₁) (h₂ : Run c n T₂ s₂) : s₁ = s₂ :=
  (h₁.deterministic h₂).2

/-! ### The `ℕ∞`-valued transition count -/

open Classical in
/-- The **transition count** of evaluating `c` on `input`, or `⊤` if the computation
does not halt. Defined as the least transition count over evaluation derivations; by
`Run.deterministic` it is the count of the unique derivation. -/
noncomputable def numSteps (c : Code) (input : ℕ) : ℕ∞ :=
  if h : ∃ s, ∃ T, Run c input T s then (Nat.find h : ℕ∞) else ⊤

/-- A derivation bounds `numSteps` from above. -/
theorem numSteps_le_of_run {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    numSteps c n ≤ (s : ℕ∞) := by
  classical
  have hex : ∃ s, ∃ T, Run c n T s := ⟨s, T, h⟩
  rw [numSteps, dif_pos hex]
  have hle : Nat.find hex ≤ s := Nat.find_le ⟨T, h⟩
  exact_mod_cast hle

open Classical in
/-- `numSteps` is realized by an actual derivation whenever the computation halts. -/
theorem exists_run_numSteps {c : Code} {n : ℕ} (hex : ∃ s, ∃ T, Run c n T s) :
    ∃ T, Run c n T (Nat.find hex) ∧ numSteps c n = ((Nat.find hex : ℕ) : ℕ∞) := by
  obtain ⟨T, hT⟩ := Nat.find_spec hex
  exact ⟨T, hT, by rw [numSteps, dif_pos hex]⟩

/-- By determinism, any derivation computes `numSteps` exactly. -/
theorem numSteps_eq_of_run {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    numSteps c n = (s : ℕ∞) := by
  classical
  have hex : ∃ s, ∃ T, Run c n T s := ⟨s, T, h⟩
  rw [numSteps, dif_pos hex]
  obtain ⟨T', hT'⟩ := Nat.find_spec hex
  exact_mod_cast (hT'.deterministic h).2

/-- `numSteps` is `⊤` exactly when nothing halts. -/
theorem numSteps_eq_top_iff {c : Code} {n : ℕ} :
    numSteps c n = ⊤ ↔ ¬ ∃ T s, Run c n T s := by
  classical
  constructor
  · intro h hc
    obtain ⟨T, s, hs⟩ := hc
    have hex : ∃ s, ∃ T, Run c n T s := ⟨s, T, hs⟩
    rw [numSteps, dif_pos hex] at h
    exact absurd h (by simp)
  · intro h
    have hex : ¬ ∃ s, ∃ T, Run c n T s := by
      rintro ⟨s, T, hs⟩
      exact h ⟨T, s, hs⟩
    rw [numSteps, dif_neg hex]

/-! ### Concrete runs

The `prec` loop exercises both ledgers with a nonconstant separation, and the leaf and
node shapes are exhibited concretely. -/

/-- The `prec` loop with base `zero` and step `succ`, driven `m` times, commits `m + 1`
writes and makes `2 * m + 2` transitions. -/
theorem run_precLoop (a : ℕ) : ∀ m : ℕ,
    ∃ T, Run (Code.prec Code.zero Code.succ) (Nat.pair a m) T (2 * m + 2) ∧
      T.length = m + 1 := by
  intro m
  induction m with
  | zero => exact ⟨[0], Run.precZero (Run.zero a), rfl⟩
  | succ m ih =>
      obtain ⟨T, hT, hlen⟩ := ih
      obtain ⟨vi, hvi⟩ : ∃ vi, T.getLast? = some vi := by
        rcases hgl : T.getLast? with _ | vi
        · exact absurd (List.getLast?_eq_none_iff.mp hgl) hT.ne_nil
        · exact ⟨vi, rfl⟩
      refine ⟨T ++ [Nat.succ (Nat.pair a (Nat.pair m vi))], ?_, by simp [hlen]⟩
      have hstep := Run.precSucc hT hvi (Run.succ (Nat.pair a (Nat.pair m vi)))
      have harith : 2 * m + 2 + 1 + 1 = 2 * (m + 1) + 2 := by omega
      rwa [harith] at hstep

example : Run (Code.pair Code.succ Code.succ) 0 [1, 1, Nat.pair 1 1] 3 :=
  Run.pair (Run.succ 0) (Run.succ 0) rfl rfl

example : Run (Code.comp Code.succ Code.succ) 0 [1, 2] 3 :=
  Run.comp (Run.succ 0) rfl (Run.succ 1)

end TimedKt
