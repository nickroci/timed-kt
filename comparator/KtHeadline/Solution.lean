/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import KtHeadline.Statement
import TimedKt

/-!
# Proofs of the claims of `Statement.lean`, each from its namesake in `TimedKt`

The bridge: every definition of `Statement.lean` agrees with the library's (`run_iff`,
`universalRuns_iff`, `flaggedRuns_iff`, `gammaCode_eq`, `compRuns_iff`, `Kt_cond_eq`,
`KtU_cond_eq`), a statement `TimedDecompressor` is a library one with the same fields (`toLib`,
`condKt_eq`), and a statement `Realization` is a library one with the same code and constants
(`Realization.toLib`, `overhead_eq`). Layout after anthropics/formal-math `vp-vnp` (Apache-2.0).
-/

namespace KtHeadline.Solution

open Nat.Partrec

theorem ceilLog2_eq (t : ℕ) : KtHeadline.ceilLog2 t = TimedKt.ceilLog2 t := rfl

theorem run_iff {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} :
    KtHeadline.Run c n T s ↔ TimedKt.Run c n T s := by
  constructor
  · intro h
    induction h with
    | zero n => exact .zero n
    | succ n => exact .succ n
    | left n => exact .left n
    | right n => exact .right n
    | pair _ _ hvf hvg ihf ihg => exact .pair ihf ihg hvf hvg
    | comp _ hvg _ ihg ihf => exact .comp ihg hvg ihf
    | precZero _ ih => exact .precZero ih
    | precSucc _ hvi _ ihi ihg => exact .precSucc ihi hvi ihg
    | rfindFound _ h0 ih => exact .rfindFound ih h0
    | rfindStep _ hx hx0 _ ihx ihr => exact .rfindStep ihx hx hx0 ihr
  · intro h
    induction h with
    | zero n => exact .zero n
    | succ n => exact .succ n
    | left n => exact .left n
    | right n => exact .right n
    | pair _ _ hvf hvg ihf ihg => exact .pair ihf ihg hvf hvg
    | comp _ hvg _ ihg ihf => exact .comp ihg hvg ihf
    | precZero _ ih => exact .precZero ih
    | precSucc _ hvi _ ihi ihg => exact .precSucc ihi hvi ihg
    | rfindFound _ h0 ih => exact .rfindFound ih h0
    | rfindStep _ hx hx0 _ ihx ihr => exact .rfindStep ihx hx hx0 ihr

theorem universalRuns_iff (s y x : BitString) (t : ℕ) :
    KtHeadline.UniversalRuns s y x t ↔ TimedKt.UniversalRuns s y x t := by
  simp only [KtHeadline.UniversalRuns, TimedKt.UniversalRuns, run_iff]

theorem flaggedRuns_iff (s y x : BitString) (t : ℕ) :
    KtHeadline.FlaggedRuns s y x t ↔ TimedKt.FlaggedRuns s y x t := by
  simp only [KtHeadline.FlaggedRuns, TimedKt.FlaggedRuns, universalRuns_iff]

theorem gammaCode_eq (n : ℕ) : KtHeadline.gammaCode n = TimedKt.gammaCode n := rfl

theorem compRuns_iff {s z x : BitString} {t : ℕ} :
    KtHeadline.CompRuns s z x t ↔ TimedKt.CompRuns s z x t := by
  constructor
  · intro h
    induction h with
    | embed hF => exact .embed ((flaggedRuns_iff _ _ _ _).1 hF)
    | comp _ _ ih₂ ih₁ =>
        rw [gammaCode_eq]
        exact .comp ih₂ ih₁
  · intro h
    induction h with
    | embed hF => exact .embed ((flaggedRuns_iff _ _ _ _).2 hF)
    | comp _ _ ih₂ ih₁ =>
        rw [← gammaCode_eq]
        exact .comp ih₂ ih₁

/-- A statement clocked relation that agrees with a library machine's has the same timed
complexity. -/
theorem condKtOf_eq {R : BitString → BitString → BitString → ℕ → Prop}
    {D : TimedKt.TimedDecompressor} (h : ∀ p y x t, R p y x t ↔ D.Runs p y x t)
    (x y : BitString) : condKtOf R x y = D.condKt x y := by
  unfold condKtOf TimedKt.TimedDecompressor.condKt ktCandidates
    TimedKt.TimedDecompressor.ktCandidates
  simp only [h, ceilLog2_eq, Kolmogorov.programLength]

theorem Kt_cond_eq (x y : BitString) : KtHeadline.Kt_cond x y = TimedKt.Kt_cond x y :=
  condKtOf_eq (D := TimedKt.timedCompUniversal) (fun _ _ _ _ => compRuns_iff) x y

theorem Kt_eq (x : BitString) : KtHeadline.Kt x = TimedKt.Kt x :=
  Kt_cond_eq x []

theorem KtU_cond_eq (x y : BitString) :
    KtHeadline.KtU_cond x y = TimedKt.timedUniversal.condKt x y :=
  condKtOf_eq (D := TimedKt.timedUniversal) universalRuns_iff x y

/-- A statement timed decompressor is a library timed decompressor with the same fields. -/
def toLib (D : KtHeadline.TimedDecompressor) : TimedKt.TimedDecompressor where
  toMap := D.toMap
  Runs := D.Runs
  partrec := D.partrec
  runs_iff_produces := D.runs_iff_produces
  one_le_time := D.one_le_time

theorem condKt_eq (D : KtHeadline.TimedDecompressor) (x y : BitString) :
    D.condKt x y = (toLib D).condKt x y :=
  condKtOf_eq (D := toLib D) (fun _ _ _ _ => Iff.rfl) x y

/-- A statement realization is a library realization with the same code and constants. -/
def Realization.toLib {D : KtHeadline.TimedDecompressor} (R : KtHeadline.Realization D) :
    (toLib D).Realization where
  code := R.code
  a := R.a
  b := R.b
  sim p y x t h := by
    obtain ⟨T, steps, r, hrun, hlast, hx, hle⟩ := R.sim p y x t h
    exact ⟨T, steps, r, run_iff.1 hrun, hlast, hx, hle⟩

theorem overhead_eq {D : KtHeadline.TimedDecompressor} (R : KtHeadline.Realization D) :
    R.overhead = (Realization.toLib R).overhead := rfl

/-! ## The claims -/

/-- From `TimedKt.exists_run_of_tracen` / `TimedKt.exists_tracen_of_run` and the trace bridge
`TimedKt.evaln_of_tracen` / `TimedKt.tracen_isSome_of_evaln`. -/
theorem runEvalSpec : KtHeadline.RunEvalSpec := by
  intro c n v
  constructor
  · intro hv
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hv
    obtain ⟨T, hT, hlast⟩ := TimedKt.tracen_isSome_of_evaln (Option.mem_def.mp hk)
    obtain ⟨s, hrun⟩ := TimedKt.exists_run_of_tracen k c hT
    exact ⟨T, s, run_iff.2 hrun, hlast⟩
  · rintro ⟨T, s, hrun, hlast⟩
    obtain ⟨k, hk⟩ := TimedKt.exists_tracen_of_run (run_iff.1 hrun)
    have hev : Code.evaln k c n = some v := by
      rw [TimedKt.evaln_of_tracen hk, hlast]
    exact Code.evaln_sound (Option.mem_def.mpr hev)

/-- From `TimedKt.Run.deterministic`. -/
theorem runDeterministic : KtHeadline.RunDeterministic :=
  fun _ _ _ _ _ _ h₁ h₂ => (run_iff.1 h₁).deterministic (run_iff.1 h₂)

/-- From `TimedKt.isDecompressor_compUniversal` and `TimedKt.compRuns_iff_produces`. -/
theorem compRunsComputable : KtHeadline.CompRunsComputable :=
  ⟨TimedKt.compUniversal, TimedKt.isDecompressor_compUniversal, fun p y x =>
    (TimedKt.compRuns_iff_produces p y x).trans (exists_congr fun _ => compRuns_iff.symm)⟩

/-- From `TimedKt.CompRuns.unique`. -/
theorem compRunsUnique : KtHeadline.CompRunsUnique :=
  fun _ _ _ _ _ _ h₁ h₂ => (compRuns_iff.1 h₁).unique (compRuns_iff.1 h₂)

/-- From `TimedKt.Kt_cond_le_Kt`. -/
theorem conditioning : KtHeadline.Conditioning := fun x y => by
  rw [Kt_cond_eq, Kt_eq]
  exact TimedKt.Kt_cond_le_Kt x y

/-- From `TimedKt.condKt_timedUniversal_le`. -/
theorem invarianceUniversal : KtHeadline.InvarianceUniversal := fun D R x y => by
  rw [KtU_cond_eq, condKt_eq, overhead_eq]
  exact TimedKt.condKt_timedUniversal_le (toLib D) (Realization.toLib R) x y

/-- From `TimedKt.Kt_cond_le_realized`. -/
theorem invariance : KtHeadline.Invariance := fun D R x y => by
  rw [Kt_cond_eq, condKt_eq, overhead_eq]
  exact TimedKt.Kt_cond_le_realized (toLib D) (Realization.toLib R) x y

/-- From `TimedKt.Kt_cond_le_length`. -/
theorem lengthBound : KtHeadline.LengthBound := by
  obtain ⟨c, hc⟩ := TimedKt.Kt_cond_le_length
  exact ⟨c, fun x y => by rw [Kt_cond_eq]; exact hc x y⟩

/-- From `TimedKt.Kt_triangle`. -/
theorem triangle : KtHeadline.Triangle := fun x y z n₁ n₂ h₁ h₂ => by
  rw [Kt_cond_eq] at h₁ h₂ ⊢
  rw [ceilLog2_eq]
  exact TimedKt.Kt_triangle x y z n₁ n₂ h₁ h₂

/-- From `TimedKt.Kt_le_Kt_cond_add_Kt`. -/
theorem symmetryEasy : KtHeadline.SymmetryEasy := fun x y n₁ n₂ h₁ h₂ => by
  rw [Kt_cond_eq] at h₁
  rw [Kt_eq] at h₂ ⊢
  rw [ceilLog2_eq]
  exact TimedKt.Kt_le_Kt_cond_add_Kt x y n₁ n₂ h₁ h₂

/-- From `TimedKt.five_le_Kt_cond`. -/
theorem fiveLeKtCond : KtHeadline.FiveLeKtCond := fun x y => by
  rw [Kt_cond_eq]
  exact TimedKt.five_le_Kt_cond x y

/-- From `TimedKt.Kt_nil`. -/
theorem ktNil : KtHeadline.KtNil := by
  rw [KtHeadline.KtNil, Kt_eq]
  exact TimedKt.Kt_nil

/-- From `TimedKt.idTimedRealization`. -/
theorem idTimedRealized : KtHeadline.IdTimedRealized :=
  ⟨{ code := TimedKt.idTimedRealization.code
     a := TimedKt.idTimedRealization.a
     b := TimedKt.idTimedRealization.b
     sim := fun p y x t h => by
       obtain ⟨T, steps, r, hrun, hlast, hx, hle⟩ := TimedKt.idTimedRealization.sim p y x t h
       exact ⟨T, steps, r, run_iff.2 hrun, hlast, hx, hle⟩ }⟩

/-- Upper bound from `TimedKt.idTimed_condKt_le`; the lower bound holds because every run of the
identity machine is the output itself in one transition. -/
theorem idTimedCondKt : KtHeadline.IdTimedCondKt := fun x y => by
  refine le_antisymm ?_ ?_
  · rw [condKt_eq]
    exact TimedKt.idTimed_condKt_le x y
  · refine le_sInf ?_
    rintro n ⟨p, t, ⟨rfl, rfl⟩, rfl⟩
    simp [KtHeadline.ceilLog2]

/-! ## The separating guard `fastTimed`

A `Run` of `s` transitions outputs at most `sqGrow^[3 s]` of its input (`run_output_le`): every
constructor adds one transition and grows values by at most two applications of `sqGrow`
(`pair a b ≤ sqGrow (max a b)`). A realization of `fastTimed` would therefore output, within
`a + b` transitions, a value of size at most `sqGrow^[3 (a + b)] m` on input `m`, while the output
list has length `fastLen m = sqGrow^[m] m` and a list decodes only from a code at least its length
(`length_le_of_decode`). -/

theorem le_sqGrow (v : ℕ) : v + 1 ≤ sqGrow v := by
  unfold sqGrow
  nlinarith

theorem sqGrow_mono : Monotone sqGrow := fun a b h => by
  unfold sqGrow
  exact Nat.mul_le_mul (by omega) (by omega)

theorem iter_le_succ (k v : ℕ) : sqGrow^[k] v ≤ sqGrow^[k + 1] v := by
  rw [Function.iterate_succ_apply']
  exact (Nat.le_succ _).trans (le_sqGrow _)

theorem iter_mono_k {j k : ℕ} (h : j ≤ k) (v : ℕ) : sqGrow^[j] v ≤ sqGrow^[k] v := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (iter_le_succ _ _)

theorem iter_mono_arg (k : ℕ) {a b : ℕ} (h : a ≤ b) : sqGrow^[k] a ≤ sqGrow^[k] b :=
  sqGrow_mono.iterate k h

theorem le_iter (k v : ℕ) : v ≤ sqGrow^[k] v :=
  iter_mono_k (Nat.zero_le k) v

theorem pair_le_sqGrow {a b w : ℕ} (ha : a ≤ w) (hb : b ≤ w) : Nat.pair a b ≤ sqGrow w := by
  have h1 := Nat.pair_lt_max_add_one_sq a b
  have h2 : (max a b + 1) ^ 2 ≤ sqGrow w := by
    unfold sqGrow
    rw [sq]
    have : max a b ≤ w := max_le ha hb
    exact Nat.mul_le_mul (by omega) (by omega)
  omega

theorem getLast?_append_right {l l' : List ℕ} (h : l' ≠ []) :
    (l ++ l').getLast? = l'.getLast? := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr h)
  rw [List.getLast?_append, hw]
  rfl

/-- The output of a `Run` of `s` transitions is at most `sqGrow^[3 s]` of its input. -/
theorem run_output_le {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : TimedKt.Run c n T s) :
    ∀ v, T.getLast? = some v → v ≤ sqGrow^[3 * s] n := by
  induction h with
  | zero n =>
      intro v hv
      simp only [List.getLast?_singleton, Option.some.injEq] at hv
      omega
  | succ n =>
      intro v hv
      simp only [List.getLast?_singleton, Option.some.injEq] at hv
      subst hv
      calc n.succ ≤ sqGrow n := le_sqGrow n
        _ = sqGrow^[1] n := rfl
        _ ≤ sqGrow^[3 * 1] n := iter_mono_k (by norm_num) n
  | left n =>
      intro v hv
      simp only [List.getLast?_singleton, Option.some.injEq] at hv
      subst hv
      exact (Nat.unpair_left_le n).trans (le_iter _ _)
  | right n =>
      intro v hv
      simp only [List.getLast?_singleton, Option.some.injEq] at hv
      subst hv
      exact (Nat.unpair_right_le n).trans (le_iter _ _)
  | @pair cf cg n tf tg vf vg sf sg _ _ hvf hvg ihf ihg =>
      intro v hv
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.some.injEq] at hv
      subst hv
      have h1 : vf ≤ sqGrow^[3 * sf + 3 * sg] n :=
        (ihf vf hvf).trans (iter_mono_k (by omega) n)
      have h2 : vg ≤ sqGrow^[3 * sf + 3 * sg] n :=
        (ihg vg hvg).trans (iter_mono_k (by omega) n)
      calc Nat.pair vf vg ≤ sqGrow (sqGrow^[3 * sf + 3 * sg] n) := pair_le_sqGrow h1 h2
        _ = sqGrow^[3 * sf + 3 * sg + 1] n := (Function.iterate_succ_apply' _ _ _).symm
        _ ≤ sqGrow^[3 * (sf + sg + 1)] n := iter_mono_k (by omega) n
  | @comp cf cg n tg tf vg sg sf _ hvg hf ihg ihf =>
      intro v hv
      rw [getLast?_append_right hf.ne_nil] at hv
      calc v ≤ sqGrow^[3 * sf] vg := ihf v hv
        _ ≤ sqGrow^[3 * sf] (sqGrow^[3 * sg] n) := iter_mono_arg _ (ihg vg hvg)
        _ = sqGrow^[3 * sf + 3 * sg] n := (Function.iterate_add_apply _ _ _ _).symm
        _ ≤ sqGrow^[3 * (sf + sg + 1)] n := iter_mono_k (by omega) n
  | @precZero cf cg a t s _ ih =>
      intro v hv
      calc v ≤ sqGrow^[3 * s] a := ih v hv
        _ ≤ sqGrow^[3 * s] (Nat.pair a 0) := iter_mono_arg _ (Nat.left_le_pair a 0)
        _ ≤ sqGrow^[3 * (s + 1)] (Nat.pair a 0) := iter_mono_k (by omega) _
  | @precSucc cf cg a y ti tg vi si sg _ hvi hg ihi ihg =>
      intro v hv
      rw [getLast?_append_right hg.ne_nil] at hv
      set N := Nat.pair a (y + 1) with hN
      set W := sqGrow^[3 * si] N with hW
      have hNW : N ≤ W := le_iter _ _
      have hvi' : vi ≤ W :=
        (ihi vi hvi).trans (iter_mono_arg _ (Nat.pair_lt_pair_right a (Nat.lt_succ_self y)).le)
      have hy : y ≤ W := by
        have := Nat.right_le_pair a (y + 1)
        omega
      have ha : a ≤ W := (Nat.left_le_pair a (y + 1)).trans hNW
      have hin : Nat.pair a (Nat.pair y vi) ≤ sqGrow^[3 * si + 2] N := by
        have h1 : Nat.pair y vi ≤ sqGrow W := pair_le_sqGrow hy hvi'
        have h2 : Nat.pair a (Nat.pair y vi) ≤ sqGrow (sqGrow W) :=
          pair_le_sqGrow (ha.trans ((Nat.le_succ _).trans (le_sqGrow W))) h1
        have h3 : sqGrow (sqGrow W) = sqGrow^[3 * si + 2] N := by
          rw [hW, Function.iterate_succ_apply', Function.iterate_succ_apply']
        omega
      calc v ≤ sqGrow^[3 * sg] (Nat.pair a (Nat.pair y vi)) := ihg v hv
        _ ≤ sqGrow^[3 * sg] (sqGrow^[3 * si + 2] N) := iter_mono_arg _ hin
        _ = sqGrow^[3 * sg + (3 * si + 2)] N := (Function.iterate_add_apply _ _ _ _).symm
        _ ≤ sqGrow^[3 * (si + sg + 1)] N := iter_mono_k (by omega) N
  | @rfindFound cf a m tx sx _ _ _ =>
      intro v hv
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.some.injEq] at hv
      rw [← hv]
      exact (Nat.right_le_pair a m).trans (le_iter _ _)
  | @rfindStep cf a m x tx tr sx sr _ _ _ hr _ ihr =>
      intro v hv
      rw [getLast?_append_right hr.ne_nil] at hv
      set N := Nat.pair a m with hN
      have hin : Nat.pair a (m + 1) ≤ sqGrow^[2] N := by
        have h1 : Nat.pair a (m + 1) ≤ sqGrow (N + 1) := by
          have := Nat.left_le_pair a m
          have := Nat.right_le_pair a m
          exact pair_le_sqGrow (by omega) (by omega)
        have h2 : sqGrow (N + 1) ≤ sqGrow (sqGrow N) := sqGrow_mono (le_sqGrow N)
        have h3 : sqGrow^[2] N = sqGrow (sqGrow N) := rfl
        omega
      calc v ≤ sqGrow^[3 * sr] (Nat.pair a (m + 1)) := ihr v hv
        _ ≤ sqGrow^[3 * sr] (sqGrow^[2] N) := iter_mono_arg _ hin
        _ = sqGrow^[3 * sr + 2] N := (Function.iterate_add_apply _ _ _ _).symm
        _ ≤ sqGrow^[3 * (sx + sr + 1)] N := iter_mono_k (by omega) N

/-- A list decodes only from a code at least its length. -/
theorem length_le_of_decode (r : ℕ) :
    ∀ x : BitString, (Encodable.decode r : Option BitString) = some x → x.length ≤ r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro x h
    cases r with
    | zero =>
        rw [Encodable.decode_list_zero] at h
        cases h
        simp
    | succ r =>
        rw [Encodable.decode_list_succ] at h
        cases h1 : (Encodable.decode r.unpair.1 : Option Bool) with
        | none => simp [h1, Seq.seq] at h
        | some b =>
        cases h2 : (Encodable.decode r.unpair.2 : Option BitString) with
        | none => simp [h1, h2, Seq.seq] at h
        | some l =>
        simp only [h1, h2, Seq.seq, Option.map_eq_map, Option.map_some, Option.bind_some,
          Option.some.injEq] at h
        subst h
        have hl := ih r.unpair.2 (Nat.lt_succ_of_le (Nat.unpair_right_le r)) _ h2
        have hr := Nat.unpair_right_le r
        simp only [List.length_cons]
        omega

theorem length_iterate_cons (k : ℕ) : ((List.cons true)^[k] ([] : BitString)).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', List.length_cons, ih]

/-- `fastTimed` has no realization. -/
theorem fastTimedUnrealized : KtHeadline.FastTimedUnrealized := by
  refine ⟨fun R => ?_⟩
  obtain ⟨K, hK⟩ : ∃ K, K = R.a + R.b := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : BitString, p = List.replicate (3 * K + 1) true := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = Encodable.encode (p, ([] : BitString)) := ⟨_, rfl⟩
  have hm : 3 * K + 1 ≤ m := by
    have h1 : p.length ≤ Encodable.encode p := Encodable.length_le_encode p
    have h2 : Encodable.encode p ≤ m := by
      rw [hmdef, Encodable.encode_prod_val]
      exact Nat.left_le_pair _ _
    have hpl : p.length = 3 * K + 1 := by rw [hp, List.length_replicate]
    omega
  have hrun : fastTimed.Runs p [] (fastOut (p, [])) 1 := ⟨rfl, rfl⟩
  obtain ⟨T, steps, r, hR, hlast, hx, hle⟩ := R.sim p [] _ 1 hrun
  have hlen : (fastOut (p, [])).length = fastLen m := by
    rw [fastOut, length_iterate_cons, hmdef]
  have hfast : m ≤ fastLen m := le_iter m m
  have hpos : fastOut (p, []) ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [hlen, List.length_nil] at this
    omega
  have hdec : (Encodable.decode r : Option BitString) = some (fastOut (p, [])) := by
    cases hd : (Encodable.decode r : Option BitString) with
    | none =>
        rw [hd, Option.getD_none] at hx
        exact absurd hx hpos
    | some x' =>
        rw [hd, Option.getD_some] at hx
        rw [hx]
  have h1 := length_le_of_decode r _ hdec
  rw [hlen] at h1
  have h2 := run_output_le (run_iff.1 hR) r hlast
  rw [← hmdef] at h2
  have h3 : sqGrow^[3 * steps] m ≤ sqGrow^[3 * K] m := iter_mono_k (by omega) m
  have h4 : sqGrow^[3 * K] m < fastLen m := by
    have h5 : sqGrow^[3 * K + 1] m ≤ sqGrow^[m] m := iter_mono_k hm m
    have h6 := le_sqGrow (sqGrow^[3 * K] m)
    rw [Function.iterate_succ_apply'] at h5
    unfold fastLen
    omega
  omega

end KtHeadline.Solution
