/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.TMSim
import Mathlib.Tactic.IrreducibleDef

/-!
# `Kt` Is Bounded by Turing-Machine `Kt`

For every fixed finite-state binary multi-tape Turing machine `M` (`TimedKt.TM.MultiTapeTM`, the
CSLib model), one fixed `Nat.Partrec.Code` (`TMSim.tmSimCode M`) maps `encode (p, y)` to
`encode x` within `a * t + b` `Run` transitions whenever `M`, started on `frame p ++ y`, halts
after `t` steps with output `x` (`TMSim.tmSim_spec`). Running that code on the universal machine
gives, for all `x` and `y`,

```
Kt(x | y) ≤ tmKt M x y + c_M        (TimedKt.Kt_cond_le_tmKt)
```

so the transition-clocked `Kt` of this package is at most the Turing-machine-clocked `Kt` of any
fixed machine, up to an additive constant depending on the machine.

## The search over time budgets

The number of steps is not known in advance. The code searches (`rfind'`) for the least `m` such
that `M` has halted after `2 ^ m` steps, each trial re-running the simulation from the start;
then it runs `2 ^ m` steps once more and decodes the output. The trials cost
`O(2 ^ 0 + ... + 2 ^ m) = O(2 ^ m)`, and `2 ^ m < 2 t` by minimality, so the total is `O(t)`.

## Scope

The converse direction, bounding Turing-machine `Kt` by this package's `Kt`, is not proved here:
it needs a Turing-machine simulation of `Run`, whose transitions act on unbounded naturals at unit
cost (see the README).

## Main results

* `TimedKt.TMSim.tmSim_spec`: the linear-time simulation.
* `TimedKt.Kt_cond_le_tmKt`, `TimedKt.Kt_le_tmKtPlain`: `Kt ≤ Kt_M + O(1)`, conditional and plain.
* `TimedKt.TM.copyTM_outputsAt`, `TimedKt.TM.tmKt_copyTM_le`, `TimedKt.Kt_cond_le_length_add_log`:
  a two-state copying machine with finite `tmKt` on every string, so the comparison is not vacuous.
-/

open Nat.Partrec (Code)
open Kolmogorov

namespace TimedKt

namespace TMSim

open ListDestruct RunLib TMCode TM

variable {k : ℕ} {State : Type*} [Finite State]

/-! ### The whole simulation -/

omit [Finite State] in
theorem output_length_step {I : List Bool} (M : MultiTapeTM k Bool State)
    (cfg : Cfg k Bool State I) : (M.step cfg).output.length ≤ cfg.output.length + 1 := by
  rw [step_eq_apply]
  simp only [Action.apply, List.length_append]
  have : (cfgAct M cfg).output.toList.length ≤ 1 := by
    cases (cfgAct M cfg).output <;> simp
  omega

omit [Finite State] in
theorem output_length_runFrom {I : List Bool} (M : MultiTapeTM k Bool State)
    (cfg : Cfg k Bool State I) : ∀ s, (M.runFrom cfg s).output.length ≤ cfg.output.length + s
  | 0 => by simp [MultiTapeTM.runFrom]
  | s + 1 => by
      have := output_length_runFrom M cfg s
      have h2 := output_length_step M (M.runFrom cfg s)
      rw [MultiTapeTM.runFrom, Function.iterate_succ_apply'] at *
      omega

theorem sum_two_pow_lt : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), 2 ^ j < 2 ^ (m + 1)
  | 0 => by simp
  | m + 1 => by
      rw [Finset.sum_range_succ, Nat.pow_succ 2 (m + 1)]
      have := sum_two_pow_lt m
      omega

theorem sum_trials_le (A B : ℕ) : ∀ m : ℕ,
    ∑ j ∈ Finset.range (m + 1), (A * 2 ^ j + B + 1) + (A + B + 1) ≤ (A + B + 1) * 2 ^ (m + 1)
  | 0 => by simp; ring_nf; omega
  | m + 1 => by
      rw [Finset.sum_range_succ]
      have ih := sum_trials_le A B m
      have h1 : A * 2 ^ (m + 1) + B + 1 ≤ (A + B + 1) * 2 ^ (m + 1) := by
        have := Nat.one_le_two_pow (n := m + 1)
        nlinarith
      have h2 : (A + B + 1) * 2 ^ (m + 1 + 1) = (A + B + 1) * 2 ^ (m + 1) +
          (A + B + 1) * 2 ^ (m + 1) := by rw [Nat.pow_succ]; ring
      omega

/-- Run `2 ^ m` steps from the initial configuration and decode the output, on
`pair (encode (p, y)) m`. -/
noncomputable def finalCode (M : MultiTapeTM k Bool State) : Code :=
  .comp convCode (.comp (pth [true, true, true])
    (.comp (iterCode M) (.pair (.comp (initCode M) .left) (.comp pow2 .right))))

/-- **The simulating code**: search for the least `m` such that `M` has halted after `2 ^ m`
steps, then run `2 ^ m` steps and decode the output. Irreducible, so that no tactic tries to
evaluate its encoding. -/
noncomputable irreducible_def tmSimCode (M : MultiTapeTM k Bool State) : Code :=
  .comp (finalCode M) (.pair Code.id (.comp (.rfind' (testCode M)) (.pair Code.id .zero)))

/-- **Linear-time simulation.** If `M`, started on `frame p ++ y`, halts after `t` steps with
output `x`, then `tmSimCode M` maps `encode (p, y)` to `encode x` within `a * t + b` `Run`
transitions, for constants `a`, `b` depending only on `M`. -/
theorem tmSim_spec (M : MultiTapeTM k Bool State) : ∃ a b : ℕ, ∀ (p y x : List Bool) (t : ℕ),
    M.OutputsAt (frame p ++ y) x t →
    RunsLe (tmSimCode M) (Encodable.encode (p, y)) (Encodable.encode x) (a * t + b) := by
  classical
  obtain ⟨At, Bt, htest⟩ := test_spec M
  obtain ⟨Bi, hi⟩ := init_spec M
  obtain ⟨Bit, hit⟩ := iter_spec M
  refine ⟨4 * (At + Bt + 1) + 2 * (Bit + 27) + 72, Bi + 100, fun p y x t hout => ?_⟩
  rw [Encodable.encode_prod_val, tmSimCode_def]
  set N := Nat.pair (enc p) (enc y) with hN
  set cfg0 := M.initCfg (frame p ++ y) with hcfg0
  have ht1 := M.one_le_of_outputsAt hout
  -- the search
  set f : ℕ → ℕ := fun j => stCode (M.runFrom cfg0 (2 ^ j)).state with hf
  have hhalt_t : (M.runFrom cfg0 t).state = none := hout.1
  have hfix : ∀ u, t ≤ u → M.runFrom cfg0 u = M.runFrom cfg0 t := fun u hu => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hu
    exact M.runFrom_add_of_halted hhalt_t d
  have hex : ∃ j, f j = 0 := ⟨t, by
    simp only [hf, stCode_eq_zero_iff]
    rw [hfix _ (Nat.lt_two_pow_self).le]
    exact hhalt_t⟩
  set m := Nat.find hex with hm
  have hm0 : f m = 0 := Nat.find_spec hex
  have hlt : ∀ j < m, f j ≠ 0 := fun j hj => Nat.find_min hex hj
  have hrf := rfind_spec f (fun j => At * 2 ^ j + Bt) (htest p y) hm0 hlt m 0 (by omega)
  -- the final configuration
  have hhalt_m : (M.runFrom cfg0 (2 ^ m)).state = none := by
    have := hm0
    simp only [hf, stCode_eq_zero_iff] at this
    exact this
  have hsame : M.runFrom cfg0 (2 ^ m) = M.runFrom cfg0 t := by
    rcases le_total t (2 ^ m) with h | h
    · exact hfix _ h
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      rw [hd]
      exact (M.runFrom_add_of_halted hhalt_m d).symm
  have hu : 2 ^ m ≤ 2 * t := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]; omega
    · have hne := hlt (m - 1) (by omega)
      have : ¬ t ≤ 2 ^ (m - 1) := by
        intro hle
        apply hne
        simp only [hf, stCode_eq_zero_iff]
        rw [hfix _ hle]
        exact hhalt_t
      have e : 2 ^ m = 2 * 2 ^ (m - 1) := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega]
        rw [Nat.pow_succ]; ring
      omega
  have hxlen : x.length ≤ 2 ^ m := by
    have := output_length_runFrom M cfg0 (2 ^ m)
    rw [hsame, hout.2] at this
    simpa [hcfg0, MultiTapeTM.initCfg] using this
  obtain ⟨E0, hE0, hsim0⟩ := hi p y
  obtain ⟨E', hE', hsim'⟩ := hit _ E0 _ hsim0 (2 ^ m)
  have hout' : pathVal [true, true, true] E' = encOut x := by
    rw [simRel_out hsim', hsame, hout.2]
  -- composing the runs
  have r1 := ((runsLe_id N).pair (runsLe_zero N)).comp hrf
  have r3 := (runsLe_id N).pair r1
  have hl : RunsLe .left (Nat.pair N m) N 1 := by simpa using runsLe_left (Nat.pair N m)
  have hr : RunsLe .right (Nat.pair N m) m 1 := by simpa using runsLe_right (Nat.pair N m)
  have r4 := ((hl.comp hE0).pair (hr.comp (pow2_spec m))).comp hE'
  have r5 := r4.comp (pth_spec [true, true, true] E')
  rw [hout'] at r5
  have r6 := r5.comp (conv_spec x)
  have total := r3.comp r6
  refine total.mono ?_
  rw [← Finset.range_eq_Ico]
  simp only [List.length_cons, List.length_nil]
  have hS := sum_trials_le At Bt m
  have hK : (At + Bt + 1) * 2 ^ (m + 1) ≤ (At + Bt + 1) * (4 * t) :=
    Nat.mul_le_mul_left _ (by rw [Nat.pow_succ]; omega)
  have h2 : Bit * 2 ^ m ≤ Bit * (2 * t) := Nat.mul_le_mul_left _ hu
  have h3 : (4 * (At + Bt + 1) + 2 * (Bit + 27) + 72) * t =
      (At + Bt + 1) * (4 * t) + Bit * (2 * t) + 126 * t := by ring
  rw [h3]
  generalize (∑ j ∈ Finset.range (m + 1), (At * 2 ^ j + Bt + 1)) = S at *
  generalize (At + Bt + 1) * 2 ^ (m + 1) = P0 at *
  generalize (At + Bt + 1) * (4 * t) = P1 at *
  generalize Bit * 2 ^ m = P2 at *
  generalize Bit * (2 * t) = P3 at *
  omega

end TMSim

open TMSim TM in
/-- **`Kt` is bounded by Turing-machine `Kt`.** For every finite-state binary multi-tape Turing
machine `M` there is a constant `c` such that, for all `x` and `y`,
`Kt(x | y) ≤ tmKt M x y + c`. The transition clock of this package simulates Turing-machine
time with linear overhead (`TMSim.tmSim_spec`), and the logarithm of a linear overhead is an
additive constant. -/
theorem Kt_cond_le_tmKt {k : ℕ} {State : Type*} [Finite State] (M : MultiTapeTM k Bool State) :
    ∃ c : ℕ, ∀ x y : BitString, Kt_cond x y ≤ tmKt M x y + c := by
  obtain ⟨a, b, hsim⟩ := tmSim_spec M
  generalize he : Encodable.encode (tmSimCode M) = e
  refine ⟨e + 3 + ceilLog2 (a + (b + e + 4)), fun x y => ?_⟩
  rw [← tsub_le_iff_right]
  refine le_sInf ?_
  rintro n ⟨p, t, hout, rfl⟩
  rw [tsub_le_iff_right]
  have ht := M.one_le_of_outputsAt hout
  obtain ⟨T, s, hrun, hlast, hs⟩ := hsim p y x t hout
  have hU := universalRuns_of_run hrun hlast
  rw [Encodable.encodek, Option.getD_some, he] at hU
  have hF : FlaggedRuns (false :: (unaryPrefix e ++ p)) y x (e + 1 + s + 1 + 1) :=
    ⟨false, _, _, rfl, hU, rfl⟩
  refine (Kt_cond_le_of_flaggedRuns hF).trans ?_
  have hlog : ceilLog2 (e + 1 + s + 1 + 1 + 1) ≤ ceilLog2 (a + (b + e + 4)) + ceilLog2 t := by
    calc ceilLog2 (e + 1 + s + 1 + 1 + 1) ≤ ceilLog2 (a * t + (b + e + 4)) :=
          ceilLog2_mono (by omega)
      _ ≤ ceilLog2 (a + (b + e + 4)) + ceilLog2 t := ceilLog2_linear_le a _ ht
  have hlen : programLength (false :: (unaryPrefix e ++ p)) = e + 2 + programLength p := by
    simp only [programLength, List.length_cons, List.length_append, length_unaryPrefix]
    omega
  rw [hlen]
  push_cast
  have : ((ceilLog2 (e + 1 + s + 1 + 1 + 1) : ℕ) : ENat) ≤
      ((ceilLog2 (a + (b + e + 4)) + ceilLog2 t : ℕ) : ENat) := by exact_mod_cast hlog
  push_cast at this
  calc ((e : ENat) + 2 + (programLength p : ENat)) + 1 + (ceilLog2 (e + 1 + s + 1 + 1 + 1) : ENat)
      ≤ ((e : ENat) + 2 + (programLength p : ENat)) + 1 +
          ((ceilLog2 (a + (b + e + 4)) : ENat) + (ceilLog2 t : ENat)) := by gcongr
    _ = (programLength p : ENat) + (ceilLog2 t : ENat) +
          ((e : ENat) + 3 + (ceilLog2 (a + (b + e + 4)) : ENat)) := by ring

open TM in
/-- **Plain form**: `Kt(x) ≤ tmKtPlain M x + c`. -/
theorem Kt_le_tmKtPlain {k : ℕ} {State : Type*} [Finite State] (M : MultiTapeTM k Bool State) :
    ∃ c : ℕ, ∀ x : BitString, Kt x ≤ tmKtPlain M x + c := by
  obtain ⟨c, hc⟩ := Kt_cond_le_tmKt M
  exact ⟨c, fun x => hc x []⟩

/-! ### Guard: the comparison is not vacuous

`tmKt M x y = ⊤` for every `x` would make `Kt_cond_le_tmKt` empty. The copying machine below
(no work tapes, two states) prints the program `p` from `frame p ++ y` in `2 |p| + 1` steps, so
its `tmKt` is finite on every string, and the theorem specializes to a concrete bound. -/

namespace TM

/-- The copying machine: in state `false` read a marker (`true`: move on; otherwise halt), in
state `true` copy the bit under the head to the output. -/
def copyTM : MultiTapeTM 0 Bool Bool where
  q₀ := false
  tr q s _ :=
    match q, s with
    | false, some true => ⟨.pos, fun i => i.elim0, none, some true⟩
    | true, some b => ⟨.pos, fun i => i.elim0, some b, some false⟩
    | _, _ => ⟨.zero, fun i => i.elim0, none, none⟩

theorem frame_cons (b : Bool) (p : List Bool) : frame (b :: p) = true :: b :: frame p := by
  simp [frame]

theorem frame_append_getElem (y : List Bool) : ∀ (p : List Bool) (i : ℕ), i < p.length →
    (frame p ++ y)[2 * i]? = some true ∧ (frame p ++ y)[2 * i + 1]? = p[i]?
  | [], i, h => by simp at h
  | b :: p, 0, _ => by simp [frame_cons]
  | b :: p, i + 1, h => by
      have := frame_append_getElem y p i (by simpa using h)
      rw [frame_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by ring,
        show 2 * i + 1 + 1 + 1 = 2 * i + 1 + 1 + 1 from rfl]
      simpa [List.cons_append, show 2 * i + 1 + 1 = 2 * i + 2 by ring] using this

theorem frame_append_getElem_length (y : List Bool) : ∀ p : List Bool,
    (frame p ++ y)[2 * p.length]? = some false
  | [] => by simp [frame]
  | b :: p => by
      rw [frame_cons, List.length_cons, show 2 * (p.length + 1) = 2 * p.length + 1 + 1 by ring]
      simpa using frame_append_getElem_length y p

theorem length_frame (p : List Bool) : (frame p).length = 2 * p.length + 1 := by
  induction p with
  | nil => simp [frame]
  | cons b p ih => rw [frame_cons]; simp only [List.length_cons] at *; omega

theorem length_frame_append (p y : List Bool) :
    (frame p ++ y).length = 2 * p.length + 1 + y.length := by
  induction p with
  | nil => simp [frame]; omega
  | cons b p ih => simp only [frame_cons, List.cons_append, List.length_cons] at *; omega

theorem copyTM_run (p y : List Bool) : ∀ i, i ≤ p.length →
    (copyTM.runFrom (copyTM.initCfg (frame p ++ y)) (2 * i)).state = some false ∧
    (copyTM.runFrom (copyTM.initCfg (frame p ++ y)) (2 * i)).inputPos.val = 2 * i + 1 ∧
    (copyTM.runFrom (copyTM.initCfg (frame p ++ y)) (2 * i)).output = p.take i
  | 0, _ => by simp [MultiTapeTM.runFrom, MultiTapeTM.initCfg, copyTM]
  | i + 1, h => by
      obtain ⟨hs, hp, ho⟩ := copyTM_run p y i (by omega)
      have hlen := length_frame_append p y
      have hlf := length_frame p
      obtain ⟨hm, hb⟩ := frame_append_getElem y p i (by omega)
      set c := copyTM.runFrom (copyTM.initCfg (frame p ++ y)) (2 * i) with hc
      have e : copyTM.runFrom (copyTM.initCfg (frame p ++ y)) (2 * (i + 1)) =
          copyTM.step (copyTM.step c) := by
        rw [hc, MultiTapeTM.runFrom, MultiTapeTM.runFrom, show 2 * (i + 1) = 2 * i + 1 + 1 by ring,
          Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hin1 : c.inputSymbol = some true := by
        rw [Cfg.inputSymbol, hp, if_neg (by omega), Nat.add_sub_cancel, hm]
      set c1 := copyTM.step c with hc1
      have h1 : c1 = (⟨.pos, fun i => i.elim0, none, some true⟩ : Action 0 Bool Bool).apply c := by
        rw [hc1, copyTM.step_of_state_some hs, hin1]; rfl
      have hs1 : c1.state = some true := by rw [h1]; rfl
      have hp1 : c1.inputPos.val = 2 * i + 2 := by
        rw [h1]; simp only [Action.apply]; rw [TMSim.moveInputPos_val, hp]; simp; omega
      have ho1 : c1.output = p.take i := by rw [h1]; simp [Action.apply, ho]
      have hlt : i < p.length := by omega
      have hin2 : c1.inputSymbol = some p[i] := by
        rw [Cfg.inputSymbol, hp1, if_neg (by omega), show 2 * i + 2 - 1 = 2 * i + 1 by omega, hb,
          List.getElem?_eq_getElem hlt]
      have h2 : copyTM.step c1 =
          (⟨.pos, fun i => i.elim0, some p[i], some false⟩ : Action 0 Bool Bool).apply c1 := by
        rw [copyTM.step_of_state_some hs1, hin2]; rfl
      rw [e, h2]
      refine ⟨rfl, ?_, ?_⟩
      · simp only [Action.apply]; rw [TMSim.moveInputPos_val, hp1]; simp; omega
      · simp only [Action.apply, Option.toList_some, ho1]
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]
        rfl

/-- The copying machine prints `p` from `frame p ++ y` after `2 |p| + 1` steps. -/
theorem copyTM_outputsAt (p y : List Bool) :
    copyTM.OutputsAt (frame p ++ y) p (2 * p.length + 1) := by
  obtain ⟨hs, hp, ho⟩ := copyTM_run p y p.length le_rfl
  set c := copyTM.runFrom (copyTM.initCfg (frame p ++ y)) (2 * p.length) with hc
  have hlen := length_frame_append p y
  have hin : c.inputSymbol = some false := by
    rw [Cfg.inputSymbol, hp, if_neg (by omega), Nat.add_sub_cancel,
      frame_append_getElem_length]
  have e : copyTM.runFrom (copyTM.initCfg (frame p ++ y)) (2 * p.length + 1) = copyTM.step c := by
    rw [hc, MultiTapeTM.runFrom, MultiTapeTM.runFrom, Function.iterate_succ_apply']
  have h1 : copyTM.step c =
      (⟨.zero, fun i => i.elim0, none, none⟩ : Action 0 Bool Bool).apply c := by
    rw [copyTM.step_of_state_some hs, hin]; rfl
  refine ⟨by rw [e, h1]; rfl, ?_⟩
  rw [e, h1]
  simp [Action.apply, ho]

/-- `tmKt` of the copying machine is finite on every string. -/
theorem tmKt_copyTM_le (x y : BitString) :
    tmKt copyTM x y ≤ ((x.length + ceilLog2 (2 * x.length + 1) : ℕ) : ENat) :=
  sInf_le ⟨x, _, copyTM_outputsAt x y, rfl⟩

end TM

/-- **Guard.** Instantiated at the copying machine, `Kt_cond_le_tmKt` is a finite bound on
every string: `Kt(x | y) ≤ |x| + ⌈log₂ (2 |x| + 1)⌉ + c`. This is an inhabitation check only;
it is weaker than `Kt_cond_le_length`. -/
theorem Kt_cond_le_length_add_log : ∃ c : ℕ, ∀ x y : BitString,
    Kt_cond x y ≤ ((x.length + ceilLog2 (2 * x.length + 1) : ℕ) : ENat) + c := by
  obtain ⟨c, hc⟩ := Kt_cond_le_tmKt TM.copyTM
  exact ⟨c, fun x y => (hc x y).trans (add_le_add (TM.tmKt_copyTM_le x y) le_rfl)⟩

end TimedKt
