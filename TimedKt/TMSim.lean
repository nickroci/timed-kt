/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.TMCode
import TimedKt.TuringMachine
import TimedKt.Kt
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Simulating a Turing-Machine Step in Constant Transitions

For a fixed finite-state binary multi-tape Turing machine `M` (`TimedKt.TM.MultiTapeTM`), this
module encodes configurations as natural numbers and builds fixed `Nat.Partrec.Code`s that act on
the encodings; the full simulation and the comparison of `Kt` with Turing-machine `Kt` are in
`TimedKt.TMBridge`.

## The encoding

A configuration is encoded as `pair q (pair Zn (pair W OP))` (`TimedKt.TMCode.encE`): the state
code (`0` once halted), the input zipper (`TimedKt.TMCode.Zip`), the `k` work tapes, and the
output buffer. `TMSim.SimRel E cfg` states that `E` encodes `cfg`; the input zipper is related to
the input head position by `TMSim.ZRel` and each encoded tape to its tape by `TMSim.TapeRel`.

## One step

`TMSim.stepCode M` reads the state and the head symbols into a key, looks the encoded action up in
a finite table (`TMSim.tableF`; a halted configuration reads the no-op action, so halted
configurations are fixed), and applies it (`TMCode.newECode`). Every part costs a constant number
of transitions, because the tapes are stacks of `Nat.pair` and the input is produced lazily from
the list encodings of `p` and `y`.

## Main results

* `TMSim.zrel_move`, `TMSim.tapeRel_update`, `TMSim.oupdN_encOut`: the encodings track the input
  head, a work-tape action, and the output.
* `TMSim.simRel_apply`: applying the encoded action of a configuration to its encoding encodes the
  next configuration.
* `TMSim.step_spec`: one step of `M` in a constant number of `Run` transitions, preserving
  `SimRel`.
* `TMSim.iter_spec`, `TMSim.init_spec`, `TMSim.test_spec`, `TMSim.conv_spec`: `m` steps in
  `O(m)` transitions, the initial configuration from `encode (p, y)` in `O(1)`, the state after
  `2 ^ j` steps in `O(2 ^ j)`, and the output decoded in `O(|output|)`.
-/

open Nat.Partrec (Code)
open Kolmogorov

namespace TimedKt

namespace TMSim

open ListDestruct RunLib TMCode TM

variable {k : ℕ} {State : Type*} [Finite State]

/-! ### Codes of states, symbols and actions -/

/-- A fixed enumeration of the states. -/
noncomputable def stEquiv (State : Type*) [Finite State] : State ≃ Fin (Nat.card State) :=
  Finite.equivFin State

/-- State code: `0` for halted, `i + 1` for the `i`-th state. -/
noncomputable def stCode : Option State → ℕ
  | none => 0
  | some q => (stEquiv State q : ℕ) + 1

/-- Decode a state code. -/
noncomputable def stDec (State : Type*) [Finite State] (n : ℕ) : Option State :=
  if h : n ≠ 0 ∧ n - 1 < Nat.card State then some ((stEquiv State).symm ⟨n - 1, h.2⟩) else none

theorem stDec_stCode (s : Option State) : stDec State (stCode s) = s := by
  cases s with
  | none => simp [stCode, stDec]
  | some q =>
      have h := (stEquiv State q).isLt
      simp only [stCode, stDec, Nat.add_sub_cancel]
      rw [dif_pos ⟨by omega, h⟩]
      simp

theorem stCode_le (s : Option State) : stCode s ≤ Nat.card State := by
  cases s with
  | none => simp [stCode]
  | some q => have := (stEquiv State q).isLt; simp only [stCode]; omega

theorem stCode_eq_zero_iff (s : Option State) : stCode s = 0 ↔ s = none := by
  cases s <;> simp [stCode]

/-- Cell code: blank `0`, `false` `1`, `true` `2`. -/
def symCode : Option Bool → ℕ
  | none => 0
  | some b => bcode b

/-- Decode a cell code (`1 ↦ false`, `2 ↦ true`, otherwise blank). -/
def symDec (n : ℕ) : Option Bool :=
  if n = 1 then some false else if n = 2 then some true else none

@[simp] theorem symDec_symCode (o : Option Bool) : symDec (symCode o) = o := by
  rcases o with _ | _ | _ <;> simp [symCode, symDec, bcode_false, bcode_true]

theorem symCode_le (o : Option Bool) : symCode o ≤ 2 := by
  rcases o with _ | _ | _ <;> simp [symCode, bcode_false, bcode_true]

/-- Code of a work-tape write: `0` none, `s + 1` write `s`. -/
def wsCode : Option (Option Bool) → ℕ
  | none => 0
  | some s => symCode s + 1

theorem wsCode_le (o : Option (Option Bool)) : wsCode o ≤ 3 := by
  cases o with
  | none => simp [wsCode]
  | some s => have := symCode_le s; simp only [wsCode]; omega

/-- The encoded work-tape actions of an action. -/
def waEnc (a : Action k Bool State) (i : Fin k) : ℕ :=
  Nat.pair (wsCode (a.workTapes i).1) (mvCode (a.workTapes i).2)

/-- The encoded action `pair qn (pair im (pair os WA))`. -/
noncomputable def actEnc (a : Action k Bool State) : ℕ :=
  Nat.pair (stCode a.state) (Nat.pair (mvCode a.inputTape)
    (Nat.pair (symCode a.output) (wenc k (waEnc a))))

/-- The no-op action read by a halted configuration. -/
def noopAct : Action k Bool State := ⟨0, fun _ => (none, 0), none, none⟩

/-- The action selected by a key `pair q (pair H S)`. -/
noncomputable def decAct (M : MultiTapeTM k Bool State) (key : ℕ) : Action k Bool State :=
  match stDec State key.unpair.1 with
  | none => noopAct
  | some q => M.tr q (symDec key.unpair.2.unpair.1) (fun i => symDec (sget key.unpair.2.unpair.2 i))

/-- The finite transition table. -/
noncomputable def tableF (M : MultiTapeTM k Bool State) (key : ℕ) : ℕ := actEnc (decAct M key)

/-! ### The simulation relation -/

/-- The code of the input cell at head position `j` (`3` at position `0`). -/
def hcode (I : List Bool) (j : ℕ) : ℕ := if j = 0 then 3 else symCode I[j - 1]?

theorem hcode_le (I : List Bool) (j : ℕ) : hcode I j ≤ 3 := by
  unfold hcode; split
  · omega
  · have := symCode_le I[j - 1]?; omega

/-- The zipper `z` represents head position `j` on the input `I`. -/
def ZRel (z : Zip) (I : List Bool) (j : ℕ) : Prop :=
  z.md ≤ 2 ∧ z.Ls = (I.take (j - 1)).reverse ∧ z.H = hcode I j ∧
    z.Rb ++ genList z.md z.P z.Y = I.drop j

/-- The encoded tape `T` represents the tape `tape` with head at `pos`. -/
def TapeRel (T : ℕ) (tape : ℤ → Option Bool) (pos : ℤ) : Prop :=
  ∀ i : ℕ, sget T.unpair.2 i = symCode (tape (pos + i)) ∧
    sget T.unpair.1 i = symCode (tape (pos - 1 - i))

/-- The encoded output buffer. -/
def encOut (out : List Bool) : ℕ :=
  Nat.pair (pairStack (out.reverse.map Encodable.encode)) out.length

/-- **The simulation relation**: `E` encodes the configuration `cfg`. -/
def SimRel {I : List Bool} (E : ℕ) (cfg : Cfg k Bool State I) : Prop :=
  ∃ (z : Zip) (Ts : Fin k → ℕ),
    E = encE (stCode cfg.state) z.enc (wenc k Ts) (encOut cfg.output) ∧
    ZRel z I cfg.inputPos.val ∧ ∀ i, TapeRel (Ts i) (cfg.workTapes i) (cfg.workTapePos i)

/-! #### The input head -/

@[simp] theorem signType_cast_zero : ((SignType.zero : SignType) : ℤ) = 0 := rfl

@[simp] theorem signType_cast_pos : ((SignType.pos : SignType) : ℤ) = 1 := rfl

@[simp] theorem signType_cast_neg : ((SignType.neg : SignType) : ℤ) = -1 := rfl

theorem moveInputPos_val_int {n : ℕ} (pos : Fin (n + 2)) (m : SignType) :
    ((moveInputPos pos m).val : ℤ) = min ((n : ℤ) + 1) (max 0 ((pos.val : ℤ) + (m : ℤ))) := by
  unfold moveInputPos
  dsimp only
  split_ifs with h
  · simp only
    omega
  · simp only
    omega

theorem moveInputPos_val {n : ℕ} (pos : Fin (n + 2)) (m : SignType) :
    (moveInputPos pos m).val =
      match m with
      | .neg => pos.val - 1
      | .zero => pos.val
      | .pos => min (pos.val + 1) (n + 1) := by
  have h := moveInputPos_val_int pos m
  have hp := pos.isLt
  cases m with
  | zero =>
      simp only [signType_cast_zero] at h
      change (moveInputPos pos .zero).val = pos.val
      omega
  | neg =>
      simp only [signType_cast_neg] at h
      change (moveInputPos pos .neg).val = pos.val - 1
      omega
  | pos =>
      simp only [signType_cast_pos] at h
      change (moveInputPos pos .pos).val = min (pos.val + 1) (n + 1)
      omega

theorem drop_cases (I : List Bool) (j : ℕ) :
    (I.drop j = [] ∧ I[j]? = none ∧ I.drop (j + 1) = []) ∨
      ∃ b, I.drop j = b :: I.drop (j + 1) ∧ I[j]? = some b := by
  by_cases h : j < I.length
  · exact Or.inr ⟨I[j], List.drop_eq_getElem_cons h, List.getElem?_eq_getElem h⟩
  · refine Or.inl ⟨List.drop_eq_nil_of_le (by omega), List.getElem?_eq_none (by omega),
      List.drop_eq_nil_of_le (by omega)⟩

/-- Popping the right side at head position `j` produces the cell `j + 1`. -/
theorem popR_drop {Rb P Y : List Bool} {md : ℕ} {I : List Bool} {j : ℕ} (hmd : md ≤ 2)
    (h : Rb ++ genList md P Y = I.drop j) :
    (popR Rb md P Y).1 = symCode I[j]? ∧
      (popR Rb md P Y).2.1 ++ genList (popR Rb md P Y).2.2.1 (popR Rb md P Y).2.2.2.1
        (popR Rb md P Y).2.2.2.2 = I.drop (j + 1) := by
  have hc := popR_correct hmd Rb P Y
  rcases drop_cases I j with ⟨h0, h1, h2⟩ | ⟨b, h0, h1⟩
  · rw [h0] at h
    obtain ⟨e1, e2⟩ := hc.1 h
    exact ⟨by rw [e1, h1]; rfl, by rw [e2, h2]⟩
  · rw [h0] at h
    obtain ⟨e1, e2⟩ := hc.2 b _ h
    exact ⟨by rw [e1, h1]; rfl, e2⟩

theorem take_reverse_succ (I : List Bool) {j : ℕ} (hj : j < I.length) :
    (I.take (j + 1)).reverse = I[j] :: (I.take j).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp

/-- **The zipper tracks the input head.** -/
theorem zrel_move {z : Zip} {I : List Bool} {j : ℕ} (h : ZRel z I j) (hj : j ≤ I.length + 1)
    (m : SignType) :
    ZRel (z.move m) I
      (match m with
        | .neg => j - 1
        | .zero => j
        | .pos => min (j + 1) (I.length + 1)) := by
  obtain ⟨hmd, hLs, hH, hR⟩ := h
  cases m with
  | zero => exact ⟨hmd, hLs, hH, hR⟩
  | pos =>
      change ZRel z.moveR I (min (j + 1) (I.length + 1))
      obtain ⟨e1, e2⟩ := popR_drop hmd hR
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · -- left boundary
        have h3 : z.H = 3 := by simp [hH, hcode]
        simp only [Zip.moveR, h3, if_neg (by omega : (3 : ℕ) ≠ 0), if_true]
        refine ⟨popR_md_le hmd _ _, ?_, ?_, ?_⟩
        · simp [hLs]
        · rw [e1]; simp [hcode]
        · rw [e2, min_eq_left (by omega)]
      · by_cases hjn : j ≤ I.length
        · -- inside the input
          have hlt : j - 1 < I.length := by omega
          have hHv : z.H = bcode I[j - 1] := by
            rw [hH, hcode, if_neg (by omega), List.getElem?_eq_getElem hlt]; rfl
          have h0 : z.H ≠ 0 := by have := one_le_bcode I[j - 1]; omega
          have h3 : z.H ≠ 3 := by have := bcode_le_two I[j - 1]; omega
          simp only [Zip.moveR, h0, h3, if_false]
          refine ⟨popR_md_le hmd _ _, ?_, ?_, ?_⟩
          · rw [min_eq_left (by omega), hHv, bdec_bcode, hLs, Nat.add_sub_cancel,
              ← take_reverse_succ I hlt, Nat.sub_add_cancel hj0]
          · rw [e1, min_eq_left (by omega)]; simp [hcode]
          · rw [e2, min_eq_left (by omega)]
        · -- right boundary
          have hjn' : j = I.length + 1 := by omega
          have h0 : z.H = 0 := by
            rw [hH, hcode, if_neg (by omega), List.getElem?_eq_none (by omega)]; rfl
          simp only [Zip.moveR, h0, if_true]
          rw [min_eq_right (by omega), ← hjn']
          exact ⟨hmd, hLs, hH, hR⟩
  | neg =>
      change ZRel z.moveL I (j - 1)
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have h3 : z.H = 3 := by simp [hH, hcode]
        simp only [Zip.moveL, h3, if_true]
        exact ⟨hmd, hLs, hH, hR⟩
      · have h3 : z.H ≠ 3 := by
          rw [hH, hcode, if_neg (by omega)]; have := symCode_le I[j - 1]?; omega
        simp only [Zip.moveL, h3, if_false]
        refine ⟨hmd, ?_, ?_, ?_⟩
        · -- the left side
          rcases Nat.lt_or_ge j 2 with hj1 | hj2
          · have : j = 1 := by omega
            subst this
            simp [hLs, popL]
          · have hlt : j - 2 < I.length := by omega
            have : z.Ls = I[j - 2] :: (I.take (j - 2)).reverse := by
              rw [hLs, show j - 1 = j - 2 + 1 by omega, take_reverse_succ I hlt]
            simp only [this, popL]
            congr 2
        · rcases Nat.lt_or_ge j 2 with hj1 | hj2
          · have : j = 1 := by omega
            subst this
            simp [hLs, popL, hcode]
          · have hlt : j - 2 < I.length := by omega
            have : z.Ls = I[j - 2] :: (I.take (j - 2)).reverse := by
              rw [hLs, show j - 1 = j - 2 + 1 by omega, take_reverse_succ I hlt]
            simp only [this, popL, hcode, if_neg (by omega : j - 1 ≠ 0),
              show j - 1 - 1 = j - 2 by omega, List.getElem?_eq_getElem hlt]
            rfl
        · -- the pushed-back cells
          by_cases hjn : j ≤ I.length
          · have hlt : j - 1 < I.length := by omega
            have hHv : z.H = bcode I[j - 1] := by
              rw [hH, hcode, if_neg (by omega), List.getElem?_eq_getElem hlt]; rfl
            have h0 : z.H ≠ 0 := by have := one_le_bcode I[j - 1]; omega
            rw [if_neg h0, List.cons_append, hR, hHv, bdec_bcode,
              List.drop_eq_getElem_cons hlt, Nat.sub_add_cancel hj0]
          · have h0 : z.H = 0 := by
              rw [hH, hcode, if_neg (by omega), List.getElem?_eq_none (by omega)]; rfl
            rw [if_pos h0, hR, List.drop_eq_nil_of_le (by omega),
              List.drop_eq_nil_of_le (by omega)]

/-! #### Work tapes -/

/-- The tape after an optional write at `pos`. -/
def writeCell (tape : ℤ → Option Bool) (pos : ℤ) : Option (Option Bool) → ℤ → Option Bool
  | none => tape
  | some s => Function.update tape pos s

omit [Finite State] in
theorem apply_workTapes {I : List Bool} (a : Action k Bool State) (cfg : Cfg k Bool State I)
    (i : Fin k) :
    (a.apply cfg).workTapes i =
      writeCell (cfg.workTapes i) (cfg.workTapePos i) (a.workTapes i).1 := by
  simp only [Action.apply]
  split <;> simp_all [writeCell]

omit [Finite State] in
theorem apply_workTapePos {I : List Bool} (a : Action k Bool State) (cfg : Cfg k Bool State I)
    (i : Fin k) :
    (a.apply cfg).workTapePos i = cfg.workTapePos i + (a.workTapes i).2 := rfl

theorem symCode_getD_ws (T : ℕ) (tape : ℤ → Option Bool) (pos : ℤ)
    (hT : TapeRel T tape pos) (wo : Option (Option Bool)) :
    [T.unpair.2.unpair.1, 0, 1, 2].getD (wsCode wo) 0 =
      symCode (writeCell tape pos wo pos) := by
  rcases wo with _ | _ | _ | _
  · have := (hT 0).1
    simpa [wsCode, writeCell] using this
  · simp [wsCode, symCode, writeCell]
  · simp [wsCode, symCode, bcode_false, writeCell]
  · simp [wsCode, symCode, bcode_true, writeCell]

theorem update_tape_ne (tape : ℤ → Option Bool) (pos x : ℤ) (h : x ≠ pos)
    (wo : Option (Option Bool)) :
    writeCell tape pos wo x = tape x := by
  cases wo with
  | none => rfl
  | some s => exact Function.update_of_ne h _ _

/-- **The encoded tape tracks one work-tape action.** -/
theorem tapeRel_update {T : ℕ} {tape : ℤ → Option Bool} {pos : ℤ} (hT : TapeRel T tape pos)
    (wo : Option (Option Bool)) (mv : SignType) :
    TapeRel (tapeUpdN T (Nat.pair (wsCode wo) (mvCode mv))) (writeCell tape pos wo) (pos + mv) := by
  set tape' := writeCell tape pos wo with htape'
  have hs := symCode_getD_ws T tape pos hT wo
  rw [← htape'] at hs
  have hne : ∀ x, x ≠ pos → tape' x = tape x := fun x hx => update_tape_ne tape pos x hx wo
  set s' := [T.unpair.2.unpair.1, 0, 1, 2].getD (wsCode wo) 0 with hs'
  have hR : ∀ i : ℕ, sget T.unpair.2.unpair.2 i = symCode (tape' (pos + (i + 1 : ℕ))) := by
    intro i
    rw [← sget_succ, (hT (i + 1)).1, hne _ (by omega)]
  have hL : ∀ i : ℕ, sget T.unpair.1 i = symCode (tape' (pos - 1 - i)) := by
    intro i
    rw [(hT i).2, hne _ (by omega)]
  have hL2 : ∀ i : ℕ, sget T.unpair.1.unpair.2 i = symCode (tape' (pos - 1 - (i + 1 : ℕ))) := by
    intro i
    rw [← sget_succ, hL]
  cases mv with
  | zero =>
      intro i
      simp only [tapeUpdN, mvCode, Nat.unpair_pair, ← hs', signType_cast_zero, add_zero]
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.unpair_pair]
      refine ⟨?_, hL i⟩
      cases i with
      | zero => simpa using hs
      | succ i => rw [sget_pair_succ, hR]
  | pos =>
      intro i
      simp only [tapeUpdN, mvCode, Nat.unpair_pair, ← hs', signType_cast_pos]
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.unpair_pair]
      refine ⟨?_, ?_⟩
      · rw [hR]; exact congrArg (fun x => symCode (tape' x)) (by omega)
      · cases i with
        | zero => simpa using hs
        | succ i => rw [sget_pair_succ, hL]; exact congrArg (fun x => symCode (tape' x)) (by omega)
  | neg =>
      intro i
      simp only [tapeUpdN, mvCode, Nat.unpair_pair, ← hs', signType_cast_neg]
      simp only [List.getD_cons_zero, Nat.unpair_pair]
      refine ⟨?_, ?_⟩
      · rcases i with _ | _ | i
        · rw [sget_pair_zero, ← sget_zero, hL]
          exact congrArg (fun x => symCode (tape' x)) (by omega)
        · rw [sget_pair_succ, sget_pair_zero, hs]
          exact congrArg (fun x => symCode (tape' x)) (by omega)
        · rw [sget_pair_succ, sget_pair_succ, hR]
          exact congrArg (fun x => symCode (tape' x)) (by omega)
      · rw [hL2]; exact congrArg (fun x => symCode (tape' x)) (by omega)

/-! #### Output -/

theorem oupdN_encOut (out : List Bool) (o : Option Bool) :
    oupdN (encOut out) (symCode o) = encOut (out ++ o.toList) := by
  rcases o with _ | _ | _
  · simp [oupdN, symCode, encOut]
  · simp [oupdN, symCode, encOut, bcode_false]
  · simp [oupdN, symCode, encOut, bcode_true]

/-! #### One step -/

/-- The action a configuration takes: the transition for a running configuration, the no-op for
a halted one. -/
noncomputable def cfgAct {I : List Bool} (M : MultiTapeTM k Bool State) (cfg : Cfg k Bool State I) :
    Action k Bool State :=
  match cfg.state with
  | none => noopAct
  | some q => M.tr q cfg.inputSymbol cfg.workTapeSymbols

theorem moveInputPos_zero {n : ℕ} (pos : Fin (n + 2)) : moveInputPos pos 0 = pos :=
  Fin.ext (moveInputPos_val pos .zero)

omit [Finite State] in
theorem noopAct_apply {I : List Bool} (cfg : Cfg k Bool State I) (h : cfg.state = none) :
    (noopAct : Action k Bool State).apply cfg = cfg := by
  cases cfg with
  | mk st ip wt wp out =>
      simp only at h
      subst h
      simp [Action.apply, noopAct, moveInputPos_zero]

omit [Finite State] in
theorem step_eq_apply {I : List Bool} (M : MultiTapeTM k Bool State) (cfg : Cfg k Bool State I) :
    M.step cfg = (cfgAct M cfg).apply cfg := by
  unfold cfgAct
  cases h : cfg.state with
  | some q => exact M.step_of_state_some h
  | none => rw [M.step_of_state_none h, noopAct_apply cfg h]

theorem stCode_some_ne_zero (q : State) : stCode (some q) ≠ 0 := by simp [stCode]

/-- **One step preserves the simulation relation**: applying the encoded action `a` to an
encoding of `cfg` encodes `a.apply cfg`. -/
theorem simRel_apply {I : List Bool} {cfg : Cfg k Bool State I} {z : Zip} {Ts : Fin k → ℕ}
    (a : Action k Bool State) (hz : ZRel z I cfg.inputPos.val)
    (hT : ∀ i, TapeRel (Ts i) (cfg.workTapes i) (cfg.workTapePos i)) :
    SimRel (encE (stCode a.state) (z.move a.inputTape).enc
        (wenc k (fun i => tapeUpdN (Ts i) (waEnc a i)))
        (oupdN (encOut cfg.output) (symCode a.output)))
      (a.apply cfg) := by
  refine ⟨z.move a.inputTape, fun i => tapeUpdN (Ts i) (waEnc a i), ?_, ?_, ?_⟩
  · simp only [Action.apply, oupdN_encOut]
  · have hj : cfg.inputPos.val ≤ I.length + 1 := by have := cfg.inputPos.isLt; omega
    simp only [Action.apply]
    rw [moveInputPos_val]
    cases a.inputTape <;> exact zrel_move hz hj _
  · intro i
    have h := tapeRel_update (hT i) (a.workTapes i).1 (a.workTapes i).2
    rw [apply_workTapes, apply_workTapePos]
    exact h

/-! ### The step code -/

theorem pair_le_pair {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nat.pair a b ≤ Nat.pair a' b' := by
  have h1 : Nat.pair a b ≤ Nat.pair a' b := by
    rcases ha.lt_or_eq with h | h
    · exact (Nat.pair_lt_pair_left b h).le
    · rw [h]
  have h2 : Nat.pair a' b ≤ Nat.pair a' b' := by
    rcases hb.lt_or_eq with h | h
    · exact (Nat.pair_lt_pair_right a' h).le
    · rw [h]
  exact h1.trans h2

theorem wenc_mono : ∀ (k : ℕ) (f g : Fin k → ℕ), (∀ i, f i ≤ g i) → wenc k f ≤ wenc k g
  | 0, _, _, _ => le_rfl
  | k + 1, _, _, h => pair_le_pair (h 0) (wenc_mono k _ _ (fun i => h i.succ))

/-- An upper bound on the keys of encoded configurations. -/
noncomputable def keyBound (k : ℕ) (State : Type*) [Finite State] : ℕ :=
  Nat.pair (Nat.card State) (Nat.pair 3 (wenc k (fun _ => 2)))

/-- The transition table as a code: a multiplexer over the table entries, selected by the key.
Irreducible, so that no tactic tries to evaluate the (very large) table. -/
noncomputable irreducible_def tblCode (M : MultiTapeTM k Bool State) : Code :=
  mux ((List.range (keyBound k State + 1)).map (fun i => Code.const (tableF M i))) Code.id

theorem tbl_spec (M : MultiTapeTM k Bool State) : ∃ B, ∀ key, key ≤ keyBound k State →
    RunsLe (tblCode M) key (tableF M key) B := by
  set K := keyBound k State + 1 with hK
  set Bc := ∑ i ∈ Finset.range K, (2 * tableF M i + 1) with hBc
  refine ⟨3 + K * (Bc + 1) + 6 * K + 10, fun key hkey => ?_⟩
  have hall : ∀ c ∈ (List.range K).map (fun i => Code.const (tableF M i)), Halts c key Bc := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    refine ((runsLe_const (tableF M i) key).mono ?_).halts
    exact Finset.single_le_sum (f := fun i => 2 * tableF M i + 1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (List.mem_range.mp hi))
  have hsel : ((List.range K).map (fun i => Code.const (tableF M i)))[key]? =
      some (Code.const (tableF M key)) := by
    simp [List.getElem?_range (by omega : key < K)]
  have hw := (runsLe_const (tableF M key) key).mono
    (Finset.single_le_sum (f := fun i => 2 * tableF M i + 1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : key < K)))
  rw [tblCode_def]
  exact (mux_spec (runsLe_id key) hall hsel hw).mono (by simp)

/-- The key `pair q (pair H S)` of an encoded configuration: state code, input cell code, and the
work-tape cell codes. -/
def keyCode (k : ℕ) : Code :=
  .pair .left (.pair (pth [true, false, false]) (.comp (symsCode k) (pth [true, true, false])))

theorem key_spec (k : ℕ) : ∃ B, ∀ (q OP : ℕ) (z : Zip) (Ts : Fin k → ℕ),
    RunsLe (keyCode k) (encE q z.enc (wenc k Ts) OP)
      (Nat.pair q (Nat.pair z.H (wenc k (fun i => (Ts i).unpair.2.unpair.1)))) B := by
  obtain ⟨Bs, hs⟩ := syms_spec k
  refine ⟨Bs + 30, fun q OP z Ts => ?_⟩
  have e : encE q z.enc (wenc k Ts) OP = Nat.pair q (Nat.pair (Nat.pair z.H
      (Nat.pair (bstk z.Ls) (encRS z.Rb z.md z.P z.Y))) (Nat.pair (wenc k Ts) OP)) := rfl
  rw [e]
  have hl := runsLe_left (Nat.pair q (Nat.pair (Nat.pair z.H
      (Nat.pair (bstk z.Ls) (encRS z.Rb z.md z.P z.Y))) (Nat.pair (wenc k Ts) OP)))
  have h1 := pth_spec [true, false, false] (Nat.pair q (Nat.pair (Nat.pair z.H
      (Nat.pair (bstk z.Ls) (encRS z.Rb z.md z.P z.Y))) (Nat.pair (wenc k Ts) OP)))
  have h2 := pth_spec [true, true, false] (Nat.pair q (Nat.pair (Nat.pair z.H
      (Nat.pair (bstk z.Ls) (encRS z.Rb z.md z.P z.Y))) (Nat.pair (wenc k Ts) OP)))
  simp only [Nat.unpair_pair, pathVal_cons_true, pathVal_cons_false, pathVal_nil,
    List.length_cons, List.length_nil] at hl h1 h2
  exact (hl.pair (h1.pair (h2.comp (hs Ts)))).mono (by omega)

/-- **One machine step** as a code on encoded configurations. -/
noncomputable def stepCode (M : MultiTapeTM k Bool State) : Code :=
  .comp (newECode k) (.pair Code.id (.comp (tblCode M) (keyCode k)))

theorem decAct_eq {I : List Bool} (M : MultiTapeTM k Bool State) {cfg : Cfg k Bool State I}
    {z : Zip} {Ts : Fin k → ℕ} (hz : ZRel z I cfg.inputPos.val)
    (hT : ∀ i, TapeRel (Ts i) (cfg.workTapes i) (cfg.workTapePos i)) :
    decAct M (Nat.pair (stCode cfg.state)
        (Nat.pair z.H (wenc k (fun i => (Ts i).unpair.2.unpair.1))))
      = cfgAct M cfg := by
  have h1 : symDec z.H = cfg.inputSymbol := by
    rw [hz.2.2.1, hcode, Cfg.inputSymbol]
    split_ifs
    · rfl
    · exact symDec_symCode _
  have h2 : (fun i : Fin k => symDec (sget (wenc k (fun i => (Ts i).unpair.2.unpair.1)) (i : ℕ)))
      = cfg.workTapeSymbols := by
    funext i
    rw [sget_wenc, ← sget_zero, ((hT i) 0).1]
    simp [Cfg.workTapeSymbols]
  unfold decAct cfgAct
  simp only [Nat.unpair_pair, stDec_stCode]
  rcases cfg.state with _ | q
  · rfl
  · simp only [h1, h2]

theorem key_le {I : List Bool} {cfg : Cfg k Bool State I} {z : Zip} {Ts : Fin k → ℕ}
    (hz : ZRel z I cfg.inputPos.val)
    (hT : ∀ i, TapeRel (Ts i) (cfg.workTapes i) (cfg.workTapePos i)) :
    Nat.pair (stCode cfg.state) (Nat.pair z.H (wenc k (fun i => (Ts i).unpair.2.unpair.1)))
      ≤ keyBound k State := by
  refine pair_le_pair (stCode_le _) (pair_le_pair ?_ (wenc_mono k _ _ (fun i => ?_)))
  · rw [hz.2.2.1]; exact hcode_le I _
  · rw [← sget_zero, ((hT i) 0).1]; exact symCode_le _

/-- **One step in constant time.** -/
theorem step_spec (M : MultiTapeTM k Bool State) : ∃ B, ∀ (I : List Bool) (E : ℕ)
    (cfg : Cfg k Bool State I), SimRel E cfg →
    ∃ E', RunsLe (stepCode M) E E' B ∧ SimRel E' (M.step cfg) := by
  obtain ⟨Bk, hk⟩ := key_spec k
  obtain ⟨Bt, ht⟩ := tbl_spec M
  obtain ⟨Bn, hn⟩ := newE_spec k
  refine ⟨Bk + Bt + Bn + 10, fun I E cfg hsim => ?_⟩
  obtain ⟨z, Ts, rfl, hz, hT⟩ := hsim
  set a := cfgAct M cfg with ha
  have hkey := hk (stCode cfg.state) (encOut cfg.output) z Ts
  have htab := ht _ (key_le hz hT)
  rw [tableF, decAct_eq M hz hT, ← ha] at htab
  have hx := (runsLe_id _).pair (hkey.comp htab)
  have hA : ∀ i, (waEnc a i).unpair.1 ≤ 3 ∧ (waEnc a i).unpair.2 ≤ 2 := fun i => by
    simp only [waEnc, Nat.unpair_pair]
    exact ⟨wsCode_le _, mvCode_le_two _⟩
  have hnew := hn (stCode cfg.state) (stCode a.state) (symCode a.output) (encOut cfg.output) z
    a.inputTape Ts (waEnc a) hz.1 (by rw [hz.2.2.1]; exact hcode_le I _) (symCode_le _) hA
  refine ⟨_, (hx.comp hnew).mono (by omega), ?_⟩
  rw [step_eq_apply, ← ha]
  exact simRel_apply a hz hT

/-! ### Iteration, initialization, and the doubling search -/

/-- Run the step code `m` times, on `pair E m`. -/
noncomputable def iterCode (M : MultiTapeTM k Bool State) : Code :=
  .prec Code.id (.comp (stepCode M) (pth [true, true]))

theorem iter_spec (M : MultiTapeTM k Bool State) : ∃ B, ∀ (I : List Bool) (E : ℕ)
    (cfg : Cfg k Bool State I), SimRel E cfg → ∀ m,
    ∃ E', RunsLe (iterCode M) (Nat.pair E m) E' (B * m + 4) ∧ SimRel E' (M.runFrom cfg m) := by
  obtain ⟨Bs, hs⟩ := step_spec M
  refine ⟨Bs + 9, fun I E cfg hsim m => ?_⟩
  refine prec_iter (B0 := 3) (fun j v => SimRel v (M.runFrom cfg j)) (fun _ => Bs + 8)
    (fun m => (Bs + 9) * m + 4) ⟨E, runsLe_id E, hsim⟩ (fun j v hv => ?_) (by omega)
    (fun j => by rw [Nat.mul_succ]; omega) m
  obtain ⟨v', hv', hP⟩ := hs I v _ hv
  have hp := pth_spec [true, true] (Nat.pair E (Nat.pair j v))
  simp only [pathVal_cons_true, pathVal_nil, List.length_cons, List.length_nil] at hp
  refine ⟨v', (hp.comp hv').mono (by omega), ?_⟩
  rw [MultiTapeTM.runFrom, Function.iterate_succ_apply']
  exact hP

/-- The input zipper before the first move: head on the left boundary blank. -/
def zpre (p y : List Bool) : Zip := ⟨3, [], [], 0, p, y⟩

/-- The initial configuration, encoded from `encode (p, y)`. -/
noncomputable def initCode (M : MultiTapeTM k Bool State) : Code :=
  .pair (Code.const (stCode (some M.q₀)))
    (.pair (.comp zmoveCode (.pair (.pair (Code.const 3) (.pair .zero (.pair .zero
      (.pair .zero Code.id)))) (Code.const 2))) (.pair .zero .zero))

theorem encOut_nil : encOut [] = 0 := rfl

omit [Finite State] in
theorem zrel_zpre (p y : List Bool) : ZRel (zpre p y) (frame p ++ y) 0 := by
  refine ⟨by simp [zpre], by simp [zpre], by simp [zpre, hcode], ?_⟩
  simp [zpre, genList, frame]

theorem init_spec (M : MultiTapeTM k Bool State) : ∃ B, ∀ p y : List Bool,
    ∃ E, RunsLe (initCode M) (Nat.pair (enc p) (enc y)) E B ∧
      SimRel E (M.initCfg (frame p ++ y)) := by
  obtain ⟨Bz, hz⟩ := zmove_spec
  refine ⟨2 * stCode (some M.q₀) + Bz + 40, fun p y => ?_⟩
  set N := Nat.pair (enc p) (enc y)
  have hpre : RunsLe (.pair (Code.const 3) (.pair .zero (.pair .zero (.pair .zero Code.id)))) N
      (zpre p y).enc 20 := by
    have := (runsLe_const 3 N).pair ((runsLe_zero N).pair ((runsLe_zero N).pair
      ((runsLe_zero N).pair (runsLe_id N))))
    exact this.of_eq (by simp [zpre, Zip.enc, encRS, encG, N]) (by norm_num)
  have hmv := (hpre.pair (runsLe_const 2 N)).comp
    (hz (zpre p y) .pos (by simp [zpre]) (by simp [zpre]))
  have := (runsLe_const (stCode (some M.q₀)) N).pair (hmv.pair ((runsLe_zero N).pair
    (runsLe_zero N)))
  refine ⟨_, this.mono (by omega), (zpre p y).move .pos, fun _ => 0, ?_, ?_, ?_⟩
  · simp [encE, MultiTapeTM.initCfg, wenc_zero, encOut_nil]
  · have := zrel_move (zrel_zpre p y) (by omega) .pos
    simpa [MultiTapeTM.initCfg] using this
  · intro i i'
    simp [MultiTapeTM.initCfg, symCode]

/-- Trial `j` of the search: the state code after `2 ^ j` steps, on `pair (encode (p, y)) j`. -/
noncomputable def testCode (M : MultiTapeTM k Bool State) : Code :=
  .comp .left (.comp (iterCode M) (.pair (.comp (initCode M) .left) (.comp pow2 .right)))

theorem simRel_left {I : List Bool} {E : ℕ} {cfg : Cfg k Bool State I} (h : SimRel E cfg) :
    E.unpair.1 = stCode cfg.state := by
  obtain ⟨z, Ts, rfl, -, -⟩ := h
  simp [encE]

theorem simRel_out {I : List Bool} {E : ℕ} {cfg : Cfg k Bool State I} (h : SimRel E cfg) :
    pathVal [true, true, true] E = encOut cfg.output := by
  obtain ⟨z, Ts, rfl, -, -⟩ := h
  simp [encE]

theorem test_spec (M : MultiTapeTM k Bool State) : ∃ A B, ∀ (p y : List Bool) (j : ℕ),
    RunsLe (testCode M) (Nat.pair (Nat.pair (enc p) (enc y)) j)
      (stCode (M.runFrom (M.initCfg (frame p ++ y)) (2 ^ j)).state) (A * 2 ^ j + B) := by
  obtain ⟨Bi, hi⟩ := init_spec M
  obtain ⟨Bit, hit⟩ := iter_spec M
  refine ⟨Bit + 27, Bi + 20, fun p y j => ?_⟩
  obtain ⟨E0, hE0, hsim0⟩ := hi p y
  obtain ⟨E', hE', hsim'⟩ := hit _ E0 _ hsim0 (2 ^ j)
  have hl : RunsLe .left (Nat.pair (Nat.pair (enc p) (enc y)) j) (Nat.pair (enc p) (enc y)) 1 := by
    simpa using runsLe_left (Nat.pair (Nat.pair (enc p) (enc y)) j)
  have hr : RunsLe .right (Nat.pair (Nat.pair (enc p) (enc y)) j) j 1 := by
    simpa using runsLe_right (Nat.pair (Nat.pair (enc p) (enc y)) j)
  have := ((((hl.comp hE0).pair (hr.comp (pow2_spec j))).comp hE').comp (runsLe_left E'))
  rw [simRel_left hsim'] at this
  refine this.mono ?_
  nlinarith

/-! ### Decoding the output -/

/-- Convert the output buffer `pair O n` to the list encoding of the output. -/
def convCode : Code :=
  .comp .right (.prec (.pair Code.id .zero)
    (.pair (pth [true, true, false, true])
      (.comp .succ (.pair (pth [true, true, false, false]) (pth [true, true, true])))))

theorem conv_spec (out : List Bool) :
    RunsLe convCode (encOut out) (Encodable.encode out) (36 * out.length + 8) := by
  unfold convCode
  set r := out.reverse with hr
  have hloop := prec_iter (cf := .pair Code.id .zero)
    (cg := .pair (pth [true, true, false, true])
      (.comp .succ (.pair (pth [true, true, false, false]) (pth [true, true, true]))))
    (a := pairStack (r.map Encodable.encode)) (B0 := 5)
    (fun j v => j ≤ out.length →
      v = Nat.pair (pairStack ((r.drop j).map Encodable.encode))
        (Encodable.encode ((r.take j).reverse)))
    (fun _ => 35) (fun m => 36 * m + 6)
    ⟨_, (runsLe_id _).pair (runsLe_zero _), fun _ => by simp⟩
    (fun j v hv => ?_) (by omega) (fun j => by omega) out.length
  · obtain ⟨v, hv, hP⟩ := hloop
    have hv' := hP le_rfl
    have hlen : r.length = out.length := by simp [hr]
    rw [List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega), hr,
      List.reverse_reverse] at hv'
    have := hv.comp (runsLe_right v)
    rw [hv'] at this
    simpa [encOut, hr] using this.mono (by omega)
  · have hrun := (pth_spec [true, true, false, true]
        (Nat.pair (pairStack (r.map Encodable.encode)) (Nat.pair j v))).pair
      (((pth_spec [true, true, false, false] _).pair (pth_spec [true, true, true] _)).comp
        (runsLe_succ _))
    refine ⟨_, hrun.mono (by simp), fun hj => ?_⟩
    have hlt : j < r.length := by simp [hr]; omega
    rw [hv (by omega)]
    simp only [pathVal_cons_true, pathVal_cons_false, pathVal_nil]
    rw [List.drop_eq_getElem_cons hlt]
    simp only [List.map_cons, pairStack_cons, pathVal_single_true, pathVal_single_false,
      Nat.unpair_pair]
    simp only [List.take_add_one,
      List.getElem?_eq_getElem hlt, Option.toList_some, List.reverse_append, List.reverse_singleton,
      List.singleton_append, Encodable.encode_list_cons]

end TMSim

end TimedKt
