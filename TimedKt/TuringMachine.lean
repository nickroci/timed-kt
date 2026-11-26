/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import KolmogorovMathlib.Core.Basic
import TimedKt.CeilLog2
import Mathlib.Data.Sign.Defs
import Mathlib.Algebra.Order.Group.Int

/-!
# Multi-Tape Turing Machines and Turing-Machine-Clocked `Kt`

This module fixes a standard Turing-machine model and defines Levin's `Kt` clocked by its
steps, so that the transition clock of this package can be compared with Turing-machine
time (`TimedKt.TMSim`).

## The model

The model is the deterministic multi-tape machine of
[CSLib](https://github.com/leanprover/cslib) (`Cslib/Computability/Machines/Turing/MultiTape`,
after Papadimitriou, *Computational Complexity*, §2.3 and §2.5), the model under the
Turing-machine-clocked `Cslib.Kolmogorov.levinKt` of
[cslib-frontier](https://github.com/cslib-community/cslib-frontier). It is restated here
because that library is on a newer toolchain; the definitions follow it clause by clause:

* a read-only input tape whose head position is `Fin (|input| + 2)`, starting at `1`; positions
  `0` and `|input| + 1` read the blank, and a move beyond them is clamped (`moveInputPos`);
* `k` two-way infinite work tapes `ℤ → Option Symbol` (`none` is the blank), initially blank,
  heads at `0`;
* a write-only output tape (`List Symbol`) to which each step appends at most one symbol;
* one step reads the state and the symbols under the input and work heads, and performs an
  `Action`: move the input head, optionally write and move on each work tape, optionally emit an
  output symbol, and go to the successor state or halt (`state := none`);
* a halted configuration steps to itself.

CSLib presents a deterministic machine as a transition relation with a uniqueness proof and
derives the transition function; here the transition function `tr` is the primitive (CSLib's
`MultiTapeTM.ofTr` is the same construction in the other direction). `Cfg.inputSymbol` is
stated with `getElem?`, which reads the blank at both boundary positions exactly as CSLib's
two-case definition does.

## Turing-machine `Kt`

A program `p` and a condition `y` are presented on the input tape as `frame p ++ y`, where
`frame p` writes each bit of `p` behind a `true` marker and ends with `false`. This is
cslib-frontier's pair encoding `encPair encBits encBits (p, y)` for its conditional `Kt`. For a
fixed machine `M`,

```
tmKt M x y = min { |p| + ⌈log₂ t⌉ : M halts on frame p ++ y after t steps with output x }.
```

The machine is fixed, so this is the textbook `Kt_M`; instantiated at a universal machine it is
Levin's `Kt`. (cslib-frontier's `levinKt` instead reads a machine description from the program
and counts the steps of the described machine.)

## Main definitions

* `TimedKt.TM.MultiTapeTM`, `TimedKt.TM.Cfg`, `TimedKt.TM.Action`: the machine model.
* `TimedKt.TM.MultiTapeTM.step`, `runFrom`, `initCfg`: its semantics.
* `TimedKt.TM.frame`: the self-delimiting encoding of the program.
* `TimedKt.TM.MultiTapeTM.OutputsAt`: halting after `t` steps with a given output.
* `TimedKt.TM.tmKt`, `TimedKt.TM.tmKtPlain`: Turing-machine-clocked conditional and plain `Kt`.
-/

open Kolmogorov

namespace TimedKt

namespace TM

variable {k : ℕ} {Symbol State : Type*}

/-- What a machine does in one step. -/
structure Action (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputTape : SignType
  /-- Actions on the work tapes: optionally a symbol to write (`some none` writes the blank),
  and the head movement. -/
  workTapes : Fin k → Option (Option Symbol) × SignType
  /-- An optional symbol to output. -/
  output : Option Symbol
  /-- The successor state, or `none` to halt. -/
  state : Option State

/-- A configuration on a given input: the state (`none` once halted), the input head position
(shifted by one), the work tapes and their head positions, and the output written so far. -/
structure Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- The state, or `none` for the halting state. -/
  state : Option State
  /-- The position of the input head, shifted by one. -/
  inputPos : Fin (input.length + 2)
  /-- The work tapes. -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- The positions of the work-tape heads. -/
  workTapePos : Fin k → ℤ
  /-- The contents of the write-only output tape. -/
  output : List Symbol

/-- Attempt to move the input head. The head can visit one blank cell on either side of the
input; an attempt to move further does not move it. -/
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : ℤ) + (m : ℤ)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

variable {input : List Symbol}

/-- The symbol under the input head (`none` at both boundary positions). -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if cfg.inputPos.val = 0 then none else input[cfg.inputPos.val - 1]?

/-- The symbol under the head of work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- The effect of an action on a configuration: move the input head, write and move on the work
tapes, append the emitted symbol to the output tape, and go to the successor state. -/
def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList

/-- A deterministic multi-tape Turing machine with `k` work tapes over the alphabet
`Option Symbol` (`none` is the blank), given by its initial state and transition function. -/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- The initial state. -/
  q₀ : State
  /-- The transition function: state, input symbol, work-tape symbols ↦ action. -/
  tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State

namespace MultiTapeTM

variable (tm : MultiTapeTM k Symbol State)

/-- One step. A halted configuration steps to itself. -/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration: initial state, input head on the first input cell, blank work
tapes with heads at `0`, empty output. -/
def initCfg (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some tm.q₀, 1, fun _ _ => none, fun _ => 0, []⟩

/-- The configuration reached after `t` steps. -/
def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input :=
  tm.step^[t] cfg

/-- The machine, started on `input`, has halted after `t` steps with output `x`. -/
def OutputsAt (input x : List Symbol) (t : ℕ) : Prop :=
  (tm.runFrom (tm.initCfg input) t).state = none ∧ (tm.runFrom (tm.initCfg input) t).output = x

theorem step_of_state_none {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  simp [step, h]

theorem step_of_state_some {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) :
    tm.step cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by
  simp [step, h]

/-- Once halted, a machine stays halted with the same configuration. -/
theorem runFrom_of_halted {cfg : Cfg k Symbol State input} (h : cfg.state = none) (t : ℕ) :
    tm.runFrom cfg t = cfg := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih, tm.step_of_state_none h]

/-- Halting is monotone in the number of steps. -/
theorem runFrom_add_of_halted {cfg : Cfg k Symbol State input} {t : ℕ}
    (h : (tm.runFrom cfg t).state = none) (d : ℕ) :
    tm.runFrom cfg (t + d) = tm.runFrom cfg t := by
  rw [runFrom, Nat.add_comm, Function.iterate_add_apply, ← runFrom, ← runFrom,
    tm.runFrom_of_halted h]

/-- The initial configuration is not halted, so a halting run takes at least one step. -/
theorem one_le_of_outputsAt {input x : List Symbol} {t : ℕ} (h : tm.OutputsAt input x t) :
    1 ≤ t := by
  rcases t with _ | t
  · simp [OutputsAt, runFrom, initCfg] at h
  · omega

end MultiTapeTM

/-- The self-delimiting program encoding: each bit behind a `true` marker, then `false`
(cslib-frontier's `Turing.MultiTapeTM.frame`). -/
def frame (w : List Bool) : List Bool :=
  w.flatMap (fun b => [true, b]) ++ [false]

/-- The candidate costs `|p| + ⌈log₂ t⌉` of `M` producing `x` from `y`. -/
def tmKtCandidates (M : MultiTapeTM k Bool State) (x y : BitString) : Set ENat :=
  {n | ∃ p t, M.OutputsAt (frame p ++ y) x t ∧ ((programLength p + ceilLog2 t : ℕ) : ENat) = n}

/-- **Turing-machine-clocked conditional `Kt`** of a fixed binary multi-tape machine `M`:
the least `|p| + ⌈log₂ t⌉` such that `M`, started on `frame p ++ y`, halts after `t` steps
with output `x`; `⊤` if there is none. -/
noncomputable def tmKt (M : MultiTapeTM k Bool State) (x y : BitString) : ENat :=
  sInf (tmKtCandidates M x y)

/-- **Turing-machine-clocked plain `Kt`**: the empty condition. -/
noncomputable def tmKtPlain (M : MultiTapeTM k Bool State) (x : BitString) : ENat :=
  tmKt M x []

end TM

end TimedKt
