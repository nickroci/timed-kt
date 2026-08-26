/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.FuelCost
import TimedKt.Kt

/-!
# Validation Examples

Concrete transition counts for the basic code shapes — constants, successor,
composition, primitive recursion, and search — and the comparison that motivated the
timed measure: the successor's native transition cost is the constant `1`, while its
legacy `evaln` fuel is `N + 1`, linear in the input's magnitude.

This module is the only place the public theory and the legacy fuel measure meet, and
they meet only to be compared.
-/

open Nat.Partrec

namespace TimedKt

/-! ### Basic code shapes, with exact transition counts -/

/-- Constant zero: one transition. -/
example (n : ℕ) : Run Code.zero n [0] 1 := Run.zero n

/-- Successor: one transition, for every input. -/
example (n : ℕ) : Run Code.succ n [Nat.succ n] 1 := Run.succ n

/-- Composition: three transitions for two successors and the `comp` node. -/
example : Run (Code.comp Code.succ Code.succ) 0 [1, 2] 3 :=
  Run.comp (Run.succ 0) rfl (Run.succ 1)

/-- Primitive recursion: the counting loop makes exactly `2 * m + 2` transitions and
`m + 1` writes (`run_precLoop`). -/
example (a m : ℕ) :
    ∃ T, Run (Code.prec Code.zero Code.succ) (Nat.pair a m) T (2 * m + 2) ∧
      T.length = m + 1 :=
  run_precLoop a m

/-- Search: an `rfind'` that succeeds on its first trial makes two transitions. -/
example : Run (Code.rfind' Code.left) (Nat.pair 0 0) [0, 0] 2 := by
  have h : Run Code.left (Nat.pair 0 0) [0] 1 := by
    have hl := Run.left (Nat.pair 0 0)
    simpa using hl
  exact Run.rfindFound h rfl

/-! ### Native transitions versus legacy fuel

The check required of the corrected measure: the successor has constant native
transition cost even though its `evaln` fuel is input-magnitude dependent. -/

/-- The successor's transition count is the constant `1`. -/
theorem numSteps_succ (n : ℕ) : numSteps Code.succ n = 1 :=
  numSteps_eq_of_run (Run.succ n)

/-- The successor: one transition and one write for every input, yet fuel `N + 1`.
The two cost scales separate on the simplest possible code. -/
theorem succ_transitions_constant_fuel_linear (N : ℕ) :
    numSteps Code.succ N = 1 ∧ minFuel Code.succ N (Nat.succ N) = ((N + 1 : ℕ) : ℕ∞) :=
  ⟨numSteps_succ N, minFuel_succ N⟩

/-- The write and transition ledgers of the counting loop: `m + 1` writes against
`2 * m + 2` transitions. The two operational ledgers differ, but only linearly
(`Run.sandwich`) — unlike fuel, which separates from both unboundedly. -/
theorem precLoop_ledgers (a m : ℕ) :
    numWrites (Code.prec Code.zero Code.succ) (Nat.pair a m) = ((m + 1 : ℕ) : ℕ∞) ∧
      numSteps (Code.prec Code.zero Code.succ) (Nat.pair a m) = ((2 * m + 2 : ℕ) : ℕ∞) := by
  obtain ⟨T, hT, hlen⟩ := run_precLoop a m
  constructor
  · rw [numWrites_of_run hT, hlen]
  · exact numSteps_eq_of_run hT

end TimedKt
