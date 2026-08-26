/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.Trace
import Mathlib.Order.Lattice.Nat

/-!
# The Fuel Cost, and Its Divergence from Computational Work

The obvious first candidate for a runtime notion over `Nat.Partrec.Code` is Mathlib's
own evaluation bound: price a computation by its least `Code.evaln` fuel. That fuel
is a value-magnitude quantity, not a transition count: `Code.evaln_bound` (the
`guard (n ≤ k)`) forces the fuel past the input value at every node, so a fuel-priced
measure charges for the magnitude of values rather than for work performed. This
module defines the least-fuel cost `minFuel` together with the theorem that separates
it from the write ledger.

## Main results

* `fuel_exceeds_writes_unboundedly`: for every bound `M` there is a computation that
  commits exactly one write yet needs fuel at least `M`. This is the divergence theorem
  recording why the fuel-priced measure was replaced: the public `Kt` of this package
  prices operational transitions (`TimedKt.Run`) instead.
-/

open Nat.Partrec

namespace TimedKt

/-- The set of fuels `r` for which `c` produces `x` from `input` within `r` stages. -/
def fuelsFor (c : Code) (input x : ℕ) : Set ℕ :=
  {r | Code.evaln r c input = some x}

/-- A produced output gives a nonempty fuel set. -/
theorem fuelsFor_nonempty_of_eval {c : Code} {input x : ℕ}
    (h : Code.eval c input = Part.some x) : (fuelsFor c input x).Nonempty := by
  obtain ⟨k, hk⟩ := Code.evaln_complete.mp (Part.eq_some_iff.mp h)
  exact ⟨k, hk⟩

/-- A witnessing fuel gives a nonempty fuel set. -/
theorem fuelsFor_nonempty_of_evaln {c : Code} {input x r : ℕ}
    (h : Code.evaln r c input = some x) : (fuelsFor c input x).Nonempty :=
  ⟨r, h⟩

open Classical in
/-- The **least fuel**: the least `r` with `Code.evaln r c input = some x`, or `⊤` if
no such `r` exists. A value-magnitude quantity, not a transition count; see the module
documentation. -/
noncomputable def minFuel (c : Code) (input x : ℕ) : ℕ∞ :=
  if _h : (fuelsFor c input x).Nonempty then
    ((sInf (fuelsFor c input x) : ℕ) : ℕ∞)
  else ⊤

/-- When `c` produces `x`, the least fuel is finite. -/
theorem minFuel_of_evaln {c : Code} {input x r : ℕ}
    (h : Code.evaln r c input = some x) :
    minFuel c input x = ((sInf (fuelsFor c input x) : ℕ) : ℕ∞) := by
  classical
  rw [minFuel, dif_pos (fuelsFor_nonempty_of_evaln h)]

/-- The least fuel actually produces `x`. -/
theorem evaln_sInf_fuels {c : Code} {input x : ℕ}
    (hne : (fuelsFor c input x).Nonempty) :
    Code.evaln (sInf (fuelsFor c input x)) c input = some x :=
  Nat.sInf_mem hne

/-- The least fuel is at most any witnessing fuel. -/
theorem minFuel_le_of_evaln {c : Code} {input x r : ℕ}
    (h : Code.evaln r c input = some x) :
    minFuel c input x ≤ (r : ℕ∞) := by
  rw [minFuel_of_evaln h]
  exact_mod_cast Nat.sInf_le h

/-! ### Fuel diverges from writes -/

/-- `Code.succ` on input `N` produces `N + 1` at fuel exactly `N + 1` and no less: the
fuel is the value-magnitude reading floor. -/
theorem minFuel_succ (N : ℕ) :
    minFuel Code.succ N (Nat.succ N) = ((N + 1 : ℕ) : ℕ∞) := by
  have hev : Code.evaln (N + 1) Code.succ N = some (Nat.succ N) := by simp [Code.evaln]
  have hle : minFuel Code.succ N (Nat.succ N) ≤ ((N + 1 : ℕ) : ℕ∞) :=
    minFuel_le_of_evaln hev
  have hne : (fuelsFor Code.succ N (Nat.succ N)).Nonempty :=
    fuelsFor_nonempty_of_evaln hev
  have hmem : Code.evaln (sInf (fuelsFor Code.succ N (Nat.succ N))) Code.succ N
      = some (Nat.succ N) := evaln_sInf_fuels hne
  have hb : N < sInf (fuelsFor Code.succ N (Nat.succ N)) :=
    Code.evaln_bound (Option.mem_def.mpr hmem)
  have hge : ((N + 1 : ℕ) : ℕ∞) ≤ minFuel Code.succ N (Nat.succ N) := by
    rw [minFuel_of_evaln hev]; exact_mod_cast hb
  exact le_antisymm hle hge

/-- **Fuel exceeds writes unboundedly.** For every bound `M` there is a computation
that commits exactly one write yet has fuel cost at least `M`: the fuel measure is not
a faithful account of computational work. -/
theorem fuel_exceeds_writes_unboundedly :
    ∀ M : ℕ, ∃ (c : Code) (input x : ℕ),
      numWrites c input = 1 ∧ (M : ℕ∞) ≤ minFuel c input x := by
  intro M
  refine ⟨Code.succ, M, Nat.succ M, numWrites_succ M, ?_⟩
  rw [minFuel_succ M]
  exact_mod_cast Nat.le_succ M

end TimedKt
