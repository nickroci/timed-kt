/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.Kt

/-!
# The Certified Step-Budgeted Evaluator

This module defines `runBounded`, the executable evaluator of the operational
semantics `Run` under a transition budget. Where `tracen` is fueled by value
magnitude (the `Code.evaln` reading floor), `runBounded b c n` charges exactly the
transitions that `Run` charges — one per dispatched `Code` constructor — and returns
the exact write-once trace together with the exact transition count, or `none` when
the run does not fit within `b` transitions.

The recursion is structural on the budget: every node hands the decremented budget to
its sub-runs, and the binary nodes re-check the combined count against the original
budget. Since each sub-count is a summand of the total, a derivation within budget
restricts to derivations of its sub-runs within the decremented budget, which is what
makes the evaluator complete and not merely sound.

## Main results

* `runBounded`: the executable, budget-structural evaluator.
-/

open Nat.Partrec

namespace TimedKt

/-- Every run makes at least one transition: the trace is nonempty and writes never
exceed transitions. -/
theorem Run.one_le_steps {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    1 ≤ s :=
  le_trans h.one_le_length h.length_le_steps

/-- The **step-budgeted evaluator**. `runBounded b c n` mirrors the clauses of `Run`
one for one and returns the write-once trace and the exact transition count of the
evaluation of `c` on `n`, or `none` when the evaluation does not fit within `b`
transitions. Leaves cost `1`; `pair`, `comp`, `prec`-successor and `rfind'`-failure
combine their sub-runs at cost `+1` and re-check the budget; `prec`-at-zero and
`rfind'`-success add `1`, which the decremented budget covers by construction. -/
def runBounded : ℕ → Code → ℕ → Option (List ℕ × ℕ)
  | 0, _, _ => none
  | _ + 1, Code.zero, _ => some ([0], 1)
  | _ + 1, Code.succ, n => some ([Nat.succ n], 1)
  | _ + 1, Code.left, n => some ([n.unpair.1], 1)
  | _ + 1, Code.right, n => some ([n.unpair.2], 1)
  | b + 1, Code.pair cf cg, n => do
      let rf ← runBounded b cf n
      let rg ← runBounded b cg n
      let vf ← rf.1.getLast?
      let vg ← rg.1.getLast?
      guard (rf.2 + rg.2 + 1 ≤ b + 1)
      pure (rf.1 ++ rg.1 ++ [Nat.pair vf vg], rf.2 + rg.2 + 1)
  | b + 1, Code.comp cf cg, n => do
      let rg ← runBounded b cg n
      let vg ← rg.1.getLast?
      let rf ← runBounded b cf vg
      guard (rf.2 + rg.2 + 1 ≤ b + 1)
      pure (rg.1 ++ rf.1, rf.2 + rg.2 + 1)
  | b + 1, Code.prec cf cg, n =>
      n.unpaired fun a m =>
        m.casesOn
          (do
            let rf ← runBounded b cf a
            pure (rf.1, rf.2 + 1))
          fun y => do
            let ri ← runBounded b (Code.prec cf cg) (Nat.pair a y)
            let vi ← ri.1.getLast?
            let rg ← runBounded b cg (Nat.pair a (Nat.pair y vi))
            guard (ri.2 + rg.2 + 1 ≤ b + 1)
            pure (ri.1 ++ rg.1, ri.2 + rg.2 + 1)
  | b + 1, Code.rfind' cf, n =>
      n.unpaired fun a m => do
        let rx ← runBounded b cf (Nat.pair a m)
        let x ← rx.1.getLast?
        if x = 0 then
          pure (rx.1 ++ [m], rx.2 + 1)
        else do
          let rr ← runBounded b (Code.rfind' cf) (Nat.pair a (m + 1))
          guard (rx.2 + rr.2 + 1 ≤ b + 1)
          pure (rx.1 ++ rr.1, rx.2 + rr.2 + 1)

end TimedKt
