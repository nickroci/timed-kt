/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/

import KolmogorovMathlib.Prefix.ConditionalSymmetry

/-!
# Static Direction-Independence of Information

This file records the proved, untimed theorem that motivates the proposed
write-once law in the `irreducibility` project.

For an optimal conditional prefix machine, define the information in the
direction `x then y` by

    K(x) + K(y | x, K(x)).

Prefix symmetry of information says that this differs by only a machine
constant from `K(x,y)`.  Since pair complexity is invariant under swapping its
coordinates up to a machine constant, the two directional decompositions

    K(x) + K(y | x, K(x))
    K(y) + K(x | y, K(y))

are within one uniform additive constant of one another.

This is a theorem about static description length.  It does **not** mention
runtime, a write-once trace, or the amount of information committed while a
program runs.  The resource-sensitive lift is therefore kept as an explicit
open proposition in `Irreducibility.IntrinsicTapeSymmetry`, rather than being
silently inferred from this theorem.

Uses only the Lean/Mathlib baseline assumptions and contains no proof holes.
-/

open Nat.Partrec Kolmogorov

namespace TimedKt

/-- The prefix-information decomposition in the direction `x` then `y`.

The witness `kx` is required to be the actual finite value of `K(x)`.  It is
included in the conditional context because that is the exact prefix-free
symmetry-of-information theorem; it is mathematical context, not a
cutoff-dependent advice string. -/
noncomputable def prefixDirectionalInformation
    (U : Map) (x y : BitString) (kx : ℕ) : ENat :=
  KPPlain U x + KP U y (prefixComplexityContext x kx)

/-- **Static information has no preferred direction.**

For one optimal conditional prefix machine, the `x then y` and `y then x`
decompositions differ by at most one machine-dependent additive constant,
uniformly over all finite strings.  Both inequalities are stated because
`ENat` has no subtraction operation suitable for writing an absolute
difference.

This packages the fully proved upstream prefix symmetry-of-information theorem
and the `O(1)` symmetry of pair encoding. -/
theorem prefixDirectionalInformation_directionIndependent
    (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y : BitString, ∀ kx ky : ℕ,
      HasPrefixComplexityValue U x kx →
      HasPrefixComplexityValue U y ky →
        prefixDirectionalInformation U x y kx ≤
            prefixDirectionalInformation U y x ky + (c : ENat) ∧
        prefixDirectionalInformation U y x ky ≤
            prefixDirectionalInformation U x y kx + (c : ENat) := by
  obtain ⟨cUpper, cLower, hStage⟩ :=
    KPPair_symmetryOfInformation_staged U hU
  obtain ⟨cSwap, hSwap⟩ := KPPair_symm U hU
  refine ⟨cLower + cSwap + cUpper, ?_⟩
  intro x y kx ky hx hy
  have hxy := hStage x y kx hx
  have hyx := hStage y x ky hy
  constructor
  · calc
      prefixDirectionalInformation U x y kx
          ≤ KPPair U x y + (cLower : ENat) := hxy.2
      _ ≤ (KPPair U y x + (cSwap : ENat)) + (cLower : ENat) := by
        gcongr
        exact hSwap x y
      _ ≤ ((prefixDirectionalInformation U y x ky + (cUpper : ENat)) +
            (cSwap : ENat)) + (cLower : ENat) := by
        gcongr
        exact hyx.1
      _ = prefixDirectionalInformation U y x ky +
            ((cLower + cSwap + cUpper : ℕ) : ENat) := by
        rw [Nat.cast_add, Nat.cast_add]
        ac_rfl
  · calc
      prefixDirectionalInformation U y x ky
          ≤ KPPair U y x + (cLower : ENat) := hyx.2
      _ ≤ (KPPair U x y + (cSwap : ENat)) + (cLower : ENat) := by
        gcongr
        exact hSwap y x
      _ ≤ ((prefixDirectionalInformation U x y kx + (cUpper : ENat)) +
            (cSwap : ENat)) + (cLower : ENat) := by
        gcongr
        exact hxy.1
      _ = prefixDirectionalInformation U x y kx +
            ((cLower + cSwap + cUpper : ℕ) : ENat) := by
        rw [Nat.cast_add, Nat.cast_add]
        ac_rfl

end TimedKt
