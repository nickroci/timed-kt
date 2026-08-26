/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import Mathlib.Data.Nat.Log
import Mathlib.Order.Bounds.Basic

/-!
# The Ceiling Base-Two Logarithm

The timed complexity `Kt` prices a run of `t` transitions at `ceilLog2 t` bits, where
`ceilLog2 t` is the least `k` with `t ≤ 2 ^ k`. This module defines `ceilLog2` as
`Nat.clog 2` and proves that characterization (`ceilLog2_isLeast`), rather than
substituting the floor-valued `Nat.log2`.

Convention at zero: `ceilLog2 0 = 0` and `ceilLog2 1 = 0`; the first positive value is
`ceilLog2 2 = 1`. Runs of the timed machines in this package always take at least one
transition, so the value at `0` never prices a run.

The composition lemmas (`ceilLog2_mul_le`, `ceilLog2_linear_le`) bound the price of a
simulated run: a machine that runs in time `a * t + b` costs at most
`ceilLog2 (a + b)` more than one that runs in time `t`. This is the arithmetic behind
the additive constants of the invariance theorem.
-/

namespace TimedKt

/-- The **ceiling base-two logarithm**: the least `k` with `t ≤ 2 ^ k`.
Defined as `Nat.clog 2 t`; the characterization is `ceilLog2_isLeast`. -/
def ceilLog2 (t : ℕ) : ℕ :=
  Nat.clog 2 t

@[simp] theorem ceilLog2_zero : ceilLog2 0 = 0 :=
  Nat.clog_zero_right 2

@[simp] theorem ceilLog2_one : ceilLog2 1 = 0 :=
  Nat.clog_one_right 2

@[simp] theorem ceilLog2_two_pow (k : ℕ) : ceilLog2 (2 ^ k) = k :=
  Nat.clog_pow 2 k Nat.one_lt_two

/-- Every `t` is bounded by two to its ceiling logarithm. -/
theorem le_two_pow_ceilLog2 (t : ℕ) : t ≤ 2 ^ ceilLog2 t :=
  Nat.le_pow_clog Nat.one_lt_two t

/-- `ceilLog2 t ≤ k` exactly when `t ≤ 2 ^ k`. -/
theorem ceilLog2_le_iff {t k : ℕ} : ceilLog2 t ≤ k ↔ t ≤ 2 ^ k :=
  Nat.clog_le_iff_le_pow Nat.one_lt_two

/-- `ceilLog2 t` is the least `k` with `t ≤ 2 ^ k`. This is the defining property
required of the run-time price. -/
theorem ceilLog2_isLeast (t : ℕ) : IsLeast {k | t ≤ 2 ^ k} (ceilLog2 t) :=
  ⟨le_two_pow_ceilLog2 t, fun _ hk => ceilLog2_le_iff.mpr hk⟩

/-- `ceilLog2` is monotone. -/
theorem ceilLog2_mono {a b : ℕ} (h : a ≤ b) : ceilLog2 a ≤ ceilLog2 b :=
  Nat.clog_mono_right 2 h

/-- One extra transition costs at most one bit: `ceilLog2 (t + 1) ≤ ceilLog2 t + 1`
for `t ≥ 1`. -/
theorem ceilLog2_succ_le {t : ℕ} (ht : 1 ≤ t) : ceilLog2 (t + 1) ≤ ceilLog2 t + 1 := by
  refine ceilLog2_le_iff.mpr ?_
  have h := le_two_pow_ceilLog2 t
  have hp : 2 ^ (ceilLog2 t + 1) = 2 ^ ceilLog2 t * 2 := Nat.pow_succ ..
  omega

/-- The ceiling logarithm is subadditive over products. -/
theorem ceilLog2_mul_le (a b : ℕ) : ceilLog2 (a * b) ≤ ceilLog2 a + ceilLog2 b := by
  refine ceilLog2_le_iff.mpr ?_
  calc a * b ≤ 2 ^ ceilLog2 a * 2 ^ ceilLog2 b :=
        Nat.mul_le_mul (le_two_pow_ceilLog2 a) (le_two_pow_ceilLog2 b)
    _ = 2 ^ (ceilLog2 a + ceilLog2 b) := (Nat.pow_add 2 _ _).symm

/-- Pricing a linearly simulated run: for `t ≥ 1`,
`ceilLog2 (a * t + b) ≤ ceilLog2 (a + b) + ceilLog2 t`. The additive overhead of a
time-`a * t + b` simulation is a constant depending only on `a` and `b`. -/
theorem ceilLog2_linear_le {t : ℕ} (a b : ℕ) (ht : 1 ≤ t) :
    ceilLog2 (a * t + b) ≤ ceilLog2 (a + b) + ceilLog2 t := by
  have h : a * t + b ≤ (a + b) * t := by
    have hb : b ≤ b * t := Nat.le_mul_of_pos_right b ht
    calc a * t + b ≤ a * t + b * t := Nat.add_le_add_left hb _
      _ = (a + b) * t := (Nat.add_mul a b t).symm
  calc ceilLog2 (a * t + b) ≤ ceilLog2 ((a + b) * t) := ceilLog2_mono h
    _ ≤ ceilLog2 (a + b) + ceilLog2 t := ceilLog2_mul_le _ _

end TimedKt
