/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.InfoTransfer
import TimedKt.BitCost

/-!
# The Triangle Inequality

The composition theorem for the timed complexity:

```
Kt(x | z) ≤ Kt(x | y) + Kt(y | z) + 3 ⌈log₂ (Kt(x | y) + 1)⌉ + 7.
```

The two optimal witnesses are attained by actual runs
(`TimedDecompressor.exists_runs_condKt`); composing them on one comp tape of the
machine — erase bit `false`, so the outer context flows through — produces `x`
from `z` directly, with the middle value `y` recovered by output determinism. The
description overhead is the two flag bits plus the gamma code of the split point
(`2 ⌈log₂⌉ + 1` bits, `gammaCode_length`), and the time overhead is the ceiling
logarithm of a sum, which exceeds the sum of the ceiling logarithms by at most two
bits (`ceilLog2_add_le`) plus a log-log term that collapses into the constant
(`ceilLog2_two_mul_add_three_le`).

The logarithmic term is necessary for any plain-style (non-prefix-free) program
format: an injective packing of two arbitrary programs into one program must spend
`Ω(log)` bits delimiting the split on some inputs. A uniform additive constant is
the signature of a prefix-free sibling measure, not of plain `Kt` (Li–Vitányi,
*An Introduction to Kolmogorov Complexity and Its Applications*, 3rd ed., §2.1 and
Chapter 7).

The corollary at `z = []` is the easy direction of symmetry of information:
`Kt(x) ≤ Kt(x | y) + Kt(y) + 3 ⌈log₂ (Kt(x | y) + 1)⌉ + 7`
(`Kt_le_Kt_cond_add_Kt`).

The write and bit ledgers compose over the same tape with smaller overhead — the
gamma scan costs transitions but commits nothing — giving `Wt_triangle` and
`Bt_triangle` with `2 ⌈log₂⌉ + 4` in place of `3 ⌈log₂⌉ + 7`.
-/

open Kolmogorov

namespace TimedKt

/-- **The triangle inequality** for the timed complexity, with the explicit constant
`c = 7`: if `Kt(x | y) = n₁` and `Kt(y | z) = n₂`, then
`Kt(x | z) ≤ n₁ + n₂ + 3 ⌈log₂ (n₁ + 1)⌉ + 7`. The logarithmic overhead is the
self-delimitation of the split point — necessary for a plain-style program format —
and the constant absorbs the two flag bits and the log-of-log terms. -/
theorem Kt_triangle : ∃ c : ℕ, ∀ (x y z : BitString) (n₁ n₂ : ℕ),
    Kt_cond x y = (n₁ : ENat) → Kt_cond y z = (n₂ : ENat) →
    Kt_cond x z ≤ ((n₁ + n₂ + 3 * ceilLog2 (n₁ + 1) + c : ℕ) : ENat) := by
  refine ⟨7, fun x y z n₁ n₂ h₁ h₂ => ?_⟩
  have hfin₁ : timedCompUniversal.condKt x y < ⊤ := by
    have hlt : Kt_cond x y < ⊤ := by
      rw [h₁]; exact ENat.natCast_lt_top _
    exact hlt
  have hfin₂ : timedCompUniversal.condKt y z < ⊤ := by
    have hlt : Kt_cond y z < ⊤ := by
      rw [h₂]; exact ENat.natCast_lt_top _
    exact hlt
  obtain ⟨p₁, t₁, hr₁, hc₁⟩ := timedCompUniversal.exists_runs_condKt hfin₁
  obtain ⟨p₂, t₂, hr₂, hc₂⟩ := timedCompUniversal.exists_runs_condKt hfin₂
  have hn₁ : p₁.length + ceilLog2 t₁ = n₁ := by
    have hcast : ((programLength p₁ + ceilLog2 t₁ : ℕ) : ENat) = (n₁ : ENat) := by
      rw [← hc₁]; exact h₁
    exact_mod_cast hcast
  have hn₂ : p₂.length + ceilLog2 t₂ = n₂ := by
    have hcast : ((programLength p₂ + ceilLog2 t₂ : ℕ) : ENat) = (n₂ : ENat) := by
      rw [← hc₂]; exact h₂
    exact_mod_cast hcast
  have hcomp : CompRuns (true :: false :: (gammaCode p₁.length ++ p₁ ++ p₂)) z x
      (t₂ + t₁ + (gammaCode p₁.length).length + 2) :=
    CompRuns.comp (b := false) hr₂ hr₁
  refine le_trans (Kt_cond_le_of_runs hcomp) ?_
  refine Nat.cast_le.mpr ?_
  have hGval : (gammaCode p₁.length).length = 2 * ceilLog2 (p₁.length + 1) + 1 :=
    gammaCode_length p₁.length
  have hlen : programLength (true :: false :: (gammaCode p₁.length ++ p₁ ++ p₂)) =
      (gammaCode p₁.length).length + p₁.length + p₂.length + 2 := by
    simp only [programLength, List.length_cons, List.length_append]
  have harr : t₂ + t₁ + (gammaCode p₁.length).length + 2 =
      t₂ + (t₁ + ((gammaCode p₁.length).length + 2)) := by omega
  have hlog1 : ceilLog2 (t₂ + t₁ + (gammaCode p₁.length).length + 2) ≤
      ceilLog2 t₂ + ceilLog2 (t₁ + ((gammaCode p₁.length).length + 2)) + 1 := by
    rw [harr]
    exact ceilLog2_add_le _ _
  have hlog2 : ceilLog2 (t₁ + ((gammaCode p₁.length).length + 2)) ≤
      ceilLog2 t₁ + ceilLog2 ((gammaCode p₁.length).length + 2) + 1 :=
    ceilLog2_add_le _ _
  have hlog3 : ceilLog2 ((gammaCode p₁.length).length + 2) ≤
      ceilLog2 (p₁.length + 1) + 2 := by
    have hcoll := ceilLog2_two_mul_add_three_le (ceilLog2 (p₁.length + 1))
    have heq : (gammaCode p₁.length).length + 2 =
        2 * ceilLog2 (p₁.length + 1) + 3 := by omega
    rw [heq]
    exact hcoll
  have hmono : ceilLog2 (p₁.length + 1) ≤ ceilLog2 (n₁ + 1) :=
    ceilLog2_mono (by omega)
  simp only [programLength] at hlen ⊢
  omega

/-- **The easy direction of symmetry of information**: `Kt(x) ≤ Kt(x | y) + Kt(y)`
up to the triangle overhead — the triangle inequality at the empty outer context. -/
theorem Kt_le_Kt_cond_add_Kt : ∃ c : ℕ, ∀ (x y : BitString) (n₁ n₂ : ℕ),
    Kt_cond x y = (n₁ : ENat) → Kt y = (n₂ : ENat) →
    Kt x ≤ ((n₁ + n₂ + 3 * ceilLog2 (n₁ + 1) + c : ℕ) : ENat) := by
  obtain ⟨c, hc⟩ := Kt_triangle
  exact ⟨c, fun x y n₁ n₂ h₁ h₂ => hc x y [] n₁ n₂ h₁ h₂⟩

end TimedKt
