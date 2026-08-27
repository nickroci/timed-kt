/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import Mathlib.Data.Fintype.BigOperators
import TimedKt.Asymptotic

/-!
# The Probabilistic Layer: `pKt` and Randomness as Context

Probabilistic time-bounded Kolmogorov complexity replaces the single program run by a
**majority over random tapes**: a string is cheap when a short program produces it on
at least two thirds of the uniformly chosen random tapes, within the priced time
bound. The measure is the probabilistic sibling of `Kt`, in the shape of the `rKt` of
I. C. Oliveira (*Randomness and intractability in Kolmogorov complexity*, ICALP 2019)
and the `pKt` of H. Goldberg, V. Kabanets, Z. Lu, and I. C. Oliveira (*Probabilistic
Kolmogorov complexity with applications to average-case complexity*, CCC 2022):
success probability at least `2/3`, description and time priced, randomness free.

On a machine with a context slot no new machinery is needed: the natural convention
is to pass the randomness **as** a distinguished context. A random tape of length `R`
is a function `Fin R → Bool` — a Fintype of cardinality `2 ^ R`
(`card_randomTapes`) — realized as the bitstring `List.ofFn v` and handed to the
flagged machine of `TimedKt.Flagged` through its context argument. `SucceedsOn`
records success of one program on one tape within a time bound; the clock enters only
as an explicit cutoff `∃ t' ≤ t` over the deterministic clocked relation
`FlaggedRuns`, so monotonicity in the bound is definitional (`SucceedsOn.mono`,
`successCountAt_mono`, `HasMajorityAt.mono`).

The counting layer is parameterized by a **context map** `ctx : BitString →
BitString` describing how the tape enters the context: `successCountAt ctx` counts
the length-`R` tapes `v` on which the program succeeds at context `ctx (List.ofFn
v)`, and `HasMajorityAt ctx` asks for two thirds of `2 ^ R`. The identity map gives
the plain probabilistic measure; a map joining a conditioning string with the tape
gives the conditional one. Decidability of success is classical, so the counts are
noncomputable — they are measure ingredients, not algorithms.

## Main definitions

* `SucceedsOn p x t ρ` — some run of the flagged machine on context `ρ` produces `x`
  from `p` within `t` transitions;
* `successCountAt ctx p x t R`, `successCount` — the number of succeeding length-`R`
  tapes, at a context map / at the identity;
* `HasMajorityAt ctx p x t R`, `HasMajority` — success on at least two thirds of the
  `2 ^ R` tapes.

## Main results

* `card_randomTapes` — there are `2 ^ R` random tapes of length `R`;
* `successCount_le` — the count never exceeds the number of tapes;
* `SucceedsOn.mono`, `successCount_mono`, `HasMajority.mono` — monotonicity in the
  time bound, definitional from the cutoff.
-/

open Kolmogorov

namespace TimedKt

/-! ### Random tapes and success -/

/-- There are `2 ^ R` **random tapes** of length `R`: tapes are functions
`Fin R → Bool`, and the Fintype of all of them has cardinality `2 ^ R`. A tape `v`
enters the machine as the bitstring `List.ofFn v`. -/
theorem card_randomTapes (R : ℕ) : Fintype.card (Fin R → Bool) = 2 ^ R := by
  simp

/-- **Success on one tape.** `SucceedsOn p x t ρ`: some run of the flagged machine on
program `p` and context `ρ` produces `x` within `t` transitions. The clock enters
only as the explicit cutoff `∃ t' ≤ t` over the deterministic clocked relation
`FlaggedRuns` — the runs themselves carry exact transition counts, and the
probabilistic layer merely truncates them, so monotonicity in the bound is
definitional. -/
def SucceedsOn (p x : BitString) (t : ℕ) (ρ : BitString) : Prop :=
  ∃ t' ≤ t, FlaggedRuns p ρ x t'

/-- Success is monotone in the time bound: the cutoff only widens. -/
theorem SucceedsOn.mono {p x ρ : BitString} {t₁ t₂ : ℕ} (h : t₁ ≤ t₂)
    (hs : SucceedsOn p x t₁ ρ) : SucceedsOn p x t₂ ρ := by
  obtain ⟨t', ht', hrun⟩ := hs
  exact ⟨t', ht'.trans h, hrun⟩

/-! ### Counting succeeding tapes -/

open Classical in
/-- The **success count at a context map**: the number of length-`R` random tapes `v`
on which `p` produces `x` within `t` transitions, the tape entering the machine
through the context `ctx (List.ofFn v)`. The identity map passes the raw tape;
`pKt_cond` will join a conditioning string with the tape. Success is not decidable,
so the count is classical and noncomputable — an ingredient of a measure, not an
algorithm. -/
noncomputable def successCountAt (ctx : BitString → BitString)
    (p x : BitString) (t R : ℕ) : ℕ :=
  (Finset.univ.filter fun v : Fin R → Bool =>
    SucceedsOn p x t (ctx (List.ofFn v))).card

/-- The success count never exceeds the number of tapes. -/
theorem successCountAt_le (ctx : BitString → BitString) (p x : BitString) (t R : ℕ) :
    successCountAt ctx p x t R ≤ 2 ^ R := by
  classical
  unfold successCountAt
  rw [← card_randomTapes R, ← Finset.card_univ]
  exact Finset.card_filter_le _ _

/-- The success count is monotone in the time bound: every tape succeeding under the
smaller cutoff succeeds under the larger one. -/
theorem successCountAt_mono (ctx : BitString → BitString) (p x : BitString)
    {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) (R : ℕ) :
    successCountAt ctx p x t₁ R ≤ successCountAt ctx p x t₂ R := by
  unfold successCountAt
  refine Finset.card_le_card fun v hv => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact hv.mono h

/-! ### The two-thirds majority -/

/-- **Two-thirds majority at a context map**: `p` produces `x` within `t` transitions
on at least `2/3` of the `2 ^ R` random tapes of length `R`, stated integrally as
`2 * 2 ^ R ≤ 3 * successCountAt`. The threshold is the standard convention of the
probabilistic time-bounded measures. -/
def HasMajorityAt (ctx : BitString → BitString) (p x : BitString) (t R : ℕ) : Prop :=
  2 * 2 ^ R ≤ 3 * successCountAt ctx p x t R

/-- Majority is monotone in the time bound. -/
theorem HasMajorityAt.mono {ctx : BitString → BitString} {p x : BitString}
    {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) {R : ℕ} (hm : HasMajorityAt ctx p x t₁ R) :
    HasMajorityAt ctx p x t₂ R :=
  hm.trans (Nat.mul_le_mul_left 3 (successCountAt_mono ctx p x h R))

/-! ### The identity instance: randomness as the whole context -/

/-- The **success count**: the number of length-`R` random tapes on which `p`
produces `x` within `t` transitions, the tape passed directly as the flagged
machine's context. -/
noncomputable def successCount (p x : BitString) (t R : ℕ) : ℕ :=
  successCountAt id p x t R

/-- **Two-thirds majority** over the length-`R` random tapes. -/
def HasMajority (p x : BitString) (t R : ℕ) : Prop :=
  2 * 2 ^ R ≤ 3 * successCount p x t R

/-- The success count never exceeds the number of tapes. -/
theorem successCount_le (p x : BitString) (t R : ℕ) :
    successCount p x t R ≤ 2 ^ R :=
  successCountAt_le id p x t R

/-- The success count is monotone in the time bound. -/
theorem successCount_mono (p x : BitString) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) (R : ℕ) :
    successCount p x t₁ R ≤ successCount p x t₂ R :=
  successCountAt_mono id p x h R

/-- Majority is monotone in the time bound. -/
theorem HasMajority.mono {p x : BitString} {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) {R : ℕ}
    (hm : HasMajority p x t₁ R) : HasMajority p x t₂ R :=
  HasMajorityAt.mono h hm

end TimedKt
