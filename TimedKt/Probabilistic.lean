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

The measure `pKtAt ctx x` is the least `|p| + ceilLog2 t` over majorities at `ctx`,
with the tape length `R` minimized over but **not priced**: randomness is free, only
description and time are priced — the standard `rKt`/`pKt` convention. The public
instances are `pKt` (the raw tape as context) and `pKt_cond` (the context `ctxJoin y
ρ`, joining the conditioning string with the tape through the canonical enumeration
`bitStringEnum`).

## Main definitions

* `SucceedsOn p x t ρ` — some run of the flagged machine on context `ρ` produces `x`
  from `p` within `t` transitions;
* `successCountAt ctx p x t R`, `successCount` — the number of succeeding length-`R`
  tapes, at a context map / at the identity;
* `HasMajorityAt ctx p x t R`, `HasMajority` — success on at least two thirds of the
  `2 ^ R` tapes;
* `pKtAt ctx x`, `pKt x`, `pKt_cond x y` — the probabilistic timed complexity at a
  context map, at the identity, and at the joined context `ctxJoin y`.

## Main results

* `card_randomTapes` — there are `2 ^ R` random tapes of length `R`;
* `successCount_le` — the count never exceeds the number of tapes;
* `SucceedsOn.mono`, `successCount_mono`, `HasMajority.mono` — monotonicity in the
  time bound, definitional from the cutoff;
* `pKtAt_le_of_hasMajority` — the witness upper bound: any majority prices the
  output;
* `pKt_le_Kt`, `pKt_cond_le_Kt` — **the zero-constant embeddings**: an attained
  `Kt`-witness runs with empty context, so flipping its flag to `true` erases
  whatever context it receives — it succeeds on *every* random tape, a majority of
  `2 ^ R` out of `2 ^ R`, with the same length and transition count. The
  deterministic measure therefore bounds the probabilistic one with additive
  constant zero, plain and conditional alike;
* `one_le_pKt`, `pKt_lt_top`, `pKt_cond_lt_top` — positivity (every majority witness
  carries the context flag) and everywhere-finiteness (through the embeddings).

## Scope

`pKt_cond x y ≤ pKt x` — conditioning for the probabilistic measure — is **not**
proved here. The public machine's flag erases the whole context, conditioning string
and randomness together: a plain-probabilistic witness that actually reads its
random tape cannot be transported to the joined context by the flag, and the
context-erasing embedding above only reaches the deterministic `Kt`. The statement
needs a randomness-preserving erase convention — a machine variant that discards the
conditioning string while keeping the tape — which is a further machine-design step,
recorded as open in `COVERAGE.md`. The coding theorem and the average-case theory of
the probabilistic measures require probability-weighted enumeration and clocked
self-simulation, deliberately out of scope here (clocked self-simulation is the
linear-overhead self-interpreter open item of the invariance layer).
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

/-! ### The measure -/

/-- The **probabilistic timed complexity at a context map**: the least
`|p| + ceilLog2 t` over all programs `p`, time bounds `t`, and tape lengths `R` with
a two-thirds majority at `ctx`, as an `ENat` infimum in the shape of `condKt`. The
tape length `R` is minimized over but not priced: randomness is free, only
description and time are priced — the standard convention of the probabilistic
time-bounded measures. -/
noncomputable def pKtAt (ctx : BitString → BitString) (x : BitString) : ENat :=
  sInf {n | ∃ p t R, HasMajorityAt ctx p x t R ∧
    ((programLength p + ceilLog2 t : ℕ) : ENat) = n}

/-- The witness upper bound: any majority prices the output. -/
theorem pKtAt_le_of_hasMajority {ctx : BitString → BitString} {p x : BitString}
    {t R : ℕ} (h : HasMajorityAt ctx p x t R) :
    pKtAt ctx x ≤ ((programLength p + ceilLog2 t : ℕ) : ENat) :=
  sInf_le ⟨p, t, R, h, rfl⟩

/-- **Probabilistic timed complexity** `pKt x`: the least `|p| + ceilLog2 t` over
programs producing `x` within `t` transitions on at least two thirds of the random
tapes of some length, the tape passed directly as the flagged machine's context. -/
noncomputable def pKt (x : BitString) : ENat :=
  pKtAt id x

/-- The **joined context**: the canonical bitstring carrying the conditioning string
`y` alongside the random tape `ρ` — the bitstring enumerated (by `bitStringEnum`) at
the pairing of their encodings. Passing `ctxJoin y ρ` as the context gives the
conditional probabilistic measure with no machine change: the machine's context slot
carries both the conditioning data and the randomness. -/
def ctxJoin (y ρ : BitString) : BitString :=
  bitStringEnum (Nat.pair (Encodable.encode y) (Encodable.encode ρ))

/-- **Conditional probabilistic timed complexity** `pKt(x | y)`: the probabilistic
measure at the joined context — each random tape `ρ` enters the machine as
`ctxJoin y ρ`. -/
noncomputable def pKt_cond (x y : BitString) : ENat :=
  pKtAt (ctxJoin y) x

/-! ### The zero-constant embeddings -/

/-- A program that succeeds on every context has the full success count: all `2 ^ R`
tapes succeed, whatever the context map feeds the machine. -/
theorem successCountAt_eq_two_pow {p x : BitString} {t : ℕ}
    (h : ∀ ρ, SucceedsOn p x t ρ) (ctx : BitString → BitString) (R : ℕ) :
    successCountAt ctx p x t R = 2 ^ R := by
  classical
  unfold successCountAt
  rw [Finset.filter_true_of_mem fun v _ => h (ctx (List.ofFn v)),
    Finset.card_univ, card_randomTapes]

/-- A program that succeeds on every context has the majority at every context map
and every tape length: `2 ^ R` of `2 ^ R`. -/
theorem hasMajorityAt_of_forall_succeedsOn {p x : BitString} {t : ℕ}
    (h : ∀ ρ, SucceedsOn p x t ρ) (ctx : BitString → BitString) (R : ℕ) :
    HasMajorityAt ctx p x t R := by
  unfold HasMajorityAt
  rw [successCountAt_eq_two_pow h]
  exact Nat.mul_le_mul (by omega) le_rfl

/-- **The context-erasing witness.** An attained `Kt`-witness has the form `b :: q`
and runs with empty context; the flag-`true` program `true :: q` erases whatever
context it receives, so it succeeds on *every* random tape — with the same length
and the same transition count, hence at exactly the `Kt` price. -/
theorem exists_forall_succeedsOn_Kt (x : BitString) :
    ∃ p t, (∀ ρ, SucceedsOn p x t ρ) ∧
      Kt x = ((programLength p + ceilLog2 t : ℕ) : ENat) := by
  obtain ⟨p, t, hrun, heq⟩ :=
    timedFlaggedUniversal.exists_runs_condKt (Kt_lt_top x)
  have heq' : Kt x = ((programLength p + ceilLog2 t : ℕ) : ENat) := heq
  have hF : FlaggedRuns p [] x t := hrun
  obtain ⟨b, q, t', rfl, hrun', rfl⟩ := hF
  have hctx : (bif b then [] else ([] : BitString)) = ([] : BitString) := by
    cases b <;> rfl
  rw [hctx] at hrun'
  refine ⟨true :: q, t' + 1,
    fun ρ => ⟨t' + 1, le_rfl, true, q, t', rfl, hrun', rfl⟩, ?_⟩
  simpa only [programLength, List.length_cons] using heq'

/-- **The zero-constant embedding, general form**: `pKtAt ctx x ≤ Kt x` for every
context map. The context-erasing witness succeeds on every random tape, whatever the
context map feeds it, so it has the majority at every tape length — at the `Kt`
price. -/
theorem pKtAt_le_Kt (ctx : BitString → BitString) (x : BitString) :
    pKtAt ctx x ≤ Kt x := by
  obtain ⟨p, t, hall, heq⟩ := exists_forall_succeedsOn_Kt x
  rw [heq]
  exact pKtAt_le_of_hasMajority (hasMajorityAt_of_forall_succeedsOn hall ctx 0)

/-- **The deterministic embedding is exact**: `pKt x ≤ Kt x`, with additive constant
zero. A deterministic witness is a probabilistic one — its erased context makes every
random tape a success. -/
theorem pKt_le_Kt (x : BitString) : pKt x ≤ Kt x :=
  pKtAt_le_Kt id x

/-- **The conditional embedding**: `pKt(x | y) ≤ Kt x`, with additive constant zero —
the erased context makes the joined context `ctxJoin y ρ` irrelevant. -/
theorem pKt_cond_le_Kt (x y : BitString) : pKt_cond x y ≤ Kt x :=
  pKtAt_le_Kt (ctxJoin y) x

/-! ### Positivity and finiteness -/

/-- A majority forces at least one succeeding tape: with none, the count is `0` and
`2 * 2 ^ R ≤ 0` is impossible. -/
theorem HasMajorityAt.exists_succeedsOn {ctx : BitString → BitString}
    {p x : BitString} {t R : ℕ} (h : HasMajorityAt ctx p x t R) :
    ∃ v : Fin R → Bool, SucceedsOn p x t (ctx (List.ofFn v)) := by
  classical
  by_contra hno
  have hno' : ∀ v : Fin R → Bool, ¬SucceedsOn p x t (ctx (List.ofFn v)) :=
    fun v hv => hno ⟨v, hv⟩
  have hzero : successCountAt ctx p x t R = 0 := by
    unfold successCountAt
    rw [Finset.filter_false_of_mem fun v _ => hno' v, Finset.card_empty]
  have h' : 2 * 2 ^ R ≤ 3 * successCountAt ctx p x t R := h
  rw [hzero, Nat.mul_zero] at h'
  have hpos := Nat.two_pow_pos R
  omega

/-- Every majority witness program is nonempty: some tape actually runs it, and every
run of the flagged machine reads a context flag. -/
theorem HasMajorityAt.one_le_programLength {ctx : BitString → BitString}
    {p x : BitString} {t R : ℕ} (h : HasMajorityAt ctx p x t R) :
    1 ≤ programLength p := by
  obtain ⟨v, t', -, b, q, t'', hpq, -, -⟩ := h.exists_succeedsOn
  rw [hpq]
  simp only [programLength, List.length_cons]
  omega

/-- **Positivity, general form**: `1 ≤ pKtAt ctx x` — every candidate cost carries at
least the context flag. -/
theorem one_le_pKtAt (ctx : BitString → BitString) (x : BitString) :
    1 ≤ pKtAt ctx x := by
  refine le_sInf fun n hn => ?_
  obtain ⟨p, t, R, hmaj, rfl⟩ := hn
  have h1 : 1 ≤ programLength p + ceilLog2 t :=
    hmaj.one_le_programLength.trans (Nat.le_add_right _ _)
  exact_mod_cast h1

/-- **Positivity**: `1 ≤ pKt x`. -/
theorem one_le_pKt (x : BitString) : 1 ≤ pKt x :=
  one_le_pKtAt id x

/-- Positivity for the conditional measure. -/
theorem one_le_pKt_cond (x y : BitString) : 1 ≤ pKt_cond x y :=
  one_le_pKtAt (ctxJoin y) x

/-- The probabilistic measure is everywhere finite, through the embedding and the
finiteness of `Kt`. -/
theorem pKt_lt_top (x : BitString) : pKt x < ⊤ :=
  (pKt_le_Kt x).trans_lt (Kt_lt_top x)

/-- The conditional probabilistic measure is everywhere finite. -/
theorem pKt_cond_lt_top (x y : BitString) : pKt_cond x y < ⊤ :=
  (pKt_cond_le_Kt x y).trans_lt (Kt_lt_top x)

end TimedKt
