/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import Mathlib.Data.Fintype.BigOperators
import TimedKt.Asymptotic

/-!
# The Randomized Layer: `rKt` and Randomness as Context

Randomized time-bounded Kolmogorov complexity replaces the single program run by a
**majority over random tapes**: a string is cheap when a short program produces it on
at least two thirds of the uniformly chosen random tapes, within the priced time
bound. The measure formalized here is **in the style of the `rKt` of I. C. Oliveira**
(*Randomness and intractability in Kolmogorov complexity*, ICALP 2019): the program
is fixed first, the randomness varies, success probability is at least `2/3`,
description and time are priced, randomness is free.

Three differences from Oliveira's `rKt` are deliberate and should be read as part of
the definition:

1. **Machine-relative.** The measure is defined over this package's composing
   universal machine (`TimedKt.Comp`), not over a time-optimal universal randomized
   machine; no invariance or optimality theorem is proved for the randomized
   measure.
2. **Randomness as context.** The random tape enters through the machine's context
   slot as an ordinary bitstring, handed to the run wholesale — not as a separate
   one-way random tape read bit by bit.
3. **Tape length tied to the clock.** A random tape for time bound `t` has length
   exactly `t`: the majority is over `ρ : Fin t → Bool`, all `2 ^ t` of them. This
   is the `rKt` rationale that a `t`-step run consumes at most `t` random bits,
   built into the definition — the tape length is not a separately minimized (and
   unpriced) parameter, so it cannot act as a free side channel of the measure.

The `pKt` of H. Goldberg, V. Kabanets, Z. Lu, and I. C. Oliveira (*Probabilistic
Kolmogorov complexity with applications to average-case complexity*, CCC 2022) is
**not** formalized here: in `pKt` the description may vary with the random string
(for a majority of random strings *there exists* a short program), which is a
different quantifier order from the fixed-program majority above. The citation is a
comparison point, not the model implemented.

A random tape of length `t` is a function `Fin t → Bool` — a Fintype of cardinality
`2 ^ t` (`card_randomTapes`) — realized as the bitstring `List.ofFn ρ` and handed to
the composing machine through its context argument. `SucceedsOn` records success of
one program on one tape within a time bound; the clock enters only as an explicit
cutoff `∃ t' ≤ t` over the deterministic clocked relation `CompRuns`, so per-tape
monotonicity in the bound is definitional (`SucceedsOn.mono`). Count-level
monotonicity in the bound does not survive the tape/clock tie — raising `t` changes
the tape space itself — so the count and majority monotonicity conveniences of an
earlier fixed-length-cutoff draft are gone.

The counting layer is parameterized by a **context map** `ctx : BitString →
BitString` describing how the tape enters the context: `successCountAt ctx` counts
the length-`t` tapes `ρ` on which the program succeeds at context `ctx (List.ofFn
ρ)` within `t` transitions, and `HasMajorityAt ctx` asks for two thirds of `2 ^ t`.
The identity map gives the plain randomized measure; a map joining a conditioning
string with the tape gives the conditional one. Decidability of success is
classical, so the counts are noncomputable — they are measure ingredients, not
algorithms.

The measure `rKtAt ctx x` is the least `|p| + ceilLog2 t` over majorities at `ctx`:
only description and time are priced, and the randomness — `t` bits per candidate
`t` — is free. The public instances are `rKt` (the raw tape as context) and
`rKt_cond` (the context `ctxJoin y ρ`, joining the conditioning string with the tape
through the canonical enumeration `bitStringEnum`).

## Main definitions

* `SucceedsOn p x t ρ` — some run of the composing machine on context `ρ` produces
  `x` from `p` within `t` transitions;
* `successCountAt ctx p x t`, `successCount` — the number of succeeding length-`t`
  tapes, at a context map / at the identity;
* `HasMajorityAt ctx p x t`, `HasMajority` — success on at least two thirds of the
  `2 ^ t` tapes;
* `rKtAt ctx x`, `rKt x`, `rKt_cond x y` — the randomized timed complexity at a
  context map, at the identity, and at the joined context `ctxJoin y`.

## Main results

* `card_randomTapes` — there are `2 ^ t` random tapes of length `t`;
* `successCountAt_le` — the count never exceeds the number of tapes;
* `SucceedsOn.mono` — per-tape monotonicity in the time bound, definitional from
  the cutoff;
* `rKtAt_le_of_hasMajority` — the witness upper bound: any majority prices the
  output;
* `rKt_le_Kt`, `rKt_cond_le_Kt` — **the zero-constant embeddings**: an attained
  `Kt`-witness runs with empty context, so flipping the single erase bit at its root
  (the flagged context flag for an embed node, the comp erase bit for a composition
  node) erases whatever context it receives — it succeeds on *every* random tape of
  its own time bound, a majority of `2 ^ t` out of `2 ^ t`, with the same length and
  transition count. The deterministic measure therefore bounds the randomized one
  with additive constant zero, plain and conditional alike;
* `one_le_rKt`, `rKt_lt_top`, `rKt_cond_lt_top` — positivity (every majority witness
  carries at least the comp flag) and everywhere-finiteness (through the
  embeddings).

## Scope

`rKt_cond x y ≤ rKt x` — conditioning for the randomized measure — is **not** proved
here. The composing machine's erase bits discard the whole context, conditioning
string and randomness together: a plain-randomized witness that actually reads its
random tape cannot be transported to the joined context by the erase bit, and the
context-erasing embedding above only reaches the deterministic `Kt`. The statement
needs a randomness-preserving erase convention — a machine variant that discards the
conditioning string while keeping the tape — which is a further machine-design step,
recorded as open in `COVERAGE.md`. The coding theorem and the average-case theory of
the randomized measures require probability-weighted enumeration and clocked
self-simulation, deliberately out of scope here (clocked self-simulation is the
linear-overhead self-interpreter open item of the invariance layer).
-/

open Kolmogorov

namespace TimedKt

/-! ### Random tapes and success -/

/-- There are `2 ^ t` **random tapes** of length `t`: tapes are functions
`Fin t → Bool`, and the Fintype of all of them has cardinality `2 ^ t`. A tape `ρ`
enters the machine as the bitstring `List.ofFn ρ`. -/
theorem card_randomTapes (t : ℕ) : Fintype.card (Fin t → Bool) = 2 ^ t := by
  simp

/-- **Success on one tape.** `SucceedsOn p x t ρ`: some run of the composing machine
on program `p` and context `ρ` produces `x` within `t` transitions. The clock enters
only as the explicit cutoff `∃ t' ≤ t` over the deterministic clocked relation
`CompRuns` — the runs themselves carry exact transition counts, and the randomized
layer merely truncates them, so per-tape monotonicity in the bound is
definitional. -/
def SucceedsOn (p x : BitString) (t : ℕ) (ρ : BitString) : Prop :=
  ∃ t' ≤ t, CompRuns p ρ x t'

/-- Success on a fixed tape is monotone in the time bound: the cutoff only widens.
(This is the per-tape statement; no count-level analogue exists, because the tape
space itself varies with the bound.) -/
theorem SucceedsOn.mono {p x ρ : BitString} {t₁ t₂ : ℕ} (h : t₁ ≤ t₂)
    (hs : SucceedsOn p x t₁ ρ) : SucceedsOn p x t₂ ρ := by
  obtain ⟨t', ht', hrun⟩ := hs
  exact ⟨t', ht'.trans h, hrun⟩

/-! ### Counting succeeding tapes -/

open Classical in
/-- The **success count at a context map**: the number of length-`t` random tapes `ρ`
on which `p` produces `x` within `t` transitions — the tape length is the time
bound — the tape entering the machine through the context `ctx (List.ofFn ρ)`. The
identity map passes the raw tape; `rKt_cond` will join a conditioning string with
the tape. Success is not decidable, so the count is classical and noncomputable — an
ingredient of a measure, not an algorithm. -/
noncomputable def successCountAt (ctx : BitString → BitString)
    (p x : BitString) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun ρ : Fin t → Bool =>
    SucceedsOn p x t (ctx (List.ofFn ρ))).card

/-- The success count never exceeds the number of tapes. -/
theorem successCountAt_le (ctx : BitString → BitString) (p x : BitString) (t : ℕ) :
    successCountAt ctx p x t ≤ 2 ^ t := by
  classical
  unfold successCountAt
  rw [← card_randomTapes t, ← Finset.card_univ]
  exact Finset.card_filter_le _ _

/-! ### The two-thirds majority -/

/-- **Two-thirds majority at a context map**: `p` produces `x` within `t` transitions
on at least `2/3` of the `2 ^ t` random tapes of length `t`, stated integrally as
`2 * 2 ^ t ≤ 3 * successCountAt`. The threshold is the standard convention of the
randomized time-bounded measures. -/
def HasMajorityAt (ctx : BitString → BitString) (p x : BitString) (t : ℕ) : Prop :=
  2 * 2 ^ t ≤ 3 * successCountAt ctx p x t

/-! ### The identity instance: randomness as the whole context -/

/-- The **success count**: the number of length-`t` random tapes on which `p`
produces `x` within `t` transitions, the tape passed directly as the composing
machine's context. -/
noncomputable def successCount (p x : BitString) (t : ℕ) : ℕ :=
  successCountAt id p x t

/-- **Two-thirds majority** over the length-`t` random tapes. -/
def HasMajority (p x : BitString) (t : ℕ) : Prop :=
  2 * 2 ^ t ≤ 3 * successCount p x t

/-- The success count never exceeds the number of tapes. -/
theorem successCount_le (p x : BitString) (t : ℕ) :
    successCount p x t ≤ 2 ^ t :=
  successCountAt_le id p x t

/-! ### The measure -/

/-- The **randomized timed complexity at a context map**: the least
`|p| + ceilLog2 t` over all programs `p` and time bounds `t` with a two-thirds
majority at `ctx` over the length-`t` tapes, as an `ENat` infimum in the shape of
`condKt`. Only description and time are priced: the randomness — `t` bits per
candidate `t` — is free, and its amount is fixed by the clock rather than minimized
separately. -/
noncomputable def rKtAt (ctx : BitString → BitString) (x : BitString) : ENat :=
  sInf {n | ∃ p t, HasMajorityAt ctx p x t ∧
    ((programLength p + ceilLog2 t : ℕ) : ENat) = n}

/-- The witness upper bound: any majority prices the output. -/
theorem rKtAt_le_of_hasMajority {ctx : BitString → BitString} {p x : BitString}
    {t : ℕ} (h : HasMajorityAt ctx p x t) :
    rKtAt ctx x ≤ ((programLength p + ceilLog2 t : ℕ) : ENat) :=
  sInf_le ⟨p, t, h, rfl⟩

/-- **Randomized timed complexity** `rKt x`: the least `|p| + ceilLog2 t` over
programs producing `x` within `t` transitions on at least two thirds of the random
tapes of length `t`, the tape passed directly as the composing machine's context. -/
noncomputable def rKt (x : BitString) : ENat :=
  rKtAt id x

/-- The **joined context**: the canonical bitstring carrying the conditioning string
`y` alongside the random tape `ρ` — the bitstring enumerated (by `bitStringEnum`) at
the pairing of their encodings. Passing `ctxJoin y ρ` as the context gives the
conditional randomized measure with no machine change: the machine's context slot
carries both the conditioning data and the randomness. -/
def ctxJoin (y ρ : BitString) : BitString :=
  bitStringEnum (Nat.pair (Encodable.encode y) (Encodable.encode ρ))

/-- **Conditional randomized timed complexity** `rKt(x | y)`: the randomized
measure at the joined context — each random tape `ρ` enters the machine as
`ctxJoin y ρ`. -/
noncomputable def rKt_cond (x y : BitString) : ENat :=
  rKtAt (ctxJoin y) x

/-! ### The zero-constant embeddings -/

/-- A program that succeeds on every context has the full success count: all `2 ^ t`
tapes succeed, whatever the context map feeds the machine. -/
theorem successCountAt_eq_two_pow {p x : BitString} {t : ℕ}
    (h : ∀ ρ, SucceedsOn p x t ρ) (ctx : BitString → BitString) :
    successCountAt ctx p x t = 2 ^ t := by
  classical
  unfold successCountAt
  rw [Finset.filter_true_of_mem fun ρ _ => h (ctx (List.ofFn ρ)),
    Finset.card_univ, card_randomTapes]

/-- A program that succeeds on every context has the majority at every context map:
`2 ^ t` of `2 ^ t`. -/
theorem hasMajorityAt_of_forall_succeedsOn {p x : BitString} {t : ℕ}
    (h : ∀ ρ, SucceedsOn p x t ρ) (ctx : BitString → BitString) :
    HasMajorityAt ctx p x t := by
  unfold HasMajorityAt
  rw [successCountAt_eq_two_pow h]
  exact Nat.mul_le_mul (by omega) le_rfl

/-- **The context-erasing witness.** An attained `Kt`-witness runs with empty
context; flipping the single erase bit at its root — the flagged context flag for an
embed node, the comp erase bit for a composition node — yields a program of the same
length that erases whatever context it receives, so it succeeds on *every* random
tape with the same transition count, hence at exactly the `Kt` price. -/
theorem exists_forall_succeedsOn_Kt (x : BitString) :
    ∃ p t, (∀ ρ, SucceedsOn p x t ρ) ∧
      Kt x = ((programLength p + ceilLog2 t : ℕ) : ENat) := by
  obtain ⟨p, t, hrun, heq⟩ :=
    timedCompUniversal.exists_runs_condKt (Kt_lt_top x)
  have heq' : Kt x = ((programLength p + ceilLog2 t : ℕ) : ENat) := heq
  cases hrun with
  | embed hF =>
      obtain ⟨fb, q, t', heq2, hU, rfl⟩ := hF
      have hctx : (bif fb then [] else ([] : BitString)) = ([] : BitString) := by
        cases fb <;> rfl
      rw [hctx] at hU
      refine ⟨false :: true :: q, t' + 1 + 1, fun ρ =>
        ⟨t' + 1 + 1, le_rfl, CompRuns.embed ⟨true, q, t', rfl, hU, rfl⟩⟩, ?_⟩
      subst heq2
      simpa only [programLength, List.length_cons] using heq'
  | comp hp₂ hp₁ =>
      have hctx : ∀ b : Bool, (bif b then [] else ([] : BitString)) = [] := by
        intro b; cases b <;> rfl
      rw [hctx] at hp₂
      refine ⟨_, _, fun ρ =>
        ⟨_, le_rfl, CompRuns.comp (b := true) (z := ρ) hp₂ hp₁⟩, ?_⟩
      simpa only [programLength, List.length_cons] using heq'

/-- **The zero-constant embedding, general form**: `rKtAt ctx x ≤ Kt x` for every
context map. The context-erasing witness succeeds on every random tape of its own
time bound, whatever the context map feeds it, so it has the majority — at the `Kt`
price. -/
theorem rKtAt_le_Kt (ctx : BitString → BitString) (x : BitString) :
    rKtAt ctx x ≤ Kt x := by
  obtain ⟨p, t, hall, heq⟩ := exists_forall_succeedsOn_Kt x
  rw [heq]
  exact rKtAt_le_of_hasMajority (hasMajorityAt_of_forall_succeedsOn hall ctx)

/-- **The deterministic embedding is exact**: `rKt x ≤ Kt x`, with additive constant
zero. A deterministic witness is a randomized one — its erased context makes every
random tape a success. -/
theorem rKt_le_Kt (x : BitString) : rKt x ≤ Kt x :=
  rKtAt_le_Kt id x

/-- **The conditional embedding**: `rKt(x | y) ≤ Kt x`, with additive constant zero —
the erased context makes the joined context `ctxJoin y ρ` irrelevant. -/
theorem rKt_cond_le_Kt (x y : BitString) : rKt_cond x y ≤ Kt x :=
  rKtAt_le_Kt (ctxJoin y) x

/-! ### Positivity and finiteness -/

/-- A majority forces at least one succeeding tape: with none, the count is `0` and
`2 * 2 ^ t ≤ 0` is impossible. -/
theorem HasMajorityAt.exists_succeedsOn {ctx : BitString → BitString}
    {p x : BitString} {t : ℕ} (h : HasMajorityAt ctx p x t) :
    ∃ ρ : Fin t → Bool, SucceedsOn p x t (ctx (List.ofFn ρ)) := by
  classical
  by_contra hno
  have hno' : ∀ ρ : Fin t → Bool, ¬SucceedsOn p x t (ctx (List.ofFn ρ)) :=
    fun ρ hρ => hno ⟨ρ, hρ⟩
  have hzero : successCountAt ctx p x t = 0 := by
    unfold successCountAt
    rw [Finset.filter_false_of_mem fun ρ _ => hno' ρ, Finset.card_empty]
  have h' : 2 * 2 ^ t ≤ 3 * successCountAt ctx p x t := h
  rw [hzero, Nat.mul_zero] at h'
  have hpos := Nat.two_pow_pos t
  omega

/-- Every majority witness program is nonempty: some tape actually runs it, and every
run of the composing machine reads a comp flag. -/
theorem HasMajorityAt.one_le_programLength {ctx : BitString → BitString}
    {p x : BitString} {t : ℕ} (h : HasMajorityAt ctx p x t) :
    1 ≤ programLength p := by
  obtain ⟨ρ, t', -, hrun⟩ := h.exists_succeedsOn
  cases hrun <;> simp [programLength]

/-- **Positivity, general form**: `1 ≤ rKtAt ctx x` — every candidate cost carries at
least the context flag. -/
theorem one_le_rKtAt (ctx : BitString → BitString) (x : BitString) :
    1 ≤ rKtAt ctx x := by
  refine le_sInf fun n hn => ?_
  obtain ⟨p, t, hmaj, rfl⟩ := hn
  have h1 : 1 ≤ programLength p + ceilLog2 t :=
    hmaj.one_le_programLength.trans (Nat.le_add_right _ _)
  exact_mod_cast h1

/-- **Positivity**: `1 ≤ rKt x`. -/
theorem one_le_rKt (x : BitString) : 1 ≤ rKt x :=
  one_le_rKtAt id x

/-- Positivity for the conditional measure. -/
theorem one_le_rKt_cond (x y : BitString) : 1 ≤ rKt_cond x y :=
  one_le_rKtAt (ctxJoin y) x

/-- The randomized measure is everywhere finite, through the embedding and the
finiteness of `Kt`. -/
theorem rKt_lt_top (x : BitString) : rKt x < ⊤ :=
  (rKt_le_Kt x).trans_lt (Kt_lt_top x)

/-- The conditional randomized measure is everywhere finite. -/
theorem rKt_cond_lt_top (x y : BitString) : rKt_cond x y < ⊤ :=
  (rKt_cond_le_Kt x y).trans_lt (Kt_lt_top x)

end TimedKt
