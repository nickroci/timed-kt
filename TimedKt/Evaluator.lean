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

* `runBounded_sound`: a success of the evaluator is a `Run` derivation within budget.
* `runBounded_complete`: every `Run` derivation is found at any sufficient budget.
* `runBounded_eq_some_iff`: the two directions packaged as an equivalence.
* `runBounded_isSome_iff` and the resulting `Decidable` instance: **bounded halting
  is decidable** — `∃ T s, Run c n T s ∧ s ≤ b` is decided by running `runBounded`.
* `numSteps_of_runBounded`: a success computes `numSteps` exactly.
* `Kt_cond_le_of_runBounded` / `Kt_le_of_runBounded`: **the certificate pipeline** —
  an evaluator success on an encoded pair `(d, y)` prices the public `Kt_cond` of its
  decoded output, through the timed universal machine, the flagged layer, and the
  embed bridge of the composing machine.
* `Kt_singleton_true_le`, `Kt_singleton_false_le`, `Kt_cond_singleton_true_self_le`:
  concrete certified bounds `Kt [true] ≤ 9`, `Kt [false] ≤ 7`,
  `Kt_cond [true] [true] ≤ 9`.
* `five_le_Kt_cond` and `Kt_cond_nil` / `Kt_nil`: the machine floor `5 ≤ Kt_cond`,
  attained by the empty string — **the first exact value, `Kt [] = 5`**.

Concrete values are machine-relative: these are the composing-machine values (the
flagged-machine numerals are two smaller — one comp-flag bit, one transition inside
the logarithm).
-/

open Nat.Partrec Kolmogorov

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

/-! ### Soundness -/

/-- **Soundness.** A success of the step-budgeted evaluator is an evaluation
derivation, and its transition count fits the budget. -/
theorem runBounded_sound {b : ℕ} {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ}
    (h : runBounded b c n = some (T, s)) : Run c n T s ∧ s ≤ b := by
  induction b generalizing c n T s with
  | zero => simp only [runBounded, reduceCtorEq] at h
  | succ b ih =>
      cases c with
      | zero =>
          simp only [runBounded, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨Run.zero n, by omega⟩
      | succ =>
          simp only [runBounded, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨Run.succ n, by omega⟩
      | left =>
          simp only [runBounded, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨Run.left n, by omega⟩
      | right =>
          simp only [runBounded, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨Run.right n, by omega⟩
      | pair cf cg =>
          simp only [runBounded, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rf, hf, rg, hg, vf, hvf, vg, hvg, _, hle, rfl, rfl⟩ := h
          obtain ⟨hrf, -⟩ := ih hf
          obtain ⟨hrg, -⟩ := ih hg
          exact ⟨Run.pair hrf hrg hvf hvg, hle⟩
      | comp cf cg =>
          simp only [runBounded, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
            Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rg, hg, vg, hvg, rf, hf, _, hle, rfl, rfl⟩ := h
          obtain ⟨hrg, -⟩ := ih hg
          obtain ⟨hrf, -⟩ := ih hf
          exact ⟨Run.comp hrg hvg hrf, hle⟩
      | prec cf cg =>
          simp only [runBounded, Nat.unpaired] at h
          have hn : Nat.pair n.unpair.1 n.unpair.2 = n := Nat.pair_unpair n
          by_cases hm : n.unpair.2 = 0
          · rw [hm] at h
            simp only [Nat.rec_zero, bind, Option.bind_eq_some_iff, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rf, hf, rfl, rfl⟩ := h
            obtain ⟨hrf, hsf⟩ := ih hf
            have key : Run (Code.prec cf cg) (Nat.pair n.unpair.1 0) rf.1 (rf.2 + 1) :=
              Run.precZero hrf
            rw [hm] at hn
            rw [hn] at key
            exact ⟨key, by omega⟩
          · obtain ⟨y, hy⟩ : ∃ y, n.unpair.2 = y + 1 := ⟨n.unpair.2 - 1, by omega⟩
            rw [hy] at h
            simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some',
              Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨ri, hi, vi, hvi, rg, hg, _, hle, rfl, rfl⟩ := h
            obtain ⟨hri, -⟩ := ih hi
            obtain ⟨hrg, -⟩ := ih hg
            have key : Run (Code.prec cf cg) (Nat.pair n.unpair.1 (y + 1))
                (ri.1 ++ rg.1) (ri.2 + rg.2 + 1) := Run.precSucc hri hvi hrg
            rw [hy] at hn
            rw [hn] at key
            exact ⟨key, hle⟩
      | rfind' cf =>
          simp only [runBounded, Nat.unpaired, bind, Option.bind_eq_some_iff] at h
          obtain ⟨rx, hx, x, hgl, h⟩ := h
          have hn : Nat.pair n.unpair.1 n.unpair.2 = n := Nat.pair_unpair n
          obtain ⟨hrx, hsx⟩ := ih hx
          by_cases hx0 : x = 0
          · rw [if_pos hx0, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            subst hx0
            have key : Run (Code.rfind' cf) (Nat.pair n.unpair.1 n.unpair.2)
                (rx.1 ++ [n.unpair.2]) (rx.2 + 1) := Run.rfindFound hrx hgl
            rw [hn] at key
            exact ⟨key, by omega⟩
          · rw [if_neg hx0] at h
            simp only [Option.bind_eq_some_iff, Option.guard_eq_some',
              Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rr, hr, _, hle, rfl, rfl⟩ := h
            obtain ⟨hrr, -⟩ := ih hr
            have key : Run (Code.rfind' cf) (Nat.pair n.unpair.1 n.unpair.2)
                (rx.1 ++ rr.1) (rx.2 + rr.2 + 1) := Run.rfindStep hrx hgl hx0 hrr
            rw [hn] at key
            exact ⟨key, hle⟩

/-! ### Completeness -/

/-- **Completeness.** Every evaluation derivation is found by the evaluator at any
budget that accommodates its transition count — with the exact trace and the exact
count. -/
theorem runBounded_complete {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} (h : Run c n T s) :
    ∀ b, s ≤ b → runBounded b c n = some (T, s) := by
  induction h with
  | zero n =>
      intro b hb
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [runBounded]
  | succ n =>
      intro b hb
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [runBounded]
  | left n =>
      intro b hb
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [runBounded]
  | right n =>
      intro b hb
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [runBounded]
  | @pair cf cg n tf tg vf vg sf sg hf hg hvf hvg ihf ihg =>
      intro b hb
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have h1 := hf.one_le_steps
      have h2 := hg.one_le_steps
      rw [runBounded]
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some']
      exact ⟨(tf, sf), ihf b (by omega), (tg, sg), ihg b (by omega), vf, hvf, vg, hvg,
        (), by omega, rfl⟩
  | @comp cf cg n tg tf vg sg sf hg hvg hf ihg ihf =>
      intro b hb
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have h1 := hg.one_le_steps
      have h2 := hf.one_le_steps
      rw [runBounded]
      simp only [bind, Option.bind_eq_some_iff, Option.guard_eq_some']
      exact ⟨(tg, sg), ihg b (by omega), vg, hvg, (tf, sf), ihf b (by omega),
        (), by omega, rfl⟩
  | @precZero cf cg a t s hs ih =>
      intro b hb
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [runBounded]
      simp only [Nat.unpaired, Nat.unpair_pair, Nat.rec_zero, bind,
        Option.bind_eq_some_iff]
      exact ⟨(t, s), ih b (by omega), rfl⟩
  | @precSucc cf cg a y ti tg vi si sg hi hvi hg ihi ihg =>
      intro b hb
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have h1 := hi.one_le_steps
      have h2 := hg.one_le_steps
      rw [runBounded]
      simp only [Nat.unpaired, Nat.unpair_pair, bind, Option.bind_eq_some_iff,
        Option.guard_eq_some']
      exact ⟨(ti, si), ihi b (by omega), vi, hvi, (tg, sg), ihg b (by omega),
        (), by omega, rfl⟩
  | @rfindFound cf a m tx sx hx hgl ih =>
      intro b hb
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [runBounded]
      simp only [Nat.unpaired, Nat.unpair_pair, bind, Option.bind_eq_some_iff]
      refine ⟨(tx, sx), ih b (by omega), 0, hgl, ?_⟩
      simp
  | @rfindStep cf a m x tx tr sx sr hx hgl hx0 hr ihx ihr =>
      intro b hb
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have h1 := hx.one_le_steps
      have h2 := hr.one_le_steps
      rw [runBounded]
      simp only [Nat.unpaired, Nat.unpair_pair, bind, Option.bind_eq_some_iff]
      refine ⟨(tx, sx), ihx b (by omega), x, hgl, ?_⟩
      rw [if_neg hx0]
      simp only [Option.bind_eq_some_iff, Option.guard_eq_some']
      exact ⟨(tr, sr), ihr b (by omega), (), by omega, rfl⟩

/-! ### The equivalence, decidable bounded halting, and agreement with `numSteps` -/

/-- The evaluator succeeds with `(T, s)` exactly when `Run` derives `(T, s)` within
the budget. -/
theorem runBounded_eq_some_iff {b : ℕ} {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ} :
    runBounded b c n = some (T, s) ↔ Run c n T s ∧ s ≤ b :=
  ⟨runBounded_sound, fun ⟨h, hs⟩ => runBounded_complete h b hs⟩

/-- A success at a smaller budget is a success at every larger budget, unchanged. -/
theorem runBounded_mono {b₁ b₂ : ℕ} {c : Code} {n : ℕ} {r : List ℕ × ℕ}
    (hb : b₁ ≤ b₂) (h : runBounded b₁ c n = some r) : runBounded b₂ c n = some r := by
  obtain ⟨T, s⟩ := r
  obtain ⟨hrun, hs⟩ := runBounded_sound h
  exact runBounded_complete hrun b₂ (le_trans hs hb)

/-- **Bounded halting, semi-packaged**: a derivation within budget exists exactly when
the evaluator succeeds. -/
theorem runBounded_isSome_iff {b : ℕ} {c : Code} {n : ℕ} :
    (∃ T s, Run c n T s ∧ s ≤ b) ↔ (runBounded b c n).isSome = true := by
  constructor
  · rintro ⟨T, s, hrun, hs⟩
    rw [runBounded_complete hrun b hs]
    rfl
  · intro h
    obtain ⟨⟨T, s⟩, hTs⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hrun, hs⟩ := runBounded_sound hTs
    exact ⟨T, s, hrun, hs⟩

/-- **Bounded halting is decidable**: whether `c` on `n` halts within `b` transitions
is decided by running the evaluator. -/
instance decidableRunWithin (b : ℕ) (c : Code) (n : ℕ) :
    Decidable (∃ T s, Run c n T s ∧ s ≤ b) :=
  decidable_of_iff' _ runBounded_isSome_iff

/-- A success of the evaluator computes the transition count `numSteps` exactly. -/
theorem numSteps_of_runBounded {b : ℕ} {c : Code} {n : ℕ} {T : List ℕ} {s : ℕ}
    (h : runBounded b c n = some (T, s)) : numSteps c n = (s : ℕ∞) :=
  numSteps_eq_of_run (runBounded_sound h).1

/-! ### Certificates: from an evaluator success to a public `Kt_cond` bound

An evaluator success is a `Run` derivation (`runBounded_sound`), a `Run` on an
encoded pair `(d, y)` is a clocked universal run on the tape
`unaryPrefix (encode c) ++ d` (`universalRuns_of_run`), a `false` context flag
turns it into a run of the flagged machine, and the embed bridge
(`Kt_cond_le_of_flaggedRuns`) carries it into the public composing measure at one
extra bit and one extra transition. The concrete certificates below evaluate every
component on tiny instances by `rfl`/`simp`/kernel `decide`. -/

/-- Compute `ceilLog2` at explicit positive targets: `ceilLog2 t = k + 1` exactly
when `2 ^ k < t ≤ 2 ^ (k + 1)`. -/
theorem ceilLog2_eq_succ_iff {t k : ℕ} :
    ceilLog2 t = k + 1 ↔ 2 ^ k < t ∧ t ≤ 2 ^ (k + 1) := by
  constructor
  · intro h
    refine ⟨?_, ceilLog2_le_iff.mp h.le⟩
    by_contra hc
    have := ceilLog2_le_iff.mpr (not_lt.mp hc)
    omega
  · rintro ⟨h1, h2⟩
    have hle : ceilLog2 t ≤ k + 1 := ceilLog2_le_iff.mpr h2
    have hgt : ¬ ceilLog2 t ≤ k := fun hc => absurd (ceilLog2_le_iff.mp hc) (not_le.mpr h1)
    omega

/-- The evaluator on the left projection at a paired input. -/
private theorem runBounded_left_pair (b u v : ℕ) :
    runBounded (b + 1) Code.left (Nat.pair u v) = some ([u], 1) := by
  simp only [runBounded, Nat.unpair_pair]

/-- The evaluator on the right projection at a paired input. -/
private theorem runBounded_right_pair (b u v : ℕ) :
    runBounded (b + 1) Code.right (Nat.pair u v) = some ([v], 1) := by
  simp only [runBounded, Nat.unpair_pair]

/-- The evaluator on the successor. -/
private theorem runBounded_succ_eq (b n : ℕ) :
    runBounded (b + 1) Code.succ n = some ([Nat.succ n], 1) := by
  simp only [runBounded]

/-- **Certificate packaging.** An evaluator success on the encoded pair `(d, y)`,
whose trace ends in `r`, is a clocked run of the flagged machine on the tape
`false :: unaryPrefix (encode c) ++ d` with context `y`, producing the decoded
output in `encode c + s + 3` transitions (prefix scan + code run + decode + flag). -/
theorem flaggedRuns_of_runBounded {b : ℕ} {c : Code} {d y : BitString}
    {T : List ℕ} {s r : ℕ}
    (h : runBounded b c (Encodable.encode (d, y)) = some (T, s))
    (hr : T.getLast? = some r) :
    FlaggedRuns (false :: (unaryPrefix (Encodable.encode c) ++ d)) y
      ((Encodable.decode r : Option BitString).getD [])
      (Encodable.encode c + s + 3) := by
  have hU := universalRuns_of_run (runBounded_sound h).1 hr
  exact ⟨false, unaryPrefix (Encodable.encode c) ++ d,
    Encodable.encode c + 1 + s + 1, rfl, hU, by omega⟩

/-- **The certificate bound.** Every evaluator success on an encoded pair `(d, y)`
prices the conditional timed complexity of its decoded output: program side
`encode c + 3 + |d|` bits (unary prefix, both flags, and the input tape), time side
`ceilLog2 (encode c + s + 4)` bits — the flagged certificate carried through the
embed bridge. -/
theorem Kt_cond_le_of_runBounded {b : ℕ} {c : Code} {d y : BitString}
    {T : List ℕ} {s r : ℕ}
    (h : runBounded b c (Encodable.encode (d, y)) = some (T, s))
    (hr : T.getLast? = some r) :
    Kt_cond ((Encodable.decode r : Option BitString).getD []) y ≤
      ((Encodable.encode c + 3 + programLength d
        + ceilLog2 (Encodable.encode c + s + 4) : ℕ) : ENat) := by
  refine le_trans (Kt_cond_le_of_flaggedRuns (flaggedRuns_of_runBounded h hr)) ?_
  refine Nat.cast_le.mpr ?_
  have hcl : Encodable.encode c + s + 3 + 1 = Encodable.encode c + s + 4 := rfl
  rw [hcl]
  have hlen : programLength (false :: (unaryPrefix (Encodable.encode c) ++ d))
      = Encodable.encode c + 2 + programLength d := by
    simp only [programLength, List.length_cons, List.length_append, length_unaryPrefix]
    omega
  omega

/-- The certificate bound at the empty context prices the plain `Kt`. -/
theorem Kt_le_of_runBounded {b : ℕ} {c : Code} {d : BitString} {T : List ℕ} {s r : ℕ}
    (h : runBounded b c (Encodable.encode (d, ([] : BitString))) = some (T, s))
    (hr : T.getLast? = some r) :
    Kt ((Encodable.decode r : Option BitString).getD []) ≤
      ((Encodable.encode c + 3 + programLength d
        + ceilLog2 (Encodable.encode c + s + 4) : ℕ) : ENat) :=
  Kt_cond_le_of_runBounded h hr

/-! ### Concrete certificates

Everything below is evaluated on tiny instances: the evaluator runs by `simp` on its
equations, the encodings reduce by `rfl`/`decide`, and the resulting bounds are
literal numerals. -/

/-- **A concrete certificate: `Kt [true] ≤ 9`.** The left projection `Code.left`
outputs its program tail `[true]`: tape `false :: false :: unaryPrefix 2 ++ [true]`
(6 bits), 7 transitions, `⌈log₂ 7⌉ = 3`. -/
theorem Kt_singleton_true_le : Kt [true] ≤ (9 : ENat) := by
  have h : runBounded 2 Code.left
      (Encodable.encode (([true] : BitString), ([] : BitString)))
      = some ([Encodable.encode ([true] : BitString)], 1) := by
    rw [Encodable.encode_prod_val]
    exact runBounded_left_pair 1 _ _
  have hb := Kt_le_of_runBounded h List.getLast?_singleton
  rw [Encodable.encodek, Option.getD_some] at hb
  have harith : Encodable.encode Code.left + 3 + programLength ([true] : BitString)
      + ceilLog2 (Encodable.encode Code.left + 1 + 4) = 9 := by
    have he : Encodable.encode Code.left = 2 := rfl
    have h7 : ceilLog2 (2 + 1 + 4) = 3 := ceilLog2_eq_succ_iff.mpr (by decide)
    rw [he, h7]
    rfl
  rw [harith] at hb
  exact_mod_cast hb

/-- **A concrete certificate: `Kt [false] ≤ 7`.** The successor `Code.succ` on the
empty tail maps the encoded pair `0` to `1 = encode [false]`: tape
`false :: false :: unaryPrefix 1` (4 bits), 6 transitions, `⌈log₂ 6⌉ = 3`. -/
theorem Kt_singleton_false_le : Kt [false] ≤ (7 : ENat) := by
  have h : runBounded 2 Code.succ
      (Encodable.encode (([] : BitString), ([] : BitString)))
      = some ([Nat.succ (Encodable.encode (([] : BitString), ([] : BitString)))], 1) :=
    runBounded_succ_eq 1 _
  have hb := Kt_le_of_runBounded h List.getLast?_singleton
  have hx : ((Encodable.decode
      (Nat.succ (Encodable.encode (([] : BitString), ([] : BitString))))
      : Option BitString)).getD [] = [false] := by
    have he : Nat.succ (Encodable.encode (([] : BitString), ([] : BitString)))
        = Encodable.encode ([false] : BitString) := rfl
    rw [he, Encodable.encodek, Option.getD_some]
  rw [hx] at hb
  have harith : Encodable.encode Code.succ + 3 + programLength ([] : BitString)
      + ceilLog2 (Encodable.encode Code.succ + 1 + 4) = 7 := by
    have he : Encodable.encode Code.succ = 1 := rfl
    have h6 : ceilLog2 (1 + 1 + 4) = 3 := ceilLog2_eq_succ_iff.mpr (by decide)
    rw [he, h6]
    rfl
  rw [harith] at hb
  exact_mod_cast hb

/-- **A concrete conditional certificate: `Kt_cond [true] [true] ≤ 9`.** The right
projection `Code.right` reads the context through the `false` flags: tape
`false :: false :: unaryPrefix 3` (6 bits), 8 transitions, `⌈log₂ 8⌉ = 3`. -/
theorem Kt_cond_singleton_true_self_le : Kt_cond [true] [true] ≤ (9 : ENat) := by
  have h : runBounded 2 Code.right
      (Encodable.encode (([] : BitString), ([true] : BitString)))
      = some ([Encodable.encode ([true] : BitString)], 1) := by
    rw [Encodable.encode_prod_val]
    exact runBounded_right_pair 1 _ _
  have hb := Kt_cond_le_of_runBounded h List.getLast?_singleton
  rw [Encodable.encodek, Option.getD_some] at hb
  have harith : Encodable.encode Code.right + 3 + programLength ([] : BitString)
      + ceilLog2 (Encodable.encode Code.right + 1 + 4) = 9 := by
    have he : Encodable.encode Code.right = 3 := rfl
    have h8 : ceilLog2 (3 + 1 + 4) = 3 := ceilLog2_eq_succ_iff.mpr (by decide)
    rw [he, h8]
    rfl
  rw [harith] at hb
  exact_mod_cast hb

/-! ### Exactness: the machine floor and the first exact `Kt` value

Every run of the composing machine spends its comp flag on top of a flagged run —
which itself takes at least four transitions (the context flag, the prefix scan, at
least one code transition, and the decode) on at least one program bit — or is a
composition of such runs, which only costs more. So every witness value is at least
`2 + ⌈log₂ 5⌉ = 5`. The empty string attains the floor: the two-bit program
`[false, true]` embeds the flagged one-bit eraser, whose empty tail parses to
`Code.zero` and whose single write `0` decodes to `[]` — five transitions in all.
No enumeration is needed for the matching lower bound — the floor holds for every
string at once. Concrete values are machine-relative; these are the
composing-machine values. -/

/-- Every clocked run of the flagged machine takes at least four transitions: the
context flag, the prefix scan, at least one code transition, and the decode. -/
theorem FlaggedRuns.four_le_time {s y x : BitString} {t : ℕ}
    (h : FlaggedRuns s y x t) : 4 ≤ t := by
  obtain ⟨b, p, t', -, hU, rfl⟩ := h
  obtain ⟨code, T, steps, r, -, hrun, -, -, rfl⟩ := hU
  have := hrun.one_le_steps
  omega

/-- Every program of the flagged machine carries at least the flag bit. -/
theorem FlaggedRuns.one_le_length {s y x : BitString} {t : ℕ}
    (h : FlaggedRuns s y x t) : 1 ≤ programLength s := by
  obtain ⟨b, p, t', rfl, -, -⟩ := h
  simp [programLength]

/-- Every clocked run of the composing machine takes at least five transitions: the
comp flag on top of the flagged floor for an embed node; a composition node spends
its two flag transitions, the gamma scan, and two stages that recursively obey the
floor. -/
theorem CompRuns.five_le_time {s y x : BitString} {t : ℕ}
    (h : CompRuns s y x t) : 5 ≤ t := by
  induction h with
  | embed hF =>
      have := hF.four_le_time
      omega
  | comp _ _ ih₂ ih₁ => omega

/-- Every program of the composing machine carries at least two bits: the comp flag
and the flagged context flag for an embed node, the comp flag and the erase bit for
a composition node. -/
theorem CompRuns.two_le_length {s y x : BitString} {t : ℕ}
    (h : CompRuns s y x t) : 2 ≤ programLength s := by
  cases h with
  | embed hF =>
      have h1 := hF.one_le_length
      simp only [programLength, List.length_cons] at h1 ⊢
      omega
  | comp _ _ => simp [programLength]

/-- **The machine floor**: every conditional timed complexity is at least `5` — two
program bits for the flags and `⌈log₂ 5⌉ = 3` bits for the five mandatory
transitions. -/
theorem five_le_Kt_cond (x y : BitString) : (5 : ENat) ≤ Kt_cond x y := by
  refine le_sInf ?_
  rintro n ⟨p, t, hrun, rfl⟩
  have hp : 2 ≤ programLength p := hrun.two_le_length
  have ht : 5 ≤ t := hrun.five_le_time
  have hlog : 3 ≤ ceilLog2 t := by
    have hmono : ceilLog2 5 ≤ ceilLog2 t := ceilLog2_mono ht
    have h5 : ceilLog2 5 = 3 := ceilLog2_eq_succ_iff.mpr (by decide)
    omega
  exact_mod_cast (by omega : 5 ≤ programLength p + ceilLog2 t)

/-- The machine floor for the plain measure: `5 ≤ Kt x` for every string. -/
theorem five_le_Kt (x : BitString) : (5 : ENat) ≤ Kt x :=
  five_le_Kt_cond x []

/-- The one-bit program `[true]`: the flag erases the context, the empty tail parses
to prefix value `0` — that is, `Code.zero` — and the single write `0` decodes to the
empty string. Four transitions in all. -/
theorem flaggedRuns_nil_output (y : BitString) : FlaggedRuns [true] y [] 4 := by
  refine ⟨true, [], 3, rfl, ?_, rfl⟩
  refine ⟨Code.zero, [0], 1, 0, ?_, Run.zero _, rfl, ?_, rfl⟩
  · have h0 : (List.takeWhile id ([] : BitString)).length
        = Encodable.encode Code.zero := rfl
    rw [h0, Encodable.encodek]
  · have h0 : (0 : ℕ) = Encodable.encode ([] : BitString) := rfl
    rw [h0, Encodable.encodek, Option.getD_some]

/-- The embedded eraser: the two-bit program `[false, true]` runs the flagged
one-bit eraser through the embed node, producing the empty string in five
transitions at every context. -/
theorem compRuns_nil_output (y : BitString) : CompRuns [false, true] y [] 5 :=
  CompRuns.embed (flaggedRuns_nil_output y)

/-- The empty string meets the floor at every context: `Kt_cond [] y ≤ 5`. -/
theorem Kt_cond_nil_le (y : BitString) : Kt_cond [] y ≤ (5 : ENat) := by
  have hb := Kt_cond_le_of_runs (compRuns_nil_output y)
  have harith : programLength ([false, true] : BitString) + ceilLog2 5 = 5 := by
    have h5 : ceilLog2 5 = 3 := ceilLog2_eq_succ_iff.mpr (by decide)
    rw [h5]
    rfl
  rw [harith] at hb
  exact_mod_cast hb

/-- **The first exact `Kt` value**: the empty string attains the machine floor at
every context, `Kt_cond [] y = 5`. -/
theorem Kt_cond_nil (y : BitString) : Kt_cond [] y = 5 :=
  le_antisymm (Kt_cond_nil_le y) (five_le_Kt_cond [] y)

/-- `Kt [] = 5`: the exact timed complexity of the empty string on the composing
machine. -/
theorem Kt_nil : Kt [] = 5 :=
  Kt_cond_nil []

end TimedKt
