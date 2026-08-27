/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.Flagged
import TimedKt.Gamma

/-!
# The Composing Universal Machine — Semantics

The triangle inequality `Kt(x|z) ≤ Kt(x|y) + Kt(y|z) + O(log)` composes two
programs on one tape. On a plain-style (non-prefix-free) program format the split
point must be written down, which is where the logarithmic term comes from; making
the composition a *machine primitive* keeps the rest of the overhead constant,
avoiding both code-wrapping inflation and self-interpretation. This module defines
the machine; its clock is `TimedKt.CompRun`, its computability `TimedKt.CompPartrec`.

The **composing universal machine** `compUniversal` dispatches on the first tape bit:

* `compUniversal (false :: s, z) = flaggedUniversal (s, z)` — the flagged universal
  machine of `TimedKt.Flagged` embedded verbatim;
* `compUniversal (true :: b :: gammaCode ℓ ++ p₁ ++ p₂, z)` with `|p₁| = ℓ` — a
  **composition node**: run `p₂` (recursively) on context `[]` or `z` as the erase
  bit `b` selects, obtaining `y`, then run `p₁` (recursively) on context `y`;
* undefined (`Part.none`) on every other tape — the empty tape, a bare comp flag,
  and any comp tape whose gamma parse fails (`gammaParse` is exact, so this is
  every comp tape not of the displayed form).

The recursion is essential: composing only one level would price the outer program
by a different measure than the one being defined, yielding a mixed statement
rather than a triangle inequality for `Kt`. The comp node's own erase bit is what
keeps the conditioning theorem at additive constant zero after the swap — a plain
witness becomes a conditional witness by flipping the single bit at the root, with
no induction over the tape.

Sub-tapes are strictly shorter than their comp tape, so tape length bounds the
recursion depth: the machine is defined through the fueled evaluator `compEvalFuel`
at fuel `tape length + 1`, and any sufficient fuel computes the same map
(`compEvalFuel_eq_compUniversal`). The unfolding equations are stated per tape
shape (`compUniversal_embed`, `compUniversal_comp_of_parse`, …).
-/

open Kolmogorov

namespace TimedKt

/-- The fueled evaluator of the composing machine. Fuel bounds the recursion depth;
each composition node spends one unit and recurses on strictly shorter tapes, so
fuel `tape length + 1` always suffices (`compEvalFuel_eq_compUniversal`). -/
def compEvalFuel : ℕ → Map
  | 0, _ => Part.none
  | k + 1, sy =>
    match sy with
    | (false :: s, z) => flaggedUniversal (s, z)
    | (true :: b :: r, z) =>
      match gammaParse r with
      | some (ℓ, rest) =>
          (compEvalFuel k (rest.drop ℓ, bif b then [] else z)).bind fun y =>
            compEvalFuel k (rest.take ℓ, y)
      | none => Part.none
    | _ => Part.none

@[simp] theorem compEvalFuel_zero (sy : BitString × BitString) :
    compEvalFuel 0 sy = Part.none := rfl

@[simp] theorem compEvalFuel_nil (k : ℕ) (z : BitString) :
    compEvalFuel (k + 1) ([], z) = Part.none := rfl

@[simp] theorem compEvalFuel_embed (k : ℕ) (s z : BitString) :
    compEvalFuel (k + 1) (false :: s, z) = flaggedUniversal (s, z) := rfl

@[simp] theorem compEvalFuel_flag_nil (k : ℕ) (z : BitString) :
    compEvalFuel (k + 1) ([true], z) = Part.none := rfl

theorem compEvalFuel_comp (k : ℕ) (b : Bool) (r z : BitString) :
    compEvalFuel (k + 1) (true :: b :: r, z) =
      match gammaParse r with
      | some (ℓ, rest) =>
          (compEvalFuel k (rest.drop ℓ, bif b then [] else z)).bind fun y =>
            compEvalFuel k (rest.take ℓ, y)
      | none => Part.none := rfl

/-- The composition step of the fueled evaluator, conditioned on a successful
parse. -/
theorem compEvalFuel_comp_of_parse {r : BitString} {ℓ : ℕ} {rest : BitString}
    (hp : gammaParse r = some (ℓ, rest)) (k : ℕ) (b : Bool) (z : BitString) :
    compEvalFuel (k + 1) (true :: b :: r, z) =
      (compEvalFuel k (rest.drop ℓ, bif b then [] else z)).bind fun y =>
        compEvalFuel k (rest.take ℓ, y) := by
  rw [compEvalFuel_comp, hp]

/-- The composition step of the fueled evaluator, conditioned on a failed parse. -/
theorem compEvalFuel_comp_of_parse_none {r : BitString}
    (hp : gammaParse r = none) (k : ℕ) (b : Bool) (z : BitString) :
    compEvalFuel (k + 1) (true :: b :: r, z) = Part.none := by
  rw [compEvalFuel_comp, hp]

/-- The remainder of a successfully parsed comp tape is strictly shorter than the
tape: the gamma code always spends at least one bit. -/
theorem length_rest_lt_of_gammaParse {r : BitString} {ℓ : ℕ} {rest : BitString}
    (hp : gammaParse r = some (ℓ, rest)) : rest.length < r.length := by
  have h1 := one_le_gammaCode_length ℓ
  rw [eq_gammaCode_append_of_gammaParse hp, List.length_append]
  omega

/-- **Fuel invariance**: any two fuels strictly above the tape length compute the
same value. Strong induction on the tape length; both sub-tapes of a composition
node are strictly shorter. -/
theorem compEvalFuel_eq_of_lt :
    ∀ (n : ℕ) {s z : BitString} {k k' : ℕ}, s.length ≤ n → s.length < k →
      s.length < k' → compEvalFuel k (s, z) = compEvalFuel k' (s, z) := by
  intro n
  induction n with
  | zero =>
      intro s z k k' hn hk hk'
      obtain rfl : s = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k') (by omega)
      rfl
  | succ n ih =>
      intro s z k k' hn hk hk'
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k') (by omega)
      rcases s with - | ⟨hd, tl⟩
      · rfl
      rcases hd
      · rfl
      rcases tl with - | ⟨b, r⟩
      · rfl
      simp only [List.length_cons] at hn hk hk'
      cases hp : gammaParse r with
      | none =>
          rw [compEvalFuel_comp_of_parse_none hp, compEvalFuel_comp_of_parse_none hp]
      | some lr =>
          obtain ⟨ℓ, rest⟩ := lr
          have hrest : rest.length < r.length := length_rest_lt_of_gammaParse hp
          have htake : (rest.take ℓ).length ≤ rest.length := by
            rw [List.length_take]; omega
          have hdrop : (rest.drop ℓ).length ≤ rest.length := by
            rw [List.length_drop]; omega
          have h1 : compEvalFuel k (rest.drop ℓ, bif b then [] else z) =
              compEvalFuel k' (rest.drop ℓ, bif b then [] else z) :=
            ih (by omega) (by omega) (by omega)
          have h2 : ∀ y, compEvalFuel k (rest.take ℓ, y) =
              compEvalFuel k' (rest.take ℓ, y) :=
            fun y => ih (by omega) (by omega) (by omega)
          rw [compEvalFuel_comp_of_parse hp, compEvalFuel_comp_of_parse hp, h1]
          exact congrArg _ (funext h2)

/-- The **composing universal machine**: the fueled evaluator at the canonical fuel
`tape length + 1`, which always suffices. -/
def compUniversal : Map := fun sy => compEvalFuel (sy.1.length + 1) sy

/-- Any fuel strictly above the tape length computes `compUniversal`. -/
theorem compEvalFuel_eq_compUniversal {k : ℕ} {s z : BitString}
    (h : s.length < k) : compEvalFuel k (s, z) = compUniversal (s, z) :=
  compEvalFuel_eq_of_lt s.length le_rfl h (Nat.lt_succ_self _)

@[simp] theorem compUniversal_nil (z : BitString) :
    compUniversal ([], z) = Part.none := rfl

/-- **The embed equation**: on a `false` comp flag the machine is the flagged
universal machine on the rest of the tape, verbatim. -/
@[simp] theorem compUniversal_embed (s z : BitString) :
    compUniversal (false :: s, z) = flaggedUniversal (s, z) := rfl

@[simp] theorem compUniversal_flag_nil (z : BitString) :
    compUniversal ([true], z) = Part.none := rfl

/-- **The composition equation**: on a comp tape with a successful gamma parse, the
machine runs the second block on the selected context and pipes its output into the
first block — both through `compUniversal` itself. -/
theorem compUniversal_comp_of_parse {r : BitString} {ℓ : ℕ} {rest : BitString}
    (hp : gammaParse r = some (ℓ, rest)) (b : Bool) (z : BitString) :
    compUniversal (true :: b :: r, z) =
      (compUniversal (rest.drop ℓ, bif b then [] else z)).bind fun y =>
        compUniversal (rest.take ℓ, y) := by
  have h0 : compUniversal (true :: b :: r, z) =
      compEvalFuel (r.length + 2 + 1) (true :: b :: r, z) := rfl
  rw [h0, compEvalFuel_comp_of_parse hp]
  have hrest : rest.length < r.length := length_rest_lt_of_gammaParse hp
  have h1 : compEvalFuel (r.length + 2) (rest.drop ℓ, bif b then [] else z) =
      compUniversal (rest.drop ℓ, bif b then [] else z) :=
    compEvalFuel_eq_compUniversal (by rw [List.length_drop]; omega)
  have h2 : ∀ y, compEvalFuel (r.length + 2) (rest.take ℓ, y) =
      compUniversal (rest.take ℓ, y) :=
    fun y => compEvalFuel_eq_compUniversal (by rw [List.length_take]; omega)
  rw [h1]
  exact congrArg _ (funext h2)

/-- A comp tape whose gamma parse fails is outside the machine's domain. -/
theorem compUniversal_comp_of_parse_none {r : BitString}
    (hp : gammaParse r = none) (b : Bool) (z : BitString) :
    compUniversal (true :: b :: r, z) = Part.none := by
  have h0 : compUniversal (true :: b :: r, z) =
      compEvalFuel (r.length + 2 + 1) (true :: b :: r, z) := rfl
  rw [h0, compEvalFuel_comp_of_parse_none hp]

end TimedKt
