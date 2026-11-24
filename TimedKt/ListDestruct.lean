/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.Run
import Mathlib.Logic.Equiv.List

/-!
# Constant-Cost Destructuring of the List Encoding

Bitstrings reach a `Nat.Partrec.Code` through Mathlib's list encoding
`encode [] = 0`, `encode (b :: l) = succ (pair (encode b) (encode l))`, and `Code` has no
predecessor primitive. A priori, then, reading one cell of an encoded list might cost a number of
`Run` transitions proportional to the encoded *value* (up to `2 ^ |l|`).

This module shows that it does not: three fixed codes compute the nil test, the head bit and the
tail of `encode l`, for **every** `l : List Bool`, each within a literal constant number of `Run`
transitions (`TimedKt.list_destruct_const`, bound `163`; the individual bounds are
`TimedKt.nonNil_runsLe` (`46`), `TimedKt.head_runsLe` (`119`) and `TimedKt.tail_runsLe` (`163`)).

## Why it works

For a cell `b :: t` with `encode b + 1 < encode t` one has
`encode (b :: t) = (encode t)² + (encode b + 1) = pair (encode b + 1) (encode t)`, so `unpair` alone
returns `(encode b + 1, encode t)` (`unpair_encode_cons_generic`). The remaining cells are five
lists of length `≤ 3` (`list_cases`). They are separated by case splits whose
selector is `left` of a list encoding, which is always `≤ 2` (`left_encode_le_two`); a `prec`
whose recursion variable is `≤ 2` is a constant-cost three-way branch (`sw3`, `sw3_spec`).

## Scope

This is a statement about the unit-cost `Run` clock only (one transition per `Code` node, with
`pair`/`unpair` on unbounded naturals at unit cost). It does **not** prove any relation between
`Kt` and Turing-machine `Kt`; in particular, the informal direction `Kt ≤ Kt_TM + O(1)` still
needs a linear-time simulation of a universal Turing machine inside one `Code` under doubling time
budgets, which is not formalized here.
-/

open Nat.Partrec Nat

namespace TimedKt

namespace ListDestruct

/-- `c` run on `n` halts with output `v` within `B` transitions. -/
def RunsLe (c : Code) (n v B : ℕ) : Prop :=
  ∃ T s, Run c n T s ∧ T.getLast? = some v ∧ s ≤ B

theorem RunsLe.mono {c : Code} {n v B B' : ℕ} (h : RunsLe c n v B) (hB : B ≤ B') :
    RunsLe c n v B' := by
  obtain ⟨T, s, hr, hl, hs⟩ := h
  exact ⟨T, s, hr, hl, le_trans hs hB⟩

theorem runsLe_zero (n : ℕ) : RunsLe .zero n 0 1 := ⟨_, _, Run.zero n, rfl, le_rfl⟩
theorem runsLe_succ (n : ℕ) : RunsLe .succ n (n + 1) 1 := ⟨_, _, Run.succ n, rfl, le_rfl⟩
theorem runsLe_left (n : ℕ) : RunsLe .left n n.unpair.1 1 := ⟨_, _, Run.left n, rfl, le_rfl⟩
theorem runsLe_right (n : ℕ) : RunsLe .right n n.unpair.2 1 := ⟨_, _, Run.right n, rfl, le_rfl⟩

theorem RunsLe.pair {cf cg : Code} {n a b Bf Bg : ℕ} (hf : RunsLe cf n a Bf)
    (hg : RunsLe cg n b Bg) : RunsLe (.pair cf cg) n (Nat.pair a b) (Bf + Bg + 1) := by
  obtain ⟨Tf, sf, hf, hlf, hsf⟩ := hf
  obtain ⟨Tg, sg, hg, hlg, hsg⟩ := hg
  exact ⟨_, _, Run.pair hf hg hlf hlg, by simp, by omega⟩

theorem RunsLe.comp {cf cg : Code} {n b c Bf Bg : ℕ} (hg : RunsLe cg n b Bg)
    (hf : RunsLe cf b c Bf) : RunsLe (.comp cf cg) n c (Bf + Bg + 1) := by
  obtain ⟨Tg, sg, hg, hlg, hsg⟩ := hg
  obtain ⟨Tf, sf, hf, hlf, hsf⟩ := hf
  refine ⟨_, _, Run.comp hg hlg hf, ?_, by omega⟩
  rw [List.getLast?_append, hlf]
  rfl

theorem RunsLe.precZero {cf cg : Code} {a v B : ℕ} (h : RunsLe cf a v B) :
    RunsLe (.prec cf cg) (Nat.pair a 0) v (B + 1) := by
  obtain ⟨T, s, hr, hl, hs⟩ := h
  exact ⟨_, _, Run.precZero hr, hl, by omega⟩

theorem RunsLe.precSucc {cf cg : Code} {a y vi v Bi Bg : ℕ}
    (hi : RunsLe (.prec cf cg) (Nat.pair a y) vi Bi)
    (hg : RunsLe cg (Nat.pair a (Nat.pair y vi)) v Bg) :
    RunsLe (.prec cf cg) (Nat.pair a (y + 1)) v (Bi + Bg + 1) := by
  obtain ⟨Ti, si, hi, hli, hsi⟩ := hi
  obtain ⟨Tg, sg, hg, hlg, hsg⟩ := hg
  refine ⟨_, _, Run.precSucc hi hli hg, ?_, by omega⟩
  rw [List.getLast?_append, hlg]
  rfl

theorem runsLe_id (n : ℕ) : RunsLe Code.id n n 3 := by
  have := (runsLe_left n).pair (runsLe_right n)
  rwa [Nat.pair_unpair] at this

/-! ### Constant-cost three-way branch -/

/-- Branch on the value `y ∈ {0, 1, 2}` of `sel`: run `c0`, `c1` or `c2` on the input. -/
def sw3 (c0 c1 c2 sel : Code) : Code :=
  .comp (.prec c0 (.comp (.prec c1 (.comp c2 .left)) (.pair .left (.comp .left .right))))
    (.pair Code.id sel)

/-- The branch selects by `y`; `c0` always runs, `c1` runs when `y ≥ 1` (both are wasted work
when not selected and are charged). -/
theorem sw3_spec {c0 c1 c2 sel : Code} {v y w0 w1 w2 Bs B0 B1 B2 : ℕ}
    (hsel : RunsLe sel v y Bs) (hy : y ≤ 2) (h0 : RunsLe c0 v w0 B0)
    (h1 : 1 ≤ y → RunsLe c1 v w1 B1) (h2 : y = 2 → RunsLe c2 v w2 B2) :
    RunsLe (sw3 c0 c1 c2 sel) v (if y = 0 then w0 else if y = 1 then w1 else w2)
      (Bs + B0 + 2 * B1 + B2 + 30) := by
  unfold sw3
  have hin : RunsLe (.pair Code.id sel) v (Nat.pair v y) (3 + Bs + 1) := (runsLe_id v).pair hsel
  -- the reshuffle `pair v (pair k w) ↦ pair v k`, 5 transitions
  have shuf : ∀ k w, RunsLe (.pair .left (.comp .left .right)) (Nat.pair v (Nat.pair k w))
      (Nat.pair v k) 5 := by
    intro k w
    have := (runsLe_left _).pair ((runsLe_right (Nat.pair v (Nat.pair k w))).comp (runsLe_left _))
    simpa [Nat.unpair_pair] using this
  have p0 : RunsLe (.prec c0 (.comp (.prec c1 (.comp c2 .left)) (.pair .left (.comp .left .right))))
      (Nat.pair v 0) w0 (B0 + 1) := h0.precZero
  rcases (by omega : y = 0 ∨ y = 1 ∨ y = 2) with rfl | rfl | rfl
  · simpa using (hin.comp p0).mono (by omega)
  · have h1' := h1 le_rfl
    have g1 : RunsLe (.comp (.prec c1 (.comp c2 .left)) (.pair .left (.comp .left .right)))
        (Nat.pair v (Nat.pair 0 w0)) w1 (B1 + 1 + 5 + 1) := (shuf 0 w0).comp h1'.precZero
    have p1 := p0.precSucc g1
    simpa using (hin.comp p1).mono (by omega)
  · have h1' := h1 (by norm_num)
    have h2' := h2 rfl
    have g1 : RunsLe (.comp (.prec c1 (.comp c2 .left)) (.pair .left (.comp .left .right)))
        (Nat.pair v (Nat.pair 0 w0)) w1 (B1 + 1 + 5 + 1) := (shuf 0 w0).comp h1'.precZero
    have p1 := p0.precSucc g1
    have hl : RunsLe .left (Nat.pair v (Nat.pair 0 w1)) v 1 := by
      simpa [Nat.unpair_pair] using runsLe_left (Nat.pair v (Nat.pair 0 w1))
    have c2l : RunsLe (.comp c2 .left) (Nat.pair v (Nat.pair 0 w1)) w2 (B2 + 1 + 1) := hl.comp h2'
    have q1 : RunsLe (.prec c1 (.comp c2 .left)) (Nat.pair v (0 + 1)) w2 (B1 + 1 + (B2 + 2) + 1) :=
      h1'.precZero.precSucc c2l
    have g2 : RunsLe (.comp (.prec c1 (.comp c2 .left)) (.pair .left (.comp .left .right)))
        (Nat.pair v (Nat.pair 1 w1)) w2 (B1 + 1 + (B2 + 2) + 1 + 5 + 1) := (shuf 1 w1).comp q1
    have p2 := p1.precSucc g2
    simpa using (hin.comp p2).mono (by omega)

/-! ### Arithmetic of the list encoding -/

/-- The bit value `encode b`. -/
theorem encode_bool_le_one (b : Bool) : Encodable.encode b ≤ 1 := by
  cases b <;> simp [Encodable.encode_true, Encodable.encode_false]

/-- Generic cell: `unpair` alone destructures it. -/
theorem unpair_encode_cons_generic (b : Bool) (t : List Bool)
    (h : Encodable.encode b + 1 < Encodable.encode t) :
    (Encodable.encode (b :: t)).unpair = (Encodable.encode b + 1, Encodable.encode t) := by
  rw [Encodable.encode_list_cons]
  have e1 : Nat.pair (Encodable.encode b) (Encodable.encode t)
      = Encodable.encode t * Encodable.encode t + Encodable.encode b := by
    rw [Nat.pair, if_pos (by omega)]
  have e2 : Nat.pair (Encodable.encode b + 1) (Encodable.encode t)
      = Encodable.encode t * Encodable.encode t + (Encodable.encode b + 1) := by
    rw [Nat.pair, if_pos h]
  rw [show (Nat.pair (Encodable.encode b) (Encodable.encode t)).succ
      = Nat.pair (Encodable.encode b + 1) (Encodable.encode t) by rw [e1, e2]; rfl,
    Nat.unpair_pair]

/-- A list whose encoding is `≤ 2` is `[]`, `[false]` or `[false, false]`. -/
theorem eq_of_encode_le_two {t : List Bool} (h : Encodable.encode t ≤ 2) :
    t = [] ∨ t = [false] ∨ t = [false, false] := by
  have inj := @Encodable.encode_injective (List Bool) _
  rcases (by omega : Encodable.encode t = 0 ∨ Encodable.encode t = 1 ∨ Encodable.encode t = 2)
    with h0 | h1 | h2
  · exact Or.inl (inj (h0.trans rfl))
  · exact Or.inr (Or.inl (inj (h1.trans rfl)))
  · exact Or.inr (Or.inr (inj (h2.trans rfl)))

/-- Every list is `[]`, a generic cell, or one of five short exceptional lists. -/
theorem list_cases (l : List Bool) :
    l = [] ∨ (∃ b t, l = b :: t ∧ Encodable.encode b + 1 < Encodable.encode t) ∨
    l = [false] ∨ l = [true] ∨ l = [false, false] ∨ l = [true, false] ∨
    l = [true, false, false] := by
  rcases l with _ | ⟨b, t⟩
  · exact Or.inl rfl
  by_cases h : Encodable.encode b + 1 < Encodable.encode t
  · exact Or.inr (Or.inl ⟨b, t, rfl, h⟩)
  have hb := encode_bool_le_one b
  rcases eq_of_encode_le_two (t := t) (by omega) with rfl | rfl | rfl <;> cases b <;>
    simp_all +decide [Encodable.encode_false]

/-! Concrete values at `[]` and the five exceptional lists. -/

theorem enc0 : Encodable.encode ([] : List Bool) = 0 := rfl
theorem enc1 : Encodable.encode [false] = 1 := rfl
theorem enc3 : Encodable.encode [true] = 3 := rfl
theorem enc2 : Encodable.encode [false, false] = 2 := rfl
theorem enc4 : Encodable.encode [true, false] = 4 := rfl
theorem enc6 : Encodable.encode [true, false, false] = 6 := rfl

theorem unpair_of_pair {a b n : ℕ} (h : Nat.pair a b = n) : n.unpair = (a, b) :=
  h ▸ Nat.unpair_pair a b

theorem up0 : (0 : ℕ).unpair = (0, 0) := unpair_of_pair rfl
theorem up1 : (1 : ℕ).unpair = (0, 1) := unpair_of_pair rfl
theorem up2 : (2 : ℕ).unpair = (1, 0) := unpair_of_pair rfl
theorem up3 : (3 : ℕ).unpair = (1, 1) := unpair_of_pair rfl
theorem up4 : (4 : ℕ).unpair = (0, 2) := unpair_of_pair rfl
theorem up5 : (5 : ℕ).unpair = (1, 2) := unpair_of_pair rfl
theorem up6 : (6 : ℕ).unpair = (2, 0) := unpair_of_pair rfl
theorem up7 : (7 : ℕ).unpair = (2, 1) := unpair_of_pair rfl

/-- `left` of a list encoding is at most 2. -/
theorem left_encode_le_two (l : List Bool) : (Encodable.encode l).unpair.1 ≤ 2 := by
  rcases list_cases l with rfl | ⟨b, t, rfl, h⟩ | rfl | rfl | rfl | rfl | rfl
  · rw [enc0, up0]; decide
  · rw [unpair_encode_cons_generic b t h]; exact Nat.succ_le_succ (encode_bool_le_one b)
  · rw [enc1, up1]; decide
  · rw [enc3, up3]; decide
  · rw [enc2, up2]; decide
  · rw [enc4, up4]; decide
  · rw [enc6, up6]

/-- `left` of a list encoding vanishes only at the encodings `0, 1, 4`. -/
theorem encode_of_left_eq_zero {l : List Bool} (h : (Encodable.encode l).unpair.1 = 0) :
    Encodable.encode l = 0 ∨ Encodable.encode l = 1 ∨ Encodable.encode l = 4 := by
  rcases list_cases l with rfl | ⟨b, t, rfl, hg⟩ | rfl | rfl | rfl | rfl | rfl
  · rw [enc0]; decide
  · rw [unpair_encode_cons_generic b t hg] at h; simp at h
  · rw [enc1]; decide
  · rw [enc3, up3] at h; exact absurd h (by decide)
  · rw [enc2, up2] at h; exact absurd h (by decide)
  · rw [enc4]; decide
  · rw [enc6, up6] at h; exact absurd h (by decide)

/-! ### The three destructors -/

/-- The constant 1. -/
def one : Code := .comp .succ .zero

theorem runsLe_one (n : ℕ) : RunsLe one n 1 3 := (runsLe_zero n).comp (runsLe_succ 0)

/-- Nil test: `0` on `[]`, `1` on every nonempty list. -/
def nonNilCode : Code := sw3 (.comp (.comp .left .succ) .right) one one .left

/-- Head bit (`encode b` for `b :: t`; `0` on `[]`). -/
def headCode : Code :=
  sw3 (.comp .left .right)
    (sw3 (.comp (.comp .right .right) .right) .zero .zero (.comp .left .right))
    one .left

/-- `t ↦ k t` with `k 0 = 1`, `k 1 = 0`, `k 4 = 4`. -/
def kCode : Code := .pair .zero (.comp .right .succ)

/-- `t ↦ k' t` with `k' 0 = 2`, `k' 4 = 4`. -/
def k'Code : Code := .comp .succ (.comp .succ .right)

/-- Tail (`encode t` for `b :: t`; `0` on `[]`). -/
def tailCode : Code :=
  sw3 (.comp .left .right)
    (sw3 (.comp kCode .right) .right .right (.comp .left .right))
    (sw3 (.comp k'Code .right) .right .right (.comp .left .right)) .left

theorem RunsLe.of_eq {c : Code} {n v v' B B' : ℕ} (h : RunsLe c n v B) (hv : v = v') (hB : B ≤ B') :
    RunsLe c n v' B' := hv ▸ h.mono hB

/-- `right` of a list encoding is again a list encoding. -/
theorem right_encode (l : List Bool) :
    ∃ t : List Bool, (Encodable.encode l).unpair.2 = Encodable.encode t := by
  rcases list_cases l with rfl | ⟨b, t, rfl, h⟩ | rfl | rfl | rfl | rfl | rfl
  · exact ⟨[], by rw [enc0, up0]; try rfl⟩
  · exact ⟨t, by rw [unpair_encode_cons_generic b t h]⟩
  · exact ⟨[false], by rw [enc1, up1]; try rfl⟩
  · exact ⟨[false], by rw [enc3, up3]; try rfl⟩
  · exact ⟨[], by rw [enc2, up2]; try rfl⟩
  · exact ⟨[false, false], by rw [enc4, up4]; try rfl⟩
  · exact ⟨[], by rw [enc6, up6]; try rfl⟩

/-- `left (right v) ≤ 2` on list encodings. -/
theorem left_right_encode_le_two (l : List Bool) :
    ((Encodable.encode l).unpair.2).unpair.1 ≤ 2 := by
  obtain ⟨t, ht⟩ := right_encode l
  rw [ht]; exact left_encode_le_two t

theorem runsLe_leftRight (n : ℕ) : RunsLe (.comp .left .right) n (n.unpair.2.unpair.1) 3 :=
  (runsLe_right n).comp (runsLe_left _)

/-- Generic cells: a generic tail with `left = 0` encodes to `4`. -/
theorem encode_eq_four {b : Bool} {t : List Bool} (h : Encodable.encode b + 1 < Encodable.encode t)
    (h0 : (Encodable.encode t).unpair.1 = 0) : Encodable.encode t = 4 := by
  rcases encode_of_left_eq_zero h0 with h' | h' | h' <;> omega

end ListDestruct

/-! ### Main theorems: constant-cost destructuring -/

open ListDestruct

/-- **Nil test in at most 46 transitions**, for every `l : List Bool`. -/
theorem nonNil_runsLe (l : List Bool) :
    RunsLe nonNilCode (Encodable.encode l) (if l = [] then 0 else 1) 46 := by
  set v := Encodable.encode l with hv
  have h0 : RunsLe (.comp (.comp .left .succ) .right) v ((v.unpair.2 + 1).unpair.1) 5 :=
    (runsLe_right v).comp ((runsLe_succ _).comp (runsLe_left _))
  refine (sw3_spec (runsLe_left v) (left_encode_le_two l) h0 (fun _ => runsLe_one v)
    (fun _ => runsLe_one v)).of_eq ?_ (by norm_num)
  rcases list_cases l with rfl | ⟨b, t, rfl, h⟩ | rfl | rfl | rfl | rfl | rfl
  · rw [hv, enc0]; simp [up1]
  · rw [hv, unpair_encode_cons_generic b t h]; simp
  · rw [hv, enc1]; simp [up1, up2]
  · rw [hv, enc3]; simp [up3]
  · rw [hv, enc2]; simp [up2]
  · rw [hv, enc4]; simp [up3, up4]
  · rw [hv, enc6]; simp [up6]

/-- **Head bit in at most 119 transitions**, for every `l : List Bool`. -/
theorem head_runsLe (l : List Bool) :
    RunsLe headCode (Encodable.encode l) (Encodable.encode (l.headD false)) 119 := by
  set v := Encodable.encode l with hv
  have h0 : RunsLe (.comp .left .right) v (v.unpair.2.unpair.1) 3 := runsLe_leftRight v
  have i0 : RunsLe (.comp (.comp .right .right) .right) v (v.unpair.2.unpair.2.unpair.2) 5 :=
    (runsLe_right v).comp ((runsLe_right _).comp (runsLe_right _))
  have h1 := sw3_spec (c1 := .zero) (c2 := .zero) (w1 := 0) (w2 := 0) (runsLe_leftRight v)
    (left_right_encode_le_two l) i0 (fun _ => runsLe_zero v) (fun _ => runsLe_zero v)
  refine (sw3_spec (runsLe_left v) (left_encode_le_two l) h0 (fun _ => h1)
    (fun _ => runsLe_one v)).of_eq ?_ (by norm_num)
  rcases list_cases l with rfl | ⟨b, t, rfl, h⟩ | rfl | rfl | rfl | rfl | rfl
  · rw [hv, enc0]; simp
  · rw [hv, unpair_encode_cons_generic b t h]
    cases b
    · by_cases hL0 : (Encodable.encode t).unpair.1 = 0
      · have h4 := encode_eq_four h hL0
        simp [h4, up4, up2]
      · simp [hL0]
    · simp
  · rw [hv, enc1]; simp [up1]
  · rw [hv, enc3]; simp [up1, up3]
  · rw [hv, enc2]; simp [up2]
  · rw [hv, enc4]; simp [up2, up4]
  · rw [hv, enc6]; simp [up6]

/-- **Tail in at most 163 transitions**, for every `l : List Bool`. -/
theorem tail_runsLe (l : List Bool) :
    RunsLe tailCode (Encodable.encode l) (Encodable.encode l.tail) 163 := by
  set v := Encodable.encode l with hv
  have h0 : RunsLe (.comp .left .right) v (v.unpair.2.unpair.1) 3 := runsLe_leftRight v
  have k0 : RunsLe (.comp kCode .right) v (Nat.pair 0 ((v.unpair.2 + 1).unpair.2)) 7 :=
    (runsLe_right v).comp ((runsLe_zero _).pair ((runsLe_succ _).comp (runsLe_right _)))
  have k'0 : RunsLe (.comp k'Code .right) v (v.unpair.2.unpair.2 + 1 + 1) 7 :=
    (runsLe_right v).comp (((runsLe_right _).comp (runsLe_succ _)).comp (runsLe_succ _))
  have t1 := sw3_spec (runsLe_leftRight v) (left_right_encode_le_two l) k0
    (fun _ => runsLe_right v) (fun _ => runsLe_right v)
  have t2 := sw3_spec (runsLe_leftRight v) (left_right_encode_le_two l) k'0
    (fun _ => runsLe_right v) (fun _ => runsLe_right v)
  refine (sw3_spec (runsLe_left v) (left_encode_le_two l) h0 (fun _ => t1)
    (fun _ => t2)).of_eq ?_ (by norm_num)
  rcases list_cases l with rfl | ⟨b, t, rfl, h⟩ | rfl | rfl | rfl | rfl | rfl
  · rw [hv, enc0]; simp
  · rw [hv, unpair_encode_cons_generic b t h]
    by_cases hL0 : (Encodable.encode t).unpair.1 = 0
    · have h4 := encode_eq_four h hL0
      cases b <;> simp +decide [h4, up4, up5]
    · cases b <;> simp [hL0]
  · rw [hv, enc1]; simp [up1]
  · rw [hv, enc3]; simp +decide [up1, up2, up3]
  · rw [hv, enc2]; simp +decide [up1, up2]
  · rw [hv, enc4]; simp +decide [up2, up4]
  · rw [hv, enc6]; simp +decide [up6]

/-- **Constant-cost destructuring.** Mathlib's list encoding of bitstrings is destructured in a
constant number of `Run` transitions: fixed codes compute the nil test, the head bit and the tail of
`encode l` for every `l : List Bool`, each within 163 transitions. -/
theorem list_destruct_const (l : List Bool) :
    RunsLe nonNilCode (Encodable.encode l) (if l = [] then 0 else 1) 163 ∧
    RunsLe headCode (Encodable.encode l) (Encodable.encode (l.headD false)) 163 ∧
    RunsLe tailCode (Encodable.encode l) (Encodable.encode l.tail) 163 :=
  ⟨(nonNil_runsLe l).mono (by norm_num), (head_runsLe l).mono (by norm_num), tail_runsLe l⟩

/-! ### Guards

The headline has no hypotheses beyond `l : List Bool`, so no inhabitation witness is owed. The
separating facts below show the case split is needed: the one-node candidates `right` (tail) and
`left ∘ left` (head) are wrong on some list, so the theorem is not met by the naive destructor. -/

namespace ListDestruct

/-- `right` alone is not the tail: on `[false]` it returns `1 = encode [false]`, not `0`. -/
theorem right_not_tail :
    ((Encodable.encode [false]).unpair.2) ≠ Encodable.encode ([false].tail) := by
  rw [enc1, up1]; decide

/-- `left ∘ left` is not the head: on `[true]` it returns `0`, not `1`. -/
theorem leftLeft_not_head :
    ((Encodable.encode [true]).unpair.1.unpair.1) ≠ Encodable.encode ([true].headD false) := by
  rw [enc3, up3, up1]; decide

/-- The clock is live: `tailCode` takes more than one transition on every input
(`Run` of a `comp` costs at least 2). -/
theorem tailCode_cost_ge (n : ℕ) {T : List ℕ} {s : ℕ} (h : Run tailCode n T s) : 2 ≤ s := by
  unfold tailCode sw3 at h
  cases h with
  | comp hg _ hf => have := hg.one_le_length.trans hg.length_le_steps
                    have := hf.one_le_length.trans hf.length_le_steps; omega

end ListDestruct

end TimedKt
