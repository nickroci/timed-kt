/-
Copyright (c) 2026 Nicholas Holden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Holden
-/
import TimedKt.ListDestruct
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Costed Building Blocks for `Run`

Small `Nat.Partrec.Code` combinators with transition bounds under the `Run` clock, used to
program the Turing-machine simulation of `TimedKt.TMSim`:

* `RunLib.pairStack`, `RunLib.sget`: stacks of naturals built from `Nat.pair`, with `0` as the
  empty stack (so popping the empty stack yields `0` and the empty stack again);
* `RunLib.mux`: evaluate a list of candidate codes and select one by the value of a selector
  code, in time linear in the candidates' costs and the list length (`RunLib.mux_spec`);
* `RunLib.runsLe_const`: the constant code `Code.const n` runs in `2 n + 1` transitions;
* `RunLib.prec_iter`: an invariant-indexed bound for `prec` loops;
* `RunLib.rfind_spec`: the transition count of an unbounded search `rfind'` is the sum of its
  trials;
* `RunLib.pow2_spec`: `m ↦ 2 ^ m` within `27 * 2 ^ m` transitions.

All statements are about the unit-cost `Run` clock.
-/

open Nat.Partrec Nat

namespace TimedKt

namespace RunLib

open ListDestruct

/-! ### Determinism of `RunsLe` -/

/-- Two bounded runs of the same code on the same input have the same output. -/
theorem _root_.TimedKt.ListDestruct.RunsLe.val_unique {c : Code} {n v v' B B' : ℕ}
    (h : RunsLe c n v B) (h' : RunsLe c n v' B') : v = v' := by
  obtain ⟨T, s, hr, hl, -⟩ := h
  obtain ⟨T', s', hr', hl', -⟩ := h'
  obtain ⟨rfl, -⟩ := Run.deterministic hr hr'
  rw [hl] at hl'
  exact Option.some_injective _ hl'

/-- `c` halts on `n` within `B` transitions. -/
def Halts (c : Code) (n B : ℕ) : Prop :=
  ∃ v, RunsLe c n v B

theorem _root_.TimedKt.ListDestruct.RunsLe.halts {c : Code} {n v B : ℕ} (h : RunsLe c n v B) :
    Halts c n B := ⟨v, h⟩

theorem Halts.mono {c : Code} {n B B' : ℕ} (h : Halts c n B) (hB : B ≤ B') : Halts c n B' := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, hv.mono hB⟩

/-! ### Constants -/

/-- `Code.const n` outputs `n` in `2 n + 1` transitions. -/
theorem runsLe_const (n v : ℕ) : RunsLe (Code.const n) v n (2 * n + 1) := by
  induction n with
  | zero => exact runsLe_zero v
  | succ n ih =>
      have := ih.comp (runsLe_succ n)
      exact this.mono (by omega)

/-! ### Pair stacks -/

/-- The pair stack of a list: `pairStack [] = 0`, `pairStack (a :: l) = pair a (pairStack l)`. -/
def pairStack : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.pair a (pairStack l)

@[simp] theorem pairStack_nil : pairStack [] = 0 := rfl

@[simp] theorem pairStack_cons (a : ℕ) (l : List ℕ) :
    pairStack (a :: l) = Nat.pair a (pairStack l) := rfl

/-- The `i`-th entry of a pair stack: `left` after `i` applications of `right`. -/
def sget (s i : ℕ) : ℕ :=
  ((fun s : ℕ => s.unpair.2)^[i] s).unpair.1

@[simp] theorem sget_zero (s : ℕ) : sget s 0 = s.unpair.1 := rfl

theorem sget_succ (s i : ℕ) : sget s (i + 1) = sget s.unpair.2 i := by
  simp only [sget, Function.iterate_succ_apply]

@[simp] theorem sget_pair_zero (a b : ℕ) : sget (Nat.pair a b) 0 = a := by simp

@[simp] theorem sget_pair_succ (a b i : ℕ) : sget (Nat.pair a b) (i + 1) = sget b i := by
  rw [sget_succ, Nat.unpair_pair]

theorem unpair_zero' : (0 : ℕ).unpair = (0, 0) := rfl

@[simp] theorem sget_zero_stack (i : ℕ) : sget 0 i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [sget_succ, unpair_zero', ih]

theorem sget_pairStack (l : List ℕ) (i : ℕ) : sget (pairStack l) i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih => cases i <;> simp [ih]

/-! ### Selection -/

/-- On `pair T i`, output `sget T i`. -/
def pick : Code :=
  .comp .left (.prec Code.id (.comp .right (.comp .right .right)))

theorem pick_iter (T : ℕ) : ∀ i : ℕ,
    RunsLe (.prec Code.id (.comp .right (.comp .right .right))) (Nat.pair T i)
      ((fun s : ℕ => s.unpair.2)^[i] T) (6 * i + 4)
  | 0 => by simpa using (runsLe_id T).precZero
  | i + 1 => by
      have hi := pick_iter T i
      have hg : RunsLe (.comp .right (.comp .right .right))
          (Nat.pair T (Nat.pair i ((fun s : ℕ => s.unpair.2)^[i] T)))
          ((fun s : ℕ => s.unpair.2)^[i + 1] T) 5 := by
        have := ((runsLe_right (Nat.pair T (Nat.pair i ((fun s : ℕ => s.unpair.2)^[i] T)))).comp
          (runsLe_right _)).comp (runsLe_right _)
        simpa [Nat.unpair_pair, Function.iterate_succ_apply'] using this
      exact (hi.precSucc hg).mono (by omega)

theorem pick_spec (T i : ℕ) : RunsLe pick (Nat.pair T i) (sget T i) (6 * i + 6) :=
  ((pick_iter T i).comp (runsLe_left _)).mono (by omega)

/-- The tuple of a list of codes, as a pair stack of their outputs. -/
def tup : List Code → Code
  | [] => .zero
  | c :: cs => .pair c (tup cs)

theorem tup_spec {n B : ℕ} : ∀ {cs : List Code}, (∀ c ∈ cs, Halts c n B) →
    ∃ T, RunsLe (tup cs) n T (cs.length * (B + 1) + 1) ∧
      ∀ (i : ℕ) (c : Code) (w B' : ℕ), cs[i]? = some c → RunsLe c n w B' → sget T i = w
  | [], _ => ⟨0, by simpa [tup] using runsLe_zero n, by simp⟩
  | c :: cs, h => by
      obtain ⟨v, hv⟩ := h c (by simp)
      obtain ⟨T, hT, hget⟩ := tup_spec (cs := cs) (fun c' hc' => h c' (by simp [hc']))
      refine ⟨Nat.pair v T, (hv.pair hT).mono (by simp; nlinarith), ?_⟩
      intro i c' w B' hi hw
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          simpa using hv.val_unique hw
      | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          simpa using hget i c' w B' hi hw

/-- **Multiplexer.** Evaluate every candidate of `cs` and output the one selected by the value
of `sel`. -/
def mux (cs : List Code) (sel : Code) : Code :=
  .comp pick (.pair (tup cs) sel)

/-- The multiplexer runs within the selector's cost, the candidates' costs, and a term linear in
the number of candidates; every candidate must halt (all are evaluated). -/
theorem mux_spec {cs : List Code} {sel c : Code} {n i w Bs B : ℕ}
    (hsel : RunsLe sel n i Bs) (hall : ∀ c ∈ cs, Halts c n B) (hc : cs[i]? = some c)
    (hw : RunsLe c n w B) :
    RunsLe (mux cs sel) n w (Bs + cs.length * (B + 1) + 6 * cs.length + 10) := by
  obtain ⟨T, hT, hget⟩ := tup_spec hall
  have hi : i < cs.length := (List.getElem?_eq_some_iff.mp hc).1
  have := (hT.pair hsel).comp (pick_spec T i)
  rw [hget i c w B hc hw] at this
  exact this.mono (by omega)

theorem forall₂_getElem? {cs : List Code} {ws : List ℕ} {R : Code → ℕ → Prop}
    (h : List.Forall₂ R cs ws) :
    ∀ i, i < cs.length → ∃ c w, cs[i]? = some c ∧ ws[i]? = some w ∧ R c w := by
  induction h with
  | nil => intro i hi; simp at hi
  | @cons c w cs ws hcw _ ih =>
      intro i hi
      cases i with
      | zero => exact ⟨c, w, rfl, rfl, hcw⟩
      | succ i =>
          obtain ⟨c', w', h1, h2, h3⟩ := ih i (by simpa using hi)
          exact ⟨c', w', by simpa using h1, by simpa using h2, h3⟩

/-- **Multiplexer, list form.** With the candidates' outputs listed in `ws`, the multiplexer
outputs `ws.getD i 0` for a selector value `i < |cs|`. -/
theorem mux_spec' {cs : List Code} {ws : List ℕ} {sel : Code} {n i Bs B : ℕ}
    (hsel : RunsLe sel n i Bs) (hcs : List.Forall₂ (fun c w => RunsLe c n w B) cs ws)
    (hi : i < cs.length) :
    RunsLe (mux cs sel) n (ws.getD i 0) (Bs + cs.length * (B + 1) + 6 * cs.length + 10) := by
  obtain ⟨c, w, hc, hw, hcw⟩ := forall₂_getElem? hcs i hi
  have hall : ∀ c ∈ cs, Halts c n B := by
    intro c' hc'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc'
    obtain ⟨c'', w'', h1, -, h3⟩ := forall₂_getElem? hcs j hj
    rw [List.getElem?_eq_getElem hj, Option.some.injEq] at h1
    exact h1 ▸ h3.halts
  rw [List.getD_eq_getElem?_getD, hw, Option.getD_some]
  exact mux_spec hsel hall hc hcw

theorem fa2 {c₁ c₂ : Code} {n w₁ w₂ B : ℕ} (h₁ : RunsLe c₁ n w₁ B) (h₂ : RunsLe c₂ n w₂ B) :
    List.Forall₂ (fun c w => RunsLe c n w B) [c₁, c₂] [w₁, w₂] :=
  .cons h₁ (.cons h₂ .nil)

theorem fa3 {c₁ c₂ c₃ : Code} {n w₁ w₂ w₃ B : ℕ} (h₁ : RunsLe c₁ n w₁ B)
    (h₂ : RunsLe c₂ n w₂ B) (h₃ : RunsLe c₃ n w₃ B) :
    List.Forall₂ (fun c w => RunsLe c n w B) [c₁, c₂, c₃] [w₁, w₂, w₃] :=
  .cons h₁ (.cons h₂ (.cons h₃ .nil))

theorem fa4 {c₁ c₂ c₃ c₄ : Code} {n w₁ w₂ w₃ w₄ B : ℕ} (h₁ : RunsLe c₁ n w₁ B)
    (h₂ : RunsLe c₂ n w₂ B) (h₃ : RunsLe c₃ n w₃ B) (h₄ : RunsLe c₄ n w₄ B) :
    List.Forall₂ (fun c w => RunsLe c n w B) [c₁, c₂, c₃, c₄] [w₁, w₂, w₃, w₄] :=
  .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ .nil)))

/-! ### Loops -/

/-- **`prec` loops.** If the base case produces a value satisfying `P 0` and every step from a
value satisfying `P j` produces one satisfying `P (j + 1)` within `B j` transitions, then the
loop driven `m` times halts within any accumulated bound `C m` with `C 0 ≥ B0 + 1` and
`C (j + 1) ≥ C j + B j + 1`. -/
theorem prec_iter {cf cg : Code} {a B0 : ℕ} (P : ℕ → ℕ → Prop) (B C : ℕ → ℕ)
    (h0 : ∃ v, RunsLe cf a v B0 ∧ P 0 v)
    (hs : ∀ j v, P j v → ∃ v', RunsLe cg (Nat.pair a (Nat.pair j v)) v' (B j) ∧ P (j + 1) v')
    (hC0 : B0 + 1 ≤ C 0) (hCs : ∀ j, C j + B j + 1 ≤ C (j + 1)) :
    ∀ m, ∃ v, RunsLe (.prec cf cg) (Nat.pair a m) v (C m) ∧ P m v
  | 0 => by
      obtain ⟨v, hv, hP⟩ := h0
      exact ⟨v, hv.precZero.mono hC0, hP⟩
  | m + 1 => by
      obtain ⟨v, hv, hP⟩ := prec_iter P B C h0 hs hC0 hCs m
      obtain ⟨v', hv', hP'⟩ := hs m v hP
      exact ⟨v', (hv.precSucc hv').mono (hCs m), hP'⟩

/-- **Unbounded search.** If trial `j` of `rfind' cf` returns `f j` within `B j` transitions and
`m` is the least zero of `f` at or after `s`, the search started at `s` returns `m` within the
summed trial costs. -/
theorem rfind_spec {cf : Code} {a m : ℕ} (f B : ℕ → ℕ)
    (hf : ∀ j, RunsLe cf (Nat.pair a j) (f j) (B j)) (hm : f m = 0)
    (hlt : ∀ j < m, f j ≠ 0) :
    ∀ d s, s + d = m →
      RunsLe (.rfind' cf) (Nat.pair a s) m (∑ j ∈ Finset.Ico s (m + 1), (B j + 1))
  | 0, s, h => by
      subst h
      obtain ⟨T, st, hr, hl, hs⟩ := hf (s + 0)
      rw [hm] at hl
      refine ⟨_, _, Run.rfindFound hr hl, by simp, ?_⟩
      simp only [Nat.add_zero, Nat.Ico_succ_singleton, Finset.sum_singleton]
      simpa using hs
  | d + 1, s, h => by
      have hs' : f s ≠ 0 := hlt s (by omega)
      obtain ⟨T, st, hr, hl, hst⟩ := hf s
      obtain ⟨T', st', hr', hl', hst'⟩ := rfind_spec f B hf hm hlt d (s + 1) (by omega)
      refine ⟨_, _, Run.rfindStep hr hl hs' hr', ?_, ?_⟩
      · rw [List.getLast?_append, hl']
        rfl
      · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
        omega

/-! ### Powers of two -/

/-- `v ↦ 2 v`. -/
def dbl : Code :=
  .comp (.prec .zero (.comp .succ (.comp .succ (.comp .right .right)))) (.pair .zero Code.id)

theorem dbl_spec (v : ℕ) : RunsLe dbl v (2 * v) (8 * v + 8) := by
  have hloop := prec_iter (cf := .zero) (cg := .comp .succ (.comp .succ (.comp .right .right)))
    (a := 0) (B0 := 1) (fun j w => w = 2 * j) (fun _ => 7) (fun j => 8 * j + 2)
    ⟨0, runsLe_zero 0, rfl⟩
    (fun j w hw => ⟨2 * (j + 1), by
      subst hw
      have := (((runsLe_right (Nat.pair 0 (Nat.pair j (2 * j)))).comp (runsLe_right _)).comp
        (runsLe_succ _)).comp (runsLe_succ _)
      simpa [Nat.unpair_pair, Nat.mul_succ] using this, rfl⟩)
    (by omega) (fun j => by omega) v
  obtain ⟨w, hw, rfl⟩ := hloop
  have hin : RunsLe (.pair .zero Code.id) v (Nat.pair 0 v) 5 := (runsLe_zero v).pair (runsLe_id v)
  exact (hin.comp hw).mono (by omega)

/-- `m ↦ 2 ^ m`. -/
def pow2 : Code :=
  .comp (.prec one (.comp dbl (.comp .right .right))) (.pair .zero Code.id)

theorem pow2_spec (m : ℕ) : RunsLe pow2 m (2 ^ m) (27 * 2 ^ m) := by
  have hloop := prec_iter (cf := one) (cg := .comp dbl (.comp .right .right))
    (a := 0) (B0 := 3) (fun j w => w = 2 ^ j) (fun j => 8 * 2 ^ j + 12) (fun j => 21 * 2 ^ j)
    ⟨1, runsLe_one 0, rfl⟩
    (fun j w hw => ⟨2 ^ (j + 1), by
      subst hw
      have := ((runsLe_right (Nat.pair 0 (Nat.pair j (2 ^ j)))).comp (runsLe_right _)).comp
        (dbl_spec _)
      simp only [Nat.unpair_pair] at this
      exact this.of_eq (by rw [Nat.pow_succ, Nat.mul_comm]) (by omega), rfl⟩)
    (by norm_num) (fun j => by have := Nat.one_le_two_pow (n := j); rw [Nat.pow_succ]; omega) m
  obtain ⟨w, hw, rfl⟩ := hloop
  have hin : RunsLe (.pair .zero Code.id) m (Nat.pair 0 m) 5 := (runsLe_zero m).pair (runsLe_id m)
  have h1 := Nat.one_le_two_pow (n := m)
  exact (hin.comp hw).mono (by omega)

end RunLib

end TimedKt
